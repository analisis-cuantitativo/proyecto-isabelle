FROM node:22-alpine AS build

WORKDIR /app

COPY package.json ./

RUN npm install

COPY . .

RUN npm run build

FROM nginx:alpine

COPY --from=build /app/dist /usr/share/nginx/html

COPY nginx.conf.template /etc/nginx/templates/default.conf.template

# Local docker-compose default; override with the backend's Render-internal
# "host:port" in production (see render.yaml).
ENV BACKEND_ADDR=backend:8000

EXPOSE 80

CMD ["nginx", "-g", "daemon off;"]
