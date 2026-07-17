FROM node:22-alpine as build

WORKDIR /app

COPY package.json package-lick.json* ./

RUN npm install

COPY . .

RUN npm run build

FROM ngix:apline

COPY --from=build /app/dist /usr/share/ngix/html

COPY nginx.conf /etc/nginx/conf.d/default.conf

EXPOSE 80

CMD ["ngixnx", "-g", "daemon off;"]
