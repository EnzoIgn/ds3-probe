# DS3 Probe

Appli de diagnostic **en lecture seule** pour autoradio Android (UIS7862S, Android 15, boîtier CANBUS Raise, Citroën DS3).
Le but est de comprendre comment l'écran reçoit les données de la voiture, sans prise OBD et sans ADB.

## Installer

Sur l'autoradio, ouvre le navigateur et télécharge :

`https://github.com/EnzoIgn/ds3-probe/releases/latest/download/ds3-probe.apk`

Ouvre ensuite le fichier pour l'installer.

## Utiliser

1. **1. Scanner** : liste les applis constructeur et CANBUS, leurs composants, les actions de broadcast et les URI trouvées dans leur code, les fournisseurs de contenu lisibles, les propriétés système et les ports série.
2. **2. Écouter** : s'abonne à toutes les actions trouvées. Ouvre une portière, passe la marche arrière, allume les phares, puis appuie sur **Arrêter**.
3. Récupère le rapport :
   - depuis l'iPhone connecté au même Wi-Fi, avec l'adresse affichée en haut (`http://IP:8080/ds3probe.txt`) ;
   - ou avec **Enregistrer**, qui crée le fichier dans `Download/`.
4. **4. Ordi de bord** (moteur allumé) : écoute les trames brutes du boîtier Raise via le service système `mcu_service`
   et décode l'ordinateur de bord PSA (autonomie, conso instantanée et moyenne, trajets, température extérieure).
   Les valeurs s'affichent en direct en jaune. Réappuie pour arrêter.

L'appli ne modifie rien et n'ouvre aucun port série.
