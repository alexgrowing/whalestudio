package main

import (
	"goquery"
	"strings"
	"ws/monitor"
)

func main() {
	// monitor.Test()
	monitor.Start()
	// test()
	// test2()
}

func test2() {
	ostring := "http://www.rmdown.com/link.php?hash=203b4cd30f33774ad641d04ceadaf15dd2f9719a1ca"
	number := strings.LastIndex(ostring, "http://www.rmdown.com")
	newString := ostring[number:len(ostring)]
	println(newString)
}

func test() {
	var bigText = `<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.0 Transitional//EN">
	<html>
	<head>
	<title>File-Save 2009</title>
	<meta http-equiv="Content-Type" content="text/html; charset=utf-8">
	<style type="text/css">
	body,td,th {color: #004080;font-family:Verdana;font-size:12px;}
	body {background-color: #888888;padding:0;margin:0}
	a{color: #006600;text-decoration: none;}
	a:hover{text-decoration:underline;}
	.btn{padding:5px 20px;margin-top:5px;width:120px;}
	.container {width:100%;max-width:800px;}
	.list {padding-bottom:20px;}
	.list a{display:block;margin-top:20px;}
	.list img{width:100%;max-width:760px;max-height:90px;}
	.list li{list-style:none;width:100%;max-width:760px;height:90px;margin-top:20px;display:table;border:1px #003366 solid}
	.list ul{display:table-cell;vertical-align:middle;text-align:center;line-height:150%;padding:0px;}
	#foo1ter { position: fixed; bottom: 0;width: 100%; background-color:#ED4C67}
	#foo1ter li{list-style:none;text-align:center;font-size:2em;color: white; padding:10px;}
	</style>
	</head>
	<body>
	<BR>
	
	<script src="//cdn.jsdelivr.net/npm/jquery@3.2.1/dist/jquery.min.js"></script>
	<SCRIPT LANGUAGE="JavaScript">
	var rmJson = '[{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2018\/384\/982\/9460289483_1746120392.jpg","u":"https:\/\/www.lul8.com\/jiba123.htm"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2018\/510\/234\/9439432015_1746120392.jpg","u":"https:\/\/1156.xgcsgs.net\/feng88.htm"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/343\/047\/11109740343_1746120392.jpg","u":"http:\/\/wvw.baidu-jxf.co\/77577.html"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2018\/454\/444\/9439444454_1746120392.jpg","u":"https:\/\/www.0937js.com\/dxiazai.html"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/937\/626\/10289626739_1746120392.jpg","u":"https:\/\/www.e5yx.com\/caoliu1.html"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2018\/444\/980\/9641089444_1746120392.jpg","u":"https:\/\/www.lady177.com\/ylcgg3.htm"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/245\/283\/12791382542_255861743.jpg","u":"https:\/\/www.22588888.com\/sd11\/"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2018\/292\/534\/9439435292_1746120392.jpg","u":"https:\/\/www.ok9803.com\/caoliu33.html"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/695\/920\/10276029596_1746120392.jpg","u":"https:\/\/www.jjy118.com\/ffgg06.htm"},{"i":"http:\/\/21511.ua96.com\/images\/760x100.gif","u":"http:\/\/www.hhy36.com"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/123\/342\/10837243321_1746120392.jpg","u":"https:\/\/www.0710522.com\/baidu\/"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/751\/848\/12778848157_1980598585.jpg","u":"https:\/\/www.h6295.com\/a001\/"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2019\/608\/074\/12432470806_1980598585.jpg","u":"https:\/\/www.xdh0808.com\/bygg26.htm"},{"i":"https:\/\/www.x6img.com\/u\/20191207\/13005723.gif","u":"https:\/\/clgoes.com\/"},{"i":"https:\/\/cbu01.alicdn.com\/img\/ibank\/2020\/356\/532\/20910235653_1980598585.jpg","u":"https:\/\/www.361dai.com\/daili08.htm"},{"i":"https:\/\/ae04.alicdn.com\/kf\/Hb393cf05c0424b07b80aafe543620205i.jpg","u":"https:\/\/ppj8.cc"},{"i":"http:\/\/bvmqkla.de\/files\/photo\/2020\/12\/21\/85a5d8f719f34f2c9fc362f77b2716f5.gif","u":"https:\/\/site.tea123.me\/?code=tcp6&c=681"}]';
	var poJson = '[{"u":"https:\/\/www.lelechen.com\/av12com.htm"},{"u":"https:\/\/1156.xgcsgs.net\/feng88.htm"},{"u":"https:\/\/do.uaj3eyef8s.net\/do34.php"}]';var dlData = '<li><ul>Code: 203a6505e9a8a8f7f6d57f86657c8604a9196ee61c2<br>Downloaded: 1<br><INPUT class="btn" type="button" value="MAGNET" onclick="magnet()">銆€<INPUT class="btn" type="submit" value="DOWNLOAD"></ul></li>';
	var rmData = JSON.parse(rmJson);
	var poData = JSON.parse(poJson);
	
	var ert6j = false;
	function dpos(form){
		var imgs = document.getElementsByTagName('img');
		if(imgs[0].height==0){
			alert('璇峰叧闂�箍鍛婂睆钄芥彃浠讹紙濡侫DBLOCK锛夊啀灏濊瘯涓嬭浇');
			return false;
		}
		if(ert6j){
			alert('璇峰叧闂�箍鍛婂睆钄芥彃浠讹紙濡倁Block锛夊啀灏濊瘯涓嬭浇');
			return false;
		}
		if($("img:eq(0)").css('visibility')=='collapse'){
			alert('璇峰叧闂�箍鍛婂睆钄芥彃浠讹紙濡倁Block锛夊啀灏濊瘯涓嬭浇');
			return false;
		}
		if(poData){
			var ider = Math.floor(Math.random() * poData.length);
			window.open(poData[ider].u);
		}
		return true;
	}
	
	function initDownload(){
		if(rmData){
			var ider = Math.floor(Math.random() * rmData.length);
			rmData.forEach(function(item, index){
				var dl = index==ider ? dlData : '';
				document.write('<a href="'+item.u+'" target="_blank"><img src="'+item.i+'"></a>' + dl);
			});
		}else{
			document.write(dlData);
		}
	}
	
	function magnet(){
		if(poData){
			var ider = Math.floor(Math.random() * poData.length);
			window.open(poData[ider].u);
		}
		var code = '203a6505e9a8a8f7f6d57f86657c8604a9196ee61c2';
		$.get( "download.php", { action: "magnet", ref: code })
		.done(function( data ) {
			if(data=='1'){
				setTimeout(function(){
					window.open('magnet:?xt=urn:btih:'+code.substr(3), '_self');
				}, 1000);
			}else{
				document.write(data);
			}
		});
	}
	</SCRIPT>
	
	<FORM action='download.php' method='get' onsubmit='return dpos()'>
	<INPUT TYPE="hidden" NAME="reff" value="805669684d23918ac7">
	<INPUT TYPE="hidden" name="ref" value="203a6505e9a8a8f7f6d57f86657c8604a9196ee61c2">
	<TABLE cellspacing=1 cellpadding=1 width='800' bgcolor='#003366' align="center" class="container">
	<TR>
		<TD bgcolor="#CFE2CD" height="50" align="center"><span style="font-size:24px"><B>File-Save 2009</B></span></TD>
	</TR>
	<TR>
		<TD bgcolor="white" align="center" class="list">
			<script type="text/javascript">initDownload();</script>
		</TD>
	</TR>
	</TABLE>
	</FORM>
	<div id="foo1ter"><li>鎮ㄧ殑娴忚�鍣ㄥ凡灞忚斀姝ら〉闈�笂鐨勫箍鍛婏紝RMDOWN绱�� 鍏嶈垂 鎻愪緵涓嬭浇 15 骞� 2 澶╋紝缃戠珯鐨勭淮鎶ら渶瑕佸箍鍛婂晢鐨勮禐鍔╋紝璇峰皢鎴戜滑鐨勭綉绔欐坊鍔犲埌骞垮憡灞忚斀杞�欢鐨勭櫧鍚嶅崟锛屾槸瀵规垜浠�渶澶х殑鏀�寔</li></div>
	<script type="text/javascript">
	$("li:eq(1)").css('display', 'none');
	$("img:eq(1)").on("error", function(){
		$("li:eq(1)").css('display', '');
	});
	$("img:eq(0)").on("load", function(){
		if($(this).css('visibility')=='collapse'){
			ert6j = true;
		}
	});
	</script>
	<center>Illegal files report: <a href="ticket.php">Contact us</a>, we will remove it asap, thanks!<BR>
	Copyright @ 2007-2009 <a href="./">Torrent File Save</a>. All rights reserved (Version 2.1)</center><br>
	</body>
	</html>
	`

	if doc, err := goquery.NewDocumentFromReader(strings.NewReader(bigText)); err != nil {
		println(err.Error())
	} else {
		anchors := doc.Find("td.list ul")
		println(anchors.Text())
	}
}
