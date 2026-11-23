import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMove

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerCarry

open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem sideB_facts {D : D7} {cf Rw Pq} {S : RatDat D.ntw} {hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ) {eF}
    (h : eF = B.eF) : HkLaw D S eF hL B.hs B.cHk ∧ LowIn D ∧ PqLaw B.exp Pq := by
  subst h
  refine ⟨B.hkEq, fun i p hp P hP => ?_, B.pq⟩
  rw [B.tw.ringSpec_excludedPlaces_eq i]
  exact Or.inr (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes i p hp hP)

theorem st_facts {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : LI hL x) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) :
    HkAd (sideAt x g hg a) l.rat.In.Sb ((l.rat.In.hL)) ∧ KeepsMat (D := Dof x) fun i => (l.mt.ad.PV i).ψ :=
  ⟨kc% l.rat.rat.hecke, x.r.Y.hF, l.mt.ad.id⟩

theorem series_restage : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : LI hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _ cHk hc
  obtain ⟨ι', e', h, hcf, hPq, g, g'', hg, hg'', a, a'', ⟨m⟩⟩ := GlobalTheory.HeightCounting.SerGlue.exists_move hKP hF hS' hO hB hE hf hSt hpx hsel hJ hδ
    x lb.toLI.toLA hExt x' hG N hN x'' l''.toLA ho
  obtain ⟨H, hp⟩ := st_facts lb.toLI g hg a
  obtain ⟨H', hp'⟩ := st_facts l'' g'' hg'' a''
  obtain ⟨L, hl, hq⟩ := sideB_facts lb.b.Bs lb.b.eF
  kexactB (series_move h m (kc% x.m.z.geo) (kc% x''.m.z.geo) (kKs := kc% lb.rat.kKs) (hk := kc% lb.rat.hk) (kc% l''.rat.kKs)
    (kc% l''.rat.hk) (kc% lb.b.YS) (kc% lb.b.fi) hl lb.rat.rat.Sb_le l''.rat.rat.Sb_le H H' (hs := kc% lb.b.Bs.hs) (c := lb.b.Bs.cHk)
    (kc% l''.rat.In.hs) (c' := cHk) hc (kc% L) hcf lb.a.A.chr l''.a.A.chr hp hp' hPq hq lb.b.tau (kc% lb.b.ser))

end GlobalTheory.HeightCounting.SerCarry

end
