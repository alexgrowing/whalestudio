import Formalism.LocalToGlobal.Columns.TiedFv
import Formalism.LocalToGlobal.Columns.LevPackFrLat

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

def fvMeW (w : HeightOneSpectrum (𝓞 X.F)) (P : Pr.vT u) (hov : IsOver w P.1) :
    fMod hc n (Pr.vT u) w ≃+ (𝓞 X.E ⧸ P.1.asIdeal) :=
  fvMeL hc n w (basePi_of_ok hX hPr u) P.2 hov ((basePi_of_ok hX hPr u).over_unique hc P.2 hov) _ _ (fv_unit hPr u c₀ P)

theorem fv_tieW (w : HeightOneSpectrum (𝓞 X.F)) (P : Pr.vT u) (hov : IsOver w P.1)
    (y : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (hyU : y ∈ UAd hc n) (d : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hd : decoOfD n (Pr.vT u) Pr.vGs c₀ y = d) (z : Sp X.E n) (hzL : z ∈ d.1.Lsh) (t : baseDualV hc n (Pr.vT u) w)
    (ht : ((bc (prV (E := X.E) w) y : GL (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin n) (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun a => inclE (F := X.F) (w.adicCompletion X.F) (z a)) :
    d.1.f P z = fvMeW hc hX hPr u c₀ w P hov (fLoc hc n (Pr.vT u) w t) := by
  have e : (((bc (prV (E := X.E) w) y)⁻¹ : GL (Fin n) (X.E ⊗[X.F] w.adicCompletion X.F)).1 *ᵥ
      fun a => inclE (F := X.F) (w.adicCompletion X.F) (z a)) = t.1 := by
    rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h1 := fv_tieL hc n w (basePi_of_ok hX hPr u) Pr.vGs c₀ (sepElt_of_ok hPr u) y hyU d hd P hov (tieInv_spec hPr u P) z hzL
    (by rw [e]; exact t.2)
  rw [h1]
  show _ = (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) * rll_psi hc n w (basePi_of_ok hX hPr u) P.1 t
  congr 2
  exact Subtype.ext e

def levPack_fMe (H : HCrd Pr n fun c => (s c).1.L) (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) :
    (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fM w hw ≃+ (𝓞 X.E ⧸ P.1.asIdeal) := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact fvMeW hc hX hPr u c₀ w P hov

set_option maxHeartbeats 1000000 in

theorem levPack_fv (H : HCrd Pr n fun c => (s c).1.L) (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) (z : Sp X.E n) (hzL : z ∈ (s c).1.Lsh)
    (t : latS (F := X.F) (w.adicCompletion X.F) (intV X.E w)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb)))
    (ht : ((bc (prV (E := X.E) w) ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c :
          GL (Fin H.n') (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) : GL (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun b => inclE (F := X.F) (w.adicCompletion X.F) (Formalism.L2.Forms.reV H.hn.symm X.E z b)) :
    (s c).1.f P z = levPack_fMe hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fT w hw t) := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  refine fv_tieW hc hX hPr u c₀ w P hov _ (ptOfD hc _ (Pr.vT u) Pr.vGs c₀ (s c)).2 (s c)
    (decoOfD_ptOfD hc _ (Pr.vT u) Pr.vGs hS c₀ (s c)) z hzL t ?_
  refine ht.trans ?_
  funext b
  rw [Formalism.L2.Forms.reV_rfl]

set_option maxHeartbeats 1000000 in

theorem levPack_fvQ (H : HCrd Pr n fun c => (s c).1.L) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)
    (w : HeightOneSpectrum (𝓞 X.F)) (hw : (Pr.T u : 𝓞 X.F) ∈ w.asIdeal)
    (P : Pr.vT u) (hov : IsOver w P.1) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (z : ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (t : latS (F := X.F) (w.adicCompletion X.F) (intV X.E w)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb)))
    (ht : ((bc (prV (E := X.E) w) ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c :
          GL (Fin H.n') (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) : GL (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (X.E ⊗[X.F] w.adicCompletion X.F)).mulVec t.1 =
      fun b => inclE (F := X.F) (w.adicCompletion X.F) (Formalism.L2.Forms.reV H.hn.symm X.E z.1 b)) :
    (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) = levPack_fMe hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov
      ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fT w hw t) :=
  (tie_fv hc hPr σ₀ u s Q P c z).trans
    (levPack_fv hc hX hPr σ₀ u Λ c₀ s hS hs hK H w hw P hov c z.1 ((tie_Ld_eq hc σ₀ u s Q c).le z.2) t ht)

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) (O : AtTOwed a hS hH)

theorem thf_over (u : d.what₂.Word) (w : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.T u : 𝓞 d.X.F) ∈ w.asIdeal) :
    IsOver w ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩).1 := by
  have e : (tieEV d.sp.cm d.hX d.hPr u ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩)).1 = w :=
    congrArg Subtype.val ((tieEV d.sp.cm d.hX d.hPr u).apply_symm_apply ⟨w, h⟩)
  have h1 := tieEV_over d.sp.cm d.hX d.hPr u ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩)
  rwa [e] at h1

theorem thf_pr (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u i)
    (z : ↥(CH.Ld (d.colRec a) u i c)) :
    (hermAtT a hS hH O u).pr i v c z = (levelAgreement a hS hH u i hi).pr v c (hxLd (D := d.colRec a) i hi c z) :=
  hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) i hi v c z

set_option maxHeartbeats 2000000 in

def baseLevelConditions : LevelZeroConditions a hS hH hP hK S hI O := fun u =>
  { frG_lat := fun i v h t =>
      levPack_frLat d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) S (hCrd0 hS u) i v h t
    fM_pi := fun v h x hx m =>
      levPack_fM_pi d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) v h x hx m
    fMe := fun w h =>
      levPack_fMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) w h
        ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) (thf_over u w h)
    fv0 := fun w h c z t ht =>
      (congrArg _ (thf_pr a hS hH O u 0 (Nat.zero_le _) ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) c z)).trans
        (levPack_fvQ d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
          (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) (stepCrd a hS hH u 0 (Nat.zero_le _)) w h
          ((tieEV d.sp.cm d.hX d.hPr u).symm ⟨w, h⟩) (thf_over u w h) c (hxLd (D := d.colRec a) 0 (Nat.zero_le _) c z) t ht) }

set_option maxHeartbeats 2000000 in

def formValueAgreement : CH.FvStepTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := fun u i _ hm v =>
  { fb := (levPack_fMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
        (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm)
        (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2 v (tieEV_over d.sp.cm d.hX d.hPr u v)).toAddMonoidHom.comp
      ((hermPack hS hP hK u i hm).lev.fT (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2).toAddMonoidHom
    fvI := fun c z t ht =>
      (congrArg _ (thf_pr a hS hH O u i hm v c z)).trans
        (levPack_fvQ d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
          (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm) (stepCrd a hS hH u i hm)
          (tieEV d.sp.cm d.hX d.hPr u v).1 (tieEV d.sp.cm d.hX d.hPr u v).2 v (tieEV_over d.sp.cm d.hX d.hPr u v) c
          (hxLd (D := d.colRec a) i hm c z) t ht) }

end Rec

end Formalism.L2.Col
