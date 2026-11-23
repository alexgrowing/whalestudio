import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section iota

variable {k r : ℕ}

def iotL (k r : ℕ) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => Hpk k r * gᴴ * Hpk k r
      map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [RingHom.id_apply, star_trivial] }

theorem iotL_apply (g : Mat k r) : iotL k r g = Hpk k r * gᴴ * Hpk k r := rfl

theorem iotL_iotL (g : Mat k r) : iotL k r (iotL k r g) = g := by
  obtain ⟨h1, h2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  simp only [iotL_apply, Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose]
  rw [show Hpk k r * (Hpk k r * (g * Hpk k r)) * Hpk k r = (Hpk k r * Hpk k r) * g * (Hpk k r * Hpk k r) by
    simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]

theorem iotL_mul (a b : Mat k r) : iotL k r (a * b) = iotL k r b * iotL k r a := by
  obtain ⟨-, h2, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
  simp only [iotL_apply, Matrix.conjTranspose_mul]
  rw [show Hpk k r * bᴴ * Hpk k r * (Hpk k r * aᴴ * Hpk k r) = Hpk k r * bᴴ * (Hpk k r * Hpk k r) * aᴴ * Hpk k r by
    simp only [Matrix.mul_assoc], h2, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem iotL_GV {g : Mat k r} (hg : g ∈ GV k r) : iotL k r g = g⁻¹ := (Formalism.FourierDecayAlt.P.B6.inv_eq_hermitian_form_conjTranspose hg).symm

theorem iotL_mem {g : Mat k r} (hg : g ∈ GV k r) : iotL k r g ∈ GV k r := by
  rw [iotL_GV hg]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg

end iota

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section words

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ldV_rtransl (X t : Mat k r) (f : Mat k r → E) (g : Mat k r) :
    LdV X (fun y => f (y * t)) g = LdV X f (g * t) := by
  unfold LdV
  simp only [Matrix.mul_assoc]

theorem lw_rtransl (t : Mat k r) : ∀ (u : List (Mat k r)) (f : Mat k r → E),
    u.foldr LdV (fun y => f (y * t)) = fun y => u.foldr LdV f (y * t)
  | [], _ => rfl
  | X :: u, f => by
    funext g
    show LdV X (u.foldr LdV (fun y => f (y * t))) g = LdV X (u.foldr LdV f) (g * t)
    rw [lw_rtransl t u f, ldV_rtransl]

theorem dLR_rtransl (t : Mat k r) (u : List (Mat k r)) (f : Mat k r → E) :
    dLR u [] (fun y => f (y * t)) = fun y => dLR u [] f (y * t) := lw_rtransl t u f

end words

section post

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def postL (P : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp P).restrictScalars ℝ

theorem postL_apply (P : Wp →L[ℂ] Wp) (A : Wq →L[ℂ] Wp) : postL P A = P.comp A := rfl

theorem ldV_post {P Q : Wp →L[ℂ] Wp} (hQP : Q.comp P = 1) (X : Mat k r) (f : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : LdV X (fun y => P.comp (f y)) g = P.comp (LdV X f g) := by
  show deriv (fun s : ℝ => postL P (f (NormedSpace.exp (-((s : ℂ) • X)) * g))) 0 =
    postL P (deriv (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X)) * g)) 0)
  refine Formalism.FourierDecayAlt.P.SandwichRhoAction.deriv_comp_of_leftInv (postL P) (postL Q) (fun A => ?_) _ 0
  rw [postL_apply, postL_apply, ← ContinuousLinearMap.comp_assoc, hQP]
  rfl

theorem lw_post {P Q : Wp →L[ℂ] Wp} (hQP : Q.comp P = 1) : ∀ (u : List (Mat k r)) (f : Mat k r → (Wq →L[ℂ] Wp)),
    u.foldr LdV (fun y => P.comp (f y)) = fun y => P.comp (u.foldr LdV f y)
  | [], _ => rfl
  | X :: u, f => by
    funext g
    show LdV X (u.foldr LdV (fun y => P.comp (f y))) g = P.comp (LdV X (u.foldr LdV f) g)
    rw [lw_post hQP u f, ldV_post hQP]

theorem pi_leftInv (Bs : B.RealPlaceData k r Wp Wq) {h : Mat k r} (hh : h ∈ UWset k r Bs.z) :
    (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
  have u1 := WeylGroupFacts.isUnit_of_uh hh.1
  rw [← Bs.π_rep.2 _ (WeylGroupFacts.uw_inv hh) _ hh, Matrix.nonsing_inv_mul _ u1, Bs.π_rep.1]

end post

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section comp

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem loc_iot {m : ℕ∞} {f : Mat k r → E} {g : Mat k r} (h : CapelliWordSumExpansion.Loc m f (iotL k r g)) :
    CapelliWordSumExpansion.Loc m (fun y => f (iotL k r y)) g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  exact ⟨iotL k r ⁻¹' U, fun y => f' (iotL k r y), hU.preimage (iotL k r).continuous, hgU,
    hf'.comp (iotL k r).contDiff.contDiffOn (fun y hy => hy), fun y hy hyG => he _ hy (iotL_mem hyG)⟩

theorem ckOn_iot {m : ℕ∞} {f : Mat k r → E} (hf : CkOn m (GV k r) f) :
    CkOn m (GV k r) (fun y => f (iotL k r y)) :=
  fun g hg => loc_iot (hf _ (iotL_mem hg))

theorem ckOn_rtransl {m : ℕ∞} {f : Mat k r → E} (hf : CkOn m (GV k r) f) {t : Mat k r} (ht : t ∈ GV k r) :
    CkOn m (GV k r) (fun y => f (y * t)) := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf (g * t) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hg ht)
  refine ⟨mulR t ⁻¹' U, fun y => f' (mulR t y), hU.preimage (mulR t).continuous, hgU,
    hf'.comp (mulR t).contDiff.contDiffOn (fun y hy => hy), fun y hy hyG => he _ hy (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hyG ht)⟩

end comp

section postCk

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem ckOn_post {m : ℕ∞} {f : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn m (GV k r) f) (P : Wp →L[ℂ] Wp) :
    CkOn m (GV k r) (fun y => P.comp (f y)) := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact ⟨U, fun y => postL P (f' y), hU, hgU, (postL P).contDiff.comp_contDiffOn hf',
    fun y hy hyG => by show P.comp (f y) = postL P (f' y); rw [he y hy hyG]; rfl⟩

end postCk

section fam

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sxF (e : p + ρ = n) (x : PBQ.XP k p ρ) : Mat k n :=
  D.castM e (U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1 : Mat k ρ)⁻¹ * (Matrix.of x.1.2 : Mat k ρ)⁻¹))

theorem cast_leftFactor_eq_of_good {Bj : B.RealPlaceData k ρ Wp Wq} {x : PBQ.XP k p ρ} (hx : PBQ.GoodP Bj x) (e : p + ρ = n) :
    D.castM e (PBQ.sP Bj x) = sxF e x := by
  unfold PBQ.sP sxF
  rw [if_pos hx]

theorem sxF_GV {Bj : B.RealPlaceData k ρ Wp Wq} (e : p + ρ = n) {x : PBQ.XP k p ρ} (hx : PBQ.GoodP Bj x) :
    sxF e x ∈ GV k n := by
  refine Formalism.FourierDecayAlt.P.PBE.castM_GV e (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (LeftFubiniLemmas.rn_nset _).1 ?_)
  rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_GV p ρ _
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.1.1) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.2.1))

theorem isClosed_good (Bj : B.RealPlaceData k ρ Wp Wq) : IsClosed {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} := by
  have c1 : IsClosed {x : Mt k ρ | (Matrix.of x : Mat k ρ) ∈ UWset k ρ Bj.z} := Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z
  have c2 : IsClosed {x : Mt k ρ | (Matrix.of x : Mat k ρ) ∈ Nset k ρ} := Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ
  exact (c1.preimage (continuous_fst.comp continuous_fst)).inter (c2.preimage (continuous_snd.comp continuous_fst))

theorem cont_sxF (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) :
    ContinuousOn (sxF e) {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} := by
  have hinv : ContinuousOn (fun y : Mat k ρ => y⁻¹) (GV k ρ) := Formalism.FourierDecayAlt.P.PBG.inv_cont_GV
  have h1 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.1 : Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    hinv.comp (continuous_fst.comp continuous_fst).continuousOn fun x hx => hx.1.1
  have h2 : ContinuousOn (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : Mat k ρ)⁻¹) {x | PBQ.GoodP Bj x} :=
    hinv.comp (continuous_snd.comp continuous_fst).continuousOn fun x hx => hx.2.1
  have h3 : ContinuousOn (fun x : PBQ.XP k p ρ => U.embG k p ρ ((Matrix.of x.1.1 : Mat k ρ)⁻¹ *
      (Matrix.of x.1.2 : Mat k ρ)⁻¹)) {x | PBQ.GoodP Bj x} := by
    have e1 : (U.embG k p ρ) = ιLev k p ρ := funext fun y => (Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG p ρ y).symm
    rw [e1]
    exact (Formalism.FourierDecayAlt.P.Dx2.Tower.lev_cont p ρ).comp_continuousOn (h1.mul h2)
  have h4 : Continuous (fun x : PBQ.XP k p ρ => U.Rn k p ρ (-x.2)) :=
    (Formalism.FourierDecayAlt.P.Ux10.cont_Rn k p ρ).comp continuous_snd.neg
  exact (Formalism.FourierDecayAlt.P.Dx2.Tower.castM_cont e).comp_continuousOn (h4.continuousOn.mul h3)

end fam

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section main

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Classical in

def fam (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Φt : Mat k n → (Wq →L[ℂ] Wp)) (x : PBQ.XP k p ρ)
    (g : Mat k n) : Wq →L[ℂ] Wp :=
  if PBQ.GoodP Bj x then (Bj.π (Matrix.of x.1.1)).comp (Φt (g * iotL k n (sxF e x))) else 0

def Gt (Bj : B.RealPlaceData k ρ Wp Wq) (e : p + ρ = n) (Φt : Mat k n → (Wq →L[ℂ] Wp)) (g : Mat k n) : Wq →L[ℂ] Wp :=
  ∫ x, PBQ.cP Bj x • fam Bj e Φt x g ∂(PBQ.muXP Bj)

theorem pbF_eq_Gt (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : Mat k n → (Wq →L[ℂ] Wp)) (g : Mat k n) :
    PBQ.pbF Bj B0 e H g = Gt Bj e (fun y => PBG.Kr B0 H (iotL k n y)) (iotL k n g) := by
  unfold PBQ.pbF Gt
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  unfold PBQ.pbI fam
  rw [if_pos hx]
  simp only [iotL_mul, iotL_iotL, cast_leftFactor_eq_of_good hx e]

theorem norm_cP (Bj : B.RealPlaceData k ρ Wp Wq) (x : PBQ.XP k p ρ) : ‖PBQ.cP Bj x‖ ≤ 1 := by
  unfold PBQ.cP
  rw [norm_mul, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, Formalism.FourierDecayAlt.P.LeftFubiniLemmas.norm_psi, one_mul]

theorem continuous_characterProduct (Bj : B.RealPlaceData k ρ Wp Wq) : Continuous (fun x : PBQ.XP k p ρ => PBQ.cP Bj x) := by
  unfold PBQ.cP
  have hof2 : Continuous (fun x : PBQ.XP k p ρ => (Matrix.of x.1.2 : B.Mat k ρ)) := continuous_fst.snd
  exact ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of Bj.z cStd).comp hof2).mul
    ((Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.psi_cont_of (liftVec k p ρ Bj.z) cStd).comp
      ((Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp continuous_snd))

theorem chart_zero (g0 : Mat k n) : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
  have hMv : Formalism.FourierDecayAlt.P.Ux10.Mv (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) = 0 := by
    ext a b; simp [Formalism.FourierDecayAlt.P.Ux10.Mv]
  simp [Formalism.FourierDecayAlt.P.Ux10.chart, hMv, Formalism.FourierDecayAlt.P.Ux10.prj_zero, Formalism.FourierDecayAlt.P.Ux10.kap]

end main

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fmc_RC (k p ρ : ℕ) : IsFiniteMeasureOnCompacts (U.muRC k p ρ) := by
  unfold U.muRC
  have h0 : IsFiniteMeasureOnCompacts (volume : Measure (Fin p → ℂ)) := by rw [volume_pi]; infer_instance
  have h1 : IsFiniteMeasureOnCompacts (volume : Measure (G.UT p → ℂ)) := by rw [volume_pi]; infer_instance
  have h2 : IsFiniteMeasureOnCompacts (volume : Measure (Fin p → ℝ)) := by rw [volume_pi]; infer_instance
  have h3 : IsFiniteMeasureOnCompacts (volume : Measure (Fin (2 * ρ + k + 1) → Fin p → ℂ)) := by
    rw [volume_pi]; infer_instance
  have : SigmaFinite (volume : Measure (Fin p → ℝ)) := by rw [volume_pi]; infer_instance
  have : SigmaFinite (volume : Measure (G.UT p → ℂ)) := by rw [volume_pi]; infer_instance
  have : SigmaFinite (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h4 : IsFiniteMeasureOnCompacts (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

section ck

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem muXP_lt_top_of_isCompact (Bj : B.RealPlaceData k ρ Wp Wq) {K : Set (PBQ.XP k p ρ)} (hK : IsCompact K) :
    PBQ.muXP Bj K < ⊤ := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have := fmc_RC k p ρ
  have hK1 : IsCompact ((fun x : PBQ.XP k p ρ => x.1.1) '' K) := hK.image (continuous_fst.comp continuous_fst)
  have hK2 : IsCompact ((fun x : PBQ.XP k p ρ => x.1.2) '' K) := hK.image (continuous_snd.comp continuous_fst)
  have hK3 : IsCompact ((fun x : PBQ.XP k p ρ => x.2) '' K) := hK.image continuous_snd
  have hbox : K ⊆ (((fun x : PBQ.XP k p ρ => x.1.1) '' K) ×ˢ ((fun x : PBQ.XP k p ρ => x.1.2) '' K)) ×ˢ
      ((fun x : PBQ.XP k p ρ => x.2) '' K) :=
    fun x hx => ⟨⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, ⟨x, hx, rfl⟩⟩
  refine (measure_mono hbox).trans_lt ?_
  rw [PBQ.muXP, Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (Bj.haarW.finite_compact _ hK1) (Bj.haarN.finite_compact _ hK2))
    hK3.measure_lt_top

theorem ck_at (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    {H : Mat k n → (Wq →L[ℂ] Wp)} {Cs : Set (Mat k n)} (hH : CkOn ⊤ (GV k n) H) (hCs : IsCompact Cs)
    (hHC : ∀ g ∈ GV k n, g ∉ Cs → H g = 0) {Ω : Set (Mat k n)} (hP : PartialBesselProperness.Proper Bj B0 e Cs Ω)
    (m : ℕ) {g0 : Mat k n} (hg0 : g0 ∈ GV k n) (hgU : iotL k n g0 ∈ Ω) :
    ∃ (U' : Set (Mat k n)) (F' : Mat k n → (Wq →L[ℂ] Wp)), IsOpen U' ∧ g0 ∈ U' ∧
      ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) F' U' ∧
      ∀ g ∈ U', g ∈ GV k n → Gt Bj e (fun y => PBG.Kr B0 H (iotL k n y)) g = F' g := by
  classical
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : BorelSpace (PBQ.XP k p ρ) := by
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  set Φ : Mat k n → (Wq →L[ℂ] Wp) := PBG.Kr B0 H with hΦdef
  set Φt : Mat k n → (Wq →L[ℂ] Wp) := fun y => Φ (iotL k n y) with hΦtdef
  have hΦ : CkOn ⊤ (GV k n) Φ := fun g hg => PBG.kr_loc_cpt B0 hH hCs hHC g hg
  have hΦt : CkOn ⊤ (GV k n) Φt := ckOn_iot hΦ
  set μ := PBQ.muXP (p := p) Bj with hμ

  obtain ⟨V, hV, K, hK, hKp⟩ := hP _ hgU
  set O := interior (iotL k n ⁻¹' V) with hOdef
  have hOo : IsOpen O := isOpen_interior
  have hgO : g0 ∈ O := by
    rw [hOdef, mem_interior_iff_mem_nhds]
    exact (iotL k n).continuous.continuousAt.preimage_mem_nhds hV

  have hzero : ∀ x, (x ∉ K ∨ ¬ PBQ.GoodP Bj x) → ∀ g ∈ GV k n, g ∈ O → fam Bj e Φt x g = 0 := by
    intro x hx g hg hgO'
    unfold fam
    split_ifs with hxg
    · have hxK : x ∉ K := hx.resolve_right (not_not.2 hxg)
      have hgV : iotL k n g ∈ V := (interior_subset hgO' : g ∈ iotL k n ⁻¹' V)
      have hiG := iotL_mem hg
      have h0 : Φt (g * iotL k n (sxF e x)) = 0 := by
        show PBG.Kr B0 H (iotL k n (g * iotL k n (sxF e x))) = 0
        rw [iotL_mul, iotL_iotL]
        unfold PBG.Kr
        refine integral_eq_zero_of_ae ?_
        filter_upwards [PBG.ae_inR B0] with ξ hξ
        have hnot := hKp _ hgV hiG x hxg hxK ξ hξ
        rw [cast_leftFactor_eq_of_good hxg e] at hnot
        have hmem : sxF e x * iotL k n g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ GV k n :=
          Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sxF_GV e hxg) hiG) hξ.2.1) hξ.1.1
        simp only [hHC _ hmem hnot, ContinuousLinearMap.zero_comp, smul_zero, Pi.zero_apply]
      rw [h0, ContinuousLinearMap.comp_zero]
    · rfl

  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1
    (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds (Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom (k := k) (r := n)))
  have hcc : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.continuousAt
      (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
  obtain ⟨δ2, hδ2, hsub2⟩ := Metric.mem_nhds_iff.1
    (hcc.preimage_mem_nhds (by rw [chart_zero]; exact hOo.mem_nhds hgO))
  set δ := min δ1 δ2 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; positivity
  have hδ1' : δ < δ1 := by rw [hδ]; have := min_le_left δ1 δ2; linarith
  have hδ2' : δ < δ2 := by rw [hδ]; have := min_le_right δ1 δ2; linarith
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k n :=
    fun Y hY => hsub (Metric.closedBall_subset_ball hδ1' hY)
  have hclO : ∀ Y ∈ Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ O :=
    fun Y hY => hsub2 (Metric.closedBall_subset_ball hδ2' hY)
  set Kc := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ with hKcdef
  have hKc : IsCompact Kc :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKcG : Kc ⊆ GV k n := by
    rintro _ ⟨Y, hY, rfl⟩; exact Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0 (hcl hY)
  have hmemKc : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ Kc :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  have hmemO : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ O :=
    fun Y hY => hclO Y (Metric.ball_subset_closedBall hY)

  set Kx := K ∩ {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} with hKxdef
  have hKx : IsCompact Kx := hK.inter_right (isClosed_good Bj)
  set KImage := (fun q : PBQ.XP k p ρ × Mat k n => q.2 * iotL k n (sxF e q.1)) '' (Kx ×ˢ Kc) with hKimdef
  have hKim : IsCompact KImage := by
    refine (hKx.prod hKc).image_of_continuousOn ?_
    refine continuous_snd.continuousOn.mul ?_
    exact (iotL k n).continuous.comp_continuousOn
      ((cont_sxF Bj e).comp continuous_fst.continuousOn fun q hq => hq.1.2)
  have hKimG : KImage ⊆ GV k n := by
    rintro _ ⟨q, hq, rfl⟩
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (hKcG hq.2) (iotL_mem (sxF_GV e hq.1.2))

  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k n X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hΨ : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n),
      ContinuousOn (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] Φt) (GV k n) := by
    intro w
    rw [Formalism.FourierDecayAlt.P.B4.dLR_eq]
    exact Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (m := ((0 : ℕ) : ℕ∞))
      (smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) 0 (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hΦt))
  have hbw : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n), ∃ C : ℝ,
      ∀ y ∈ KImage, ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] Φt y‖ ≤ C :=
    fun w => hKim.exists_bound_of_continuousOn ((hΨ w).mono hKimG)
  choose Cw hCw using hbw
  set Wm := (List.finite_length_le (Formalism.FourierDecayAlt.P.Ux10.J k n) m).toFinset with hWm
  set c : ℝ := ∑ w ∈ Wm, max (Cw w) 0 with hcdef
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun w _ => le_max_right _ _
  have hcw : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n), w.length ≤ m → ∀ y ∈ KImage,
      ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] Φt y‖ ≤ c := by
    intro w hw y hy
    have hwm : w ∈ Wm := by rw [hWm, Set.Finite.mem_toFinset]; exact hw
    calc _ ≤ Cw w := hCw w y hy
      _ ≤ max (Cw w) 0 := le_max_left _ _
      _ ≤ c := Finset.single_le_sum (f := fun w => max (Cw w) 0) (fun w _ => le_max_right _ _) hwm

  set β : PBQ.XP k p ρ → ℝ := Kx.indicator (fun _ => c) with hβ
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => hc0) x
  have hβI : Integrable β μ :=
    (integrableOn_const (μ := μ) (s := Kx) (C := c) (muXP_lt_top_of_isCompact Bj hKx).ne).integrable_indicator
      hKx.isClosed.measurableSet

  have hwords : ∀ (w : List (Formalism.FourierDecayAlt.P.Ux10.J k n)) x, PBQ.GoodP Bj x → ∀ y,
      dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (fam Bj e Φt x) y =
        (Bj.π (Matrix.of x.1.1)).comp (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] Φt (y * iotL k n (sxF e x))) := by
    intro w x hx y
    have hf : fam Bj e Φt x = fun g => (Bj.π (Matrix.of x.1.1)).comp (Φt (g * iotL k n (sxF e x))) := by
      funext g; unfold fam; rw [if_pos hx]
    rw [hf]
    show (w.map Formalism.FourierDecayAlt.P.Ux10.Lt).foldr LdV
      (fun g => (Bj.π (Matrix.of x.1.1)).comp (Φt (g * iotL k n (sxF e x)))) y = _
    rw [lw_post (pi_leftInv Bj hx.1)]
    show (Bj.π (Matrix.of x.1.1)).comp ((w.map Formalism.FourierDecayAlt.P.Ux10.Lt).foldr LdV
      (fun g => Φt (g * iotL k n (sxF e x))) y) =
      (Bj.π (Matrix.of x.1.1)).comp ((w.map Formalism.FourierDecayAlt.P.Ux10.Lt).foldr LdV Φt (y * iotL k n (sxF e x)))
    rw [lw_rtransl]
  have hbd : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n), w.length ≤ m →
      ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ, ∀ x,
        ‖dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (fam Bj e Φt x) (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y)‖ ≤ β x := by
    intro w hw Y hY x
    set y := Formalism.FourierDecayAlt.P.Ux10.chart g0 Y with hydef
    have hyG : y ∈ GV k n := hKcG (hmemKc Y hY)
    by_cases hxK : x ∈ Kx
    · rw [hwords w x hxK.2 y, hβ, Set.indicator_of_mem hxK]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_of_le_one_left (norm_nonneg _) (Formalism.FourierDecayAlt.P.B7.norm_pi_le Bj hxK.2.1)).trans ?_
      exact hcw w hw _ ⟨(x, y), ⟨hxK, hmemKc Y hY⟩, rfl⟩
    · have hx' : x ∉ K ∨ ¬ PBQ.GoodP Bj x := by
        by_contra hc
        push_neg at hc
        exact hxK ⟨hc.1, hc.2⟩
      have h0 : dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (fam Bj e Φt x) y = 0 := by
        rw [Formalism.FourierDecayAlt.P.B4.dLR_eq]
        exact Formalism.FourierDecayAlt.P.PBG.W_zero_near _ (allLie_lr (hunit w) (by simp)) hOo
          (fun g hg hgO' => hzero x hx' g hg hgO') y hyG (hmemO Y hY)
      rw [h0, norm_zero]
      exact hβ0 x

  have hgood : μ.restrict {x : PBQ.XP k p ρ | PBQ.GoodP Bj x} = μ :=
    Measure.restrict_eq_self_of_ae_mem (PBQ.ae_goodP (p := p) Bj)
  have hM : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k n), w.length ≤ m →
      ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k n → ℝ) δ,
        AEStronglyMeasurable (fun x => dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (fam Bj e Φt x)
          (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y)) μ := by
    intro w hw Y hY
    set y := Formalism.FourierDecayAlt.P.Ux10.chart g0 Y with hydef
    have hyG : y ∈ GV k n := hKcG (hmemKc Y hY)
    have hs : ContinuousOn (fun x : PBQ.XP k p ρ => y * iotL k n (sxF e x)) {x | PBQ.GoodP Bj x} :=
      continuousOn_const.mul ((iotL k n).continuous.comp_continuousOn (cont_sxF Bj e))
    have hmap : Set.MapsTo (fun x : PBQ.XP k p ρ => y * iotL k n (sxF e x)) {x | PBQ.GoodP Bj x} (GV k n) :=
      fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hyG (iotL_mem (sxF_GV e hx))
    have hπ : ContinuousOn (fun x : PBQ.XP k p ρ => Bj.π (Matrix.of x.1.1)) {x | PBQ.GoodP Bj x} :=
      Bj.π_cont.comp (continuous_fst.comp continuous_fst).continuousOn fun x hx => hx.1
    have hG : ContinuousOn (fun x : PBQ.XP k p ρ => (Bj.π (Matrix.of x.1.1)).comp
        (dLR (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] Φt (y * iotL k n (sxF e x)))) {x | PBQ.GoodP Bj x} :=
      hπ.clm_comp ((hΨ w).comp hs hmap)
    have hGm := hG.aestronglyMeasurable (μ := μ) (isClosed_good Bj).measurableSet
    rw [hgood] at hGm
    refine hGm.congr ?_
    filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
    exact (hwords w x hx y).symm

  have hh : ∀ x, CkOn ((m : ℕ) : ℕ∞) (GV k n) (fam Bj e Φt x) := by
    intro x
    by_cases hx : PBQ.GoodP Bj x
    · have hf : fam Bj e Φt x = fun g => (Bj.π (Matrix.of x.1.1)).comp (Φt (g * iotL k n (sxF e x))) := by
        funext g; unfold fam; rw [if_pos hx]
      rw [hf]
      exact ckOn_post (ckOn_rtransl (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hΦt) (iotL_mem (sxF_GV e hx))) _
    · have hf : fam Bj e Φt x = fun _ => 0 := by
        funext g; unfold fam; rw [if_neg hx]
      rw [hf]
      exact Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.ckOn_zero _
  have hAL := Formalism.FourierDecayAlt.P.ChartIntegralLocal.int_chart_loc (μ := μ) (fun x => PBQ.cP Bj x) (norm_cP Bj)
    (continuous_characterProduct Bj).aestronglyMeasurable (fam Bj e Φt) m hh hg0 hδp hcl hM β hβI hbd
  exact Formalism.FourierDecayAlt.P.ChartIntegralLocal.ck_at_of_chart hg0 hδp hAL

end ck

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section fin

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gt_smooth (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    {H : Mat k n → (Wq →L[ℂ] Wp)} {Cs : Set (Mat k n)} (hH : CkOn ⊤ (GV k n) H) (hCs : IsCompact Cs)
    (hHC : ∀ g ∈ GV k n, g ∉ Cs → H g = 0) {Ω : Set (Mat k n)} (hΩ : IsOpen Ω)
    (hP : PartialBesselProperness.Proper Bj B0 e Cs Ω) :
    Q.SmoothLev k n 0 (iotL k n ⁻¹' Ω) (Gt Bj e (fun y => PBG.Kr B0 H (iotL k n y))) :=
  Formalism.FourierDecayAlt.P5.Rad.smoothLev_of_ck (hΩ.preimage (iotL k n).continuous) fun m g₀ hg₀ => by
    obtain ⟨U', F', hU', hgU', hF', he⟩ := ck_at Bj B0 e hH hCs hHC hP m hg₀.1.1 hg₀.2
    exact ⟨U', F', hU', hgU', hF', fun g hg hgl => he g hg hgl.1⟩

end fin

end Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas

theorem partial_bessel_smooth_compact_support : PartialBesselProperness.PbLoc := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ Bj B0 e _ H Cs hH hCs hHC Ω hΩ hP y hy hyG
  have hS := gt_smooth Bj B0 e hH hCs hHC hΩ hP
  have hmem : iotL k n y ∈ Q.Glev k n 0 ∩ iotL k n ⁻¹' Ω := by
    refine ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 (iotL_mem hyG), ?_⟩
    show iotL k n (iotL k n y) ∈ Ω
    rw [iotL_iotL]; exact hy
  obtain ⟨U', F', hU', hgU', hF', he⟩ := hS (iotL k n y) hmem
  have hloc : CapelliWordSumExpansion.Loc ⊤ (Gt Bj e (fun z => PBG.Kr B0 H (iotL k n z))) (iotL k n y) :=
    ⟨U', F', hU', hgU', hF', fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩
  have heq : PBQ.pbF Bj B0 e H = fun z => Gt Bj e (fun y => PBG.Kr B0 H (iotL k n y)) (iotL k n z) :=
    funext (pbF_eq_Gt Bj B0 e H)
  rw [heq]
  exact loc_iot hloc

end Formalism.FourierDecayAlt.P
