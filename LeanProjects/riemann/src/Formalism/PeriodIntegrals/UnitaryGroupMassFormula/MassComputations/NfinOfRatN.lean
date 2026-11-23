import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SumKfMulZREqZero

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW.NRatW

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ratN_of_AF (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (h : HAd X.B.I)
    (hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      γ.map (inclR (AF X.B.I.F)))
    (hN : h ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
    RatN X.eR (Kf X X.eR) γ := by
  obtain ⟨h1, h2⟩ := hN
  have hlin : ∀ x : Fin X.B.I.n → X.B.I.E,
      lin (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (AF X.B.I.F) x) -
        ratV (F := X.B.I.F) (AF X.B.I.F) x = fun i => inclR (AF X.B.I.F) (((γ - 1) *ᵥ x) i) := by
    intro x
    rw [← map_sub_one_mulVec (inclR (AF X.B.I.F)) γ x]
    simp only [lin, Matrix.mulVecLin_apply, hM, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · have := h1 a
    rw [hlin] at this
    exact down_span (inclR (AF X.B.I.F)) (inclR_injective X) X.eR (Kf X X.fR) (hK_e X u) _ _ this
  · have hperp : InXperp (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) (ratV (F := X.B.I.F) (AF X.B.I.F) y) := by
      intro a
      rw [hR_ratV_left]
      have h' := congrArg (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) (hy a)
      simp only [Kf, map_sum, map_mul, map_zero] at h'
      simp only [ratV, map_sum, map_mul]
      exact h'
    have := h2 _ hperp
    rw [hlin] at this
    have h3 := down_span (inclR (AF X.B.I.F)) (inclR_injective X) X.eR (Kf X X.fR) (hK_e X u) Set.univ _ this
    rwa [Set.image_univ] at h3

theorem ratN_of_fin (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (x : X.B.I.Gf)
    (hx : X.B.I.fmat x = γ.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) (hN : x ∈ X.NfinU u) :
    RatN X.eR (Kf X X.eR) γ := by
  simp only [HidaSetting.NfinU, Nfin, Set.mem_ofPred_eq] at hN
  obtain ⟨h1, -, h3⟩ := hN
  have hlin : ∀ y : Fin X.B.I.n → X.B.I.E, (X.B.I.fmat x - 1) *ᵥ incl X.B.I y =
      fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ - 1) *ᵥ y) i) := by
    intro y
    rw [hx]
    exact map_sub_one_mulVec _ γ y
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · have := h1 a
    rw [hlin] at this
    exact down_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclE_injective X) X.eR (Kf X X.fR) (hK_e X u)
      {b | b < a} _ this
  · have hperp : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I y) = 0 := by
      intro a
      rw [hA_incl_left]
      have h' := congrArg (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) (hy a)
      simp only [Kf, map_sum, map_mul, map_zero] at h'
      simpa only [incl, map_sum, map_mul] using h'
    have := h3 _ hperp
    rw [hlin, ← Set.image_univ] at this
    have h4 := down_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclE_injective X) X.eR (Kf X X.fR)
      (hK_e X u) Set.univ _ this
    rwa [Set.image_univ] at h4

theorem nfin_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (x : X.B.I.Gf)
    (hx : X.B.I.fmat x = γ.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) (hR : RatN X.eR (Kf X X.eR) γ) :
    x ∈ X.NfinU u := by
  simp only [HidaSetting.NfinU, Nfin, Set.mem_ofPred_eq]
  have hlin : ∀ y : Fin X.B.I.n → X.B.I.E, (X.B.I.fmat x - 1) *ᵥ incl X.B.I y =
      fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ - 1) *ᵥ y) i) := by
    intro y
    rw [hx]
    exact map_sub_one_mulVec _ γ y
  refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
  · rw [hlin]
    exact up_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) X.eR {b | b < a} (hR.1 a)
  · rw [hlin]
    have := up_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) X.eR Set.univ (w := (γ - 1) *ᵥ X.zR u)
      (by rw [Set.image_univ]; exact hR.2 _ (sum_Kf_mul_zR_eq_zero X u))
    rwa [Set.image_univ] at this
  · rw [hx]
    exact perp_up (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 y
      (fun a => by have := hy a; rw [hA_incl_left] at this; exact this)

theorem hJ_rv (v : InfinitePlace X.B.I.F) (x : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v x) y =
      ∑ j, X.B.I.φ v (∑ i, star (x i) * X.B.I.J i j) * (X.B.I.P v *ᵥ y) j := by
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hst : ∀ a : X.B.I.E, star (X.B.I.φ v a) = X.B.I.φ v (star a) := by
    intro a
    rw [X.B.I.cm.cmUnram.2.1]
    rfl
  unfold hJ rv
  rw [← X.B.I.P_spec v, Matrix.star_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one,
    Matrix.vecMul_one]
  set w := X.B.I.P v *ᵥ y
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, hst, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem ninf_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (s : X.B.I.Ginf)
    (hs : ∀ v, Formalism.MainNotions.S.uMat (s v) = (X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v) (hR : RatN X.eR (Kf X X.eR) γ) :
    s ∈ X.NinfU u := by
  simp only [HidaSetting.NinfU, Ninf, Set.mem_ofPred_eq]
  intro v
  rw [hs v]
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hPP' : (X.B.I.P v)⁻¹ * X.B.I.P v = 1 := Matrix.nonsing_inv_mul _ hdet
  have key1 : ∀ y : Fin X.B.I.n → ℂ, ((X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1) *ᵥ y =
      (X.B.I.P v)⁻¹ *ᵥ ((γ.map (X.B.I.φ v) - 1) *ᵥ (X.B.I.P v *ᵥ y)) := by
    intro y
    have hmat : (X.B.I.P v)⁻¹ * (γ.map (X.B.I.φ v) - 1) * X.B.I.P v =
        (X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1 := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hPP']
    conv_rhs => rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
  have key2 : ∀ x : Fin X.B.I.n → ℂ, ((X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ x) =
      (X.B.I.P v)⁻¹ *ᵥ ((γ.map (X.B.I.φ v) - 1) *ᵥ x) := by
    intro x
    have hx : X.B.I.P v *ᵥ ((X.B.I.P v)⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [key1, hx]
  have spanP : ∀ (t : Set (Fin D.R.rS)) (w : Fin X.B.I.n → ℂ),
      w ∈ Submodule.span ℂ ((fun b i => X.B.I.φ v (X.eR b i)) '' t) →
      (X.B.I.P v)⁻¹ *ᵥ w ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' t) := by
    intro t w hw
    have := Submodule.apply_mem_span_image_of_mem_span (Matrix.mulVecLin (X.B.I.P v)⁻¹) hw
    rw [Set.image_image] at this
    exact this
  have hu : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · show _ *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (X.eR a i)) ∈ _
    rw [key2, map_sub_one_mulVec]
    exact spanP _ _ (up_span (X.B.I.φ v) X.eR _ (hR.1 a))
  · show _ *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (X.zR u i)) ∈ _
    rw [key2, map_sub_one_mulVec]
    have h := up_span (X.B.I.φ v) X.eR Set.univ (w := (γ - 1) *ᵥ X.zR u)
      (by rw [Set.image_univ]; exact hR.2 _ (sum_Kf_mul_zR_eq_zero X u))
    unfold spanLt
    rw [hu]
    exact spanP _ _ h
  · rw [key1]
    have h := perp_up (X.B.I.φ v) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 (X.B.I.P v *ᵥ y)
      (fun a => by have := hy a; rw [hJ_rv] at this; exact this)
    rw [← Set.image_univ] at h
    unfold spanLt
    rw [hu]
    exact spanP _ _ h

theorem nsub_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (h : HAd X.B.I)
    (hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      γ.map (inclR (AF X.B.I.F)))
    (hR : RatN X.eR (Kf X X.eR) γ) :
    h ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  have hlin : ∀ y, lin (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h y - y = (γ.map (inclR (AF X.B.I.F)) - 1) *ᵥ y := by
    intro y
    simp only [lin, Matrix.mulVecLin_apply, hM, Matrix.sub_mulVec, Matrix.one_mulVec]
  show _ ∧ _
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · rw [hlin]
    have := up_span (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) X.eR {b | b < a} (hR.1 a)
    have e : (γ.map (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) - 1) *ᵥ
        ratV (F := X.B.I.F) (AF X.B.I.F) ((frameOf X u).e a) =
        fun i => inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F) (((γ - 1) *ᵥ X.eR a) i) :=
      map_sub_one_mulVec _ γ (X.eR a)
    rw [e]
    exact this
  · rw [hlin]
    have := perp_up (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 y
      (fun a => by have := hy a; rw [hR_ratV_left] at this; exact this)
    rw [← Set.image_univ] at this
    exact this

end MassDataMassesW.NRatW
