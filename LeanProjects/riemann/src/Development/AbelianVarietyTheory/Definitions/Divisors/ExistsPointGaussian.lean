import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixOrderActionOnPower

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.Model

section Sign

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
  (v : Valuation C ℝ≥0)

theorem latNorm_scaleLat (La : Submodule O U) {a : C} (ha : a ≠ 0) (x : U) :
    latNorm v (scaleLat a La) x = v a⁻¹ * latNorm v La x := by
  rw [← latNorm_smul v La (inv_ne_zero ha), latNorm, latNorm]
  congr 1
  ext r
  constructor
  · rintro ⟨b, ⟨_, ⟨y, hy, rfl⟩, h⟩, rfl⟩
    refine ⟨b, ⟨y, hy, ?_⟩, rfl⟩
    change b • a • y = x at h
    change b • y = a⁻¹ • x
    rw [← h, smul_comm b a, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rintro ⟨b, ⟨y, hy, h⟩, rfl⟩
    refine ⟨b, ⟨a • y, ⟨y, hy, rfl⟩, ?_⟩, rfl⟩
    change b • y = a⁻¹ • x at h
    change b • a • y = x
    rw [smul_comm b a, h, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem grNorm_scaleLat (La : Submodule O U) {a : C} (ha : a ≠ 0) (f : Fin N → U) (k : Fin N) :
    grNorm v (scaleLat a La) f k = v a⁻¹ * grNorm v La f k := by
  rw [grNorm, grAt, grLat_scaleLat ha, latNorm_scaleLat v _ ha]
  rfl

variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']

theorem phiAt_scale_inv (p : ℕ) (h0 : v (p : C) ≠ 0) (h1 : v (p : C) < 1) (al : U →ₗ[C] U')
    (LW : Submodule O U) (Lom : Submodule O U') (f : Fin N → U) (j : ℕ) (lam : Fin N → ℝ)
    (hW : ∀ k : Fin N, (k : ℕ) < j → grNorm v LW f k ≠ 0) :
    phiAt_vp p v al (scaleLat (p : C)⁻¹ LW) Lom f j lam - phiAt_vp p v al LW Lom f j lam =
      -Real.log p * ∑ k : Fin N, if (k : ℕ) < j then lam k else 0 := by
  have hp : (p : C) ≠ 0 := fun h => h0 (by rw [h, map_zero])
  simp only [phiAt_vp, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < j
  · simp only [if_pos hk]
    rw [grNorm_scaleLat v LW (inv_ne_zero hp), inv_inv, logAbs_vp_mul p v h0 (hW k hk),
      logAbs_vp_self p v h0 h1]
    ring
  · simp [if_neg hk]

end Sign

section Sides

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
  [Algebra ℤ_[p] C] [IsAlgClosed C] [CharZero C]

theorem pairV_eq_zero {τ τ' : Λ →+* O} {x y : P.V} (hx : x ∈ P.eigV τ) (hy : y ∈ P.eigV τ') (a : Λ)
    (ha : algebraMap O C (τ a) ≠ algebraMap O C (τ' (star a))) : P.pairV x y = 0 := by
  have h := P.pairV_act a x y
  rw [mem_eigenSub.1 hx a, mem_eigenSub.1 hy (star a), map_smul, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_eq_mul] at h
  exact (mul_eq_mul_right_iff.1 h).resolve_left ha

variable {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (h : IsSplitting (embC C σ))

theorem pairV_proj (i : J) (x : P.V) {y : P.V} (hy : y ∈ P.eigV ((σ i).comp (starRingEnd Λ))) :
    P.pairV (proj h P.actV i x) y = P.pairV x y := by
  have key : ∀ t : C ⊗[ℤ] Λ, P.pairV (tensorAction P.actV t x) y =
      splitMap (embC C σ) t i * P.pairV x y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht, Pi.add_apply, add_mul]
    | tmul c a =>
      rw [tensorAction_tmul, map_smul, LinearMap.smul_apply, P.pairV_act,
        mem_eigenSub.1 hy (star a), map_smul, splitMap_tmul]
      simp only [smul_eq_mul, RingHom.comp_apply, starRingEnd_apply, star_star, _root_.mul_assoc]
  rw [proj, key, splitMap_idem, Pi.single_eq_same, _root_.one_mul]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem mem_latTSub_iff (i : J) {y : P.V} (hy : y ∈ P.eigV ((σ i).comp (starRingEnd Λ))) :
    y ∈ P.latTSub ((σ i).comp (starRingEnd Λ)) ↔
      ∀ x ∈ P.latTQuot h i, ∃ c : O, algebraMap O C c = P.pairV x y := by
  constructor
  · rintro ⟨hT, -⟩ _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change ∃ c : O, algebraMap O C c = P.pairV (proj h P.actV i _) y
    rw [pairV_proj P h i _ hy]
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x x' hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hx'
      exact ⟨c + d, by rw [map_add, map_add, map_add, LinearMap.add_apply, hc, hd]⟩
    | tmul c s =>
      obtain ⟨d, hd⟩ := (P.mem_latT_iff y).1 hT s
      refine ⟨-(c * d), ?_⟩
      have : (algebraMap O C c ⊗ₜ s : P.V) = algebraMap O C c • (1 : C) ⊗ₜ s := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [P.inclT_tmul, this, map_smul, LinearMap.smul_apply, P.pairV_swap, ← hd, map_neg, map_mul,
        smul_eq_mul, mul_neg]
  · intro H
    refine ⟨(P.mem_latT_iff y).2 fun t => ?_, hy⟩
    obtain ⟨c, hc⟩ := H _ ⟨_, P.one_tmul_mem_latT t, rfl⟩
    change _ = P.pairV (proj h P.actV i _) y at hc
    rw [pairV_proj P h i _ hy, P.pairV_swap] at hc
    exact ⟨-c, by rw [map_neg, hc, neg_neg]⟩

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem pairV_bLie_eq_zero (x : LieG P.Gt) {w : P.V} (hw : w ∈ P.W) : P.pairV (P.bLie x) w = 0 := by
  let ev : P.OmC →ₗ[C] C :=
    (Algebra.linearMap O C ∘ₗ LinearMap.proj x ∘ₗ (omega P.Gt).subtype).liftBaseChange C
  have key : ∀ w : P.V, P.pairV (P.bLie x) w = ev (P.alC w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c t =>
      have : (c ⊗ₜ t : P.V) = c • (1 : C) ⊗ₜ t := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [P.alC_tmul, this, map_smul, P.pairV_bLie]
      rfl
  rw [key, show P.alC w = 0 from hw, map_zero]

theorem omHT_le_eigOm (i : J) : P.omHT h i ≤ (P.eigOm (σ i)).restrictScalars O := by
  rw [P.omHT_eq]
  exact eigQuotLat_le _ h i _

theorem mem_wHT_iff (i : J) (x : P.V) : x ∈ P.wHT h i ↔ x ∈ P.latTQuot h i ∧ P.alC x = 0 :=
  ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, eigQuotLat_le _ h i P.latT hx.1⟩⟩

end Sides

section Gaussian

def gaussMat : GaussianInt →+* Matrix (Fin 2) (Fin 2) ℤ where
  toFun z := !![z.re, -z.im; z.im, z.re]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem gaussMat_star (z : GaussianInt) : gaussMat (star z) = star (gaussMat z) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gaussMat]

def gaussBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  Module.Basis.ofEquivFun (AddEquiv.toIntLinearEquiv
    { toFun := fun z => ![z.re, z.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by ext i; fin_cases i <;> rfl
      map_add' := fun a b => by ext i; fin_cases i <;> simp })

theorem gaussBasis_apply : gaussBasis 0 = ⟨1, 0⟩ ∧ gaussBasis 1 = ⟨0, 1⟩ := by
  constructor <;> simp [gaussBasis, Module.Basis.coe_ofEquivFun] <;> rfl

theorem exists_point_gaussian : ∃ (_ : Fact ¬IsUnit ((2 : ℕ) : 𝓞_ℂ_[2]))
    (_ : IsAdicComplete (Ideal.span {((2 : ℕ) : 𝓞_ℂ_[2])}) 𝓞_ℂ_[2]) (a₁ : Algebra ℤ_[2] 𝓞_ℂ_[2])
    (a₂ : Algebra ℤ_[2] ℂ_[2])
    (_ : @IsScalarTower ℤ_[2] 𝓞_ℂ_[2] ℂ_[2] a₁.toSMul Algebra.toSMul a₂.toSMul)
    (P : Point 2 (Valued.v : Valuation ℂ_[2] ℝ≥0) 𝓞_ℂ_[2] GaussianInt)
    (σ : Fin 2 → GaussianInt →+* 𝓞_ℂ_[2]),
    P.A.g = 2 ∧ Module.finrank ℂ_[2] P.V = 4 ∧ IsSplitting (embC ℂ_[2] σ) ∧
      (σ 0).comp (starRingEnd _) = σ 1 ∧ σ 0 ≠ σ 1 ∧ ∀ i, P.eigV (σ i) ≠ ⊥ := by
  let W : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩
  have hΔ : W.Δ = -27 := by
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have : W.IsElliptic := ⟨by
    rw [hΔ, PadicInt.isUnit_iff, norm_neg]
    exact_mod_cast (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 27)).2 (by norm_num)⟩
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨o, -⟩ := exists_oAct_int hL.cube _ (WeierstrassCurve.ellPolAV W)
  obtain ⟨A', pA, hg⟩ := GlobalTheory.exists_powPolAV _ (WeierstrassCurve.ellPolAV W) 2
  obtain ⟨rig, hrig⟩ := A'.rigid
  obtain ⟨m, -⟩ := MatrixRosati.exists_matrix_oAct _ _ A' 2 pA.toIsPowGrp pA.w pA.w_gen
    ⟨A'.L, rig, A'.isLB, hrig⟩ rfl (hL.cube _ A' _ rfl).1 ℤ o
  let og : A'.OAct GaussianInt :=
    { act := fun a => m.act (gaussMat a)
      hom := fun a => m.hom _
      map_one := by rw [map_one, m.map_one]
      map_mul := fun a b => by rw [map_mul, m.map_mul]
      map_add := fun a b => by rw [map_add, m.map_add]
      rosati := fun a => by rw [gaussMat_star]; exact m.rosati _ }
  obtain ⟨o', -⟩ := exists_oAct_polPull (spMap (padicIntHom 2)) _ og
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  letI a1 : Algebra ℤ_[2] 𝓞_ℂ_[2] := (padicIntHom 2).toAlgebra
  letI a2 : Algebra ℤ_[2] ℂ_[2] := ((algebraMap 𝓞_ℂ_[2] ℂ_[2]).comp (padicIntHom 2)).toAlgebra
  have hv := PadicComplexInt.integers 2
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ_[2]) two_pos
  obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := z) (by
    have : (Valued.v z : ℝ≥0) ^ 2 = 1 := by rw [← map_pow, hz, Valuation.map_neg, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 this).le)
  have hr2 : r * r = ((-1 : ℤ) : 𝓞_ℂ_[2]) := hv.hom_inj (by rw [map_mul, hr, ← sq, hz]; simp)
  have hr2' : (-r) * (-r) = ((-1 : ℤ) : 𝓞_ℂ_[2]) := by rw [neg_mul_neg, hr2]
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  let σ : Fin 2 → GaussianInt →+* 𝓞_ℂ_[2] := ![Zsqrtd.lift ⟨r, hr2⟩, Zsqrtd.lift ⟨-r, hr2'⟩]
  have hs : IsSplitting (embC ℂ_[2] σ) := by
    rw [isSplitting_iff_isUnit_det _ gaussBasis, Matrix.det_fin_two]
    simp only [Matrix.of_apply, gaussBasis_apply.1, gaussBasis_apply.2, σ, embC]
    simp [Zsqrtd.lift_apply_apply, hr]
    intro h
    have hr' : (r : ℂ_[2]) = z := hr
    exact hz0 (by linear_combination (-1 / 2 : ℂ_[2]) * h - (1 / 2 : ℂ_[2]) * hr')
  have hc : (σ 0).comp (starRingEnd _) = σ 1 := by
    refine RingHom.ext fun a => ?_
    simp [σ, Zsqrtd.lift_apply_apply, starRingEnd_apply]
  have hc' : (σ 1).comp (starRingEnd _) = σ 0 := by
    refine RingHom.ext fun a => ?_
    simp [σ, Zsqrtd.lift_apply_apply, starRingEnd_apply]
  have tw : @IsScalarTower ℤ_[2] 𝓞_ℂ_[2] ℂ_[2] a1.toSMul Algebra.toSMul a2.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let P := ofGoodReduction hv ε _ o'
  have hg2 : P.A.g = 2 := hg
  have hV : Module.finrank ℂ_[2] P.V = 4 := by rw [Point.finrank_V, hg2]
  have hne : σ 0 ≠ σ 1 := fun h => absurd (hs.injective (a₁ := 0) (a₂ := 1) (by
    change (algebraMap _ _).comp (σ 0) = (algebraMap _ _).comp (σ 1); rw [h])) (by decide)
  refine ⟨⟨PadicComplexHost.not_isUnit_p 2⟩, PadicComplexHost.isAdicComplete 2, a1, a2, tw,
    P, σ, hg2, hV, hs, hc, hne, ?_⟩
  have hz1 : ∀ (i : Fin 2) (x : P.V), P.eigV (σ i) = ⊥ → proj hs P.actV i x = 0 := fun i x hi => by
    have h1 : proj hs P.actV i x ∈ P.eigV (σ i) := proj_mem hs P.actV i x
    rwa [hi] at h1

  have hdual : ∀ i k : Fin 2, (σ i).comp (starRingEnd _) = σ k → P.eigV (σ i) = ⊥ →
      P.eigV (σ k) = ⊥ := by
    intro i k hik hi
    refine eq_bot_iff.2 fun y hy => P.eq_of_pairV fun t => ?_
    have h0 : proj hs P.actV i (1 ⊗ₜ t) = 0 := hz1 i _ hi
    rw [P.pairV_swap, ← pairV_proj P hs i _ (hik ▸ hy), h0]
    simp
  have hboth : ¬ (P.eigV (σ 0) = ⊥ ∧ P.eigV (σ 1) = ⊥) := by
    rintro ⟨h0, h1⟩
    have : Subsingleton P.V := ⟨fun x y => by
      have hz : ∀ x : P.V, x = 0 := fun x => by
        rw [← sum_proj hs P.actV x, Fin.sum_univ_two,
          hz1 0 x h0,
          hz1 1 x h1, add_zero]
      rw [hz x, hz y]⟩
    rw [Module.finrank_zero_of_subsingleton] at hV
    exact absurd hV (by decide)
  intro i hi
  fin_cases i
  · exact hboth ⟨hi, hdual 0 1 hc hi⟩
  · exact hboth ⟨hdual 1 0 hc' hi, hi⟩

end Gaussian

end GlobalTheory.HTLat.Model
