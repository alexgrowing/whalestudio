import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralLinearFormOnBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormRealCombination
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.ChartMono

theorem prod_mul_zpow {G ι : Type} [CommGroup G] (s : Finset ι) (x : ι → G) (y : G) (m : ι → ℤ) :
    ∏ k ∈ s, (x k * y ^ m k) = (∏ k ∈ s, x k) * y ^ (∑ k ∈ s, m k) := by
  classical
  rw [Finset.prod_mul_distrib]
  congr 1
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem fac {G : Type} [CommGroup G] (x₁ x₂ x₃ y : G) (n₁ n₂ n₃ a : ℤ) :
    ((x₁ * y ^ n₁) * (x₂ * y ^ n₂)⁻¹ * (x₃ * y ^ n₃)⁻¹) ^ a = (x₁ * x₂⁻¹ * x₃⁻¹) ^ a * y ^ (a * (n₁ - n₂ - n₃)) := by
  have e : (x₁ * y ^ n₁) * (x₂ * y ^ n₂)⁻¹ * (x₃ * y ^ n₃)⁻¹ = (x₁ * x₂⁻¹ * x₃⁻¹) * y ^ (n₁ - n₂ - n₃) := by
    simp only [mul_inv, zpow_sub]
    ac_rfl
  rw [e, mul_zpow, ← zpow_mul, mul_comm (n₁ - n₂ - n₃)]

theorem ell_eq_sum {X : Type} [AddCommGroup X] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ X)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (β : LinearMap.BilinForm ℤ X) :
    ℓ β = ∑ i, ∑ j, ℓ ((LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)) * β (b i) (b j) := by
  classical
  have e : β = ∑ i, ∑ j, β (b i) (b j) • (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) :=
    LinearMap.BilinForm.ext_basis b fun k l => by
      simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [e]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g d : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → Refines H q φs 𝒩 φ → Module.Projective (𝓞 E) P.D.toPre.X →
    Module.finrank (𝓞 E) P.D.toPre.X ≤ q → IsCN R → ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
    ∃ q : FractionRing R, q ≠ 0 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V,
      Irreducible ϖ → ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
      ∃ (n : ℤ) (w : Vˣ), (n : ℝ) = d * (resInt (𝓞 E) φs).evalZ be ∧ gam q = algebraMap V _ w * algebraMap V _ ϖ ^ n := by
  intro E _ _ _ H q g d φs 𝒩 φ R _ _ _ t P m γ hg hφs hR hproj hrk _ hcone hin
  classical
  haveI := hproj
  have : Module.Finite ℤ P.D.toPre.X := Module.Finite.trans (𝓞 E) P.D.toPre.X
  have : Module.IsTorsionFree (𝓞 E) P.D.toPre.X := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree ℤ P.D.toPre.X := Module.IsTorsionFree.trans (𝓞 E)
  have : Module.Free ℤ P.D.toPre.X := Module.free_of_finite_type_torsion_free'
  have hrkZ : Module.finrank ℤ P.D.toPre.X = Module.finrank ℚ E * Module.finrank (𝓞 E) P.D.toPre.X := by
    rw [← (TensorProduct.isBaseChange ℤ P.D.toPre.X ℚ).finrank_eq,
      ← (TensorProduct.isBaseChange (𝓞 E) P.D.toPre.X E).finrank_eq,
      Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E P.D.toPre.X).finrank_eq]
  have hφX : IsPolFanOn id φs P.D.toPre.X :=
    hφs P.D.toPre.X (by rw [hrkZ]; exact (Nat.mul_le_mul_left _ hrk).trans hg)
  have hc : IsCone H.bar φ γ := hcone
  have hlin : (resInt (𝓞 E) φs).LinearOn γ := (hR.2.2.2.2.2 P.D.toPre.X hrk m γ hc).1
  have hres : ∀ B : P.D.toPre.X → P.D.toPre.X → ℝ, (resInt (𝓞 E) φs).eval P.D.toPre.X B = φs.eval P.D.toPre.X B :=
    fun B => by
      obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) P.D.toPre.X
      rw [InvFun.eval_eq _ hr]
      exact φs.eval_comp (r := r.restrictScalars ℤ) hr B
  choose N hN using fun i => hφX.integral (γ i) (mem_balForms_int.2 (hc.mem i).1) (hc.nonneg i)
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.BalExt.exists_linearForm_ext H.bar P.D.toPre.X m γ hc.mem hc.basis (fun i => d * N i)
  let b := Module.Free.chooseBasis ℤ P.D.toPre.X
  let a : Module.Free.ChooseBasisIndex ℤ P.D.toPre.X → Module.Free.ChooseBasisIndex ℤ P.D.toPre.X → ℤ :=
    fun i j => ℓ ((LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j))
  choose r hr using fun χ : P.D.toPre.X =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre χ).2 (GlobalTheory.PeriodFormCompare.psiIn_top P.D χ)
  have hr0 : ∀ χ, algebraMap R (FractionRing R) (r χ) ≠ 0 := fun χ h =>
    GlobalTheory.PsiCoordLocal.ne_zero_of_coord (hr χ)
      (IsFractionRing.injective R (FractionRing R) (h.trans (map_zero _).symm))
  let ρ : P.D.toPre.X → (FractionRing R)ˣ := fun χ => Units.mk0 _ (hr0 χ)
  let Q : (FractionRing R)ˣ := ∏ i, ∏ j, (ρ (b i + b j) * (ρ (b i))⁻¹ * (ρ (b j))⁻¹) ^ a i j
  refine ⟨(Q : FractionRing R), Q.ne_zero, ?_⟩
  intro V _ _ _ hV ϖ hϖ ψ gam hgam be hbe hF
  have hbal : be ∈ balForms H.bar P.D.toPre.X := (balForms_eq_levelForms H P.D.toPre.X).symm ▸ hbe
  obtain ⟨c, hc0, hcs⟩ := hin V hV ϖ hϖ ψ be hbal.1 hF
  have hval : (resInt (𝓞 E) φs).evalZ be = ∑ i, c i * (N i : ℝ) := by
    have e1 : (fun a b => (be a b : ℝ)) = fun a b => ∑ i, c i * (γ i a b : ℝ) := by
      funext a b
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hcs a b
    have := hlin c hc0
    rw [InvFun.evalZ, e1, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [InvFun.evalZ, hres, ← hN i]
    rfl
  have hℓbe := GlobalTheory.PolFanReal.linearForm_of_toReal_eq P.D.toPre.X ℓ m γ c be hcs
  choose r' nn hr' hbn has using hF
  have hW : ∀ χ, ∃ w : Vˣ, ψ (r χ) = w * ϖ ^ nn χ := fun χ => by
    obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord (hr' χ) (hr χ)
    obtain ⟨w, hw⟩ := has χ
    refine ⟨Units.map ψ.toMonoidHom u * w⁻¹, ?_⟩
    rw [hu, map_mul, ← hw, Units.val_mul, Units.coe_map]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [mul_assoc, mul_left_comm ((w⁻¹ : Vˣ) : V), Units.inv_mul, mul_one]
  choose W hW using hW
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))
  let π : (FractionRing V)ˣ := Units.mk0 _ hϖ0
  let U : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V)).toMonoidHom
  have hmap : ∀ χ, Units.map gam.toMonoidHom (ρ χ) = U (W χ) * π ^ (nn χ : ℤ) := fun χ => by
    ext
    simp [ρ, U, π, hgam, hW]
  have hbe2 : ∀ x y, be x y = (nn (x + y) : ℤ) - nn x - nn y := fun x y => by
    have h1 := hbn (x + y)
    have h2 := hbn x
    have h3 := hbn y
    have h4 := hbal.1 x y
    simp only [map_add, LinearMap.add_apply] at h1
    linarith
  let w : Vˣ := ∏ i, ∏ j, (W (b i + b j) * (W (b i))⁻¹ * (W (b j))⁻¹) ^ a i j
  have key : Units.map gam.toMonoidHom Q = U w * π ^ (ℓ be) := by
    rw [ell_eq_sum b ℓ be]
    simp only [Q, w, map_prod, map_zpow, map_mul, map_inv, hmap, fac]
    simp only [prod_mul_zpow]
    congr 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hbe2]
  refine ⟨ℓ be, w, ?_, ?_⟩
  · rw [hℓbe, hval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hℓ i]
    push_cast
    ring
  · have := congrArg Units.val key
    simpa [π, U] using this

end GlobalTheory.TorRef.ChartMono
