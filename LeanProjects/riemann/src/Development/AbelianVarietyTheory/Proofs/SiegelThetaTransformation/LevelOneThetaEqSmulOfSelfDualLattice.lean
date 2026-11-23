import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaOne

private theorem floor_bilinForm_eq_of_mem_selfDual {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) {x y : V} (hx : x ∈ L)
    (hy : y ∈ L) : ((⌊B x y⌋ : ℤ) : ℚ) = B x y := by
  obtain ⟨k, hk⟩ := (hL x).1 hx y hy
  rw [hk, Int.floor_intCast]

private theorem eq_zero_of_bilinForm_eq_zero_on_selfDual {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) (x : V)
    (hx : ∀ y ∈ L, B x y = 0) : x = 0 := by
  classical
  have hq : ∀ q : ℚ, q • x ∈ L := fun q =>
    (hL _).2 fun y hy => ⟨0, by rw [LinearMap.map_smul₂, hx y hy]; simp⟩
  have : NoZeroSMulDivisors ℤ V := ⟨fun {n v} h => by
    rw [← Int.cast_smul_eq_zsmul ℚ] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr h⟩
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ L
  let xL : L := ⟨x, by simpa using hq 1⟩
  have hrep : ∀ i, b.repr xL i = 0 := by
    intro i
    set n : ℕ := (b.repr xL i).natAbs + 1 with hn
    have hn0 : (n : ℚ) ≠ 0 := by positivity
    let yL : L := ⟨(n : ℚ)⁻¹ • x, hq _⟩
    have hy : (n : ℤ) • yL = xL := by
      apply Subtype.ext
      change (n : ℤ) • ((n : ℚ)⁻¹ • x) = x
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      simp [hn0]
    have hdvd : (n : ℤ) ∣ b.repr xL i := by
      rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [hn]; push_cast; rw [Int.abs_eq_natAbs]; omega
  have : xL = 0 := b.repr.injective (by ext i; simp [hrep i])
  exact congrArg Subtype.val this

private theorem exists_mem_bilinForm_eq_of_selfDual {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (L : Submodule ℤ V) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k)
    (ψ : L →ₗ[ℤ] ℤ) : ∃ x : L, ∀ y : L, B x y = ψ y := by
  classical
  have : NoZeroSMulDivisors ℤ V := ⟨fun {n v} h => by
    rw [← Int.cast_smul_eq_zsmul ℚ] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr h⟩
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ L

  have hexp : ∀ (x : V) (y : L), B x y = ∑ j, (b.repr y j : ℚ) * B x (b j) := by
    intro x y
    conv_lhs => rw [← b.sum_repr y]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, map_zsmul, zsmul_eq_mul]
  let G : Matrix _ _ ℤ := fun i j => ⌊B (b i) (b j)⌋
  have hG : ∀ i j, (G i j : ℚ) = B (b i) (b j) := fun i j =>
    floor_bilinForm_eq_of_mem_selfDual B L hL (b i).2 (b j).2
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv0
    let xL : L := ∑ i, v i • b i
    have hx : ∀ y ∈ L, B xL y = 0 := by
      intro y hy
      rw [show y = ((⟨y, hy⟩ : L) : V) from rfl, hexp]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : B xL (b j) = ((∑ i, v i * G i j : ℤ) : ℚ) := by
        simp only [xL, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul,
          LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul]
        push_cast
        simp [hG]
      have hz : (∑ i, v i * G i j) = 0 := by
        have := congrFun hv j
        simpa [Matrix.vecMul, dotProduct] using this
      rw [hj, hz]; simp
    have h0' : xL = 0 := Subtype.ext (eq_zero_of_bilinForm_eq_zero_on_selfDual B L hfg hL _ hx)
    ext i
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v h0'
    simpa using this i
  let Gq : Matrix _ _ ℚ := G.map (Int.cast : ℤ → ℚ)
  have hdetq : Gq.det ≠ 0 := by
    have := RingHom.map_det (Int.castRingHom ℚ) G
    simp only [RingHom.mapMatrix_apply, eq_intCast] at this
    rw [show Gq = G.map (Int.castRingHom ℚ) from rfl, ← this]
    exact_mod_cast hdet
  let ψv : _ → ℚ := fun j => (ψ (b j) : ℚ)
  let cq := Matrix.vecMul ψv Gq⁻¹
  have hc : Matrix.vecMul cq Gq = ψv := by
    simp only [cq, Matrix.vecMul_vecMul]
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetq), Matrix.vecMul_one]
  let x : V := ∑ i, cq i • (b i : V)
  have hxb : ∀ j, B x (b j) = ψv j := by
    intro j
    rw [← hc]
    simp only [x, map_sum, LinearMap.map_smul₂, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Gq, Matrix.map_apply, hG]
  have hxy : ∀ y : L, B x y = ψ y := by
    intro y
    rw [hexp]
    simp only [hxb, ψv]
    conv_rhs => rw [← b.sum_repr y]
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul]; push_cast; ring
  have hxL : x ∈ L := (hL x).2 fun y hy => ⟨ψ ⟨y, hy⟩, hxy ⟨y, hy⟩⟩
  exact ⟨⟨x, hxL⟩, hxy⟩

private theorem discreteTopology_map_of_integral_bilinForm {V : Type} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (L : Submodule ℤ V) (hfg : L.FG)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) :
    DiscreteTopology (L.map p) := by
  classical
  obtain ⟨T, hT⟩ := hfg
  let U : Set (Fin g → ℂ) := ⋂ s ∈ T, {z | |(z ⬝ᵥ Hm.mulVec (star (p s))).im| < 1}
  have hU : IsOpen U := by
    refine isOpen_biInter_finset fun s _ => isOpen_lt ?_ continuous_const
    exact continuous_abs.comp (Complex.continuous_im.comp
      (continuous_id.dotProduct continuous_const))
  apply discreteTopology_of_isOpen_singleton_zero
  have hset : ({0} : Set (L.map p)) = Subtype.val ⁻¹' U := by
    ext l
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      simp [U]
    · intro hl
      obtain ⟨x, hx, hxl⟩ := Submodule.mem_map.1 l.2
      have hsT : ∀ s ∈ T, B x s = 0 := by
        intro s hs
        have hsL : s ∈ L := hT ▸ Submodule.subset_span hs
        obtain ⟨k, hk⟩ := (hL x).1 hx s hsL
        have h1 := Set.mem_iInter₂.1 hl s hs
        simp only [Set.mem_setOf_eq, ← hxl, hB, hk] at h1
        have h2 : |(k : ℝ)| < 1 := by exact_mod_cast h1
        have hk0 : k = 0 := by
          rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at h2
        rw [hk, hk0]; simp
      have hall : ∀ y ∈ L, B x y = 0 := by
        intro y hy
        rw [← hT] at hy
        induction hy using Submodule.span_induction with
        | mem s hs => exact hsT s hs
        | zero => simp
        | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
        | smul n a _ ha => rw [map_zsmul, ha, smul_zero]
      have hx0 := eq_zero_of_bilinForm_eq_zero_on_selfDual B L ⟨T, hT⟩ hL x hall
      apply Subtype.ext
      rw [← hxl, hx0, map_zero]; rfl
  rw [hset]
  exact hU.preimage continuous_subtype_val

theorem proportional_of_selfDual {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : ℕ} (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (hp : Function.Injective p)
    (L : Submodule ℤ V) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ = 1) (f : Fin 2 → (Fin g → ℂ) → ℂ) (hd : ∀ k, Differentiable ℂ (f k))
    (hf : ∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f k z) : ¬ LinearIndependent ℂ f := by
  classical
  intro hli

  let e : L ≃ₗ[ℤ] L.map p := Submodule.equivMapOfInjective p hp L
  have he : ∀ l : L.map p, p (e.symm l : V) = l := fun l => by
    have h := congrArg Subtype.val (e.apply_symm_apply l)
    rw [Submodule.coe_equivMapOfInjective_apply] at h
    exact h
  have hint := fun {x y : V} (hx : x ∈ L) (hy : y ∈ L) => floor_bilinForm_eq_of_mem_selfDual B L hL hx hy

  let Ef : LinearMap.BilinForm ℤ (L.map p) := LinearMap.mk₂ ℤ
    (fun l m => ⌊B (e.symm l) (e.symm m)⌋)
    (fun l l' m => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, hint (e.symm (l + l')).2 (e.symm m).2, hint (e.symm l).2 (e.symm m).2,
        hint (e.symm l').2 (e.symm m).2, map_add, Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun n l m => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul, hint (e.symm (n • l)).2 (e.symm m).2,
        hint (e.symm l).2 (e.symm m).2, map_zsmul, Submodule.coe_smul, map_zsmul,
        LinearMap.smul_apply, zsmul_eq_mul])
    (fun l m m' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, hint (e.symm l).2 (e.symm (m + m')).2, hint (e.symm l).2 (e.symm m).2,
        hint (e.symm l).2 (e.symm m').2, map_add, Submodule.coe_add, map_add])
    (fun n l m => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul, hint (e.symm l).2 (e.symm (n • m)).2,
        hint (e.symm l).2 (e.symm m).2, map_zsmul, Submodule.coe_smul, map_zsmul, zsmul_eq_mul])
  have hEf : ∀ l m, ((Ef l m : ℤ) : ℚ) = B (e.symm l) (e.symm m) := fun l m =>
    hint (e.symm l).2 (e.symm m).2
  have hE : ∀ l m : L.map p, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := by
    intro l m
    rw [← he l, ← he m, hB, ← hEf]
    push_cast; rfl
  have hbij : Function.Bijective Ef := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro l hl
      have hx : ∀ y ∈ L, B (e.symm l) y = 0 := by
        intro y hy
        have h1 := LinearMap.congr_fun hl (e ⟨y, hy⟩)
        have h2 := hEf l (e ⟨y, hy⟩)
        rw [h1, LinearEquiv.symm_apply_apply] at h2
        simpa using h2.symm
      have h0 := eq_zero_of_bilinForm_eq_zero_on_selfDual B L hfg hL _ hx
      have : e.symm l = 0 := Subtype.ext h0
      simpa using congrArg e this
    · intro φ
      obtain ⟨x, hx⟩ := exists_mem_bilinForm_eq_of_selfDual B L hfg hL (φ ∘ₗ e.toLinearMap)
      refine ⟨e x, LinearMap.ext fun m => ?_⟩
      apply Int.cast_injective (α := ℚ)
      rw [hEf, LinearEquiv.symm_apply_apply, hx]
      simp
  have hdisc : DiscreteTopology (L.map p) := discreteTopology_map_of_integral_bilinForm B p L hfg hL hB
  have hspan : Submodule.span ℝ ((L.map p : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) = ⊤ := by
    rw [Submodule.map_coe]; exact hsp
  have key := card_le_pow_of_linearIndependent_theta_principal
    SiegelNormalForm.exists_normal_form
    (ClassicalTheta.card_le_pow_of_linearIndependent
      fourierCoeff_unitCube_translate_of_entire_periodic
      (entire_periodic_eq_zero_of_fourierCoeff_eq_zero
        fourierCoeff_unitCube_translate_of_entire_periodic))
  have h2 := key g (L.map p) hdisc hspan Hm (fun l => c (e.symm l)) Ef hH hpos
    (fun l => hc _) hE hbij 1 le_rfl 2 f (fun k => ⟨hd k, fun l z => by
      have h := hf k (e.symm l) (e.symm l).2 z
      rw [he l] at h
      rw [pow_one]; exact h⟩) hli
  norm_num at h2

theorem exists_eq_smul_of_isTheta1 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, ∀ θ θ' : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L θ → IsTheta1 X bas idx w x L θ' → θ' ≠ 0 → ∃ a : ℂ, θ = a • θ' := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw1 L hL x hxd θ θ' h1 h2 h0
  classical
  obtain ⟨hsymm, hposx, him, -, -, hinj, -, -⟩ := hx_laws E r X g bas idx n hs hn x hxd
  have hspE := TensLat.span_of_selfD X hL
  obtain ⟨hLfg, hLd⟩ := hL
  set Hm := ThFr.Hm X bas idx x with hHm
  have hform : ∀ z z', hx X bas idx x z z' = z ⬝ᵥ Hm.mulVec (star z') := fun z z' => by
    rw [hx_eq_hermForm idx x z z']; rfl
  have hH : Hm.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    have h := hsymm (Pi.single j 1) (Pi.single i 1)
    rw [hform, hform, SiegelNormalForm.form_single, SiegelNormalForm.form_single] at h
    rw [h]; rfl
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := fun z hz => by
    rw [← hform]; exact hposx z hz
  obtain ⟨B, hBE⟩ : ∃ B : LinearMap.BilinForm ℚ (Fin r → E), ∀ u v, EF X u v = B u v :=
    ⟨_, TensLat.EF_eq_bilin X⟩
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
    intro u v; funext j
    simp only [pv, per, Function.comp_apply, Pi.add_apply]
    split_ifs
    · simp only [Data.emb, hermC]
      simp [map_add, Finset.sum_add_distrib, mul_add, add_mul, dotProduct_add]
    · first | unfold Data.emb | skip
      simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  let p : (Fin r → E) →ₗ[ℤ] (Fin g → ℂ) := (AddMonoidHom.mk' (pv X idx x) hadd).toIntLinearMap
  have hp : ∀ v, p v = pv X idx x v := fun v => rfl
  have hfg' : (L.restrictScalars ℤ).FG := hLfg.restrictScalars
  have hL' : ∀ y, y ∈ L.restrictScalars ℤ ↔ ∀ z ∈ L.restrictScalars ℤ, ∃ k : ℤ, B y z = k := by
    intro y; simpa [hBE] using hLd y
  have hsp : Submodule.span ℝ (p '' ((L.restrictScalars ℤ : Submodule ℤ (Fin r → E)) : Set (Fin r → E))) = ⊤ :=
    span_image_pv idx hs hxd L hspE
  have hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ) := fun u v => by
    rw [hp, hp, ← hform, him, hBE]
  let c : (Fin r → E) → ℂ := fun v => cexp (-(Real.pi * I * ((EF X v (w • v) : ℚ) : ℂ)))
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp [c, Complex.norm_exp]
  have hlaw : ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ∀ v ∈ L.restrictScalars ℤ, ∀ z,
      ϑ (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
        Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * ϑ z := by
    intro ϑ hϑ v hv z
    have h := congrFun (hϑ.2 v hv) z
    simp only [fock, eps1, Pi.smul_apply, smul_eq_mul] at h
    rw [hform, add_dotProduct, smul_dotProduct, smul_eq_mul] at h
    rw [hp, ← h, ← _root_.mul_assoc, ← _root_.mul_assoc]
    simp only [c]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    have hS : ∀ s : ℂ, s = 0 → ϑ (z + pv X idx x v) = cexp s * ϑ (z + pv X idx x v) := by
      intro s hs0; rw [hs0, Complex.exp_zero, _root_.one_mul]
    apply hS
    push_cast
    ring
  have hnot := proportional_of_selfDual B p hinj (L.restrictScalars ℤ) hfg' hL' hsp hH hpos hB c hc
    ![θ, θ'] (fun k => by fin_cases k <;> simp [h1.1, h2.1])
    (fun k => by
      fin_cases k
      · exact hlaw θ h1
      · exact hlaw θ' h2)
  rw [LinearIndependent.pair_iff] at hnot
  push_neg at hnot
  obtain ⟨s, t, hst, hne⟩ := hnot
  by_cases hs0 : s = 0
  · subst hs0
    have ht : t ≠ 0 := hne rfl
    simp only [zero_smul, zero_add, smul_eq_zero, ht, false_or] at hst
    exact absurd hst h0
  · refine ⟨-t / s, ?_⟩
    funext z
    have hz := congrFun hst z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hz

end GlobalTheory.Dict.ThetaOne
