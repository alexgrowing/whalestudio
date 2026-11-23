import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Overlattice

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (hermForm Hm y w).im := rfl

private theorem hermForm_swap_eq_star_of_isHermitian {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (y w : Fin g → ℂ) : hermForm Hm w y = star (hermForm Hm y w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

theorem imForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (y w : Fin g → ℂ) :
    imForm Hm w y = - imForm Hm y w := by
  rw [imForm_apply, imForm_apply, hermForm_swap_eq_star_of_isHermitian hH y w]
  exact Complex.conj_im _

theorem imForm_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    imForm Hm y (Complex.I • y) = - (hermForm Hm y y).re := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [imForm_apply, hermForm, star_smul, hI, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

theorem imForm_sepLeft {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (y : Fin g → ℂ)
    (hy : ∀ w, imForm Hm y w = 0) : y = 0 := by
  by_contra h
  have h1 := hy (Complex.I • y)
  rw [imForm_I] at h1
  have h2 := hpos y h
  linarith

theorem imForm_nondegenerate {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : (imForm Hm).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate
  refine ⟨fun y hy => imForm_sepLeft hpos y hy, fun y hy => imForm_sepLeft hpos y fun w => ?_⟩
  rw [imForm_swap hH w y, hy w, neg_zero]

end GlobalTheory.Overlattice

namespace GlobalTheory.Overlattice

theorem exists_selfDual_overlattice {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B y x = - B x y) (Λ : Submodule ℤ V) (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ n : ℤ, B a b = n) :
    ∃ Λ₁ : Submodule ℤ V, Λ ≤ Λ₁ ∧ (∀ a ∈ Λ₁, ∀ b ∈ Λ₁, ∃ n : ℤ, B a b = n) ∧
      ∀ x, (∀ l ∈ Λ₁, ∃ n : ℤ, B x l = n) → x ∈ Λ₁ := by
  classical
  have hself : ∀ x, B x x = 0 := fun x => by have := hB x x; linarith
  let S : Set (Submodule ℤ V) := {M | ∀ a ∈ M, ∀ b ∈ M, ∃ n : ℤ, B a b = n}
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨sSup c, fun a ha b hb => ?_, fun z hz => le_sSup hz⟩
    have hne : c.Nonempty := ⟨y, hy⟩
    obtain ⟨p, hp, hap⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).mp ha
    obtain ⟨q, hq, hbq⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).mp hb
    rcases hc.total hp hq with h | h
    · exact hcS hq a (h hap) b hbq
    · exact hcS hp a hap b (h hbq)
  obtain ⟨Λ₁, hle, hmax⟩ := zorn_le_nonempty₀ S hchain Λ hΛ
  refine ⟨Λ₁, hle, hmax.prop, fun x hx => ?_⟩
  have hM : Λ₁ ⊔ Submodule.span ℤ {x} ∈ S := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp ha₂
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hb₂
    obtain ⟨n₁, h₁⟩ := hmax.prop a₁ ha₁ b₁ hb₁
    obtain ⟨n₂, h₂⟩ := hx b₁ hb₁
    obtain ⟨n₃, h₃⟩ := hx a₁ ha₁
    have e : B (a₁ + m • x) (b₁ + k • x) = B a₁ b₁ + k * B a₁ x + m * B x b₁ + m * k * B x x := by
      simp only [← Int.cast_smul_eq_zsmul ℝ, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring
    refine ⟨n₁ - k * n₃ + m * n₂, ?_⟩
    rw [e, hself, hB x a₁, h₁, h₂, h₃]
    push_cast
    ring
  exact hmax.2 hM le_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))

theorem exists_nsmul_mem_of_dual {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hint : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ n : ℤ, imForm Hm a b = n) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (∀ l ∈ Λ, ∃ n : ℤ, imForm Hm x l = n) → N • x ∈ Λ := by
  classical
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set b := Module.Free.chooseBasis ℤ Λ with hb_def
  set e := b.ofZLatticeBasis ℝ Λ with he_def
  have he : ∀ i, e i = (b i : Fin g → ℂ) := fun i => b.ofZLatticeBasis_apply ℝ Λ i
  have hG : ∀ i j, ∃ n : ℤ, imForm Hm (e j) (e i) = n := fun i j => by
    rw [he, he]; exact hint _ (b j).2 _ (b i).2
  choose Gf hGe using hG
  set G : Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ) ℤ :=
    Matrix.of Gf with hG_def
  set GR : Matrix _ _ ℝ := (Int.castRingHom ℝ).mapMatrix G with hGR
  have hGRe : ∀ i j, GR i j = imForm Hm (e j) (e i) := fun i j => by
    rw [hGe]; rfl
  have key : ∀ (c : _ → ℝ) i, imForm Hm (∑ j, c j • e j) (e i) = (Matrix.mulVec GR c) i := by
    intro c i
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, hGRe]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hd : G.det ≠ 0 := by
    intro h0
    have h0' : GR.det = 0 := by rw [hGR, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0'
    have hy : (∑ j, v j • e j) = 0 := by
      apply imForm_sepLeft hpos
      have h0f : imForm Hm (∑ j, v j • e j) = 0 := e.ext fun i => by
        rw [key, hGv]; simp
      intro w
      rw [h0f]; rfl
    exact hv (funext fun j => Fintype.linearIndependent_iff.mp e.linearIndependent v hy j)
  refine ⟨G.det.natAbs, Int.natAbs_pos.mpr hd, fun x hx => ?_⟩
  have hm : ∀ i, ∃ n : ℤ, (Matrix.mulVec GR ⇑(e.repr x)) i = n := fun i => by
    rw [← key, e.sum_repr x]
    exact hx (e i) (by rw [he]; exact (b i).2)
  choose m hm using hm
  have hdc : ∀ j, ∃ k : ℤ, (G.det : ℝ) * e.repr x j = k := by
    intro j
    refine ⟨(Matrix.mulVec G.adjugate m) j, ?_⟩
    have h1 : Matrix.mulVec GR ⇑(e.repr x) = fun i => (m i : ℝ) := funext hm
    have h2 : Matrix.mulVec GR.adjugate (Matrix.mulVec GR ⇑(e.repr x)) = GR.det • ⇑(e.repr x) := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h3 := congrFun h2 j
    rw [h1, hGR, ← RingHom.map_adjugate, ← RingHom.map_det, Pi.smul_apply, smul_eq_mul] at h3
    rw [show (G.det : ℝ) * e.repr x j = _ from h3.symm]
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
    push_cast
    rfl
  choose k hk using hdc
  have hdx : G.det • x ∈ Λ := by
    have hsum : G.det • x = ∑ j, k j • (b j : Fin g → ℂ) := by
      conv_lhs => rw [← e.sum_repr x]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← he, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, hk]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
  rcases Int.natAbs_eq G.det with h | h
  · rw [h, natCast_zsmul] at hdx
    exact hdx
  · rw [h, neg_smul, natCast_zsmul, neg_mem_iff] at hdx
    exact hdx

end GlobalTheory.Overlattice

namespace GlobalTheory.Overlattice

theorem exists_unimodular_overlattice : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (hermForm Hm l l').im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (Ef : LinearMap.BilinForm ℤ Λ₁) (N : ℕ), Λ ≤ Λ₁ ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧ (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
      Function.Bijective Ef ∧ 0 < N ∧ ∀ x ∈ Λ₁, N • x ∈ Λ := by
  classical
  intro g Λ Hm hdisc hsp hH hpos hint
  have hint' : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ n : ℤ, imForm Hm a b = n := fun a ha b hb => by
    rw [imForm_apply]; exact hint a ha b hb
  obtain ⟨Λ₁, hle, hint₁, hdual₁⟩ :=
    exists_selfDual_overlattice (imForm Hm) (fun x y => imForm_swap hH x y) Λ hint'
  haveI := hdisc
  obtain ⟨N, hN, hNx⟩ := exists_nsmul_mem_of_dual hH hpos Λ hsp hint'
  have hNΛ₁ : ∀ x ∈ Λ₁, N • x ∈ Λ := fun x hx => hNx x fun l hl => hint₁ x hx l (hle hl)
  have hdisc₁ : DiscreteTopology Λ₁ := by
    let f : Λ₁ → Λ := fun x => ⟨N • (x : Fin g → ℂ), hNΛ₁ x x.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.nsmul N) _
    · intro x y hxy
      have hxy' : N • (x : Fin g → ℂ) = N • (y : Fin g → ℂ) := congrArg Subtype.val hxy
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hxy'
      exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hN.ne') hxy')
  have hsp₁ : Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ := by
    rw [eq_top_iff, ← hsp]; exact Submodule.span_mono hle
  have hF : ∀ a b : Λ₁, ∃ n : ℤ, imForm Hm a b = n := fun a b => hint₁ a a.2 b b.2
  choose F hF using hF
  have inj : Function.Injective (Int.cast : ℤ → ℝ) := Int.cast_injective
  let Ef : LinearMap.BilinForm ℤ Λ₁ := LinearMap.mk₂ ℤ F
    (fun a a' b => inj (by
      rw [Int.cast_add, ← hF, ← hF, ← hF, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun c a b => inj (by
      rw [smul_eq_mul, Int.cast_mul, ← hF, ← hF, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ,
        map_smul, LinearMap.smul_apply, smul_eq_mul]))
    (fun a b b' => inj (by
      rw [Int.cast_add, ← hF, ← hF, ← hF, Submodule.coe_add, map_add]))
    (fun c a b => inj (by
      rw [smul_eq_mul, Int.cast_mul, ← hF, ← hF, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℝ,
        map_smul, smul_eq_mul]))
  have hEf : ∀ a b : Λ₁, (Ef a b : ℝ) = imForm Hm a b := fun a b => (hF a b).symm
  have hnd := imForm_nondegenerate hH hpos
  refine ⟨Λ₁, Ef, N, hle, hdisc₁, hsp₁, fun a b => by rw [hEf, imForm_apply], ⟨?_, ?_⟩, hN, hNΛ₁⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : imForm Hm (a : Fin g → ℂ) = 0 := LinearMap.ext_on hsp₁ fun w hw => by
      have := congrArg (fun φ : Λ₁ →ₗ[ℤ] ℤ => ((φ ⟨w, hw⟩ : ℤ) : ℝ)) ha
      simp only [hEf, LinearMap.zero_apply, Int.cast_zero] at this
      simpa using this
    exact Subtype.ext (imForm_sepLeft hpos a fun w => by rw [h0]; rfl)
  · intro φ
    haveI : IsZLattice ℝ Λ₁ := ⟨hsp₁⟩
    haveI := ZLattice.module_finite ℝ Λ₁
    haveI := ZLattice.module_free ℝ Λ₁
    set b := Module.Free.chooseBasis ℤ Λ₁ with hb_def
    set e := b.ofZLatticeBasis ℝ Λ₁ with he_def
    have he : ∀ i, e i = (b i : Fin g → ℂ) := fun i => b.ofZLatticeBasis_apply ℝ Λ₁ i
    set D := (imForm Hm).dualBasis hnd e with hD
    set x : Fin g → ℂ := ∑ i, (φ (b i) : ℝ) • D i with hx_def
    have hxe : ∀ j, imForm Hm x (e j) = φ (b j) := by
      intro j
      rw [hx_def, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hD,
        LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero]
      simp
    have hmaps : ((imForm Hm x).restrictScalars ℤ).comp Λ₁.subtype = (Algebra.linearMap ℤ ℝ).comp φ :=
      b.ext fun j => by
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
          Algebra.linearMap_apply, ← he, hxe, eq_intCast]
    have hxl : ∀ l : Λ₁, imForm Hm x l = φ l := fun l => by
      have := LinearMap.congr_fun hmaps l
      simpa using this
    have hxmem : x ∈ Λ₁ := hdual₁ x fun l hl => ⟨φ ⟨l, hl⟩, hxl ⟨l, hl⟩⟩
    refine ⟨⟨x, hxmem⟩, LinearMap.ext fun l => inj ?_⟩
    rw [hEf]
    exact hxl l

end GlobalTheory.Overlattice
