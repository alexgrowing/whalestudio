import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace FiltrationStepHilb

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem finiteDimensional_piece (n : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) n) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have hfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = n}.Finite := by
    refine (Finsupp.finite_of_nat_weight_eq (fun _ => (1 : ℕ)) (fun _ => one_ne_zero)
      (∑ k, n k)).subset ?_
    intro d hd
    simp only [Set.mem_ofPred_eq] at hd ⊢
    rw [← hd]
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, smul_eq_mul,
      mul_one]
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  have := hfin.to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = n})

omit [∀ k, Fintype (ι k)] in
open Classical in

theorem component_mul {f : MRing ι F} {s : K → ℕ} (hf : IsMultiHomog f s) (c : MRing ι F)
    (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (f * c) =
      if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (b := c) n hf
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact h

omit [∀ k, Fintype (ι k)] in
open Classical in

theorem mem_sup_span {L : Ideal (MRing ι F)} {f : MRing ι F} {s : K → ℕ}
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) {n : K → ℕ} {x : MRing ι F}
    (hx : x ∈ weightedHomogeneousSubmodule F (blockWeight ι) n) (hx' : x ∈ L ⊔ Ideal.span {f}) :
    ∃ c : MRing ι F, x - (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c
      else 0) ∈ L := by
  obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨c, ?_⟩
  have hx2 := weightedHomogeneousComponent_eq_self
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hx)
  rw [← hx2, map_add, mul_comm c f, component_mul hf, add_sub_cancel_right]
  exact hL l hl n

open Classical in

theorem finrank_step (L : Ideal (MRing ι F)) (f : MRing ι F) (s : K → ℕ)
    (hL : IsMultiHomogIdeal L) (hf : IsMultiHomog f s) (n : K → ℕ) :
    Module.finrank F (gradedPiece L n) =
      Module.finrank F (gradedPiece (L ⊔ Ideal.span {f}) n) +
        if s ≤ n then Module.finrank F (gradedPiece (L.colon {f}) (n - s)) else 0 := by
  have : ∀ d : K → ℕ, FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) d) :=
    fun d => finiteDimensional_piece d
  have : FiniteDimensional F (gradedPiece L n) := by unfold gradedPiece; infer_instance
  let q := (Ideal.Quotient.factorₐ F (le_sup_left : L ≤ L ⊔ Ideal.span {f})).toLinearMap
  let g := q.domRestrict (gradedPiece L n)
  have hrange : LinearMap.range g = gradedPiece (L ⊔ Ideal.span {f}) n := by
    rw [LinearMap.range_domRestrict]
    unfold gradedPiece
    rw [← Submodule.map_comp]
    rfl
  have hker_mem : ∀ a : gradedPiece L n, g a = 0 → ∃ c : MRing ι F,
      (a : MRing ι F ⧸ L) = Ideal.Quotient.mk L
        (if s ≤ n then f * weightedHomogeneousComponent (blockWeight ι) (n - s) c else 0) := by
    rintro ⟨a, ha⟩ hga
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    have hx0 : Ideal.Quotient.mk (L ⊔ Ideal.span {f}) x = 0 := hga
    obtain ⟨c, hc⟩ := mem_sup_span hL hf hx (Ideal.Quotient.eq_zero_iff_mem.mp hx0)
    exact ⟨c, Ideal.Quotient.eq.mpr hc⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange] at h1
  by_cases hsn : s ≤ n
  · let T := weightedHomogeneousSubmodule F (blockWeight ι) (n - s)
    have hmem : ∀ y : T, ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ LinearMap.mulLeft F f ∘ₗ
        T.subtype) y ∈ gradedPiece L n := fun y => by
      refine Submodule.mem_map_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_)
      have := IsWeightedHomogeneous.mul hf y.2
      rwa [add_tsub_cancel_of_le hsn] at this
    let μ := LinearMap.codRestrict (gradedPiece L n) ((Ideal.Quotient.mkₐ F L).toLinearMap ∘ₗ
      LinearMap.mulLeft F f ∘ₗ T.subtype) hmem
    let ν := (Ideal.Quotient.mkₐ F (L.colon {f})).toLinearMap.domRestrict T
    have hν : LinearMap.range ν = gradedPiece (L.colon {f}) (n - s) :=
      LinearMap.range_domRestrict _ _
    have hker : LinearMap.ker μ = LinearMap.ker ν := by
      ext y
      simp only [LinearMap.mem_ker]
      rw [← Subtype.coe_inj]
      change Ideal.Quotient.mk L (f * (y : MRing ι F)) = 0 ↔
        Ideal.Quotient.mk (L.colon {f}) (y : MRing ι F) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
        Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    have hμg : LinearMap.range μ = LinearMap.ker g := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        change Ideal.Quotient.mk (L ⊔ Ideal.span {f}) (f * (y : MRing ι F)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨y, mul_comm _ _⟩)
      · intro a ha
        obtain ⟨c, hc⟩ := hker_mem a ha
        rw [if_pos hsn] at hc
        exact ⟨⟨_, weightedHomogeneousComponent_mem _ c (n - s)⟩, Subtype.ext hc.symm⟩
    have h2 := LinearMap.finrank_range_add_finrank_ker μ
    have h3 := LinearMap.finrank_range_add_finrank_ker ν
    rw [hker] at h2
    have e : Module.finrank F (LinearMap.range μ) = Module.finrank F (LinearMap.range ν) :=
      Nat.add_right_cancel (h2.trans h3.symm)
    rw [hμg, hν] at e
    rw [if_pos hsn, ← e]
    exact h1.symm
  · have hk : LinearMap.ker g = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro a ha
      obtain ⟨c, hc⟩ := hker_mem a ha
      rw [if_neg hsn, map_zero] at hc
      exact Subtype.ext hc
    rw [hk, finrank_bot] at h1
    rw [if_neg hsn]
    omega

end FiltrationStepHilb

theorem FiltrationStepHilb.proof : FiltrationStepHilb.Statement.{u} := by
  intro F _ K _ _ ι _ L f s hL hf m
  by_cases hm : ∀ k, 0 ≤ m k
  · have key := FiltrationStepHilb.finrank_step L f s hL hf (fun k => (m k).toNat)
    have hms : (∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k) ↔ s ≤ fun k => (m k).toNat := by
      constructor
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply] at h1
        show s k ≤ (m k).toNat
        omega
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply]
        change s k ≤ (m k).toNat at h1
        omega
    unfold hilbFn
    rw [if_pos hm, if_pos hm]
    by_cases hsn : s ≤ fun k => (m k).toNat
    · have hn : (fun k => ((m - fun k => (s k : ℤ)) k).toNat) = (fun k => (m k).toNat) - s := by
        funext k
        have h1 := hsn k
        have h2 := hm k
        change s k ≤ (m k).toNat at h1
        simp only [Pi.sub_apply]
        omega
      rw [if_pos (hms.mpr hsn), hn, key, if_pos hsn]
      push_cast
      rfl
    · rw [if_neg (fun h => hsn (hms.mp h)), key, if_neg hsn]
      simp
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k := fun h => hm fun k => by
      have h1 := h k
      simp only [Pi.sub_apply] at h1
      omega
    unfold hilbFn
    simp only [if_neg hm, if_neg hm']
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
