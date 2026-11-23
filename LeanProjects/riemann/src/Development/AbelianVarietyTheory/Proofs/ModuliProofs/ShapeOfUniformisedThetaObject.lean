import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfHermFormPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem map_sum_nsmul_eq_listProd {V G : Type} [AddCommGroup V] [Group G] (E : V → G)
    (hE : ∀ z w, E (z + w) = E z * E w) : ∀ (n : ℕ) (a : Fin n → ℕ) (z : Fin n → V),
    E (∑ i, a i • z i) = (List.ofFn fun i => E (z i) ^ a i).prod := by
  have h0 : E 0 = 1 := by
    have := hE 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hp : ∀ (m : ℕ) (x : V), E (m • x) = E x ^ m := by
    intro m x
    induction m with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ m ih => rw [succ_nsmul, hE, ih, pow_succ]
  intro n
  induction n with
  | zero => intro a z; simp [h0]
  | succ n ih =>
    intro a z
    rw [Fin.sum_univ_succ, hE, List.ofFn_succ, List.prod_cons, hp, ih]

theorem linearMap_eq_of_span_real {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z ∈ s, F z = F' z) : F = F' := by
  have : F.restrictScalars ℝ = F'.restrictScalars ℝ := LinearMap.ext_on hs h
  exact LinearMap.restrictScalars_injective ℝ this

theorem level_comb_sub_mem {g n k : ℕ} (hk : (k : ℂ) ≠ 0) {La : Type} [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
    (lam : Fin n → La) (m : Fin n → ℤ) (y : La) :
    ∃ x, (k : ℂ)⁻¹ • Q (∑ i, m i • lam i + k • y) =
      ∑ i, ((m i : ZMod k)).val • ((k : ℂ)⁻¹ • Q (lam i)) + Q x := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : NeZero k := ⟨hk0⟩
  refine ⟨∑ i, (m i / k) • lam i + y, ?_⟩
  rw [map_add, map_add, map_sum, map_sum, map_nsmul, smul_add, Finset.smul_sum, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (((m i : ZMod k).val : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) := by rw [ZMod.val_intCast]
    have h2 : ((m i : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) + (k : ℂ) * ((m i / k : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (m i) k).symm
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [Int.cast_natCast] at h1
    rw [h1]
    conv_lhs => rw [h2]
    field_simp
  · rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk]

theorem shape_of_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∀ j i, ∃ y, ac j (lam i) = ∑ i', Mat j i' i • lam i' + k • y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re) → t.Shape Mat κ := by
  intro hL hL2 _ hU o _ g k J b em w w' t La _ EF lam ac Q Hm Mat κ ⟨u, χ', hAH, hΛ, _, hpt, hact⟩ hMat hB j
  obtain ⟨F, hFQ, hF⟩ := hact j
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hMat j i
    let E : (Fin g → ℂ) → (Out.baseOver (Sp ℂ) ⟶ t.A) := u.ex
    have hE : ∀ z w, E (z + w) = E z * E w := u.ex_add
    have hpt' : ∀ i₀, t.pt i₀ = E ((k : ℂ)⁻¹ • Q (lam i₀)) := fun i₀ => Over.OverMorphism.ext (hpt i₀)
    have hF' : ∀ z, E (F z) = E z ≫ t.act j := hF
    obtain ⟨x, hx⟩ := level_comb_sub_mem hk Q lam (fun i' => Mat j i' i) y
    have h1 : E (Q x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    rw [hpt', ← hF', map_smul, hFQ, hy, hx, hE, h1, _root_.mul_one, map_sum_nsmul_eq_listProd E hE]
    simp only [TObj.lab, Out.linComb, hpt']
  · obtain ⟨F', hFQ', hF'⟩ := hB j
    have hFF : F' = F := linearMap_eq_of_span_real _ u.full _ _ fun z hz => by
      obtain ⟨x, rfl⟩ := (hΛ z).1 hz
      rw [hFQ, hFQ']
    subst hFF
    exact GlobalTheory.relAmple_of_hermForm_pos hL hL2 hU t.pol u Hm χ' (t.act j) F' κ hAH (t.hom j) hF hF'

end GlobalTheory.ZM
end
