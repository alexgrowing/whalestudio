import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem tsum_coeff_C_mul_pow_eq {K : Type} [NormedField K] (a u : K) :
    ∑' n, PowerSeries.coeff n (PowerSeries.C a) * u ^ n = a := by
  rw [tsum_eq_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])]
  simp

theorem summable_coeff_C_mul_pow {K : Type} [NormedField K] (a u : K) :
    Summable fun n => ‖PowerSeries.coeff n (PowerSeries.C a) * u ^ n‖ :=
  (hasSum_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])).summable

theorem ring_of_deformation : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  intro C _ _ _ _ e I I' _ _ Φ c π b ε hπ hε hb hsum
  classical

  set o : Subfield C := Subfield.closure (Set.range c) with ho_def
  have hoc : Countable o := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max _).trans
      (max_le (Cardinal.mk_le_aleph0_iff.2 (Set.finite_range c).countable.to_subtype) le_rfl)

  set G : Set (PowerSeries C) :=
    Set.range (fun x : o => PowerSeries.C (x : C)) ∪ Set.range Φ with hG
  set A : Subring (PowerSeries C) := Subring.closure G with hA
  obtain ⟨B, ev, t, hB, hev, ht, hevt, hfin⟩ := GlobalTheory.T.bounded_power_series_evaluation_divisibility C π hπ
  have hAB : A ≤ B := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · refine (hB _).2 ⟨‖(x : C)‖, fun n => ?_⟩
      rw [PowerSeries.coeff_C]; split_ifs <;> simp
    · exact (hB _).2 ⟨b, hb a⟩

  set S : Set (PowerSeries ℂ) := PowerSeries.map e '' G with hS
  have hSc : S.Countable :=
    ((Set.countable_range _).union (Set.finite_range Φ).countable).image _
  have hSs : ∀ Ψ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Ψ * u ^ n‖ := by
    rintro _ ⟨g, (⟨x, rfl⟩ | ⟨a, rfl⟩), rfl⟩ u hu0 hu
    · rw [PowerSeries.map_C]; exact summable_coeff_C_mul_pow _ _
    · simpa [PowerSeries.coeff_map] using hsum u hu0 hu a
  obtain ⟨u, ig, hu0, hu, hig, hige⟩ := GlobalTheory.T.exists_puncturedDisc_injective_evalAtPoint ε S hε hSc hSs
  have hmapA : ∀ x ∈ A, PowerSeries.map e x ∈ Subring.closure S := by
    intro x hx
    rw [hS, ← RingHom.map_closure]
    exact Subring.mem_map.2 ⟨x, hx, rfl⟩
  let m : A →+* Subring.closure S := (PowerSeries.map e).restrict A (Subring.closure S) hmapA
  have hm : ∀ x : A, (m x : PowerSeries ℂ) = PowerSeries.map e (x : PowerSeries C) := fun _ => rfl
  have hmapinj : Function.Injective (PowerSeries.map e) := by
    intro x y h
    ext n
    have := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_map] at this
    exact e.injective this
  have hminj : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    apply hmapinj
    rw [← hm, ← hm, h]
  let i : A →+* ℂ := ig.comp m
  have hi : Function.Injective i := hig.comp hminj
  let f : A →+* B := Subring.inclusion hAB
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  obtain ⟨W, _, _, _, _, _, g, i₀, i₁, hi₀, hgi₀, hgi₁, hunit, hprime⟩ :=
    GlobalTheory.T.exists_noetherianLocal_of_orderFunction A B C ℂ f ev t i hf hi ht hevt hfin
  let cA : o →+* A := (PowerSeries.C.comp o.subtype).codRestrict A
    (fun x => Subring.subset_closure (Or.inl ⟨x, rfl⟩))
  have hΦA : ∀ a, Φ a ∈ A := fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  haveI : CharZero W := RingHom.charZero i₁
  refine ⟨u, o, inferInstance, inferInstance, o.subtype,
    fun a => ⟨c a, Subfield.subset_closure ⟨a, rfl⟩⟩, hu0, hu, fun a => rfl,
    W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g.comp cA, i₀, i₁, fun a => g ⟨Φ a, hΦA a⟩, hi₀, ?_, ?_, hunit, hprime, fun a => ⟨?_, ?_⟩⟩
  · ext x
    have h1 := RingHom.congr_fun hgi₀ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1]
    show ig (m (cA x)) = e x
    rw [hige, hm]
    show ∑' n, PowerSeries.coeff n (PowerSeries.map e (PowerSeries.C (x : C))) * u ^ n = e x
    rw [PowerSeries.map_C, tsum_coeff_C_mul_pow_eq]
  · ext x
    have h1 := RingHom.congr_fun hgi₁ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1, hev]
    show ∑' n, PowerSeries.coeff n (PowerSeries.C (x : C)) * π ^ n = x
    rw [tsum_coeff_C_mul_pow_eq]
  · have h1 := RingHom.congr_fun hgi₀ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show ig (m ⟨Φ a, hΦA a⟩) = _
    rw [hige, hm]
    simp only [PowerSeries.coeff_map]
  · have h1 := RingHom.congr_fun hgi₁ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1, hev]
    rfl

end GlobalTheory.MBLow
