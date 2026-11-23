import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.CharRankZ

theorem finrank_int_le_mul {A M : Type} [CommRing A] [IsDomain A] [Module.Free ℤ A] [Module.Finite ℤ A]
    [AddCommGroup M] [Module A M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (hA : ∀ a : A, a ≠ 0 → ∃ (c : ℤ) (b : A), c ≠ 0 ∧ (c : A) = a * b) :
    Module.finrank ℤ M ≤ Module.finrank ℤ A * Module.finrank A M := by
  classical
  have hMA : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℤ A M
  have hmul : ∀ (a : A) (x : M), a ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ ∃ b : A, c • x = b • a • x := by
    intro a x ha
    obtain ⟨c, b, hc, hcb⟩ := hA a ha
    exact ⟨c, hc, b, by rw [← Int.cast_smul_eq_zsmul A, hcb, mul_comm, mul_smul]⟩
  haveI : NoZeroSMulDivisors A M := ⟨fun {a x} h => by
    by_contra hc
    push_neg at hc
    obtain ⟨c, hc0, b, hb⟩ := hmul a x hc.1
    rw [h, smul_zero] at hb
    exact hc.2 ((smul_eq_zero.mp hb).resolve_left hc0)⟩
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn A (id : M → M)
  have hli : LinearIndependent A (fun x : s => (x : M)) := hs
  haveI : Finite s := hli.finite
  haveI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s ≤ Module.finrank A M := hli.fintype_card_le_finrank
  let f : (s → A) →ₗ[A] M := Fintype.linearCombination A (fun x : s => (x : M))
  let S : Submodule ℤ M := LinearMap.range (f.restrictScalars ℤ)
  have hS : ∀ x : M, ∃ c : ℤ, c ≠ 0 ∧ c • x ∈ S := by
    intro x
    have hspan : Submodule.span A (id '' s) ≤ LinearMap.range f := by
      rw [Set.image_id, Fintype.range_linearCombination]
      exact Submodule.span_le.2 fun y hy => Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
    by_cases hx : x ∈ s
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact hspan (Submodule.subset_span ⟨x, hx, rfl⟩)
    · obtain ⟨a, ha, hax⟩ := hmax x hx
      obtain ⟨c, hc, b, hb⟩ := hmul a x ha
      refine ⟨c, hc, ?_⟩
      rw [hb]
      exact (LinearMap.range f).smul_mem b (hspan hax)
  have hq : Module.finrank ℤ (M ⧸ S) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨c, hc, hx⟩ := hS x
      exact ⟨c, hc, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hx⟩
  have h1 : Module.finrank ℤ (M ⧸ S) + Module.finrank ℤ S = Module.finrank ℤ M :=
    Submodule.finrank_quotient_add_finrank S
  have h2 : Module.finrank ℤ S ≤ Module.finrank ℤ (s → A) := LinearMap.finrank_range_le _
  have h3 : Module.finrank ℤ (s → A) = Fintype.card s * Module.finrank ℤ A := by
    simp [Module.finrank_pi_fintype]
  calc Module.finrank ℤ M = Module.finrank ℤ S := by omega
    _ ≤ Fintype.card s * Module.finrank ℤ A := h2.trans h3.le
    _ ≤ Module.finrank A M * Module.finrank ℤ A := Nat.mul_le_mul_right _ hcard
    _ = _ := mul_comm _ _

theorem exists_int_dvd {E : Type} [Field E] [NumberField E] (a : 𝓞 E) (ha : a ≠ 0) :
    ∃ (c : ℤ) (b : 𝓞 E), c ≠ 0 ∧ (c : 𝓞 E) = a * b := by
  have hmem := Ideal.absNorm_mem (Ideal.span {a})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨(Ideal.absNorm (Ideal.span {a}) : ℤ), b, ?_, ?_⟩
  · exact_mod_cast fun h => ha (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h))
  · rw [Int.cast_natCast, ← hb, mul_comm]

end GlobalTheory.CharRankZ

namespace GlobalTheory.CharRankZ

open GlobalTheory.CharRank

theorem finrank_oE_le_min {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (m : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (hCN : IsCN R)
    (hEt : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  obtain ⟨hNoeth, -, -, hChar⟩ := hCN
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    rw [← DomFine.spMap_comp', Category.assoc, hy]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem finrank_int_le_min : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → P.TorsionIso → Module.finrank ℤ P.D.toPre.X ≤ Module.finrank ℚ E * min D.p D.q := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hCN hEt _
  have h1 := finrank_oE_le_min Z R ξ t m P hCN hEt
  have h2 := finrank_int_le_mul (A := 𝓞 E) (M := P.D.toPre.X) (fun a ha => exists_int_dvd a ha)
  rw [RingOfIntegers.rank] at h2
  exact h2.trans (Nat.mul_le_mul_left _ h1)

end GlobalTheory.CharRankZ
