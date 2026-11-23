import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FrIcFree

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_frob {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x y : L.O, (y : E) = L.cj x →
      Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F] := by
  have := hl
  have hinj := fl_inj L
  have hmax : 𝓂[F] = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmaxI : (Ideal.span {piO L ϖ}).IsMaximal := fr_max L hl hE ϖ hϖ
  let I := Ideal.span {piO L ϖ}
  let : Field (L.O ⧸ I) := Ideal.Quotient.field I
  have hcard : Nat.card (L.O ⧸ I) = Nat.card 𝓀[F] ^ 2 := fr_card L hl hc hE ϖ hϖ
  have hq0 : 0 < Nat.card 𝓀[F] := Nat.card_pos
  have : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let : Fintype (L.O ⧸ I) := Fintype.ofFinite _
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  let ι0 : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (valuation F).integer.subtype).codRestrict L.O (fun a => fl_int_mem L a)
  have hι0 : ∀ a : 𝒪[F], (ι0 a : E) = algebraMap F E a := fun _ => rfl
  let f0 : 𝒪[F] →+* (L.O ⧸ I) := (Ideal.Quotient.mk I).comp ι0
  have hf0ϖ : f0 ϖ = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.2
    have : ι0 ϖ = piO L ϖ := rfl
    rw [this]
    exact Ideal.subset_span rfl
  have : IsLocalHom f0 := ⟨fun a ha => by
    by_contra hna
    have ham : a ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [hmax, Ideal.mem_span_singleton'] at ham
    obtain ⟨b, rfl⟩ := ham
    rw [map_mul, hf0ϖ, mul_zero] at ha
    exact not_isUnit_zero ha⟩
  let ρ : 𝓀[F] →+* (L.O ⧸ I) := IsLocalRing.ResidueField.lift f0
  let : Algebra 𝓀[F] (L.O ⧸ I) := ρ.toAlgebra
  have hρ : ∀ a : 𝒪[F], algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] a) = f0 a := fun _ => rfl
  let cjO : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, fl_cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, fl_cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) (y : E))
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) (y : E)) }
  have hcjι : ∀ a : 𝒪[F], cjO (ι0 a) = ι0 a := fun a => Subtype.ext (AlgEquiv.commutes L.cj _)
  have hIcj : I = I.map (cjO : L.O →+* L.O) := by
    show Ideal.span {piO L ϖ} = (Ideal.span {piO L ϖ}).map (cjO : L.O →+* L.O)
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (hcjι ϖ).symm
  let σ0 : (L.O ⧸ I) ≃+* (L.O ⧸ I) := Ideal.quotientEquiv I I cjO hIcj
  have hσ0 : ∀ x : L.O, σ0 (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (cjO x) := fun _ => rfl
  let σ : (L.O ⧸ I) ≃ₐ[𝓀[F]] (L.O ⧸ I) := AlgEquiv.ofRingEquiv (f := σ0) (fun a => by
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    rw [hρ]
    show σ0 (Ideal.Quotient.mk I (ι0 a')) = Ideal.Quotient.mk I (ι0 a')
    rw [hσ0, hcjι])
  have hσ : ∀ x : L.O, σ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (cjO x) := fun _ => rfl
  let Fr := FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I)
  have hFr : ∀ z, Fr z = z ^ Fintype.card 𝓀[F] := fun _ => rfl
  have hkey : ∀ z, (Fr z - z) * (Fr z - σ z) = 0 := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨t, ht⟩ := fl_trace L hinj x.2
    obtain ⟨n, hn⟩ := fl_norm L hinj x.2
    have hT : Ideal.Quotient.mk I x + σ (Ideal.Quotient.mk I x) =
        algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] t) := by
      rw [hσ, ← map_add, hρ]
      show _ = Ideal.Quotient.mk I (ι0 t)
      congr 1
      exact Subtype.ext (by rw [hι0, ht]; rfl)
    have hN : Ideal.Quotient.mk I x * σ (Ideal.Quotient.mk I x) =
        algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] n) := by
      rw [hσ, ← map_mul, hρ]
      show _ = Ideal.Quotient.mk I (ι0 n)
      congr 1
      exact Subtype.ext (by rw [hι0, hn]; rfl)
    have h0 : Ideal.Quotient.mk I x ^ 2 - algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] t) *
        Ideal.Quotient.mk I x + algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] n) = 0 := by
      rw [← hT, ← hN]; ring
    have h1 := congrArg Fr h0
    rw [map_add, map_sub, map_pow, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_zero,
      ← hT, ← hN] at h1
    linear_combination h1
  have hq1 : 1 < Fintype.card 𝓀[F] := Fintype.one_lt_card
  have hfr : Module.finrank 𝓀[F] (L.O ⧸ I) = 2 := by
    have h := Module.card_eq_pow_finrank (K := 𝓀[F]) (V := L.O ⧸ I)
    rw [Fintype.card_eq_nat_card, hcard, Fintype.card_eq_nat_card] at h
    rw [← Fintype.card_eq_nat_card] at h
    exact (Nat.pow_right_injective hq1 h).symm
  have hσFr : σ = Fr := by
    obtain ⟨m, hm⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[F] (L.O ⧸ I)).2 σ
    have hm2 : m.1 < 2 := hfr ▸ m.2
    rcases (by omega : m.1 = 0 ∨ m.1 = 1) with h | h
    · exfalso
      have hs1 : σ = 1 := by rw [← hm]; simp only [h, pow_zero]
      have hF1 : Fr = 1 := by
        ext z
        have := hkey z
        rw [hs1, AlgEquiv.one_apply, mul_self_eq_zero, sub_eq_zero] at this
        exact this
      have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I)
      rw [show FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I) = 1 from hF1, orderOf_one,
        hfr] at ho
      omega
    · rw [← hm]; simp only [h, pow_one]; rfl
  intro x y hxy
  have hy : y = cjO x := Subtype.ext hxy
  rw [hy, ← hσ x, hσFr, hFr, Fintype.card_eq_nat_card]

theorem residue_field_count : FResField := by
  intro F E _ _ _ _ _ _ L hl hc hE ϖ hϖ
  exact ⟨fr_max L hl hE ϖ hϖ, fr_card L hl hc hE ϖ hϖ, fr_frob L hl hc hE ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
