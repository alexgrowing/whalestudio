import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalDensityIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResidueFieldCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlatBasisOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open Formalism.MainNotions.S ValuativeRel PI.UnitaryGroupMassFormula.CntFormula
open Classical

theorem fld_dvd_iff {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : 𝒪[F]) :
    (∃ z ∈ L.O, algebraMap F E (a : F) = algebraMap F E (ϖ : F) * z) ↔ ϖ ∣ a := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · rintro ⟨z, hz, he⟩
    have hz' : z = algebraMap F E ((a : F) / ϖ) := by
      rw [div_eq_mul_inv, map_mul, he, mul_comm (algebraMap F E (ϖ : F)) z, mul_assoc, ← map_mul,
        mul_inv_cancel₀ hϖ0, map_one, mul_one]
    have hm : (a : F) / ϖ ∈ 𝒪[F] :=
      PI.UnitaryGroupMassFormula.CntFormula.fl_mem_int L (PI.UnitaryGroupMassFormula.CntFormula.fl_inj L) (hz' ▸ hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (a : F) = (ϖ : F) * ((a : F) / ϖ)
    field_simp
  · rintro ⟨c, rfl⟩
    exact ⟨algebraMap F E (c : F), PI.UnitaryGroupMassFormula.CntFormula.fl_int_mem L c, by simp [map_mul]⟩

theorem fld_count_core {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)
    (k : Type) [Field k] [Fintype k] (r : M.L.O →+* k) (hsurj : Function.Surjective r)
    (hker : ∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z)
    (hcard : Fintype.card k = Nat.card 𝓀[F] ^ 2)
    (hfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ Nat.card 𝓀[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ)
    (b : Fin (Module.finrank E V) → V) (hbΛ : ∀ k, b k ∈ Λ) (hbind : LinearIndependent E b)
    (hbcrd : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k)
    (Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E) (hQO : ∀ k l, Q k l ∈ M.L.O)
    (hQ : Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
        (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  have := hl
  set G₀ : Matrix ι ι E := Matrix.diagonal (fun i => algebraMap F E (a i : F)) with hG₀
  have hG1 : ∀ x y, G₀ x y ∈ M.L.O := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq]; exact fl_int_mem M.L (a x)
    · rw [hG₀, Matrix.diagonal_apply_ne _ h]; exact M.L.O.zero_mem
  have hG2 : ∀ x y, G₀ y x = M.L.cj (G₀ x y) := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq, M.L.cj.commutes]
    · rw [hG₀, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), map_zero]
  have hR : FC.RedData ϖ k r (Module.finrank E V) b Λ := ⟨hker, hsurj, hbΛ, hbind, hbcrd⟩
  have hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O := fun i j => (hΛ.2.2 (b i)).1 (hbΛ i) (b j) (hbΛ j)
  have hS := FC.card_count hR H hϖ o2 o3 hint (Nat.card 𝓀[F]) hfrob G₀ hG1
  let _ : Fintype 𝓀[F] := Fintype.ofFinite _
  have hqF : Fintype.card 𝓀[F] = Nat.card 𝓀[F] := Nat.card_eq_fintype_card.symm
  let ψ : 𝒪[F] →+* M.L.O := RingHom.codRestrict ((algebraMap F E).comp (𝒪[F]).subtype) M.L.O
    (fun c => FC.algO c)
  let φ0 : 𝒪[F] →+* k := r.comp ψ
  have hker0 : ∀ a ∈ IsLocalRing.maximalIdeal 𝒪[F], φ0 a = 0 := by
    intro a ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have h0 : r (ψ ϖ) = 0 := (hker _).2 ⟨1, M.L.O.one_mem, by
      show algebraMap F E (ϖ : F) = _
      rw [mul_one]⟩
    simp only [φ0, RingHom.comp_apply, map_mul, h0, mul_zero]
  let ι0 : 𝓀[F] →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[F]) φ0 hker0
  let _ : Algebra 𝓀[F] k := ι0.toAlgebra
  have hfin : Module.finrank 𝓀[F] k = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := 𝓀[F]) (V := k)
    rw [hcard, ← hqF] at h1
    exact (Nat.pow_right_injective (Fintype.one_lt_card (α := 𝓀[F]))).eq_iff.1 h1.symm
  let QO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O := fun i j => ⟨Q i j, hQO i j⟩
  let GO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O :=
    fun i j => ⟨H.h (b i) (b j), hint i j⟩
  have hQG : QO * GO = 1 := by
    have e1 : QO.map M.L.O.subtype = Q := by ext i j; rfl
    have e2 : GO.map M.L.O.subtype = Matrix.of fun k l => H.h (b k) (b l) := by ext i j; rfl
    apply Matrix.map_injective (f := M.L.O.subtype) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e1, e2, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPh : IsUnit (FC.Ph r H b hint).det := by
    have h2 : (QO.map r) * (GO.map r) = 1 := by
      rw [← Matrix.map_mul, hQG, Matrix.map_one _ (map_zero r) (map_one r)]
    exact Matrix.isUnit_det_of_left_inverse h2
  have hPhH : ∀ i j, FC.Ph r H b hint j i = FC.Ph r H b hint i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨H.h (b i) (b j), hint i j⟩ ⟨H.h (b j) (b i), hint j i⟩ (H.h_herm (b i) (b j))
  set m := Fintype.card ι
  let e := Fintype.equivFin ι
  let Gm : Matrix (Fin m) (Fin m) k := fun i j => r ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩
  have hGmH : ∀ i j, Gm j i = Gm i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ ⟨G₀ (e.symm i) (e.symm j), hG1 _ _⟩
      (hG2 (e.symm j) (e.symm i))

  let d : Fin m → k := fun i => r ⟨algebraMap F E (a (e.symm i) : F), fl_int_mem M.L _⟩
  have hGmd : Gm = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      exact congrArg r (Subtype.ext (show G₀ (e.symm i) (e.symm i) = _ from Matrix.diagonal_apply_eq _ _))
    · rw [Matrix.diagonal_apply_ne _ h]
      have hne : e.symm j ≠ e.symm i := fun h' => h (e.symm.injective h').symm
      exact (congrArg r (Subtype.ext (show G₀ (e.symm j) (e.symm i) = 0 from Matrix.diagonal_apply_ne _ hne) :
        (⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ : M.L.O) = 0)).trans (map_zero r)
  have hd0 : ∀ i, d i = 0 ↔ ϖ ∣ a (e.symm i) := by
    intro i
    rw [hker]
    exact fld_dvd_iff M.L hϖ _
  have hrank : m - Gm.rank = (Finset.univ.filter fun i => ϖ ∣ a i).card := by
    have hc := Fintype.card_subtype_compl (fun i : Fin m => d i ≠ 0)
    rw [Fintype.card_fin] at hc
    rw [hGmd, Matrix.rank_diagonal, ← hc]
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquiv e.symm fun i => ?_))
    rw [← hd0]
    exact not_not
  have hT : Nat.card {X : ι → Fin (Module.finrank E V) → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * FC.Ph r H b hint i j * X a j ^ Nat.card 𝓀[F] = r ⟨G₀ a a', hG1 a a'⟩} =
      Formalism.L2.SG.DensExact.countInert 𝓀[F] k (Module.finrank E V) m (FC.Ph r H b hint) Gm := by
    unfold Formalism.L2.SG.DensExact.countInert
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) fun X => ?_)
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Set.mem_ofPred_eq, hqF]
    refine and_congr (linearIndependent_equiv e.symm).symm ⟨fun h i j => h (e.symm j) (e.symm i), fun h a a' => ?_⟩
    have := h (e a') (e a)
    simpa [Gm] using this
  have hD := density_exact_inert 𝓀[F] k hfin (Module.finrank E V) m (FC.Ph r H b hint) Gm hPh hPhH hGmH
  rw [hrank, hqF] at hD
  unfold Loc.HermSp.dens
  rw [hS, hT, ← hD]
  congr 1
  have hq0 : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    rw [← hqF]; exact_mod_cast Fintype.card_ne_zero
  rw [show ((2 * Module.finrank E V * m : ℤ) - (m : ℤ) ^ 2) =
      ((2 * Module.finrank E V * m : ℕ) : ℤ) - ((m ^ 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

theorem fieldCount_holds : FieldCount := by
  intro F E _ _ _ _ _ _ _ M hl hc hE V _ _ H Λ hΛ ϖ hϖ ι _ _ a _
  obtain ⟨_, o2, o3⟩ := local_density_integral F E M.L hl hc hE ϖ hϖ
  obtain ⟨rmax, rcard, rfrob⟩ := residue_field_count F E M.L hl hc hE ϖ hϖ
  obtain ⟨b, hb1, hb2, hb3, Q, hQ1, hQ2⟩ := flatBasis_of local_density_integral F E M hl hc hE V H Λ hΛ
  let _ : Field (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Ideal.Quotient.field _
  have hq : 0 < Nat.card 𝓀[F] := Nat.card_pos
  have : Finite (M.L.O ⧸ Ideal.span {piO M.L ϖ}) :=
    Nat.finite_of_card_ne_zero (by rw [rcard]; positivity)
  let _ : Fintype (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Fintype.ofFinite _
  refine fld_count_core M hl ϖ hϖ o2 o3 (M.L.O ⧸ Ideal.span {piO M.L ϖ})
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_ ?_ rfrob V H Λ hΛ b hb1 hb2 hb3 Q hQ1 hQ2 ι a
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, by rw [← hc]; simp [piO, mul_comm]⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, he, mul_comm])⟩
  · rw [Fintype.card_eq_nat_card, rcard]

end PI.UnitaryGroupMassFormula.LocDensCorank
