import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers

set_option autoImplicit false

noncomputable section

open NumberField Module

namespace GlobalTheory

theorem exists_isShortGen_of_short_span : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) →
    (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L →
    Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) →
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧
      abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧
      n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  intro K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K V := ⟨fun q a x => by
    show (q • a) • x = (algebraMap ℚ K q) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspL : Submodule.span K (L : Set V) = ⊤ := eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)
  have hrk : Formalism.HN.rkK L = Module.finrank K V := by
    rw [Formalism.HN.rkK, hspL, finrank_top]

  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent K s
  let vb : Basis t K V := Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])
  haveI : Finite t := Module.Finite.finite_basis vb
  haveI : Fintype t := Fintype.ofFinite t
  have hm : Fintype.card t = Formalism.HN.rkK L := by rw [hrk, finrank_eq_card_basis vb]

  obtain ⟨ω, hωi, hωb⟩ := exists_short_independent_integers K
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let ob : Basis (Fin (finrank ℚ K)) ℚ K := basisOfLinearIndependentOfCardEqFinrank hωi (by simp)
  have hob : ∀ k, ob k = (ω k : K) := fun k => by
    simp [ob, coe_basisOfLinearIndependentOfCardEqFinrank]
  let E : Basis (Fin (finrank ℚ K) × t) ℚ V := ob.smulTower vb
  have hE : ∀ p, E p = ω p.1 • (p.2 : V) := fun p => by
    rw [Basis.smulTower_apply, hob, Basis.mk_apply]
    exact algebraMap_smul K (ω p.1) (p.2 : V)

  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hsm σ 0 0
  have hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i) := by
    intro σ ι S f
    induction S using Finset.induction_on with
    | empty => simp [hN0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  have hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x := fun σ q x => by
    have := hsm σ (algebraMap ℚ K q) x
    rw [eq_ratCast, map_ratCast, Complex.norm_ratCast] at this
    exact this

  set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC
  have hEle : ∀ σ p, N σ (E p) ≤ C := fun σ p => by
    rw [hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]
    have h1 := hA _ (hts p.2.2) σ
    exact mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))

  let red : V → V := fun x => ∑ p, Int.fract (E.repr x p) • E p
  have hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E) := fun x => by
    have hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p := by
      rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      conv_lhs => rw [← E.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C := fun σ x => by
    refine (hsum σ _ _).trans ?_
    have hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)),
        N σ (Int.fract (E.repr x p) • E p) ≤ C := fun p _ => by
      rw [hq]
      have h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]
        exact_mod_cast (Int.fract_lt_one _).le
      exact (mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]
    push_cast; ring

  haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by
    rw [← Int.cast_smul_eq_zsmul K] at h
    exact (smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩
  let Lz := L.restrictScalars ℤ
  haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars
  haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'
  let ZB := Module.Free.chooseBasis ℤ Lz
  let bZ : Module.Free.ChooseBasisIndex ℤ Lz → V := fun j => (ZB j : V)
  have hZq : LinearIndependent ℚ bZ := (LinearIndependent.iff_fractionRing ℤ ℚ).1
    (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))
  haveI : Module.Finite ℚ V := Module.Finite.of_basis E
  have hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t) := by
    rw [← finrank_eq_card_basis E]; exact hZq.fintype_card_le_finrank
  have hLz : Lz = Submodule.span ℤ (Set.range bZ) := by
    rw [show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span,
      ZB.span_eq, Submodule.map_top, Submodule.range_subtype]

  let F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V := Sum.elim E (fun j => red (bZ j))
  let e := Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)
  have hEL : ∀ p, E p ∈ L := fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))
  have hspanE : Submodule.span ℤ (Set.range E) ≤ Lz :=
    Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)
  have hrng : Set.range (F ∘ e.symm) = Set.range F := e.symm.surjective.range_comp F
  have hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hC]; ring
  refine ⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A),
    ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩
  · rw [hrng]
    constructor
    · intro hx
      have hx' : x ∈ Lz := hx
      rw [hLz] at hx'
      refine (Submodule.span_le.2 ?_) hx'
      rintro _ ⟨j, rfl⟩
      have h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F) := Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F) :=
        Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)
      simpa using add_mem h2 h1
    · intro hx
      have : x ∈ Lz := (Submodule.span_le (p := Lz)).2 (by
        rintro _ ⟨q | j, rfl⟩
        · exact hEL q
        · have h1 : bZ j ∈ Lz := (ZB j).2
          have h2 := hspanE (hred_sub (bZ j))
          have e1 : red (bZ j) = bZ j - (bZ j - red (bZ j)) := by abel
          show red (bZ j) ∈ Lz
          rw [e1]; exact sub_mem h1 h2) hx
      exact this
  · refine le_trans ?_ hbig
    rw [Function.comp_apply]
    generalize e.symm i = q
    rcases q with q | j
    · have hC0 : 0 ≤ C := (h0 σ _).trans (hEle σ q)
      have hpos : 0 < Fintype.card t := Fintype.card_pos_iff.2 ⟨q.2⟩
      have h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L := by
        rw [← hm]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')
      exact (hEle σ q).trans (le_mul_of_one_le_left hC0 h1)
    · exact hred_le σ _
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]
    rw [Fintype.card_prod, Fintype.card_fin, hm] at hcardZ
    linarith

end GlobalTheory
