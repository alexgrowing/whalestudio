import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdealStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharactersStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

structure IsChain (n : ℕ) (K : ℕ → Submodule F N) (t : ℕ → N) : Prop where
  mono : Monotone K
  zero : K 0 = ⊥
  top : K n = ⊤
  succ : ∀ i < n, K (i + 1) = K i ⊔ Submodule.span F {t i}
  notMem : ∀ i < n, t i ∉ K i

theorem IsChain.quot {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (n - j) (fun i => (K (j + i)).map (K j).mkQ) (fun i => (K j).mkQ (t (j + i))) where
  mono := fun a b hab => Submodule.map_mono (h.mono (by omega))
  zero := by simp
  top := by
    have : K (j + (n - j)) = ⊤ := top_le_iff.1 (h.top ▸ h.mono (by omega))
    simp only [this, Submodule.map_top, Submodule.range_mkQ]
  succ := fun i hi => by
    simp only [← add_assoc]
    rw [h.succ (j + i) (by omega), Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  notMem := fun i hi hm => by
    apply h.notMem (j + i) (by omega)
    have : t (j + i) ∈ ((K (j + i)).map (K j).mkQ).comap (K j).mkQ := hm
    rwa [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 (h.mono (by omega))] at this

theorem IsChain.mem {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) {i j : ℕ}
    (hi : i < min j n) : t i ∈ K j := by
  apply h.mono (show i + 1 ≤ j by omega)
  rw [h.succ i (by omega)]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

open Classical in
theorem IsChain.sub {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (min j n) (fun i => (K i).comap (K j).subtype)
      (fun i => if hi : t i ∈ K j then ⟨t i, hi⟩ else 0) where
  mono := fun a b hab => Submodule.comap_mono (h.mono hab)
  zero := by simp [h.zero]
  top := by
    rw [Submodule.comap_subtype_eq_top]
    rcases le_total j n with h1 | h1
    · rw [min_eq_left h1]
    · rw [min_eq_right h1, h.top]; exact le_top
  succ := fun i hi => by
    apply Submodule.map_injective_of_injective (K j).injective_subtype
    simp only [dif_pos (h.mem hi)]
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, Submodule.map_comap_subtype,
      Submodule.map_comap_subtype, inf_eq_right.2 (h.mono (by omega)),
      inf_eq_right.2 (h.mono (by omega)), h.succ i (by omega)]
    rfl
  notMem := fun i hi hm => by
    apply h.notMem i (by omega)
    simp only [dif_pos (h.mem hi)] at hm
    exact hm

theorem isChain_flag {n : ℕ} (b : Module.Basis (Fin n) F N) :
    IsChain n (flagSub b) (fun i => if h : i < n then b ⟨i, h⟩ else 0) where
  mono := fun a c hac => Submodule.span_mono (Set.image_mono fun j hj => lt_of_lt_of_le hj hac)
  zero := by simp [flagSub]
  top := by
    have : {j : Fin n | (j : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun j => j.2
    rw [flagSub, this, Set.image_univ, b.span_eq]
  succ := fun i hi => by
    have : {j : Fin n | (j : ℕ) < i + 1} = {j : Fin n | (j : ℕ) < i} ∪ {⟨i, hi⟩} := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
      omega
    simp only [dif_pos hi]
    rw [flagSub, this, Set.image_union, Submodule.span_union, Set.image_singleton]
    rfl
  notMem := fun i hi => by
    simp only [dif_pos hi]
    exact b.linearIndependent.notMem_span_image (by simp)

end

section

variable (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
  (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters)
  (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
  (hp : v (p : C) < 1) (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ)
  (hF : Fintype.card F = p ^ f)

include hex hsq hsplit hos hv hp hF

theorem chain_le (χ : MulChar F R) (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier →
    ∀ (K : ℕ → Submodule F N) (t : ℕ → N), IsChain n K t → ∀ (s : ℕ → NNReal) (r : NNReal),
    (∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i)) →
    HasLen v R (OmType AA.carrier χ) r → ∏ i ∈ Finset.range n, s i ≤ r := by
  classical
  induction n with
  | zero =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    have : Subsingleton N := (Submodule.subsingleton_iff F).1
      (subsingleton_of_bot_eq_top (h.zero.symm.trans h.top))
    rw [hasLen_trivial hv hr]
    simp
  | succ n ih =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
    have : Finite (N ⧸ K 1) := Finite.of_surjective _ (K 1).mkQ_surjective
    let _ : Fintype (N ⧸ K 1) := Fintype.ofFinite _
    let _ : Fintype (K 1) := Fintype.ofFinite _
    obtain ⟨-, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K 1)
    obtain ⟨b, -, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
    have h1 := ih _ AQ hQs _ _ (h.quot 1) (fun i => s (1 + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
    have ht : t 0 ≠ 0 := fun h0 => h.notMem 0 (by omega) (h0 ▸ Submodule.zero_mem _)
    have h2 := hs 0 (by omega)
    rw [h.zero] at h2
    have h3 := hasLen_line _ ht h2
    have hK : Submodule.span F {t 0} = K 1 := by
      rw [h.succ 0 (by omega), h.zero, bot_sup_eq]
    rw [hK] at h3
    rw [hQ] at hb
    have h4 := hos p C v R hv hp F f hF N AA hst (K 1) χ _ _ _ h3 hb hr
    rw [add_comm n 1, Finset.prod_range_add]
    refine le_trans ?_ h4
    rw [Finset.prod_range_one]
    exact mul_le_mul_right h1 _

theorem chain_partial (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (χ : MulChar F R) (n : ℕ) (N : Type)
    [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N) (hst : FStable F AA.carrier)
    (K : ℕ → Submodule F N) (t : ℕ → N) (h : IsChain n K t) (s : ℕ → NNReal)
    (hs : ∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i))
    (hr : HasLen v R (OmType AA.carrier χ) (∏ i ∈ Finset.range n, s i)) (j : ℕ) :
    HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K j → N))) χ)
      (∏ i ∈ Finset.range (min j n), s i) := by
  classical
  obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
  have : Finite (N ⧸ K j) := Finite.of_surjective _ (K j).mkQ_surjective
  let _ : Fintype (N ⧸ K j) := Fintype.ofFinite _
  let _ : Fintype (K j) := Fintype.ofFinite _
  obtain ⟨⟨AK, hK, hKs⟩, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K j)
  obtain ⟨a, -, ha⟩ := (hsplit p C v R hv hp F f hF _ AK hKs σ hσ).1 χ
  obtain ⟨b, hb0, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
  have h1 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AQ hQs _ _ (h.quot j)
    (fun i => s (j + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
  have h2 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AK hKs _ _ (h.sub j)
    s a (fun i hi => by
      rw [(hstep p C v R hv hp F f hF _ AK hKs _ _ ((h.sub j).notMem i hi)).2, hK,
        sub_stepRes _ (h.mono (by omega)), dif_pos (h.mem hi),
        ← (hstep p C v R hv hp F f hF _ AA hst _ _ (h.notMem i (by omega))).2]
      exact hs _ (by omega)) ha
  rw [hK] at ha
  rw [hQ] at hb
  have h4 := hos p C v R hv hp F f hF N AA hst (K j) χ _ _ _ ha hb hr
  have h5 : ∏ i ∈ Finset.range n, s i =
      (∏ i ∈ Finset.range (min j n), s i) * ∏ i ∈ Finset.range (n - j), s (j + i) := by
    rcases le_total j n with h6 | h6
    · rw [min_eq_left h6, ← Finset.prod_range_add, Nat.add_sub_cancel' h6]
    · rw [min_eq_right h6, Nat.sub_eq_zero_of_le h6, Finset.prod_range_zero, mul_one]
  rw [h5] at h4
  have h7 : a ≤ ∏ i ∈ Finset.range (min j n), s i :=
    le_of_mul_le_mul_right (h4.trans (mul_le_mul_right h1 _)) (pos_iff_ne_zero.2 hb0)
  rw [← le_antisymm h7 h2]
  exact ha

end

end PositivityTheory.HtPt.Rd
