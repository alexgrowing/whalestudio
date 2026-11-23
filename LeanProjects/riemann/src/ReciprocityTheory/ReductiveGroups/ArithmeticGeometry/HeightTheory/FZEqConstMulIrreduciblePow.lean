import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BlockSphereProbIsProbabilityMeasure

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def relationEliminateColumn (c : ι) : KTp K d.D d.N →ₐ[K] MvPolynomial (TVar d.D d.N) (Ω c) :=
  MvPolynomial.aeval fun t =>
    if t.2 = d.jc c then
      -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (t.1, k) *
        MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
    else MvPolynomial.X t

theorem relation_section_identity (hd : d.AxH 𝒜) (c : ι) (i : Fin (d.D + 1)) :
    d.sH c (MvPolynomial.X (i, d.jc c)) + ∑ k ∈ Finset.univ.erase (d.jc c),
      d.sH c (MvPolynomial.X (i, k)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
      if i = 0 then d.rationalBaseRow c else 0 := by
  have h1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := ratio_self_height (hd.w_base c)
  split_ifs with hi
  · subst hi
    unfold Data.rationalBaseRow
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c))]
    simp only [h1, map_one, mul_one]
  · have hsum : ∑ k ∈ Finset.univ.erase (d.jc c), d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
        ∑ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
      have e1 := Finset.add_sum_erase Finset.univ (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
          (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))) (d.jc c)
      exact add_left_cancel (e1.trans e2)
    have hX : ∀ j, d.sH c (MvPolynomial.X (i, j)) = sImg (d.jc c) (d.x c) (i, j) :=
      fun j => MvPolynomial.aeval_X _ _
    have hS0 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
        Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q (d.jc c) = y :=
      fun y q => Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
    have hS1 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c))
        (k : Fin d.N), Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
          ((d.jc c).succAbove k) = q k :=
      fun y q k => Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q k
    have hA : d.sH c (MvPolynomial.X (i, d.jc c)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k)) := by
      rw [hX]
      simp only [sImg, hS0, if_neg hi]
    have hB : ∀ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (MvPolynomial.X (Sum.inr (i, k))) := by
      intro k
      rw [hX]
      simp only [sImg, hS1]
    rw [hsum, hA]
    simp only [hB]
    rw [map_neg, map_sum, neg_add_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq]

theorem relation_ker_le_valuation_prime (hd : d.AxH 𝒜) (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hpos : 0 < w (d.rationalBaseRow c))
    (Q : KTp K d.D d.N) (hQ : d.relationEliminateColumn c Q = 0) : Q ∈ p := by
  set Ψ : MvPolynomial (TVar d.D d.N) (Ω c) →ₐ[Ω c] OmS (Ω c) d.D d.N :=
    MvPolynomial.aeval (sImg (d.jc c) (d.x c)) with hΨ
  have htop : (0 : WithTop ℤ) < ⊤ := WithTop.coe_lt_top 0
  have hsHX : ∀ n : TVar d.D d.N, d.sH c (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨX : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = sImg (d.jc c) (d.x c) n :=
    fun n => MvPolynomial.aeval_X _ _
  have hΨs : ∀ n : TVar d.D d.N, Ψ (MvPolynomial.X n) = d.sH c (MvPolynomial.X n) :=
    fun n => (hΨX n).trans (hsHX n).symm
  have hΨC : ∀ r : Ω c, Ψ (MvPolynomial.C r) = algebraMap (Ω c) (OmS (Ω c) d.D d.N) r :=
    fun r => MvPolynomial.aeval_C _ _
  have hnn : ∀ x : KTp K d.D d.N, 0 ≤ w (d.sH c x) := fun x => (hw.2 x).1
  have key : ∀ R : KTp K d.D d.N, 0 < w (d.sH c R - Ψ (d.relationEliminateColumn c R)) := by
    intro R
    induction R using MvPolynomial.induction_on
    next a =>
      have e1 : d.sH c (MvPolynomial.C a) = algebraMap K (OmS (Ω c) d.D d.N) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.sH c).commutes a
      have e2 : d.relationEliminateColumn c (MvPolynomial.C a) =
          algebraMap K (MvPolynomial (TVar d.D d.N) (Ω c)) a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (d.relationEliminateColumn c).commutes a
      rw [e1, e2, IsScalarTower.algebraMap_apply K (Ω c) (MvPolynomial (TVar d.D d.N) (Ω c)) a,
        AlgHom.commutes, ← IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) a, sub_self,
        AddValuation.map_zero]
      exact htop
    next P₁ P₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_sub_add_comm]
      exact lt_of_lt_of_le (lt_min h₁ h₂) (AddValuation.map_add _ _ _)
    next P n hP =>
      have hXn : 0 < w (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        obtain ⟨i, j⟩ := n
        have hr : d.relationEliminateColumn c (MvPolynomial.X (i, j)) = if j = d.jc c then
            -∑ k ∈ Finset.univ.erase (d.jc c), MvPolynomial.X (i, k) *
              MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))
            else MvPolynomial.X (i, j) := MvPolynomial.aeval_X _ _
        rw [hr]
        split_ifs with hj
        · subst hj
          rw [map_neg, map_sum, sub_neg_eq_add]
          simp only [map_mul, hΨs, hΨC]
          rw [relation_section_identity d hd c i]
          split_ifs with hi
          · exact hpos
          · rw [AddValuation.map_zero]
            exact htop
        · rw [hΨs, sub_self, AddValuation.map_zero]
          exact htop
      simp only [map_mul]
      have e : d.sH c P * d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c P) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) =
          d.sH c P * (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) +
            (d.sH c P - Ψ (d.relationEliminateColumn c P)) * Ψ (d.relationEliminateColumn c (MvPolynomial.X n)) := by ring
      rw [e]
      have hb : 0 ≤ w (Ψ (d.relationEliminateColumn c (MvPolynomial.X n))) := by
        have h3 := AddValuation.map_sub w (d.sH c (MvPolynomial.X n))
          (d.sH c (MvPolynomial.X n) - Ψ (d.relationEliminateColumn c (MvPolynomial.X n)))
        rw [sub_sub_cancel] at h3
        exact le_trans (le_min (hnn _) hXn.le) h3
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hXn (le_add_of_nonneg_left (hnn P))
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hP (le_add_of_nonneg_right hb)
  have h := key Q
  rw [hQ, map_zero, sub_zero] at h
  exact ((hw.2 Q).2).1 h

theorem ker_relation_map_ne_bot (hd : d.AxH 𝒜) (c : ι) : RingHom.ker (d.relationEliminateColumn c) ≠ ⊥ := by
  intro hker
  have hinj : Function.Injective (d.relationEliminateColumn c) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  let g : Fin (d.D + 1) × Fin d.N → TVar d.D d.N := fun t => (t.1, (d.jc c).succAbove t.2)
  let φ : KTp K d.D d.N →ₐ[K] MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c) :=
    MvPolynomial.aeval fun t : TVar d.D d.N =>
      Fin.insertNth (α := fun _ => MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) (d.jc c)
        (-∑ k, MvPolynomial.X (t.1, k) * MvPolynomial.C (d.x c k))
        (fun k => MvPolynomial.X (t.1, k)) t.2
  have hfac : d.relationEliminateColumn c = ((MvPolynomial.rename g).restrictScalars K).comp φ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [Data.relationEliminateColumn, φ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, MvPolynomial.aeval_X]
    by_cases hj : j = d.jc c
    · subst hj
      simp only [if_true, Fin.insertNth_apply_same, map_neg, map_sum, map_mul, MvPolynomial.rename_X,
        MvPolynomial.rename_C, g]
      congr 1
      have e1 := Finset.add_sum_erase Finset.univ (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => (MvPolynomial.X (i, k) :
        MvPolynomial (TVar d.D d.N) (Ω c)) * MvPolynomial.C (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
        (d.jc c)
      exact add_left_cancel (e1.trans e2)
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [if_neg hj, Fin.insertNth_apply_succAbove, MvPolynomial.rename_X, g]
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hinj
    rw [hfac, AlgHom.comp_apply, AlgHom.comp_apply, hab]
  refine not_injective_of_trdeg_lt φ d.D (hd.trdeg c) ?_ hφ
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

theorem fZ_eq_const_mul_irreducible_pow (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 F) :
    ∃ (F0 : KTp K d.D d.N) (κ : K) (m : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ Irreducible F0 ∧
      F = MvPolynomial.C κ * F0 ^ m ∧
      ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q := by
  obtain ⟨κ, T, e, hκ, hT, hFe, hpl⟩ := fZ_factor_positive_places (d := d) hd h c F hF
  set I : Ideal (KTp K d.D d.N) := RingHom.ker (d.relationEliminateColumn c) with hIdef
  have hIp : I.IsPrime := RingHom.ker_isPrime _
  have hIb : I ≠ ⊥ := ker_relation_map_ne_bot (d := d) hd c
  obtain ⟨q, hqI, hq⟩ := hIp.exists_mem_prime_of_ne_bot hIb
  have hprime : ∀ p ∈ d.HtOne, q ∈ p → Prime (d.gen p) := by
    intro p hp1 hqp
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgq : d.gen p ∣ q := by
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    have hg0 : d.gen p ≠ 0 := by
      intro h0
      rw [h0] at hgq
      exact hq.ne_zero (zero_dvd_iff.1 hgq)
    have hpr : (Ideal.span {d.gen p}).IsPrime := by
      rw [← hsp]
      exact hp1.1
    exact (Ideal.span_singleton_prime hg0).1 hpr
  have hcont : ∀ p ∈ T, 0 < e p → p = I := by
    intro p hpT hep
    obtain ⟨w, hw, htriv, hpos'⟩ := hpl p hpT hep
    have hIle : I ≤ p := fun Q hQ => relation_ker_le_valuation_prime (d := d) hd c p w hw htriv hpos' Q (RingHom.mem_ker.1 hQ)
    have hp1 : p ∈ d.HtOne := hT hpT
    have hsp := height_one_prime_eq_span_gen (d := d) p hp1
    have hgp := hprime p hp1 (hIle hqI)
    have hgq : d.gen p ∣ q := by
      have hqp := hIle hqI
      rw [hsp] at hqp
      exact Ideal.mem_span_singleton.1 hqp
    obtain ⟨v, hv⟩ := hgp.irreducible.dvd_symm hq.irreducible hgq
    have hgI : d.gen p ∈ I := by
      rw [hv]
      exact I.mul_mem_right v hqI
    refine le_antisymm ?_ hIle
    rw [hsp]
    exact (Ideal.span_singleton_le_iff_mem I).2 hgI
  by_cases hIT : I ∈ T ∧ 0 < e I
  · obtain ⟨hIT, heI⟩ := hIT
    have hI1 : I ∈ d.HtOne := hT hIT
    have hsp := height_one_prime_eq_span_gen (d := d) I hI1
    refine ⟨d.gen I, κ, e I, hκ, heI, (hprime I hI1 hqI).irreducible, ?_, ?_⟩
    · rw [hFe, Finset.prod_eq_single I (fun b hb hbI => ?_) (fun hn => absurd hIT hn)]
      rcases Nat.eq_zero_or_pos (e b) with h0 | h0
      · rw [h0, pow_zero]
      · exact absurd (hcont b hb h0) hbI
    · intro Q
      rw [← Ideal.mem_span_singleton, ← hsp]
      exact RingHom.mem_ker.symm
  · exfalso
    have hone : ∏ p ∈ T, d.gen p ^ e p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      rcases Nat.eq_zero_or_pos (e p) with h0 | h0
      · rw [h0, pow_zero]
      · have hpI := hcont p hp h0
        subst hpI
        exact absurd ⟨hp, h0⟩ hIT
    rw [hFe, hone, mul_one, height_const_eq_zero (Nat.succ_pos _)] at hpos
    exact lt_irrefl _ hpos

end Data

end ReciprocityTheory.ChartRestriction.G.T0
