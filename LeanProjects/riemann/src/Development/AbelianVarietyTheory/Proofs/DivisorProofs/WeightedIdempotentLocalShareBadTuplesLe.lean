import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.StmtLocFOfCountsAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvFiveLogLeSumInvPrimesStatement

noncomputable section
open Polynomial Classical
open GlobalTheory.BadShare

namespace GlobalTheory.PropWU

theorem eU_coeff_one_ne (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    ((Formalism.MainNotions.ArithmeticCylinders.eU g N ψ₀).coeff 1).re ≠ 0 := by
  unfold Formalism.MainNotions.ArithmeticCylinders.eU Formalism.MainNotions.ArithmeticCylinders.eDat
  set J := Finset.univ.filter (fun u : GL (Fin N) (ZMod g) =>
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (u : Matrix (Fin N) (Fin N) (ZMod g))) with hJ
  have h1 : (1 : GL (Fin N) (ZMod g)) ∈ J := by
    rw [hJ, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a b => ⟨fun h => ?_, fun h => ?_⟩⟩
    · simp [Matrix.one_apply, (ne_of_gt h)]
    · simp [Matrix.one_apply, h]
  have h0 : (∑ i ∈ Finset.range (N - 1), Formalism.MainNotions.ArithmeticCylinders.entN ((1 : GL (Fin N) (ZMod g)) :
      Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold Formalism.MainNotions.ArithmeticCylinders.entN
    split_ifs with h
    · rw [Units.val_one, Matrix.one_apply_ne]
      intro e; have := congrArg Fin.val e; simp at this
    · rfl
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_smul,
    Finsupp.coe_finsetSum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Complex.mul_re, Complex.inv_re,
    Complex.natCast_re, Complex.normSq_natCast, div_self_mul_self', Complex.re_sum, Complex.inv_im, Complex.natCast_im,
    neg_zero, zero_div, Complex.im_sum, zero_mul, sub_zero, ne_eq, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
    Finset.card_eq_zero, not_or]
  refine ⟨Finset.nonempty_iff_ne_empty.1 ⟨1, h1⟩, ?_⟩
  rw [Finset.sum_eq_single (1 : GL (Fin N) (ZMod g))]
  · rw [Finsupp.single_eq_same, h0, AddChar.map_zero_eq_one, inv_one, Complex.one_re]
    exact one_ne_zero
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg hb]
    simp
  · intro h; exact absurd h1 h

theorem sum_inv_primes_between_ge (N : ℕ) (hN : 100 ≤ N) : 1 / (5 * Real.log N) ≤
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p :=
  GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval N hN

theorem mass_not_hasPrimeFactor_le_five (g : ℕ) [Fact g.Prime] (N : ℕ) (hN : 100 ≤ N) :
    (GlobalTheory.BadShare.mass g N fun f => ¬ GlobalTheory.BadShare.HasPrimeFactor g N f) ≤ 1 - 1 / (5 * Real.log N) := by
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N := fun p hp => (Finset.mem_filter.1 hp).2
  have h1 : (GlobalTheory.BadShare.mass g N fun f => ¬ GlobalTheory.BadShare.HasPrimeFactor g N f) ≤
      GlobalTheory.BadShare.mass g N fun f => ∀ p ∈ S, p ∉ GlobalTheory.BadShare.degType g f := by
    refine GlobalTheory.BadShare.mass_mono fun f _ hf p hp hd => hf ?_
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.1 hd
    exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hS _ hp⟩
  have h2 := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun s => ∀ p ∈ S, p ∉ s)
  have h3 := GlobalTheory.BadShare.card_perm_no_long_cycle N S fun p hp => (hS p hp).2.1
  have h4 := sum_inv_primes_between_ge N hN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have h5 : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card : ℝ) =
      N.factorial * ((1 : ℝ) / p) := by
    intro p hp
    have e := GlobalTheory.BadShare.card_perm_long_cycle N p (hS p hp).2.1 (by have := (hS p hp).2.2; omega)
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).1.ne_zero
    rw [← e]
    push_cast
    field_simp
  have h6 : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) +
      N.factorial * ∑ p ∈ S, (1 : ℝ) / p = N.factorial := by
    rw [Finset.mul_sum, ← Finset.sum_congr rfl h5]
    exact_mod_cast h3
  refine h1.trans (le_trans ?_ (sub_le_sub_left h4 1))
  refine le_trans (h2.trans_eq (by congr!)) (?_ : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
    ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / (N.factorial : ℝ) ≤ _)
  rw [div_le_iff₀ hf]
  nlinarith [h6]

theorem tupleMass_not_good_le (g : ℕ) [Fact g.Prime] (N m q d : ℕ) (ι : Type) [Fintype ι]
    (ch : ι → Fin m → (ZMod g)ˣ) (hN : 100 ≤ N) (hg : 2 ^ 12 ≤ g)
    (hq : q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) :
    GlobalTheory.BadShare.tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ GlobalTheory.BadShare.Good g N ch F) ≤
      23 * (Fintype.card ι : ℝ) * Real.log g / Real.sqrt g +
      2 * (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) +
      (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι +
      Real.exp (-((Fintype.card ι : ℝ) / (5 * Real.log N))) := by
  have h1 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  let B2 : (ι → (ZMod g)[X]) → Prop := fun F => ∃ v ∈ (Finset.univ : Finset ι), ¬ RootsApart g N (F v)
  let B3 : (ι → (ZMod g)[X]) → Prop := fun F => ∃ p ∈ (Finset.univ : Finset (ι × Fin m × Bool)),
    ¬ RootsAvoid g (if p.2.2 then ch p.1 p.2.1 else (ch p.1 p.2.1)⁻¹) (F p.1)
  let B4 : (ι → (ZMod g)[X]) → Prop := fun F => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)
  let B5 : (ι → (ZMod g)[X]) → Prop := fun F => ∀ v, ¬ HasPrimeFactor g N (F v)
  have u0 : tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ Good g N ch F) ≤
      tupleMass g N (fun F => B2 F ∨ B3 F ∨ B4 F ∨ B5 F) + tupleMass g N (fun _ : ι → (ZMod g)[X] => False) := by
    refine tupleMass_le_add fun F hF hng => Or.inl ?_
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨c2, c3, c4, c5⟩ := hc
    refine hng (good_iff.2 ⟨hF, fun v => ?_, fun v j => ⟨?_, ?_⟩, ?_, ?_⟩)
    · by_contra h
      exact c2 ⟨v, Finset.mem_univ _, h⟩
    · by_contra h
      exact c3 ⟨(v, j, true), Finset.mem_univ _, by simpa using h⟩
    · by_contra h
      exact c3 ⟨(v, j, false), Finset.mem_univ _, by simpa using h⟩
    · rintro ⟨a, a1, a2, a3⟩
      exact c4 ⟨a, Finset.mem_Icc.2 ⟨a1, by omega⟩, a3⟩
    · by_contra h
      exact c5 fun v hv => h ⟨v, hv⟩
  have u00 : tupleMass g N (fun _ : ι → (ZMod g)[X] => False) = 0 := by
    unfold tupleMass; simp
  have u2 : tupleMass g N (fun F => B2 F ∨ B3 F ∨ B4 F ∨ B5 F) ≤
      tupleMass g N B2 + tupleMass g N (fun F => B3 F ∨ B4 F ∨ B5 F) := tupleMass_le_add fun _ _ h => h
  have u3 : tupleMass g N (fun F => B3 F ∨ B4 F ∨ B5 F) ≤
      tupleMass g N B3 + tupleMass g N (fun F => B4 F ∨ B5 F) := tupleMass_le_add fun _ _ h => h
  have u4 : tupleMass g N (fun F => B4 F ∨ B5 F) ≤
      tupleMass g N B4 + tupleMass g N B5 := tupleMass_le_add fun _ _ h => h
  have b2 : tupleMass g N B2 ≤ 23 * (Fintype.card ι : ℝ) * Real.log g / Real.sqrt g := by
    refine (tupleMass_exists_le _ fun v F => ¬ RootsApart g N (F v)).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun v _ =>
      (tupleMass_single_le h1 v fun f => ¬ RootsApart g N f).trans (GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le g N hg)).trans (le_of_eq ?_)
    rw [Finset.card_univ, nsmul_eq_mul]; ring
  have b3 : tupleMass g N B3 ≤ 2 * (Fintype.card ι : ℝ) * m *
      (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) := by
    refine (tupleMass_exists_le _ fun (p : ι × Fin m × Bool) F =>
      ¬ RootsAvoid g (if p.2.2 then ch p.1 p.2.1 else (ch p.1 p.2.1)⁻¹) (F p.1)).trans ?_
    have key : ∀ (c : (ZMod g)ˣ) (v : ι), tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsAvoid g c (F v)) ≤
        1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := fun c v =>
      (tupleMass_single_le h1 v fun f => ¬ RootsAvoid g c f).trans (GlobalTheory.T.mass_not_rootsAvoid_le' g N q d c hq)
    refine (Finset.sum_le_card_nsmul _ _ _ fun p _ => key _ p.1).trans (le_of_eq ?_)
    rw [Finset.card_univ, nsmul_eq_mul]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  have b4 : tupleMass g N B4 ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by
    refine (tupleMass_exists_le _ fun a (F : ι → (ZMod g)[X]) => ∀ v, HasDiv g a (F v)).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((7 / 8 : ℝ) ^ Fintype.card ι) fun a ha => ?_).trans ?_
    · rw [Finset.mem_Icc] at ha
      refine (tupleMass_forall (fun _ : ι => HasDiv g a)).le.trans ?_
      rw [Finset.prod_const, Finset.card_univ]
      exact pow_le_pow_left₀ (mass_nonneg _ _) (GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le g N a (by omega) (by omega)) _
    · rw [Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Nat.cast_div_le (α := ℝ) (m := N) (n := 2)
  have b5 : tupleMass g N B5 ≤ Real.exp (-((Fintype.card ι : ℝ) / (5 * Real.log N))) := by
    have e := tupleMass_forall (g := g) (N := N) (fun (_ : ι) f => ¬ HasPrimeFactor g N f)
    refine e.le.trans ?_
    rw [Finset.prod_const, Finset.card_univ]
    have h2 : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ Real.exp (-(1 / (5 * Real.log N))) :=
      (mass_not_hasPrimeFactor_le_five g N hN).trans (Real.one_sub_le_exp_neg _)
    refine (pow_le_pow_left₀ (mass_nonneg _ _) h2 _).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith

theorem host_primes (D : Formalism.BasicNotions.D7) (k : Fin 2) (hr : 100 ≤ D.R.r) :
    D.host.q.Prime ∧ D.host.d.Prime ∧ D.host.q ≠ 2 ∧ D.host.d ≠ 2 ∧ D.host.q ≠ D.host.d ∧
      16 ≤ max D.host.q D.host.d ∧ 16 * D.host.q * D.host.d ∣ D.host.g k - 1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  obtain ⟨hbq, hbd⟩ := D.host.qd_big
  have hc := D.ntypes.g_cond k
  have he := D.host.two_le_e
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have h400 : 400 ≤ 4 * D.R.t * D.R.r := by nlinarith
  refine ⟨hq, hd, by omega, by omega, by omega, by omega, ?_⟩
  have h1 : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have := Nat.dvd_sub_mod (n := D.host.QS * D.host.q * D.host.d) (D.host.g k)
    rwa [hc] at this
  have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (show 4 ≤ D.R.e + 2 by omega)).trans D.host.tower_dvd
  exact (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _).trans h1

theorem propW_eUk : ∀ (D : Formalism.BasicNotions.D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ), (∀ k, ψ₀ k ≠ 1) →
    Formalism.MainNotions.ArithmeticCylinders.admLq D → Formalism.MainNotions.ArithmeticCylinders.TieAdmG D → 100 ≤ D.R.r → (∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k) →
    ∀ (k : Fin 2) (S : Finset (Formalism.MainNotions.ArithmeticCylinders.Tup D k)), (∀ t ∈ S, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt D k t) →
    Formalism.MainNotions.ArithmeticCylinders.locShare D (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk D k (ψ₀ k)) k S ≤
      3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) * Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) +
      2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
        (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) +
      (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := by
  intro D ψ₀ hψ hA _hT hr hg k S hS
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨S0, hmem, hsum⟩ := D.ntypes.eSer_sum k
  obtain ⟨hA0, hA1, -, -⟩ := hA k (ψ₀ k) (hψ k)
  set w : (ZMod (D.host.g k))[X] → ℝ := fun f => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (Formalism.MainNotions.ArithmeticCylinders.eUk D k (ψ₀ k)) f with hw
  have hw0 : ∀ f, 0 ≤ w f := fun f => (hA0 f).1
  have hcoef : ((Formalism.MainNotions.ArithmeticCylinders.eUk D k (ψ₀ k)).coeff 1).re ≠ 0 := eU_coeff_one_ne _ _ _
  have htot : ∑ f ∈ S0, w f = 1 := by
    simp only [hw]
    unfold Formalism.MainNotions.ArithmeticCylinders.wtOf
    rw [← Finset.sum_div]
    have h : ∑ f ∈ S0, ((Formalism.MainNotions.ArithmeticCylinders.eUk D k (ψ₀ k) * D.ntypes.eSer k f).coeff 1).re =
        ((Formalism.MainNotions.ArithmeticCylinders.eUk D k (ψ₀ k)).coeff 1).re := by
      rw [← Complex.re_sum, ← Finsupp.finsetSum_apply, ← MonoidAlgebra.coeff_sum, ← Finset.mul_sum, hsum, mul_one]
    rw [h, div_self hcoef]
  have hoff : ∀ f, f ∉ S0 → w f = 0 := fun f hf =>
    Formalism.MainNotions.N.LocalShareBounds.wtOf_off k _ _ fun h => hf ((hmem f).2 h)
  have hsqS : ∀ f, f ∈ sqSet (D.host.g k) D.R.r ↔ f ∈ S0 ∧ Squarefree f := by
    intro f; rw [mem_sqSet, hmem]; tauto
  have hwsq : ∀ f ∈ sqSet (D.host.g k) D.R.r, w f = ((torusCard (D.host.g k) f : ℕ) : ℝ)⁻¹ := by
    intro f hf
    obtain ⟨h1, h2⟩ := (hsqS f).1 hf
    have hl := (hmem f).1 h1
    simp only [hw]
    rw [hA1 f hl h2, one_div]
    congr 1
    unfold torusCard degType
    rw [Multiset.map_map, Nat.cast_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun P _ => ?_
    simp only [Function.comp_apply]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (D.host.g_prime k).pos), Nat.cast_pow, Nat.cast_one]
  have hmass : mass (D.host.g k) D.R.r (fun _ => True) = ∑ f ∈ S0.filter Squarefree, w f := by
    unfold mass
    refine Finset.sum_congr (by ext f; simp [hsqS]) fun f hf => (hwsq f ?_).symm
    rw [hsqS]; exact Finset.mem_filter.1 hf
  have hnsq : ∑ f ∈ S0.filter (fun f => ¬ Squarefree f), w f ≤ 2 / (D.host.g k : ℝ) := by
    have e1 := Finset.sum_filter_add_sum_filter_not S0 Squarefree w
    have e2 := GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass (D.host.g k) D.R.r
    linarith

  have hw1 : ∀ _v : D.nd.PlG k, ∑ f ∈ S0, w f ≤ 1 := fun _ => htot.le
  have hq := host_primes D k hr
  have hTM := tupleMass_not_good_le (D.host.g k) D.R.r D.R.m D.host.q D.host.d (D.nd.PlG k) (D.nd.chiT k) hr
    (hg k) hq
  rw [D.nd.card_PlG k] at hTM
  have hF0 : ∀ t : Formalism.MainNotions.ArithmeticCylinders.Tup D k, 0 ≤ ∏ v, w (t v) := fun t => Finset.prod_nonneg fun v _ => hw0 _
  have hite : ∀ (p : Prop) [Decidable p] (t : Formalism.MainNotions.ArithmeticCylinders.Tup D k), 0 ≤ (if p then ∏ v, w (t v) else 0) := by
    intro p _ t; split_ifs
    · exact hF0 t
    · exact le_rfl
  show ∑ t ∈ S, ∏ v, w (t v) ≤ _
  have h1 : ∑ t ∈ S, ∏ v, w (t v) = ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ S0), ∏ v, w (t v) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rfl
    · push Not at ht
      obtain ⟨v, hv⟩ := ht
      exact Finset.prod_eq_zero (Finset.mem_univ v) (hoff _ hv)
  have hsplit : ∀ t : Formalism.MainNotions.ArithmeticCylinders.Tup D k, ∏ v, w (t v) ≤
      ∑ v, (if ¬ Squarefree (t v) then ∏ v, w (t v) else 0) +
        (if ∀ v, Squarefree (t v) then ∏ v, w (t v) else 0) := by
    intro t
    have hs0 := Finset.sum_nonneg (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
      hite (¬ Squarefree (t v)) t
    by_cases h : ∀ v, Squarefree (t v)
    · rw [if_pos h]; linarith
    · push Not at h
      obtain ⟨v, hv⟩ := h
      rw [if_neg (fun h => hv (h v))]
      have := Finset.single_le_sum (f := fun v => if ¬ Squarefree (t v) then ∏ v, w (t v) else 0)
        (fun v _ => hite _ t) (Finset.mem_univ v)
      simp only [if_pos hv] at this
      linarith
  set S' := S.filter (fun t => ∀ v, t v ∈ S0) with hS'
  have hA : ∑ t ∈ S', ∑ v, (if ¬ Squarefree (t v) then ∏ v, w (t v) else 0) ≤
      (D.R.f : ℝ) * (2 / (D.host.g k : ℝ)) := by
    have hsub : S' ⊆ Fintype.piFinset (fun _ : D.nd.PlG k => S0) := by
      intro t ht; rw [Fintype.mem_piFinset]; exact (Finset.mem_filter.1 ht).2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ =>
      Finset.sum_nonneg fun v _ => hite _ t).trans ?_
    rw [Finset.sum_comm]
    calc _ ≤ ∑ v : D.nd.PlG k, ∑ f ∈ S0.filter (fun f => ¬ Squarefree f), w f :=
          Finset.sum_le_sum fun v _ => Formalism.MainNotions.N.LocalShareBounds.sum_pi_single S0 (fun _ f => w f)
            (fun _ f => hw0 f) hw1 v (fun f => ¬ Squarefree f)
      _ ≤ ∑ v : D.nd.PlG k, 2 / (D.host.g k : ℝ) := Finset.sum_le_sum fun v _ => hnsq
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, D.nd.card_PlG k, nsmul_eq_mul]
  have hB : ∑ t ∈ S', (if ∀ v, Squarefree (t v) then ∏ v, w (t v) else 0) ≤
      tupleMass (D.host.g k) D.R.r (fun F : D.nd.PlG k → (ZMod (D.host.g k))[X] =>
        ¬ Good (D.host.g k) D.R.r (D.nd.chiT k) F) := by
    rw [← Finset.sum_filter]
    have eT : tupleMass (D.host.g k) D.R.r (fun F : D.nd.PlG k → (ZMod (D.host.g k))[X] =>
        ¬ Good (D.host.g k) D.R.r (D.nd.chiT k) F) =
        ∑ F ∈ (Fintype.piFinset fun _ : D.nd.PlG k => sqSet (D.host.g k) D.R.r).filter
          (fun F => ¬ Good (D.host.g k) D.R.r (D.nd.chiT k) F),
          ∏ v, ((torusCard (D.host.g k) (F v) : ℕ) : ℝ)⁻¹ := by
      unfold tupleMass
      rw [Finset.sum_filter]
      congr!
    rw [eT]
    have hin : ∀ t ∈ S'.filter (fun t => ∀ v, Squarefree (t v)), ∀ v, t v ∈ sqSet (D.host.g k) D.R.r := by
      intro t ht v
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ht
      exact (hsqS _).2 ⟨(Finset.mem_filter.1 h1).2 v, h2 v⟩
    calc ∑ t ∈ S'.filter (fun t => ∀ v, Squarefree (t v)), ∏ v, w (t v)
        = ∑ t ∈ S'.filter (fun t => ∀ v, Squarefree (t v)),
            ∏ v, ((torusCard (D.host.g k) (t v) : ℕ) : ℝ)⁻¹ :=
          Finset.sum_congr rfl fun t ht => Finset.prod_congr rfl fun v _ => hwsq _ (hin t ht v)
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => tupleWeight_nonneg t
          intro t ht
          refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 (hin t ht), ?_⟩
          have := hS t (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).1
          exact this
  have hmain : ∑ t ∈ S', ∏ v, w (t v) ≤ (D.R.f : ℝ) * (2 / (D.host.g k : ℝ)) +
      tupleMass (D.host.g k) D.R.r (fun F : D.nd.PlG k → (ZMod (D.host.g k))[X] =>
        ¬ Good (D.host.g k) D.R.r (D.nd.chiT k) F) := by
    calc _ ≤ ∑ t ∈ S', (∑ v, (if ¬ Squarefree (t v) then ∏ v, w (t v) else 0) +
          (if ∀ v, Squarefree (t v) then ∏ v, w (t v) else 0)) := Finset.sum_le_sum fun t _ => hsplit t
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hA hB
  have hgpos : (0 : ℝ) < D.host.g k := by exact_mod_cast (D.host.g_prime k).pos
  have hfg : 0 ≤ (D.R.f : ℝ) / (D.host.g k : ℝ) := by positivity
  have e1 : (D.R.f : ℝ) * (2 / (D.host.g k : ℝ)) = 2 * ((D.R.f : ℝ) / (D.host.g k : ℝ)) := by ring
  have e2 : 3 * (D.R.f : ℝ) / (D.host.g k : ℝ) = 3 * ((D.R.f : ℝ) / (D.host.g k : ℝ)) := by ring
  have e3 : -(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ)) = -((D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := neg_div _ _
  rw [h1, e2, e3]
  linarith

end GlobalTheory.PropWU
