import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit

noncomputable section

namespace GlobalTheory.NeatUni

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain
open Formalism.AUTREP (GAf)
open scoped TensorProduct

theorem int_dvd_of_mem {R : Type} [CommRing R] {P : Ideal R} (hP : P ≠ ⊤) {p : ℕ} (hp : p.Prime) (h : (p : R) ∈ P)
    {z : ℤ} (hz : (z : R) ∈ P) : (p : ℤ) ∣ z := by
  by_contra hn
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hn).map (Int.castRingHom R)
  refine hP ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hz)

theorem geom_sum_expand {R : Type} [CommRing R] (π : R) (l : ℕ) :
    ∃ t t' : R, (1 + π) ^ l = 1 + l * π + π ^ 2 * t' ∧
      ∑ i ∈ Finset.range l, (1 + π) ^ i = l + ((∑ i ∈ Finset.range l, i : ℕ) : R) * π + π ^ 2 * t := by
  induction l with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ l ih =>
    obtain ⟨t, t', h1, h2⟩ := ih
    refine ⟨t + t', l + t' * (1 + π), ?_, ?_⟩
    · rw [pow_succ, h1]; push_cast; ring
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, h2, h1]; push_cast; ring

theorem eq_one_of_finOrder {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (p : R) ∈ P) (h2 : (p : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have ho : orderOf ζ ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, c, hc⟩ := Nat.exists_prime_and_dvd ho
  have hpos := hζ.orderOf_pos
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hη1 : ζ ^ c ≠ 1 := pow_ne_one_of_lt_orderOf hc0.ne' (by rw [hc]; have := hl.two_le; nlinarith)
  have hηl : (ζ ^ c) ^ l = 1 := by rw [← pow_mul, mul_comm, ← hc, pow_orderOf_eq_one]
  have hπ : ζ ^ c - 1 ∈ P := by
    obtain ⟨u, hu⟩ := sub_one_dvd_pow_sub_one ζ c
    rw [hu]; exact P.mul_mem_right _ h1
  set π := ζ ^ c - 1 with hπd
  have hs : ∑ i ∈ Finset.range l, (1 + π) ^ i = 0 := by
    have := geom_sum_mul (ζ ^ c) l
    rw [hηl, sub_self] at this
    rw [show 1 + π = ζ ^ c by rw [hπd]; ring]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hη1)
  obtain ⟨t, -, -, ht⟩ := geom_sum_expand π l
  rw [hs] at ht
  have e : (l : R) = -(((∑ i ∈ Finset.range l, i : ℕ) : R) * π + π ^ 2 * t) := by linear_combination -ht
  have hlP : (l : R) ∈ P := by
    rw [e, pow_two, mul_assoc]
    exact P.neg_mem (P.add_mem (P.mul_mem_left _ hπ) (P.mul_mem_right _ hπ))
  have hpl : p = l := (Nat.prime_dvd_prime_iff_eq hp hl).1
    (by exact_mod_cast int_dvd_of_mem hP hp h (z := l) (by exact_mod_cast hlP))
  subst hpl
  obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
  have hsum : ∑ i ∈ Finset.range p, i = p * d := by
    have := Finset.sum_range_id_mul_two p
    have e2 : p - 1 = 2 * d := by omega
    rw [e2] at this
    nlinarith
  apply h2
  rw [e, hsum]
  refine (P ^ 2).neg_mem ((P ^ 2).add_mem ?_ ((P ^ 2).mul_mem_right _ (Ideal.pow_mem_pow hπ 2)))
  rw [pow_two, Nat.cast_mul]
  exact Ideal.mul_mem_mul (P.mul_mem_right _ h) hπ

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem monomial {n : ℕ} {g : GL (Fin n) L} (hg : g ∈ GQ0 L n)
    (hint : ∀ i j, IsIntegral ℤ ((g : Matrix (Fin n) (Fin n) L) i j)) (i : Fin n) :
    ∃ j, IsOfFinOrder ((g : Matrix (Fin n) (Fin n) L) i j) ∧ ∀ k, k ≠ j → (g : Matrix (Fin n) (Fin n) L) i k = 0 := by
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  have h0 : (g : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) g = 1 := hg
  have h1 := congrFun (congrFun h0 i) i
  simp only [Matrix.mul_apply, conjT, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] at h1
  have h2 := congrArg φ h1
  simp only [map_sum, map_mul, map_one] at h2
  have h3 : ∑ k, ((‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := IsCMField.complexEmbedding_complexConj L φ ((g : Matrix (Fin n) (Fin n) L) i k)
    rw [show ((IsCMField.complexConj L : L →+* L) ((g : Matrix (Fin n) (Fin n) L) i k)) =
      IsCMField.complexConj L ((g : Matrix (Fin n) (Fin n) L) i k) from rfl, this, Complex.mul_conj', Complex.ofReal_pow]
  have h4 : ∑ k, ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2 = 1 := by exact_mod_cast h3
  obtain ⟨j, hj⟩ : ∃ j, (g : Matrix (Fin n) (Fin n) L) i j ≠ 0 := by
    by_contra hh
    push Not at hh
    simp [hh] at h4
  obtain ⟨m, hm, hm1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one L ℂ hj (hint i j)
    (fun ψ => GlobalTheory.StabFin.norm_entry_le_one hg ψ i j)
  have hf : IsOfFinOrder ((g : Matrix (Fin n) (Fin n) L) i j) := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hm1⟩
  refine ⟨j, hf, fun k hk => ?_⟩
  have hn1 : ‖φ ((g : Matrix (Fin n) (Fin n) L) i j)‖ = 1 := (φ.toMonoidHom.isOfFinOrder hf).norm_eq_one
  have h5 := Finset.sum_le_univ_sum_of_nonneg (s := {k, j})
    (f := fun k => ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ ^ 2) (fun k => sq_nonneg _)
  rw [Finset.sum_pair hk, h4, hn1] at h5
  have h6 : ‖φ ((g : Matrix (Fin n) (Fin n) L) i k)‖ = 0 := by
    nlinarith [norm_nonneg (φ ((g : Matrix (Fin n) (Fin n) L) i k))]
  simpa using h6

def frameM (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  Matrix.of fun i j => if j = 0 then 1 else if j = 1 then (i.val : ℤ) else if i = j then 1 else 0

theorem det_frameM (m : ℕ) : (frameM m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [frameM, Matrix.of_apply, if_true]
    split_ifs with h1 h2
    · rfl
    · rw [h2]; rfl
    · rfl
  · intro i j hij
    have hij' : i < j := hij
    simp only [frameM, Matrix.of_apply]
    split_ifs with h1 h2 h3
    · subst h1; exact absurd hij' (Fin.not_lt_zero _)
    · subst h2
      have : i.val < 1 := hij'
      omega
    · exact absurd h3 hij'.ne
    · rfl

theorem exists_class (m r : ℕ) (hr : 2 ≤ r) (s : SplitPlace L) {p : ℕ} (hp : p.Prime) (hpm : 2 * (m + 2) ≤ p)
    (h : (p : 𝓞 L) ∈ s.ideal) (h2 : (p : 𝓞 L) ∉ s.ideal ^ 2) :
    ∃ g : GAf L (m + 2), ∀ γ ∈ GQ L (m + 2), g⁻¹ * γ * g ∈ Umax L (m + 2) → NG.UniRT s r (s.loc _ (g⁻¹ * γ * g)) → γ = 1 := by
  classical
  obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L (m + 2) s
  let A₀ : GL (Fin (m + 2)) ℤ := Matrix.nonsingInvUnit (frameM m) (by rw [det_frameM]; exact isUnit_one)
  let A : GL (Fin (m + 2)) (s.v.adicCompletion L⁺) := Matrix.GeneralLinearGroup.map (Int.castRingHom _) A₀
  have hA : ∀ i j, A.1 i j = ((frameM m i j : ℤ) : s.v.adicCompletion L⁺) := fun i j => rfl
  obtain ⟨g, ⟨hgT, hgA⟩, -⟩ := hlift A
  have hgU : g ∈ Umax L (m + 2) := by
    rw [← GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hgT, hgA, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
    exact ⟨fun i j => intCast_mem _ (frameM m i j), fun i j => intCast_mem _ ((A₀⁻¹).1 i j)⟩
  refine ⟨g, fun γ hγ hU hu => ?_⟩
  have hγU : γ ∈ Umax L (m + 2) := by
    have := mul_mem (mul_mem hgU hU) (inv_mem hgU)
    convert this using 1
    group
  obtain ⟨c, hc, hce⟩ := GlobalTheory.StabFin.exists_rat ⟨γ, hγ⟩
  have hint : ∀ i j, IsIntegral ℤ ((c : Matrix _ _ L) i j) := fun i j =>
    GlobalTheory.StabFin.isIntegral_of_mem _ (hce i j ▸ hγU i j)
  choose σ hσ hσ0 using monomial hc hint
  have hloc : ∀ i j, (s.loc (m + 2) γ).1 i j = s.i ((c : Matrix _ _ L) i j) := by
    intro i j
    change s.proj (γ.1.1 i j) = _
    rw [hce i j]
    simp [SplitPlace.proj]
  set H := s.loc (m + 2) (g⁻¹ * γ * g) with hH
  have hrel : (s.loc (m + 2) γ).1 * A.1 = A.1 * H.1 := by
    rw [← Units.val_mul, ← Units.val_mul, hH, map_mul, map_mul, map_inv, hgA]
    congr 1
    group
  have hrow : ∀ i b, s.i ((c : Matrix _ _ L) i (σ i)) * A.1 (σ i) b = ∑ l, A.1 i l * H.1 l b := by
    intro i b
    rw [← Matrix.mul_apply, ← hrel, Matrix.mul_apply, Finset.sum_eq_single (σ i), hloc]
    · intro k _ hk
      rw [hloc, hσ0 i k hk, map_zero, zero_mul]
    · simp
  have hAint : ∀ i j, Valued.v (A.1 i j) ≤ 1 := fun i j =>
    (intCast_mem (s.v.adicCompletionIntegers L⁺) (frameM m i j) :)
  have hcong : ∀ (i b) (x : Fin (m + 2) → s.v.adicCompletion L⁺), (∀ l, Valued.v (H.1 l b - x l) < 1) →
      Valued.v (s.i ((c : Matrix _ _ L) i (σ i)) * A.1 (σ i) b - ∑ l, A.1 i l * x l) < 1 := by
    intro i b x hx
    rw [hrow, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    rw [← mul_sub, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hAint i l)) (hx l)
  have hlow : ∀ a b : Fin (m + 2), b.val < r → b.val < a.val → Valued.v (H.1 a b) < 1 := by
    intro a b hb hab
    by_cases ha : a.val < r
    · exact (hu.2 a b ha hb).1 hab
    · exact hu.1.2 a b (not_lt.1 ha) hb
  have hone : ∀ i, (c : Matrix _ _ L) i (σ i) = 1 := by
    intro i
    have h3 := hcong i 0 (Pi.single 0 1) (by
      intro l
      by_cases hl : l = 0
      · subst hl
        rw [Pi.single_eq_same]
        exact (hu.2 0 0 (by simp; omega) (by simp; omega)).2 rfl
      · rw [Pi.single_eq_of_ne hl, sub_zero]
        exact hlow l 0 (by simp; omega) (by simpa using Fin.pos_iff_ne_zero.2 hl))
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero]) (by simp)] at h3
    simp only [hA, frameM, Matrix.of_apply, if_true, Int.cast_one, mul_one, Pi.single_eq_same] at h3
    let ζ : 𝓞 L := ⟨_, hint i (σ i)⟩
    have eζ : algebraMap (𝓞 L) L ζ = (c : Matrix _ _ L) i (σ i) := rfl
    have hζ : IsOfFinOrder ζ := by
      obtain ⟨k, hk, hk1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hσ i)
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, RingOfIntegers.ext (by simpa [eζ] using hk1)⟩
    have := eq_one_of_finOrder s.ideal_isPrime.ne_top hp (by omega) h h2 hζ (by
      rw [s.split_mem_ideal]
      simpa [eζ] using h3)
    exact congrArg (fun y : 𝓞 L => (y : L)) this
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by simp
  have hsh : ∀ i, Valued.v (((((σ i).val : ℤ) - (i.val : ℤ) : ℤ) : s.v.adicCompletion L⁺) - H.1 0 1) < 1 := by
    intro i
    have h3 := hcong i 1 (Pi.single 0 (H.1 0 1) + Pi.single 1 1) (by
      intro l
      by_cases hl : l = 0
      · subst hl
        simp
      · by_cases hl1 : l = 1
        · subst hl1
          simpa using (hu.2 1 1 (by simp; omega) (by simp; omega)).2 rfl
        · rw [Pi.add_apply, Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl1, add_zero, sub_zero]
          refine hlow l 1 (by simp; omega) ?_
          have e0 : l.val ≠ 0 := fun e => hl (Fin.ext e)
          have e1 : l.val ≠ 1 := fun e => hl1 (Fin.ext e)
          simp; omega)
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at h3
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero]) (by simp),
      Finset.sum_eq_single 1 (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero]) (by simp)] at h3
    simp only [hA, frameM, Matrix.of_apply, if_true, if_neg h10, Int.cast_one, mul_one, one_mul, Pi.single_eq_same,
      hone, map_one] at h3
    convert h3 using 2
    push_cast
    ring
  have hdiff : ∀ i j, ((σ i).val : ℤ) - i.val = ((σ j).val : ℤ) - j.val := by
    intro i j
    have h3 := Valuation.map_sub_lt _ (hsh i) (hsh j)
    have h4 : (p : ℤ) ∣ (((σ i).val : ℤ) - i.val) - (((σ j).val : ℤ) - j.val) := by
      refine int_dvd_of_mem s.ideal_isPrime.ne_top hp h ?_
      rw [s.split_mem_ideal]
      convert h3 using 2
      simp
    have h5 := Int.eq_zero_of_abs_lt_dvd h4 (by
      have := (σ i).2; have := (σ j).2; have := i.2; have := j.2
      rw [abs_lt]; constructor <;> omega)
    omega
  have hid : ∀ i, σ i = i := by
    intro i
    have a1 := hdiff i 0
    have a2 := hdiff i (Fin.last _)
    have := (σ (Fin.last _)).2
    simp only [Fin.val_zero, Fin.val_last] at a1 a2
    apply Fin.ext
    omega
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := hce i j
  refine e.trans ?_
  change _ = (1 : Matrix _ _ (AL L)) i j
  by_cases hij : j = i
  · subst hij
    have := hone j
    rw [hid] at this
    rw [this, Matrix.one_apply_eq]
    rfl
  · rw [hσ0 i j (by rwa [hid]), Matrix.one_apply_ne (Ne.symm hij), TensorProduct.zero_tmul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_trivial_stabiliser : ∀ (D : D7) (k : Fin 2) (s : SplitPlace D.host.E), s.w ∈ placesOver D.host.E (D.host.g k) → ∃ g : GAf D.host.E D.R.nV, ∀ γ ∈ GQ D.host.E D.R.nV, g⁻¹ * γ * g ∈ Umax D.host.E D.R.nV → NG.UniRT s D.R.r (s.loc _ (g⁻¹ * γ * g)) → γ = 1 := by
  intro D k s hs
  have hp := D.host.g_prime k
  have hr : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have ht : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hc := D.ntypes.g_cond k
  have hn : 0 < D.host.QS := D.host.QS_pos
  have hbig : D.host.QS * D.host.q * D.host.d ≤ D.host.g k := by
    by_contra hh
    rw [Nat.mod_eq_of_lt (not_le.1 hh)] at hc
    exact hp.ne_one hc
  have hq' : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    le_trans (Nat.le_mul_of_pos_left _ (by omega)) (Nat.le_mul_of_pos_right _ (by omega))
  have h2n : 2 * D.R.nV ≤ D.host.g k := by
    unfold Ranks.nV
    nlinarith
  have hsq : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ s.ideal ^ 2 := by
    intro hmem
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    have hsq : Squarefree (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}) :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D k).2
    have hd : s.ideal * s.ideal ∣ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
      exact hmem
    exact s.ideal_isPrime.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))
  obtain ⟨m, hm⟩ : ∃ m, D.R.nV = m + 2 := ⟨D.R.nV - 2, by unfold Ranks.nV; omega⟩
  rw [hm] at h2n ⊢
  exact exists_class m D.R.r hr s hp h2n hs hsq

end GlobalTheory.NeatUni

end
