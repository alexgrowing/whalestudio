import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualLatticeSetting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

namespace GlobalTheory.SelMatrixCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem l_mem_maximalIdeal (i : X.Tw) : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem l_mem_maxLam (i : X.Tw) (M : ℕ) (ι : Type) : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ maxLam X i M ι := by
  have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
  rw [map_natCast] at h
  exact Ideal.mem_sup_left h

theorem maxLam_le (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (m : Ideal (abelian₂ X i M ι)) [hm : m.IsMaximal] :
    maxLam X i M ι ≤ m := by
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h0 : (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ m := by
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap (X.O0 i) (abelian₂ X i M ι))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    exact (IsLocalRing.eq_maximalIdeal this).ge
  refine sup_le h0 ?_
  rw [Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  have hl : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ m := by
    have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
    rw [map_natCast] at h
    exact h0 h
  have : Nontrivial (abelian₂ X i M ι ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  have : CharP (abelian₂ X i M ι ⧸ m) (X.l i) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk m)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hl
  have hg : (Multiplicative.ofAdd (Pi.single q 1) : Del X i M ι) ^ (X.l i ^ M) = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, toAdd_one, Pi.zero_apply]
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine hm.isPrime.mem_of_pow_mem (X.l i ^ M) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  simp only [toLam, MvPolynomial.aeval_X, map_sub, map_one]
  rw [sub_pow_char_pow, ← map_pow, ← map_pow]
  rw [one_pow, sub_eq_zero]
  convert map_one (Ideal.Quotient.mk m) using 2
  convert map_one (MonoidAlgebra.of (X.O0 i) (Del X i M ι)) using 2

theorem exists_const (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    ∃ c : X.O0 i, x - algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι := by
  obtain ⟨F, rfl⟩ := toLam_surjective X i M ι x
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨a, by rw [MvPolynomial.algHom_C, sub_self]; exact zero_mem _⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := add_mem ha hb
    rw [map_add, map_add]
    convert this using 1
    ring
  | mul_X p q _ =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))

theorem mem_maxLam_iff (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    x ∈ maxLam X i M ι ↔ ¬ IsUnit x := by
  refine ⟨fun hx hu => maxLam_ne_top X i M ι (Ideal.eq_top_of_isUnit_mem _ hx hu), fun hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  obtain ⟨c, hc⟩ := exists_const X i M ι x
  have h1 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ m := by
    have := sub_mem hxm (maxLam_le X i M ι m hc)
    rwa [sub_sub_cancel] at this
  have h2 : c ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map _))
  have h3 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι :=
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h2)
  have := add_mem hc h3
  rwa [sub_add_cancel] at this

theorem maxLam_isMaximal (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : (maxLam X i M ι).IsMaximal := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (maxLam_ne_top X i M ι)
  have : maxLam X i M ι = m := le_antisymm hle fun x hx =>
    (mem_maxLam_iff X i M ι x).2 fun hu => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  rwa [this]

theorem length_resLam (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] :
    Module.length (abelian₂ X i M ι) (ResLam X i M ι) = 1 := by
  have : IsSimpleModule (abelian₂ X i M ι) (abelian₂ X i M ι ⧸ maxLam X i M ι) :=
    isSimpleModule_iff_isCoatom.2 (maxLam_isMaximal X i M ι).out
  exact Module.length_eq_one (abelian₂ X i M ι) (abelian₂ X i M ι ⧸ maxLam X i M ι)

theorem smul_resLam (i : X.Tw) (M : ℕ) (ι : Type) (x : abelian₂ X i M ι) (hx : x ∈ maxLam X i M ι) (b : ResLam X i M ι) :
    x • b = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (maxLam X i M ι) b
  exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right y _ hx)

variable {X} (bkP : BKPh X)

theorem length_sel_of_computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) (h : Computes bkP i s M d Q Φ) (hΦ : ∀ x y, Φ x y ∈ maxLam X i M ι) :
    Module.length (abelian₂ X i M ι) ↥(selOn bkP i (Tgl i s) (delInv i M d) (ResLam X i M ι) Q) = (a : ℕ∞) := by
  obtain ⟨e, -⟩ := h
  have hB : ∀ b : ResLam X i M ι, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun b =>
    ⟨1, by rw [pow_one, ← Nat.cast_smul_eq_nsmul (abelian₂ X i M ι)]; exact smul_resLam X i M ι _ (l_mem_maxLam X i M ι) b⟩
  have hk : LinearMap.ker (matAct (M := ResLam X i M ι) Φ) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [LinearMap.mem_ker]
    funext x
    change ∑ y, Φ x y • v y = 0
    exact Finset.sum_eq_zero fun y _ => smul_resLam X i M ι _ (hΦ x y) (v y)
  rw [← (e (ResLam X i M ι) hB).length_eq, (LinearEquiv.ofTop _ hk).length_eq, Module.length_pi_of_fintype]
  simp [length_resLam]

theorem isSelMatrix_iff (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) :
    IsSelMatrix bkP i s M d Q a Φ ↔ Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) :=
  ⟨fun h => ⟨h.1, fun b c => (mem_maxLam_iff X i M ι _).1 (h.2.2 b c)⟩, fun h =>
    have h2 : ∀ b c, Φ b c ∈ maxLam X i M ι := fun b c => (mem_maxLam_iff X i M ι _).2 (h.2 b c)
    ⟨h.1, length_sel_of_computes bkP i s M d Q a Φ h.1 h2, h2⟩⟩

theorem galHyp_iff (i : X.Tw) (s : X.Sig i) :
    GalHyp bkP i s ↔ TripleHyp bkP i s ∧ True ∧ 100 ≤ D.R.r :=
  ⟨fun h => ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, le_trans (by norm_num) h.2.2.2.2.2.2⟩,
      h.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.2.1, h.1.2.2.2.2.1, h.2.2⟩⟩

theorem selmer_iff_selmer_matrix_at_primes : ThmS bkP ↔ SelmerMatrixChosenPrimes bkP := by
  constructor
  · intro h i s hG M hM A ι _ P d Q hA hQ
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P d Q hM hA.empty hQ
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).2 hΦ⟩
  · intro h i s hG M ι _ P d Q hM hA hQ
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M hM ∅ ι P d Q hA hQ
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).1 hΦ⟩

theorem selMatrix_iff : SelMatrix bkP ↔
    ∀ (i : X.Tw) (s : X.Sig i), TripleHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d
      (Q : Finset (PlE D.host)), HidaSetting X i M P Q d →
      ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) := by
  constructor
  · intro h i s hG M ι _ P d Q hS
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P Q d hS
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).1 hΦ⟩
  · intro h i s hG M ι _ P Q d hS
    obtain ⟨a, Φ, hΦ⟩ := h i s hG M ι P d Q hS
    exact ⟨a, Φ, (isSelMatrix_iff bkP i s M d Q a Φ).2 hΦ⟩

theorem thmS_of_selMatrix (h : SelMatrix bkP) : ThmS bkP :=
  (selmer_iff_selmer_matrix_at_primes bkP).2 (selmerMatrixAuxiliaryPrimes_of_selMatrix bkP h)

theorem compare : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    (ThmS bkP ↔ SelmerMatrixChosenPrimes bkP) ∧ (SelMatrix bkP → ThmS bkP) ∧
      ∀ (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) [Fintype ι] (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
        (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)),
        IsSelMatrix bkP i s M d Q a Φ ↔ Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c) :=
  fun _ _ _ bkP => ⟨selmer_iff_selmer_matrix_at_primes bkP, thmS_of_selMatrix bkP,
    fun i s M _ _ d Q a Φ => isSelMatrix_iff bkP i s M d Q a Φ⟩

end GlobalTheory.SelMatrixCompare

end
