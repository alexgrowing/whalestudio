import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharpolySmulMap
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def abH : (A ℚ)ˣ →* ℝ where
  toFun := ab
  map_one' := by simp [ab]
  map_mul' a b := by simp [ab, map_mul]

private theorem ab_idl (v : H.P ℚ) (x : (H.Kv v)ˣ) : ab (H.idl v x) = ‖(x : H.Kv v)‖ := by
  obtain ⟨h1, h2⟩ := localIdele_isSupportedAt ℚ v x
  show ((IdeleGroup.ideleModule ℚ (localIdele ℚ v x) : {r : ℝ // 0 < r}) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  have e1 : ∏ w : InfinitePlace ℚ, ‖((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ).1 w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => by rw [h1 w, norm_one, one_pow]
  rw [e1, one_mul]
  refine (finprod_eq_single _ v fun u hu => ?_).trans ?_
  · rw [h2 u hu, norm_one]
  · rw [localIdele_snd_self]

private theorem norm_unif (v : H.P ℚ) :
    ‖((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v)‖ = ((normV v : ℕ) : ℝ)⁻¹ := by
  have h : Valued.v ((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v) = WithZero.exp (-1 : ℤ) := unif_spec v
  have h2 : v.valuation ℚ (unif v : ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact h
  have h3 := FinitePlace.norm_embedding' v (unif v : ℚ)
  rw [h2] at h3
  have h4 : ‖((atFin v (unif v) : (H.Kv v)ˣ) : H.Kv v)‖ = ‖FinitePlace.embedding v (unif v : ℚ)‖ := rfl
  rw [h4, h3, GlobalTheory.TwAtt.normV_eq, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp
  exact zpow_neg_one _

private theorem ab_pv (v : H.P ℚ) : ab (pv v) = ((normV v : ℕ) : ℝ)⁻¹ := by
  rw [pv, ab_idl, norm_unif]

private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : H.P ℚ, normV w = p := by
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  refine ⟨⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp), ?_⟩, ?_⟩
  · intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  · rw [GlobalTheory.TwAtt.normV_eq]
    exact hN

private theorem supp_fin (n : ℕ) :
    (Function.mulSupport fun v : H.P ℚ => pv v ^ (n.factorization (normV v))).Finite := by
  refine (Set.Finite.preimage GlobalTheory.TwAtt.normV_injective.injOn n.primeFactors.finite_toSet).subset fun v hv => ?_
  by_contra h
  apply hv
  have h0 : n.factorization (normV v) = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact h
  simp [h0]

private theorem prod_norm {n : ℕ} (hn : 0 < n) :
    ∏ᶠ v : H.P ℚ, (((normV v : ℕ) : ℝ)⁻¹) ^ (n.factorization (normV v)) = (n : ℝ)⁻¹ := by
  set g : ℕ → ℝ := fun p => ((p : ℝ)⁻¹) ^ (n.factorization p) with hg
  have h1 : ∏ᶠ v : H.P ℚ, g (normV v) = ∏ᶠ p ∈ Set.range (normV : H.P ℚ → ℕ), g p :=
    (finprod_mem_range GlobalTheory.TwAtt.normV_injective).symm
  have h2 : ∏ᶠ p ∈ Set.range (normV : H.P ℚ → ℕ), g p = ∏ p ∈ n.primeFactors, g p := by
    refine finprod_mem_eq_prod_of_inter_mulSupport_eq _ ?_
    ext p
    simp only [Set.mem_inter_iff, Set.mem_range, Function.mem_mulSupport, Finset.mem_coe]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨?_, h⟩
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      intro h0
      exact h (by simp [hg, h0])
    · rintro ⟨hp, h⟩
      exact ⟨normV_surj (Nat.prime_of_mem_primeFactors hp), h⟩
  have h3 : ∏ p ∈ n.primeFactors, g p = (n : ℝ)⁻¹ := by
    have h4 : ((∏ p ∈ n.primeFactors, p ^ (n.factorization p) : ℕ) : ℝ) = n := by
      have := Nat.factorization_prod_pow_eq_self hn.ne'
      rw [Finsupp.prod, Nat.support_factorization] at this
      rw [this]
    rw [← h4]
    push_cast
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => by simp [hg]
  exact (h1.trans h2).trans h3

private theorem ab_pin {n : ℕ} (hn : 0 < n) : ab (pin n) = (n : ℝ)⁻¹ := by
  have h := MonoidHom.map_finprod abH (supp_fin n)
  have h2 : ab (pin n) = abH (pin n) := rfl
  rw [h2, pin, h]
  refine (finprod_congr fun v => ?_).trans (prod_norm hn)
  rw [map_pow]
  congr 1
  exact ab_pv v

private theorem pin_fst (n : ℕ) : ((pin n : (A ℚ)ˣ) : A ℚ).1 = 1 := by
  refine finprod_induction (p := fun x : (A ℚ)ˣ => (x : A ℚ).1 = 1) rfl ?_ ?_
  · intro x y hx hy
    simp [Units.val_mul, hx, hy]
  · intro v
    have h : ((pv v : (A ℚ)ˣ) : A ℚ).1 = 1 := by
      funext w
      exact (localIdele_isSupportedAt ℚ v _).1 w
    have hk : ∀ k : ℕ, (((pv v ^ k : (A ℚ)ˣ)) : A ℚ).1 = 1 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ, Units.val_mul]
        show (((pv v ^ k : (A ℚ)ˣ)) : A ℚ).1 * ((pv v : (A ℚ)ˣ) : A ℚ).1 = 1
        rw [ih, h, one_mul]
    exact hk _

private theorem re_one_of {x : A ℚ} (h : x.1 = 1) : re x = 1 := by
  show (TR.infEq ℚ).symm x.1 Rat.infinitePlace = 1
  rw [h, map_one]
  rfl

private theorem iy_val {r : ℝ} (hr : r ≠ 0) : ∃ d : (TR.Rinf ℚ)ˣ, iy r = TR.infId ℚ d ∧ ∀ w, d.val w = r :=
  ⟨_, dif_neg hr, fun _ => rfl⟩

private theorem re_iy {r : ℝ} (hr : r ≠ 0) : re (iy r : A ℚ) = r := by
  obtain ⟨d, hd, hw⟩ := iy_val hr
  show (TR.infEq ℚ).symm (iy r : A ℚ).1 Rat.infinitePlace = r
  rw [hd, UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth.infId_fst, RingEquiv.symm_apply_apply, hw]

private theorem ab_iy {r : ℝ} (hr : r ≠ 0) : ab (iy r) = |r| := by
  obtain ⟨d, hd, hw⟩ := iy_val hr
  rw [hd]
  show ((IdeleGroup.ideleModule ℚ (TR.infId ℚ d) : {r : ℝ // 0 < r}) : ℝ) = _
  rw [UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth.ideleModule_infId]
  simp [hw]

private theorem ab_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : ab t = 1 := by
  show ((IdeleGroup.ideleModule ℚ t : {r : ℝ // 0 < r}) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  have e1 : ∏ w : InfinitePlace ℚ, ‖(t : A ℚ).1 w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => by rw [ht.1]; exact (by rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow])
  rw [e1, one_mul]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have h := ht.2 v
  have h' : Valued.v ((t : A ℚ).2 v) = 1 := h
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.2 h'.le) (not_lt.1 fun hlt => ?_)
  exact (Valued.toNormedField.norm_lt_one_iff.1 hlt).ne h'

theorem UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles :
    (∀ r : ℝ, r ≠ 0 → ab (iy r) = |r|) ∧ (∀ n : ℕ, 0 < n → ab (pin n) = (n : ℝ)⁻¹) ∧ (∀ t ∈ UU, ab t = 1) ∧
        (∀ (r : ℝ) (n : ℕ), r ≠ 0 → 0 < n → re ((iy r * pin n : (A ℚ)ˣ) : A ℚ) = r) := by
  refine ⟨fun r hr => ab_iy hr, fun n hn => ab_pin hn, fun t ht => ab_UU ht, fun r n hr _ => ?_⟩
  have hm : re ((iy r * pin n : (A ℚ)ˣ) : A ℚ) = re (iy r : A ℚ) * re (pin n : A ℚ) := by
    show (TR.pInf ℚ _) _ = (TR.pInf ℚ _) _ * (TR.pInf ℚ _) _
    rw [Units.val_mul, map_mul]
    rfl
  rw [hm, re_iy hr, re_one_of (pin_fst n), mul_one]
