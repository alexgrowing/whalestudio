import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.PowMemCarrier
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.HasColenNotUniqueWithoutGuard
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGenerationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengthsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisIdealsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengthsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGeneratesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColengthStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEqualityStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdealStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusValuationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProductStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslationStatement

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.FlagClose

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma v_le_of_span_le (hv : v.Integers R) {a b : R} (h : Ideal.span {a} ≤ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self a))
  rw [map_mul, map_mul]
  exact mul_le_of_le_one_right' (hv.map_le_one u)

lemma v_eq_of_span_eq (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) :=
  le_antisymm (v_le_of_span_le hv h.le) (v_le_of_span_le hv h.ge)

lemma span_eq_of_le_of_v_eq (hv : v.Integers R) {c d : R} (hc : c ≠ 0)
    (h : Ideal.span {c} ≤ Ideal.span {d})
    (hvv : v (algebraMap R C c) = v (algebraMap R C d)) :
    Ideal.span {c} = Ideal.span {d} := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.1 (h (Ideal.mem_span_singleton_self c))
  have hu0 : u ≠ 0 := by rintro rfl; simp at hc
  have hd0 : d ≠ 0 := by rintro rfl; simp at hc
  have hinj := hv.hom_inj
  have hd1 : algebraMap R C d ≠ 0 := fun e => hd0 (hinj (by simpa using e))
  have hu1 : algebraMap R C u ≠ 0 := fun e => hu0 (hinj (by simpa using e))
  have hvd : v (algebraMap R C d) ≠ 0 := (Valuation.ne_zero_iff v).2 hd1
  have hvu : v (algebraMap R C u) = 1 := by
    rw [map_mul, map_mul] at hvv
    exact mul_left_cancel₀ hvd (by rw [hvv, mul_one])
  exact Ideal.span_singleton_mul_right_unit (hv.isUnit_of_one (IsUnit.mk0 _ hu1) hvu) d

lemma hasLen_le_one' (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) : x ≤ 1 := by
  obtain ⟨m, c, -, rfl⟩ := h
  exact Finset.prod_le_one' fun i _ => hv.map_le_one _

end Val

lemma prod_fin_shift (f : ℕ) (G : ℕ → NNReal) (h : G f = G 0) (h0 : G 0 ≠ 0) :
    ∏ s : Fin f, G ((s : ℕ) + 1) = ∏ s : Fin f, G s := by
  rw [Fin.prod_univ_eq_prod_range (fun i => G (i + 1)), Fin.prod_univ_eq_prod_range G]
  have h1 := Finset.prod_range_succ' G f
  have h2 := Finset.prod_range_succ G f
  rw [h1, h] at h2
  exact mul_right_cancel₀ h0 h2

section Char

variable {R : Type} [CommRing R] {F : Type} [Field F] [Fintype F]

lemma pow_card_char (χ : MulChar F R) : χ ^ Fintype.card F = χ := by
  ext a
  rw [MulChar.pow_apply_coe, ← map_pow, FiniteField.pow_card]

lemma pow_period {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s + f) = σ ^ p ^ s := by
  rw [pow_add, pow_mul, ← hf, pow_card_char]

lemma pow_period_mul {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s k : ℕ) :
    σ ^ p ^ (s + f * k) = σ ^ p ^ s := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, pow_period hf, ih]

lemma pow_mod {p f : ℕ} (hf : Fintype.card F = p ^ f) (σ : MulChar F R) (s : ℕ) :
    σ ^ p ^ (s % f) = σ ^ p ^ s := by
  conv_rhs => rw [← Nat.mod_add_div s f]
  rw [pow_period_mul hf]

lemma prod_chars {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (σ : MulChar F R)
    (ho : orderOf σ = p ^ f - 1)
    (hfund : ∀ m, IsFund p (σ ^ m) → ∃ n < f, σ ^ m = σ ^ p ^ n)
    (L : MulChar F R → NNReal) (h1 : ∀ χ, ¬ IsFund p χ → L χ = 1) :
    ∏ m ∈ Finset.Icc 1 (p ^ f - 1), L (σ ^ m) = ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) := by
  have hp2 := hp.two_le
  have hle : ∀ n < f, 1 ≤ p ^ n ∧ p ^ n ≤ p ^ f - 1 := by
    intro n hn
    refine ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩
    have h2 : p ^ (n + 1) ≤ p ^ f := Nat.pow_le_pow_right hp.pos hn
    have h3 : p ^ (n + 1) = p ^ n * p := pow_succ p n
    have h4 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
    have h5 : p ^ n * 2 ≤ p ^ n * p := Nat.mul_le_mul_left _ hp2
    omega
  have hinj : Function.Injective (fun s : Fin f => p ^ (s : ℕ)) := fun a b e =>
    Fin.ext (Nat.pow_right_injective hp2 e)
  have himg : ∏ s : Fin f, L (σ ^ p ^ (s : ℕ)) =
      ∏ m ∈ (Finset.univ : Finset (Fin f)).image (fun s : Fin f => p ^ (s : ℕ)), L (σ ^ m) := by
    rw [Finset.prod_image (fun a _ b _ e => hinj e)]
  rw [himg]
  symm
  apply Finset.prod_subset
  · intro m hm
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_Icc.2 (hle s s.2)
  · intro m hm hnot
    apply h1
    intro hfm
    obtain ⟨n, hn, e⟩ := hfund m hfm
    apply hnot
    refine Finset.mem_image.2 ⟨⟨n, hn⟩, Finset.mem_univ _, ?_⟩
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
    obtain ⟨hn1, hn2⟩ := hle n hn
    have hmod : m ≡ p ^ n [MOD orderOf σ] := pow_eq_pow_iff_modEq.1 e
    rw [ho] at hmod
    refine (Nat.ModEq.eq_of_abs_lt hmod ?_).symm
    rw [abs_lt]
    omega

end Char

end GlobalTheory.CompanionTheory.Ar.GR.FlagClose

namespace GlobalTheory.CompanionTheory.Ar.GR

open FlagClose in

theorem flagStatement_holds : FlagStatement := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ N _ _ _ _ AA hFS hT n b hG σ hσ
  obtain ⟨f, hf0, hf⟩ : ∃ f : ℕ, 0 < f ∧ Fintype.card F = p ^ f := by
    obtain ⟨k, -, e⟩ := FiniteField.card F p
    exact ⟨k, k.pos, e⟩
  have hpp : p.Prime := Fact.out
  obtain ⟨hord, -, hfp, hfund, -⟩ := GlobalTheory.T.teichmuller_character_order_generates p C v R hv hp F f hf σ hσ
  have hFp : ∀ s, IsFund p (σ ^ p ^ s) := hfp
  have hbK : ∀ i : Fin n, b i ∉ flagSub b i := fun i =>
    b.linearIndependent.notMem_span_image (by simp)
  have hstep := fun i : Fin n =>
    GlobalTheory.T.stable_hopf_order_subgroup_translation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i)
  choose S hSc hSF using fun i => (hstep i).1
  have hres : ∀ i : Fin n, stepOrder AA.carrier (flagSub b i) (b i) =
      stepOrderRes AA.carrier (flagSub b i) (b i) := fun i => (hstep i).2
  choose c hc0 hcX using fun (i : Fin n) (s : ℕ) =>
    (GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp F f hf (S i) (hSF i) (σ ^ p ^ s)).1
  have hom := fun i : Fin n =>
    GlobalTheory.T.fundamental_ideal_frobenius_product p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)
  choose δ hδ using fun (i : Fin n) (s : ℕ) => (hom i s).2.1
  have hδL : ∀ (i : Fin n) (s : ℕ), HasLen v R (OmType (S i).carrier (σ ^ p ^ (s + 1)))
      (v (algebraMap R C (δ i s))) := fun i s => (hom i s).2.2 _ (hδ i s)
  have hstepL : ∀ (i : Fin n) (s : ℕ),
      HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ (s + 1)))
        (v (algebraMap R C (δ i s))) := by
    intro i s
    rw [← hSc i]
    exact hδL i s
  have hXc : ∀ (i : Fin n) (s : ℕ),
      idealX AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    show xIdeal (stepOrder AA.carrier (flagSub b i) (b i)) (σ ^ p ^ s) = _
    rw [← hSc i]
    exact hcX i s
  obtain ⟨d, hdD, hdL⟩ := GlobalTheory.T.stable_hopf_order_fundamental_lengths p C v R hv hp F f hf N AA hFS σ hσ n b
  obtain ⟨cA, cN, cO, hcA, hcN, hcO, e1, e2⟩ := hT
  obtain ⟨hLex, hLprod⟩ := GlobalTheory.T.stable_hopf_order_fundamental_ideal p C v R hv hp F f hf N AA hFS σ hσ
  choose L hL0 hL using hLex

  have hnf : ∀ χ : MulChar F R, ¬ IsFund p χ → L χ = 1 := by
    intro χ hχ
    have hsub : ∀ i : Fin n,
        HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) 1 := by
      intro i
      rw [← hSc i]
      have hle := GlobalTheory.T.non_fundamental_eigen_le_square_augmentation p C v R hv hp F f hf (S i) (hSF i) χ hχ
      haveI : Subsingleton (OmType (S i).carrier χ) := by
        refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
        intro x _
        exact hle x.2
      exact hasLen_subsingleton v R _
    have h1 := GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b χ (fun _ => 1) (L χ) hsub (hL χ)
    exact le_antisymm (hasLen_le_one' hv (hL χ)) (by simpa using h1)

  have hcN0 : cN ≠ 0 := by
    obtain ⟨B, hB, h⟩ := AA.lat
    have e := GlobalTheory.HopfOrderCheck.hasColen_unique v (fun r => hv.map_le_one r) hcN ⟨B, h, rfl⟩
    rw [e]
    exact (Valuation.ne_zero_iff v).2 hB.ne_zero

  have hvc0 : ∀ (i : Fin n) (s : ℕ), v (algebraMap R C (c i s)) ≠ 0 := fun i s =>
    (Valuation.ne_zero_iff v).2 fun e => hc0 i s (hv.hom_inj (by simpa using e))
  have hcmod : ∀ (i : Fin n) (s : ℕ), Ideal.span {c i (s % f)} = Ideal.span {c i s} := by
    intro i s
    rw [← hXc, ← hXc, pow_mod hf]
  have hvper : ∀ (i : Fin n), v (algebraMap R C (c i f)) = v (algebraMap R C (c i 0)) := by
    intro i
    have h := hcmod i f
    rw [Nat.mod_self] at h
    exact (v_eq_of_span_eq hv h).symm
  have hxD : ∀ (t : Fin n) (s : Fin f),
      v (algebraMap R C (c t s)) ≤ v (algebraMap R C (d t s)) := by
    intro t s
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b t) (b t) (hbK t) (hG t)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rw [hXc, hdD] at h
    exact v_le_of_span_le hv h
  have hDA : ∏ t, ∏ s, v (algebraMap R C (d t s)) = cA := hasLen_unique hv hdL hcA

  choose cs hcs using fun i : Fin n => hasColen_of_lat v (S i).lat
  have hcsq : ∀ i : Fin n, cs i ^ 2 =
      (∏ s : Fin f, v (algebraMap R C (c i s))) ^ (p ^ f * (p - 1)) := fun i =>
    (GlobalTheory.T.fundamental_ideal_frobenius_valuation p C v R hv hp F f hf (S i) (hSF i) σ hσ (c i) (hcX i)).2 _ (hcs i)
  have hcfl : cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N :=
    GlobalTheory.T.stable_hopf_order_basis_ideals p C v R hv hp F f hf N AA hFS n b cs cN
      (fun i => by rw [← hSc i]; exact hcs i) hcN
  have hxN : (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1)) =
      cN ^ 2 := by
    have hq : p ^ f ≠ 0 := pow_ne_zero _ hpp.ne_zero
    refine (pow_left_inj₀ zero_le' zero_le' hq).1 ?_
    calc ((∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (Fintype.card N * (p - 1))) ^ p ^ f
        = (∏ t, (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p ^ f * (p - 1))) ^ Fintype.card N := by
          rw [Finset.prod_pow, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = (∏ t, cs t ^ 2) ^ Fintype.card N := by simp only [hcsq]
      _ = (cN ^ 2) ^ p ^ f := by
          rw [Finset.prod_pow, ← pow_mul, pow_right_comm cN, hcfl, ← pow_mul, mul_comm 2]

  have hdx : ∏ t, ∏ s : Fin f, v (algebraMap R C (δ t s)) =
      (∏ t, ∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t _ => ?_
    have hP : ∏ s : Fin f, v (algebraMap R C (c t s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun s _ => hvc0 t s
    have hsh := prod_fin_shift f (fun s => v (algebraMap R C (c t s))) (hvper t) (hvc0 t 0)
    have hmul : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p =
        (∏ s : Fin f, v (algebraMap R C (δ t s))) *
          ∏ s : Fin f, v (algebraMap R C (c t s)) := by
      rw [← Finset.prod_pow]
      conv_rhs => rw [← hsh]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← map_pow, ← map_pow, hδ, map_mul, map_mul]
    have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hpp.one_le).symm
    have h2 : (∏ s : Fin f, v (algebraMap R C (c t s))) ^ (p - 1) *
        ∏ s : Fin f, v (algebraMap R C (c t s)) =
        (∏ s : Fin f, v (algebraMap R C (c t s))) ^ p := by
      rw [← pow_succ, ← hp1]
    exact (mul_right_cancel₀ hP (h2.trans hmul)).symm
  have hrle : ∀ s : Fin f, ∏ t, v (algebraMap R C (δ t s)) ≤ L (σ ^ p ^ ((s : ℕ) + 1)) :=
    fun s => GlobalTheory.T.stable_hopf_order_basis_lengths p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ ((s : ℕ) + 1))
      (fun i => v (algebraMap R C (δ i s))) _ (fun i => hstepL i s) (hL _)
  have hrO : ∏ s : Fin f, L (σ ^ p ^ ((s : ℕ) + 1)) = cO := by
    have h1 := prod_fin_shift f (fun s => L (σ ^ p ^ s))
      (by simpa using congrArg L (pow_period hf σ 0)) (hL0 _)
    have h2 := prod_chars hpp hf0 σ hord (fun m hm => hfund _ hm) L hnf
    have h3 := hasLen_unique hv (hLprod (fun m => L (σ ^ m)) (fun m _ => hL _)) hcO
    exact h1.trans (h2.symm.trans h3)
  obtain ⟨hDx, hlen⟩ := GlobalTheory.T.product_inequalities_force_equality (Fin n) (Fin f) (Fintype.card N) (p - 1) Fintype.card_pos
    (Nat.sub_pos_of_lt hpp.one_lt)
    (fun t s => v (algebraMap R C (c t s))) (fun t s => v (algebraMap R C (d t s)))
    (fun t s => v (algebraMap R C (δ t s))) (fun s => L (σ ^ p ^ ((s : ℕ) + 1))) cA cN cO hcN0
    hxD hDA hxN e1 hrle hrO hdx e2

  have hCD : ∀ (i : Fin n) (s : Fin f), Ideal.span {c i s} = Ideal.span {d i s} := by
    intro i s
    refine span_eq_of_le_of_v_eq hv (hc0 i s) ?_ (hDx i s).symm
    have h := GlobalTheory.T.stable_hopf_order_subgroup_generation p C v R hv hp F f hf N AA hFS (flagSub b i) (b i) (hbK i) (hG i)
      (σ ^ p ^ (s : ℕ)) (hFp s)
    rwa [hXc, hdD] at h
  have hD : ∀ (i : Fin n) (s : ℕ),
      idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ s) = Ideal.span {c i s} := by
    intro i s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hdD i ⟨s % f, hs⟩
    have h' := hCD i ⟨s % f, hs⟩
    simp only at h h'
    rw [pow_mod hf] at h
    rw [h, ← h', hcmod]
  have hsucc : ∀ s : ℕ, σ ^ p ^ (s % f + 1) = σ ^ p ^ (s + 1) := by
    intro s
    rw [pow_succ, pow_succ, pow_mul, pow_mul, pow_mod hf]
  have hall : ∀ s : ℕ, HasLen v R (OmType AA.carrier (σ ^ p ^ (s + 1)))
      (∏ i, v (algebraMap R C (δ i s))) := by
    intro s
    have hs : s % f < f := Nat.mod_lt _ hf0
    have h := hlen ⟨s % f, hs⟩
    simp only at h
    have hδe : ∀ i : Fin n, v (algebraMap R C (δ i s)) = v (algebraMap R C (δ i (s % f))) := by
      intro i
      have h2 := hδL i (s % f)
      rw [hsucc] at h2
      exact hasLen_unique hv (hδL i s) h2
    simp only [hδe]
    rw [h, hsucc]
    exact hL _
  refine ⟨c, δ, fun i s => ⟨hc0 i s, hXc i s, ?_, hD i s, hδ i s, hstepL i s⟩, hall, ?_⟩
  · rw [← hres i, ← hSc i]
    exact hcX i s
  · intro j s
    exact GlobalTheory.T.stable_hopf_order_basis_colength p C v R hv hp F f hf N AA hFS n b (σ ^ p ^ (s + 1))
      (fun i => v (algebraMap R C (δ i s))) (fun i => hstepL i s) (hall s) j

end GlobalTheory.CompanionTheory.Ar.GR
