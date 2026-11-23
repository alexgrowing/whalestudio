import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplit
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in

def splitProj (τ : E →ₐ[F] Fv F v) : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v :=
  Algebra.TensorProduct.lift (AlgHom.id _ _) τ fun _ _ => Commute.all _ _

omit [NumberField E] in
@[simp] theorem splitProj_tmul (τ : E →ₐ[F] Fv F v) (a : Fv F v) (x : E) : splitProj τ (a ⊗ₜ[F] x) = a * τ x := rfl

omit [NumberField E] in
theorem splitProj_inclR (τ : E →ₐ[F] Fv F v) (x : E) : splitProj τ (inclR (Fv F v) x) = τ x := one_mul _

omit [NumberField E] in

theorem splitProj_comp (τ : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) (y : Fv F v ⊗[F] E) :
    splitProj (τ.comp σ) y = splitProj τ (sigR _ σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem continuous_splitProj (τ : E →ₐ[F] Fv F v) : Continuous (splitProj τ) :=
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.continuous_of_linearMap (splitProj τ).toLinearMap

theorem cm_conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact φ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_cm_conj_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push Not at hc
  have := h.2.1
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk φ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x =>
      (h.2.2.2 φ x).symm.trans (congrArg φ (hc x)))))

theorem comp_conj_conj (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : (τ.comp σ).comp σ = τ :=
  AlgHom.ext fun x => congrArg τ (cm_conj_conj h x)

theorem comp_conj_ne {K : Type} [Field K] [Algebra F K] (h : IsCMExt F E σ) (τ : E →ₐ[F] K) : τ.comp σ ≠ τ :=
  fun e => by
    obtain ⟨x, hx⟩ := exists_cm_conj_ne h
    exact hx ((τ : E →+* K).injective (AlgHom.congr_fun e x))

theorem eq_or_eq_comp_conj {K : Type} [Field K] [Algebra F K] (h : IsCMExt F E σ) (τ τ' : E →ₐ[F] K) :
    τ' = τ ∨ τ' = τ.comp σ := by
  by_contra hc
  push Not at hc
  have h3 := Fintype.two_lt_card_iff.2 ⟨τ', τ, τ.comp σ, hc.1, hc.2, (comp_conj_ne h τ).symm⟩
  have h4 := card_algHom_le_finrank F E K
  rw [Nat.card_eq_fintype_card, h.2.2.1] at h4
  exact absurd h3 (not_lt.2 h4)

theorem splitProj_comp_sigR (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitProj (τ.comp σ) (sigR _ σ y) = splitProj τ y := by
  rw [← splitProj_comp, comp_conj_conj h]

theorem splitPair_bijective (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Function.Bijective ((splitProj τ).prod (splitProj (τ.comp σ))) := by
  have hsurj : Function.Surjective ((splitProj τ).prod (splitProj (τ.comp σ))).toLinearMap := by
    obtain ⟨x, hx⟩ := exists_cm_conj_ne h
    have hd : τ x - τ (σ x) ≠ 0 := sub_ne_zero.2 fun e => hx ((τ : E →+* Fv F v).injective e).symm
    rintro ⟨a, b⟩
    refine ⟨((a - b) / (τ x - τ (σ x))) ⊗ₜ[F] x + ((b * τ x - a * τ (σ x)) / (τ x - τ (σ x))) ⊗ₜ[F] 1, ?_⟩
    refine Prod.ext ?_ ?_
    · simp; field_simp; ring
    · simp; field_simp; ring
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
  rw [Module.finrank_baseChange, h.2.2.1, Module.finrank_prod, Module.finrank_self]

def splitAlgEquiv (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : Fv F v ⊗[F] E ≃ₐ[Fv F v] Fv F v × Fv F v :=
  AlgEquiv.ofBijective _ (splitPair_bijective h τ)

theorem splitAlgEquiv_apply (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitAlgEquiv h τ y = (splitProj τ y, splitProj (τ.comp σ) y) := rfl

@[simp] theorem splitProj_symm (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    splitProj τ ((splitAlgEquiv h τ).symm p) = p.1 := congrArg Prod.fst ((splitAlgEquiv h τ).apply_symm_apply p)

@[simp] theorem splitProj_comp_symm (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    splitProj (τ.comp σ) ((splitAlgEquiv h τ).symm p) = p.2 :=
  congrArg Prod.snd ((splitAlgEquiv h τ).apply_symm_apply p)

theorem split_ext (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {y z : Fv F v ⊗[F] E} (h1 : splitProj τ y = splitProj τ z)
    (h2 : splitProj (τ.comp σ) y = splitProj (τ.comp σ) z) : y = z :=
  (splitAlgEquiv h τ).injective (Prod.ext h1 h2)

theorem splitAlgEquiv_sigR (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitAlgEquiv h τ (sigR _ σ y) = (splitAlgEquiv h τ y).swap :=
  Prod.ext (splitProj_comp τ σ y).symm (splitProj_comp_sigR h τ y)

theorem continuous_splitAlgEquiv_symm (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous (splitAlgEquiv h τ).symm :=
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (Fv F v) (Fv F v ⊗[F] E)
  IsModuleTopology.continuous_of_linearMap (splitAlgEquiv h τ).symm.toLinearMap

def splitIdem (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : Fv F v ⊗[F] E := (splitAlgEquiv h τ).symm (1, 0)

@[simp] theorem splitProj_splitIdem (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : splitProj τ (splitIdem h τ) = 1 :=
  splitProj_symm h τ _

@[simp] theorem splitProj_comp_splitIdem (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    splitProj (τ.comp σ) (splitIdem h τ) = 0 := splitProj_comp_symm h τ _

theorem splitIdem_mul_self (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : splitIdem h τ * splitIdem h τ = splitIdem h τ :=
  split_ext h τ (by simp) (by simp)

theorem sigR_splitIdem (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : sigR _ σ (splitIdem h τ) = 1 - splitIdem h τ :=
  split_ext h τ (by simp [← splitProj_comp]) (by simp [splitProj_comp_sigR h])

theorem splitIdem_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : splitIdem h (τ.comp σ) = 1 - splitIdem h τ :=
  split_ext h τ (by simpa [comp_conj_conj h] using splitProj_comp_splitIdem h (τ.comp σ)) (by simp)

theorem splitIdem_mul (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitIdem h τ * y = splitProj τ y • splitIdem h τ := split_ext h τ (by simp) (by simp)

theorem splitProj_eq_zero_iff (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitProj τ y = 0 ↔ splitIdem h τ * y = 0 :=
  ⟨fun e => by rw [splitIdem_mul, e, zero_smul], fun e => by simpa using congrArg (splitProj τ) e⟩

theorem finEmb_ofId_comp (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    finEmb F v ((IsScalarTower.toAlgHom F (Fv F v) (FvBar F v)).comp τ) y =
      algebraMap (Fv F v) (FvBar F v) (splitProj τ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp

theorem nnnorm_le_one_iff_mem {a : Fv F v} : ‖a‖₊ ≤ 1 ↔ a ∈ v.adicCompletionIntegers F :=
  Iff.trans NNReal.coe_le_coe.symm Valued.toNormedField.norm_le_one_iff

theorem splitProj_mem (τ : E →ₐ[F] Fv F v) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    splitProj τ y ∈ v.adicCompletionIntegers F := by
  have := (absFin_le_iff F v).1 (absFin_le_one_of_mem_intLoc hy)
    ((IsScalarTower.toAlgHom F (Fv F v) (FvBar F v)).comp τ)
  rwa [finEmb_ofId_comp, absBar_algebraMap, nnnorm_le_one_iff_mem] at this

theorem mem_intLoc_iff_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {y : Fv F v ⊗[F] E} :
    y ∈ intLoc F E v ↔
      splitProj τ y ∈ v.adicCompletionIntegers F ∧ splitProj (τ.comp σ) y ∈ v.adicCompletionIntegers F := by
  refine ⟨fun hy => ⟨splitProj_mem _ hy, splitProj_mem _ hy⟩, fun hy => ?_⟩
  refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun ρ => ?_)
  rcases eq_or_eq_comp_conj h ((IsScalarTower.toAlgHom F (Fv F v) (FvBar F v)).comp τ) ρ with rfl | rfl
  · rw [finEmb_ofId_comp, absBar_algebraMap, nnnorm_le_one_iff_mem]; exact hy.1
  · rw [AlgHom.comp_assoc, finEmb_ofId_comp, absBar_algebraMap, nnnorm_le_one_iff_mem]; exact hy.2

theorem splitIdem_mem (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : splitIdem h τ ∈ intLoc F E v :=
  (mem_intLoc_iff_split h τ).2 (by simp)

theorem apply_coe_mem (τ : E →ₐ[F] Fv F v) (x : 𝓞 E) : τ x ∈ v.adicCompletionIntegers F := by
  simpa using splitProj_mem τ (tmul_mem_intLoc (one_mem _) x)

def splitInt (τ : E →ₐ[F] Fv F v) : 𝓞 E →+* v.adicCompletionIntegers F :=
  ((τ : E →+* Fv F v).comp (algebraMap (𝓞 E) E)).codRestrict _ (apply_coe_mem τ)

@[simp] theorem coe_splitInt (τ : E →ₐ[F] Fv F v) (x : 𝓞 E) : (splitInt τ x : Fv F v) = τ x := rfl

theorem mem_maximalIdeal_iff_valued {a : v.adicCompletionIntegers F} :
    a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (a : Fv F v) < 1 :=
  Valuation.mem_maximalIdeal_iff _ _

omit [NumberField E] in
theorem valued_apply_algebraMap (τ : E →ₐ[F] Fv F v) (a : F) : Valued.v (τ (algebraMap F E a)) = v.valuation F a := by
  rw [AlgHom.commutes]; exact ReciprocityTheory.Aut.adic_valued_algebraMap v a

theorem algebraMap_mem_comap_splitInt (τ : E →ₐ[F] Fv F v) (a : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 E) a ∈ (IsLocalRing.maximalIdeal _).comap (splitInt τ) ↔ a ∈ v.asIdeal :=
  mem_maximalIdeal_iff_valued.trans (by
    rw [← v.valuation_lt_one_iff_mem (K := F), ← valued_apply_algebraMap τ]; rfl)

def splitPrime (τ : E →ₐ[F] Fv F v) : HeightOneSpectrum (𝓞 E) where
  asIdeal := (IsLocalRing.maximalIdeal _).comap (splitInt τ)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot h0 := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have := (algebraMap_mem_comap_splitInt τ a).2 ha
    rw [h0, Ideal.mem_bot] at this
    exact ha0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this)

theorem mem_splitPrime (τ : E →ₐ[F] Fv F v) (x : 𝓞 E) : x ∈ (splitPrime τ).asIdeal ↔ Valued.v (τ x) < 1 :=
  mem_maximalIdeal_iff_valued

theorem algebraMap_mem_splitPrime (τ : E →ₐ[F] Fv F v) (a : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 E) a ∈ (splitPrime τ).asIdeal ↔ a ∈ v.asIdeal := algebraMap_mem_comap_splitInt τ a

theorem splitPrime_under (τ : E →ₐ[F] Fv F v) : (splitPrime τ).under (𝓞 F) = v :=
  HeightOneSpectrum.ext (Ideal.ext (algebraMap_mem_splitPrime τ))

instance splitPrime_liesOver (τ : E →ₐ[F] Fv F v) : (splitPrime τ).asIdeal.LiesOver v.asIdeal :=
  ⟨(Ideal.ext (algebraMap_mem_splitPrime τ)).symm⟩

theorem mem_splitPrime_comp (τ : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) (x : 𝓞 E) :
    x ∈ (splitPrime (τ.comp σ)).asIdeal ↔ RingOfIntegers.mapRingHom (σ : E →+* E) x ∈ (splitPrime τ).asIdeal := by
  rw [mem_splitPrime, mem_splitPrime]; rfl

theorem valued_apply_eq_valuation (τ : E →ₐ[F] Fv F v) (x : E) : Valued.v (τ x) = (splitPrime τ).valuation E x := by
  set w := splitPrime τ
  let u : Valuation E (WithZero (Multiplicative ℤ)) := Valued.v.comap (τ : E →+* Fv F v)
  have hu : ∀ y, u y = Valued.v (τ y) := fun _ => rfl
  have h1 : ∀ d : 𝓞 E, d ∉ w.asIdeal → u d = 1 := fun d hd =>
    le_antisymm (apply_coe_mem τ d) (not_lt.1 fun e => hd ((mem_splitPrime τ d).2 e))
  have h2 : ∀ y : E, w.valuation E y = 1 → u y = 1 := fun y hy => by
    obtain ⟨n, ⟨d, hd⟩, e | e⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
    · have e1 := congrArg (w.valuation E) e
      rw [map_mul, hy, one_mul, (w.valuation_eq_one_iff_notMem (K := E)).2 hd] at e1
      have e2 := congrArg u e
      rwa [map_mul, h1 d hd, h1 n ((w.valuation_eq_one_iff_notMem (K := E)).1 e1.symm), mul_one] at e2
    · have e1 := congrArg (w.valuation E) e
      rw [map_mul, hy, one_mul, (w.valuation_eq_one_iff_notMem (K := E)).2 hd] at e1
      have e2 := congrArg u e
      rwa [map_mul, h1 d hd, h1 n ((w.valuation_eq_one_iff_notMem (K := E)).1 e1), mul_one] at e2
  obtain ⟨p, hp⟩ := w.intValuation_exists_uniformizer
  rw [← w.valuation_of_algebraMap (K := E)] at hp
  have hp0 : algebraMap (𝓞 E) E p ≠ 0 := fun e => WithZero.exp_ne_zero (hp.symm.trans ((congrArg _ e).trans (map_zero _)))
  have hup : u (algebraMap (𝓞 E) E p) < 1 := (mem_splitPrime τ p).1
    ((w.valuation_lt_one_iff_mem (K := E) p).1 (by rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num))
  obtain ⟨k, hk⟩ : ∃ k : ℤ, u (algebraMap (𝓞 E) E p) = WithZero.exp k :=
    ⟨_, (WithZero.exp_log ((map_ne_zero u).2 hp0)).symm⟩
  have h3 : ∀ (y : E) (m : ℤ), w.valuation E y = WithZero.exp m → u y = WithZero.exp (-(m * k)) := fun y m hy => by
    have := h2 (y * algebraMap (𝓞 E) E p ^ m) (by
      rw [map_mul, map_zpow₀, hy, hp, ← WithZero.exp_zsmul, ← WithZero.exp_add]; simp)
    rw [map_mul, map_zpow₀, hk, ← WithZero.exp_zsmul] at this
    rw [WithZero.exp_neg, eq_inv_of_mul_eq_one_left this, smul_eq_mul]
  obtain ⟨q, hq⟩ := v.valuation_exists_uniformizer F
  have hq0 : algebraMap F E q ≠ 0 := (map_ne_zero _).2 fun e => by
    rw [e, map_zero] at hq; exact WithZero.exp_ne_zero hq.symm
  have h4 := h3 _ _ (WithZero.exp_log ((map_ne_zero (w.valuation E)).2 hq0)).symm
  rw [hu, valued_apply_algebraMap, hq, WithZero.exp_inj, neg_inj] at h4
  rw [hk, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hup
  have hk1 : k = -1 := by
    rcases Int.isUnit_iff.1 (IsUnit.of_mul_eq_one_right _ h4.symm) with e | e <;> omega
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' := (WithZero.exp_log ((map_ne_zero (w.valuation E)).2 hx)).symm
    rw [← hu, h3 _ _ hx', hk1, mul_neg_one, neg_neg, ← hx']

theorem residue_splitInt_surjective (τ : E →ₐ[F] Fv F v) :
    Function.Surjective ((IsLocalRing.residue _).comp (splitInt τ)) := fun y => by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := ReciprocityTheory.Aut.adic_exists_approx v (y : Fv F v) y.2
  refine ⟨algebraMap (𝓞 F) (𝓞 E) a, (Ideal.Quotient.eq.2 (mem_maximalIdeal_iff_valued.2 ?_)).symm⟩
  have e : (splitInt τ (algebraMap (𝓞 F) (𝓞 E) a) : Fv F v) = algebraMap (𝓞 F) (Fv F v) a := τ.commutes (a : F)
  rwa [AddSubgroupClass.coe_sub, e]

def splitResidueEquiv (τ : E →ₐ[F] Fv F v) :
    (𝓞 E ⧸ (splitPrime τ).asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  RingEquiv.ofBijective (Ideal.quotientMap _ (splitInt τ) le_rfl) ⟨Ideal.quotientMap_injective, fun y => by
    obtain ⟨x, rfl⟩ := residue_splitInt_surjective τ y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩⟩

theorem splitResidueEquiv_mk (τ : E →ₐ[F] Fv F v) (x : 𝓞 E) :
    splitResidueEquiv τ (Ideal.Quotient.mk _ x) = IsLocalRing.residue _ (splitInt τ x) := rfl

theorem splitPrime_comp_ne (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : splitPrime (τ.comp σ) ≠ splitPrime τ := by
  intro e
  have key : ∀ y ∈ intLoc F E v, Valued.v (splitProj τ y - splitProj (τ.comp σ) y) < 1 := fun y hy => by
    refine intLoc_induction (p := fun y => Valued.v (splitProj τ y - splitProj (τ.comp σ) y) < 1)
      (fun a ha x => ?_) (by simp) (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · obtain ⟨c, hc⟩ := ReciprocityTheory.Aut.adic_exists_approx v (τ x) (apply_coe_mem τ x)
      have h0 : ∀ ρ : E →ₐ[F] Fv F v, ρ ((x - algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E) =
          ρ x - algebraMap (𝓞 F) (Fv F v) c := fun ρ =>
        (map_sub ρ (x : E) (algebraMap F E c)).trans (congrArg _ (ρ.commutes (c : F)))
      have h1 := (mem_splitPrime τ _).2 (h0 τ ▸ hc)
      rw [← e, mem_splitPrime, h0] at h1
      rw [splitProj_tmul, splitProj_tmul, ← mul_sub, map_mul, ← sub_sub_sub_cancel_right _ _
        (algebraMap (𝓞 F) (Fv F v) c)]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) (Valuation.map_sub_lt _ hc h1)
    · rw [map_add, map_add, add_sub_add_comm]; exact Valuation.map_add_lt _ hy hz
    · rwa [map_neg, map_neg, neg_sub_neg, Valuation.map_sub_swap]
  simpa using key _ (splitIdem_mem h τ)

theorem splitPrime_injective (h : IsCMExt F E σ) :
    Function.Injective (splitPrime : (E →ₐ[F] Fv F v) → HeightOneSpectrum (𝓞 E)) := fun τ' τ e => by
  rcases eq_or_eq_comp_conj h τ τ' with rfl | rfl
  · rfl
  · exact absurd e (splitPrime_comp_ne h τ)

theorem ncard_primesOver_le_two (h : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) :
    (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2 := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E v.ne_bot
  rwa [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot, h.2.2.1] at h1

theorem primesOver_eq_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    v.asIdeal.primesOver (𝓞 E) = {(splitPrime τ).asIdeal, (splitPrime (τ.comp σ)).asIdeal} := by
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two h v
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (IsDedekindDomain.primesOver_finite _ _)).symm
  · rintro _ (rfl | rfl) <;> exact ⟨HeightOneSpectrum.isPrime _, inferInstance⟩
  · rwa [Set.ncard_pair fun e => splitPrime_comp_ne h τ (HeightOneSpectrum.ext e.symm)]

theorem nonempty_algHom_of_not_isField {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (h2 : Module.finrank K A = 2) (hf : ¬ IsField A) : Nonempty (A →ₐ[K] K) := by
  haveI : Module.Finite K A := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have h0 := Ring.ne_bot_of_isMaximal_of_not_isField hm hf
  have h3 := Submodule.finrank_quotient_add_finrank (m.restrictScalars K)
  have h4 : Module.finrank K (m.restrictScalars K) ≠ 0 := fun e =>
    h0 ((Submodule.restrictScalars_eq_bot_iff K A A).1 (Submodule.finrank_eq_zero.1 e))
  haveI : Nontrivial (A ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  have h5 : 0 < Module.finrank K (A ⧸ m) := Module.finrank_pos
  have h6 : Module.finrank K (A ⧸ m) = 1 := by
    change Module.finrank K (A ⧸ m) + _ = _ at h3
    omega
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m))
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h6)).symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m)⟩

theorem nonempty_split_iff (h : IsCMExt F E σ) :
    Nonempty (E →ₐ[F] Fv F v) ↔ (v.asIdeal.primesOver (𝓞 E)).ncard = 2 := by
  refine ⟨fun ⟨τ⟩ => ?_, fun hv => ?_⟩
  · rw [primesOver_eq_split h τ, Set.ncard_pair fun e => splitPrime_comp_ne h τ (HeightOneSpectrum.ext e.symm)]
  · obtain ⟨φ⟩ := nonempty_algHom_of_not_isField (K := Fv F v) (by rw [Module.finrank_baseChange, h.2.2.1])
      (GlobalTheory.SplitPlace.not_isField_of_split F E h.2.2.1 v hv)
    exact ⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩

theorem existsUnique_splitPrime_eq (h : IsCMExt F E σ) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w ≠ w')
    (hw : w.under (𝓞 F) = v) (hw' : w'.under (𝓞 F) = v) : ∃! τ : E →ₐ[F] Fv F v, splitPrime τ = w := by
  haveI := v.isMaximal
  have hm : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → u.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun u hu => ⟨u.isPrime, ⟨hu ▸ rfl⟩⟩
  have h1 := ncard_primesOver_le_two h v
  obtain ⟨τ⟩ := (nonempty_split_iff h).2 (le_antisymm h1 ((Set.one_lt_ncard (IsDedekindDomain.primesOver_finite _ _)).2
    ⟨_, hm w hw, _, hm w' hw', fun e => hne (HeightOneSpectrum.ext e)⟩))
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => splitPrime_injective h (ha.trans hb.symm)
  have h2 := hm w hw
  rw [primesOver_eq_split h τ] at h2
  rcases h2 with e | e <;> exact ⟨_, HeightOneSpectrum.ext e.symm⟩

end GlobalTheory.AdelicU

end
