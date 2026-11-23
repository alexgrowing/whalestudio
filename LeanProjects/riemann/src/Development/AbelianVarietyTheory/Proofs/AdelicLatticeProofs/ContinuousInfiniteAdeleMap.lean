import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal

noncomputable section

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
open scoped TensorProduct

namespace GlobalTheory.UnitaryHeckeBaseChange

section Iso

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toAdele : AE F E →+* AdeleRing (𝓞 E) E :=
  letI : Algebra F (AdeleRing (𝓞 E) E) :=
    ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨adeleMap F E, fun x => adeleMap_algebraMap F E x⟩ : AF F →ₐ[F] AdeleRing (𝓞 E) E)
    (⟨algebraMap E _, fun _ => rfl⟩ : E →ₐ[F] AdeleRing (𝓞 E) E)).toRingHom

variable {F E}

theorem toAdele_tmul (a : AF F) (x : E) :
    toAdele F E (a ⊗ₜ[F] x) = adeleMap F E a * algebraMap E _ x := rfl

theorem toAdele_incA (x : E) : toAdele F E (incA F E x) = algebraMap E _ x := by
  change toAdele F E ((1 : AF F) ⊗ₜ[F] x) = _
  rw [toAdele_tmul, map_one, one_mul]

theorem toAdele_algebraMap (a : AF F) : toAdele F E (algebraMap (AF F) (AE F E) a) = adeleMap F E a := by
  change toAdele F E (a ⊗ₜ[F] (1 : E)) = _
  rw [toAdele_tmul, map_one, mul_one]

variable (F E)

theorem continuous_toAdele : Continuous (toAdele F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (toAdele F E) ?_
  exact (continuous_adeleMap F E).congr fun a => (toAdele_algebraMap a).symm

theorem continuous_finiteAdeleMap : Continuous (finiteAdeleMap F E) :=
  continuous_snd.comp ((continuous_adeleMap F E).comp (Continuous.prodMk_right (0 : InfiniteAdeleRing F)))

theorem continuous_infiniteAdeleMap : Continuous (infiniteAdeleMap F E) :=
  continuous_fst.comp ((continuous_adeleMap F E).comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 F) F)))

theorem exists_finite : ∃ ι : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E, Function.Bijective ι ∧
    (∀ z, (toAdele F E z).2 = ι (finPart F E z)) ∧
    ∀ y, y ∈ intAE F E ↔ ∀ Q, ι y Q ∈ Q.adicCompletionIntegers E := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let c := Algebra.TensorProduct.comm F (Af F) E
  refine ⟨ι.comp c.toRingEquiv.toRingHom, Function.Bijective.comp (g := ι)
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩ c.bijective,
    fun z => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      change _ = ι (x ⊗ₜ[F] a.2)
      rw [toAdele_tmul, hι, mul_comm]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = _ * GlobalTheory.AdeleBaseChange.locMap F Q _
      rw [GlobalTheory.CharTransport.locMap_eq]
      rfl
  · have : intAE F E ≤ (Formalism.L2.DIV.RInt F E).toAddSubgroup.comap c.toRingEquiv.toRingHom.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, x, rfl⟩
      exact Formalism.UG.P.levelaf_tmul_mem x ha
    exact GlobalTheory.AdeleBaseChange.map_mem_int hι (this hy)
  · have hz := GlobalTheory.AdeleBaseChange.mem_int_of_map hι (y := c y) hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg hz
    have : y = ∑ j, r j ⊗ₜ[F] (g j : E) := by
      apply c.injective
      rw [map_sum]
      exact e
    rw [this]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩

variable {F E}

theorem finPart_mem_intAE_iff (z : AE F E) :
    finPart F E z ∈ intAE F E ↔ ∀ Q, (toAdele F E z).2 Q ∈ Q.adicCompletionIntegers E := by
  obtain ⟨ι, -, h1, h2⟩ := exists_finite F E
  rw [h1, h2]

theorem bijective_toAdele {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Bijective (toAdele F E) := by
  obtain ⟨ι, hb, h1, -⟩ := exists_finite F E
  obtain ⟨j, hjc, -, hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ h
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  have hj1 : ∀ a : Ainf F, j (a ⊗ₜ[F] (1 : E)) = infiniteAdeleMap F E a := by
    have hc : Continuous fun a : Ainf F => j (a • (1 : Ainf F ⊗[F] E)) :=
      hjc.comp (f := fun a : Ainf F => a • (1 : Ainf F ⊗[F] E)) (by fun_prop)
    have := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hc (continuous_infiniteAdeleMap F E)
      (funext fun k => by
        change j (algebraMap F (Ainf F) k • (1 : Ainf F ⊗[F] E)) = infiniteAdeleMap F E (algebraMap F _ k)
        rw [algebraMap_smul, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul, hj,
          ← Algebra.algebraMap_eq_smul_one]
        exact (congrArg Prod.fst (adeleMap_algebraMap F E k)).symm)
    intro a
    rw [← congrFun this a, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : ∀ z, (toAdele F E z).1 = j (s z).1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, s.map_zero]; exact j.map_zero.symm
    | add x y hx hy =>
      rw [RingHom.map_add, s.map_add]
      exact (congrArg₂ (· + ·) hx hy).trans (j.map_add _ _).symm
    | tmul a x =>
      rw [(hs _).1]
      change _ = j (a.1 ⊗ₜ[F] x)
      have : (a.1 ⊗ₜ[F] x : Ainf F ⊗[F] E) = (a.1 ⊗ₜ[F] 1) * (1 ⊗ₜ[F] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, hj, hj1]
      rfl
  have e : ⇑(toAdele F E) = Prod.map j ι ∘ s := funext fun z =>
    Prod.ext (h2 z) ((h1 z).trans (congrArg ι (hs z).2.symm))
  rw [e]
  exact (j.bijective.prodMap hb).comp s.bijective

def adeleEquiv {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : AE F E ≃+* AdeleRing (𝓞 E) E :=
  RingEquiv.ofBijective (toAdele F E) (bijective_toAdele h)

theorem continuous_adeleEquiv_symm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Continuous (adeleEquiv h).symm := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  have hc : Continuous (adeleEquiv h) := continuous_toAdele F E
  have ho : IsOpenMap (adeleEquiv h) :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (adeleEquiv h).toAddEquiv.toAddMonoidHom (adeleEquiv h).surjective hc
  exact ((adeleEquiv h).toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end Iso

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCMExtension_of (h : IsCMExt F E σ) : IsCMExtension F E :=
  ⟨h.1, h.2.1, { finrank_eq_two' := h.2.2.1 }⟩

theorem isCMExt_iff (σ : E →ₐ[F] E) :
    IsCMExt F E σ ↔ ∃ _ : IsCMExtension F E, σ = (conj F E : E →ₐ[F] E) := by
  constructor
  · intro h
    haveI := isCMExtension_of h
    refine ⟨this, AlgHom.ext fun x => ?_⟩
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((h.2.2.2 τ x).trans (embedding_conj F E τ x).symm)
  · rintro ⟨h, rfl⟩
    exact ⟨h.totallyReal, h.totallyComplex, h.quadratic.finrank_eq_two, embedding_conj F E⟩

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, rfl⟩ := (isCMExt_iff σ).1 h
  exact conj_conj F E x

theorem exists_of_fixed (h : IsCMExt F E σ) {x : E} (hx : σ x = x) : ∃ t, algebraMap F E t = x := by
  obtain ⟨h', rfl⟩ := (isCMExt_iff σ).1 h
  haveI := h'.totallyReal
  haveI := h'.totallyComplex
  haveI := h'.quadratic
  haveI := IsCMExtension.isCMField F E
  obtain ⟨t, ht⟩ := (CMExtension.equivMaximalRealSubfield F E).surjective
    ⟨x, (IsCMField.complexConj_eq_self_iff E x).1 hx⟩
  exact ⟨t, (CMExtension.equivMaximalRealSubfield_apply F E t).symm.trans (congrArg Subtype.val ht)⟩

abbrev adeleConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMExtension F E] : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E) E :=
  @adeleMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra

theorem adeleConj_algebraMap [IsCMExtension F E] (x : E) :
    adeleConj F E (algebraMap E _ x) = algebraMap E _ (conj F E x) :=
  @adeleMap_algebraMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra x

theorem adeleConj_adeleMap [IsCMExtension F E] (a : AF F) :
    adeleConj F E (adeleMap F E a) = adeleMap F E a := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : F, adeleConj F E (adeleMap F E (algebraMap F _ k)) = adeleMap F E (algebraMap F _ k) := by
    intro k
    rw [adeleMap_algebraMap, adeleConj_algebraMap, AlgEquiv.commutes]
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((@continuous_infiniteAdeleMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra).comp
        (continuous_infiniteAdeleMap F E)) (continuous_infiniteAdeleMap F E)
      (funext fun k => congrArg Prod.fst (key k))) a.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := F)).equalizer
      ((@continuous_finiteAdeleMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra).comp
        (continuous_finiteAdeleMap F E)) (continuous_finiteAdeleMap F E)
      (funext fun k => congrArg Prod.snd (key k))) a.2

theorem toAdele_cA [IsCMExtension F E] (z : AE F E) :
    toAdele F E (cA (conj F E : E →ₐ[F] E) z) = adeleConj F E (toAdele F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x =>
    change toAdele F E (a ⊗ₜ[F] conj F E x) = _
    rw [toAdele_tmul, toAdele_tmul, RingHom.map_mul, adeleConj_adeleMap, adeleConj_algebraMap]

def cO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom σ.toRingHom

theorem cO_cO (h : IsCMExt F E σ) (x : 𝓞 E) : cO σ (cO σ x) = x :=
  RingOfIntegers.ext (sig_sig h x)

def cP (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  HeightOneSpectrum.comap (cO σ) (fun x => ⟨_, cO_cO h x⟩) P

theorem eq_of_le {P Q : HeightOneSpectrum (𝓞 E)} (h : P.asIdeal ≤ Q.asIdeal) : P = Q :=
  HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)

theorem under_cP (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cP h P).under (𝓞 F) = P.under (𝓞 F) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have : cO σ (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
    RingOfIntegers.ext (σ.commutes (x : F))
  change cO σ (algebraMap (𝓞 F) (𝓞 E) x) ∈ P.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal
  rw [this]

theorem eq_or_eq_cP (h : IsCMExt F E σ) {P Q : HeightOneSpectrum (𝓞 E)}
    (hQ : Q.under (𝓞 F) = P.under (𝓞 F)) : Q = P ∨ Q = cP h P := by
  have hle : (Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (cP h P).asIdeal := by
    intro x hx
    obtain ⟨t, ht⟩ := exists_of_fixed h (x := (x : E) * σ x) (by rw [map_mul, sig_sig h, mul_comm])
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective]
      change IsIntegral ℤ (algebraMap F E t)
      rw [ht]
      exact (x * cO σ x).isIntegral_coe
    have e : algebraMap (𝓞 F) (𝓞 E) ⟨t, hint⟩ = x * cO σ x := RingOfIntegers.ext ht
    have h1 : (⟨t, hint⟩ : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal := by
      change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [hQ] at h1
    change algebraMap (𝓞 F) (𝓞 E) _ ∈ P.asIdeal at h1
    rw [e] at h1
    exact P.isPrime.mem_or_mem h1
  exact (Ideal.subset_union.1 hle).imp eq_of_le eq_of_le

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sig_sig h x)

theorem finPart_cA_mem {z : AE F E} (hz : finPart F E z ∈ intAE F E) : finPart F E (cA σ z) ∈ intAE F E := by
  have e : ∀ z : AE F E, finPart F E (cA σ z) = sigR (Af F) σ (finPart F E z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add x y hx hy => simp only [RingHom.map_add, hx, hy]
    | tmul a x => rfl
  rw [e]
  have : intAE F E ≤ (intAE F E).comap (sigR (Af F) σ).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, cO σ x, rfl⟩
  exact this hz

theorem fst_cA (h : IsCMExt F E σ) {z : AE F E} (hz : (toAdele F E z).1 = 0) : (toAdele F E (cA σ z)).1 = 0 := by
  obtain ⟨_, rfl⟩ := (isCMExt_iff σ).1 h
  rw [toAdele_cA]
  exact (congrArg (@infiniteAdeleMap E E _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra) hz).trans (map_zero _)

end CM

section Idem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsIndicator (S : Set (HeightOneSpectrum (𝓞 E))) (a : AdeleRing (𝓞 E) E) : Prop :=
  a.1 = 0 ∧ (∀ Q ∈ S, a.2 Q = 1) ∧ ∀ Q ∉ S, a.2 Q = 0

theorem IsIndicator.unique {S : Set (HeightOneSpectrum (𝓞 E))} {a b : AdeleRing (𝓞 E) E}
    (ha : IsIndicator S a) (hb : IsIndicator S b) : a = b := by
  refine Prod.ext (ha.1.trans hb.1.symm) (FiniteAdeleRing.ext _ fun Q => ?_)
  by_cases hQ : Q ∈ S
  · rw [ha.2.1 Q hQ, hb.2.1 Q hQ]
  · rw [ha.2.2 Q hQ, hb.2.2 Q hQ]

theorem fst_mul (a b : AdeleRing (𝓞 E) E) : (a * b).1 = a.1 * b.1 := rfl
theorem fst_add (a b : AdeleRing (𝓞 E) E) : (a + b).1 = a.1 + b.1 := rfl
theorem fst_one_sub (a : AdeleRing (𝓞 E) E) : (1 - a).1 = 1 - a.1 := rfl
theorem ev_mul (a b : AdeleRing (𝓞 E) E) (Q) : (a * b).2 Q = a.2 Q * b.2 Q := rfl
theorem ev_add (a b : AdeleRing (𝓞 E) E) (Q) : (a + b).2 Q = a.2 Q + b.2 Q := rfl
theorem ev_one_sub (a : AdeleRing (𝓞 E) E) (Q) : (1 - a).2 Q = 1 - a.2 Q := rfl

theorem IsIndicator.idem {S : Set (HeightOneSpectrum (𝓞 E))} {a : AdeleRing (𝓞 E) E}
    (ha : IsIndicator S a) : a * a = a :=
  IsIndicator.unique ⟨by rw [fst_mul, ha.1, zero_mul], fun Q hQ => by rw [ev_mul, ha.2.1 Q hQ, one_mul],
    fun Q hQ => by rw [ev_mul, ha.2.2 Q hQ, zero_mul]⟩ ha

theorem exists_isIndicator (P : HeightOneSpectrum (𝓞 E)) : ∃ a, IsIndicator {P} a :=
  ⟨(0, _), rfl, fun _ hQ => hQ ▸ GlobalTheory.PlaceIdem.single_same P, fun _ hQ => GlobalTheory.PlaceIdem.single_ne hQ⟩

theorem isPlaceIdem_iff (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) : IsPlaceIdem F v ε ↔ IsIndicator {v} ε :=
  ⟨fun ⟨_, h0, h1, h2⟩ => h0 ▸ ⟨rfl, fun _ hQ => hQ ▸ h1, h2⟩,
    fun h => ⟨ε.2, Prod.ext h.1 rfl, h.2.1 v rfl, h.2.2⟩⟩

theorem place_comp {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε) :
    IsIndicator {Q | Q.under (𝓞 F) = v} (toAdele F E (algebraMap _ _ ε)) := by
  rw [toAdele_algebraMap]
  obtain ⟨h0, h1, h2⟩ := (isPlaceIdem_iff v ε).1 h
  exact ⟨(congrArg (infiniteAdeleMap F E) h0).trans (map_zero _),
    fun Q hQ => (congrArg (finiteCompletionMap F E Q) (h1 _ hQ)).trans (map_one _),
    fun Q hQ => (congrArg (finiteCompletionMap F E Q) (h2 _ hQ)).trans (map_zero _)⟩

def Comparison₂ (F : Type) [Field F] [NumberField F] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (e : AE F E) : Prop :=
  ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)

theorem Comparison₂.conj (h : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (ht : Comparison₂ F P e) :
    Comparison₂ F (cP h P) (cA σ e) := by
  intro x hx
  have e1 : cA σ (e * incA F E ((cO σ x : E)⁻¹)) = cA σ e * incA F E ((x : E)⁻¹) := by
    rw [RingHom.map_mul]
    congr 1
    change incA F E (σ ((σ x)⁻¹)) = _
    rw [map_inv₀ σ, sig_sig h]
  have hx' : cO σ x ≠ 0 := fun h0 => hx (by rw [← cO_cO h x, h0, map_zero])
  refine (ht _ hx').trans ?_
  rw [← e1]
  refine not_congr ⟨finPart_cA_mem, fun h' => ?_⟩
  have := finPart_cA_mem (σ := σ) h'
  rwa [cA_cA h] at this

theorem not_int_iff {e : AE F E} (he : e * e = e) {x : 𝓞 E} (hx : x ≠ 0) :
    finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E ↔ ∃ Q, (toAdele F E e).2 Q ≠ 0 ∧ x ∈ Q.asIdeal := by
  rw [finPart_mem_intAE_iff, not_forall]
  refine exists_congr fun Q => ?_
  rw [RingHom.map_mul, ev_mul, toAdele_incA]
  by_cases h0 : (toAdele F E e).2 Q = 0
  · rw [h0, zero_mul]
    exact iff_of_false (fun h => h (zero_mem _)) (fun h => h.1 rfl)
  · have h1 : (toAdele F E e).2 Q = 1 :=
      mul_left_cancel₀ h0 (by rw [← ev_mul, ← RingHom.map_mul, he, mul_one])
    rw [h1, one_mul]
    exact ((GlobalTheory.PlaceIdem.val_inv_le_one Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm

theorem tie_iff {e : AE F E} (he : e * e = e) (h0 : (toAdele F E e).1 = 0)
    (P : HeightOneSpectrum (𝓞 E)) : Comparison₂ F P e ↔ IsIndicator {P} (toAdele F E e) := by
  constructor
  · intro h
    have h1 : ∀ Q, (toAdele F E e).2 Q ≠ 0 → Q = P := fun Q hQ => eq_of_le fun x hx => by
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      · exact (h x hx0).2 ((not_int_iff he hx0).2 ⟨Q, hQ, hx⟩)
    refine ⟨h0, ?_, fun Q hQ => by_contra fun h2 => hQ (h1 Q h2)⟩
    rintro P rfl
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (not_int_iff he hx0).1 ((h x hx0).1 hx)
    rw [h1 Q hQ] at hQ
    exact mul_left_cancel₀ hQ (by rw [← ev_mul, ← RingHom.map_mul, he, mul_one])
  · intro h x hx
    rw [not_int_iff he hx]
    refine ⟨fun hP => ⟨P, by rw [h.2.1 P rfl]; exact one_ne_zero, hP⟩, ?_⟩
    rintro ⟨Q, h1, h2⟩
    have : Q = P := by_contra fun h3 => h1 (h.2.2 Q h3)
    exact this ▸ h2

variable (h : IsCMExt F E σ)
include h

theorem idem_of {S : Set (HeightOneSpectrum (𝓞 E))} {e : AE F E} (he : IsIndicator S (toAdele F E e)) :
    e * e = e :=
  (bijective_toAdele h).1 (by rw [RingHom.map_mul, he.idem])

theorem delta_conj {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (hd : IsIndicator {P} (toAdele F E e)) :
    IsIndicator {cP h P} (toAdele F E (cA σ e)) := by
  have he := idem_of h hd
  exact (tie_iff (by rw [← RingHom.map_mul, he]) (fst_cA h hd.1) _).1 (((tie_iff he hd.1 P).2 hd).conj h)

theorem of_isPrimeIdem {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (hp : IsPrimeIdem σ P e f) :
    IsIndicator {P} (toAdele F E e) ∧ IsIndicator {Q | Q.under (𝓞 F) = P.under (𝓞 F)} (toAdele F E f) := by
  rcases hp with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have hc := place_comp (E := E) hε
    have hd : IsIndicator {P} (toAdele F E e) := by
      refine (tie_iff h1 ?_ P).1 ht
      have : e = (e + cA σ e) * e := by linear_combination -h1 - h2
      rw [this, h3, RingHom.map_mul, fst_mul, hc.1, zero_mul]
    have h4 : (toAdele F E (cA σ e)).2 P = 0 := by
      have := ev_mul (toAdele F E e) (toAdele F E (cA σ e)) P
      rw [← RingHom.map_mul, h2, RingHom.map_zero, hd.2.1 P rfl, one_mul] at this
      exact this.symm
    have h5 : P.under (𝓞 F) = v := by
      by_contra hv
      have := hc.2.2 P hv
      rw [← h3, RingHom.map_add, ev_add, h4, hd.2.1 P rfl, add_zero] at this
      exact one_ne_zero this
    rw [h3, h5]
    exact ⟨hd, hc⟩
  · have hc := place_comp (E := E) hε
    have hd := (tie_iff (idem_of h hc) hc.1 P).1 ht
    have h5 : P.under (𝓞 F) = v := by
      by_contra hv
      exact one_ne_zero ((hd.2.1 P rfl).symm.trans (hc.2.2 P hv))
    rw [h5]
    exact ⟨hd, hc⟩

theorem exists_isPrimeIdem (P : HeightOneSpectrum (𝓞 E)) : ∃ e f, IsPrimeIdem σ P e f := by
  obtain ⟨a, he⟩ := exists_isIndicator P
  obtain ⟨e, rfl⟩ := (bijective_toAdele h).2 a
  obtain ⟨ε, hε⟩ := exists_isIndicator (P.under (𝓞 F))
  rw [← isPlaceIdem_iff] at hε
  have hc := place_comp (E := E) hε
  have hi := idem_of h he
  have ht := (tie_iff hi he.1 P).2 he
  by_cases hP : cP h P = P
  · refine ⟨e, e, Or.inr ⟨rfl, ⟨_, ε, hε, (bijective_toAdele h).1 (he.unique
      ⟨hc.1, fun Q hQ => hc.2.1 Q (congrArg _ hQ), fun Q hQ => hc.2.2 Q fun h' => ?_⟩)⟩, ht⟩⟩
    exact (eq_or_eq_cP h h').elim hQ fun h'' => hQ (h''.trans hP)
  · have he' := delta_conj h he
    refine ⟨e, _, Or.inl ⟨⟨⟨hi, (bijective_toAdele h).1 ?_, _, ε, hε, (bijective_toAdele h).1 ?_⟩, ht⟩, rfl⟩⟩
    · rw [RingHom.map_mul, RingHom.map_zero]
      refine IsIndicator.unique (S := ∅) ⟨by rw [fst_mul, he.1, zero_mul], fun _ hQ => hQ.elim, fun Q _ => ?_⟩
        ⟨rfl, fun _ hQ => hQ.elim, fun _ _ => rfl⟩
      rw [ev_mul]
      by_cases hQ : Q = P
      · subst hQ
        rw [he'.2.2 Q (Ne.symm hP), mul_zero]
      · rw [he.2.2 Q hQ, zero_mul]
    · rw [RingHom.map_add]
      refine IsIndicator.unique ⟨by rw [fst_add, he.1, he'.1, add_zero], fun Q hQ => ?_, fun Q hQ => ?_⟩ hc
      · rw [ev_add]
        rcases eq_or_eq_cP h hQ with rfl | rfl
        · rw [he.2.1 Q rfl, he'.2.2 Q (Ne.symm hP), add_zero]
        · rw [he.2.2 _ hP, he'.2.1 _ rfl, zero_add]
      · rw [ev_add, he.2.2 Q fun h' => hQ (congrArg _ h'),
          he'.2.2 Q fun h' => hQ ((congrArg _ h').trans (under_cP h P)), add_zero]

end Idem

section Chars

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F E) in

def toIdele : (AE F E)ˣ →* Idele E := Units.map (toAdele F E).toMonoidHom

theorem coe_toIdele (x : (AE F E)ˣ) : (toIdele F E x : AdeleRing (𝓞 E) E) = toAdele F E x := rfl

theorem toIdele_principal (x : Eˣ) :
    toIdele F E (Units.map (incA F E).toMonoidHom x) = principalIdele E x := Units.ext (toAdele_incA (x : E))

def ideleEquiv (h : IsCMExt F E σ) : (AE F E)ˣ ≃ₜ* Idele E :=
  { Units.mapEquiv (adeleEquiv h).toMulEquiv with
    continuous_toFun := Continuous.units_map (toAdele F E).toMonoidHom (continuous_toAdele F E)
    continuous_invFun :=
      Continuous.units_map (adeleEquiv h).symm.toRingHom.toMonoidHom (continuous_adeleEquiv_symm h) }

theorem ideleEquiv_apply (h : IsCMExt F E σ) (x : (AE F E)ˣ) : ideleEquiv h x = toIdele F E x := rfl

variable (F) in

def pull (χ : UnitaryHeckeChar E) : (AE F E)ˣ →* Circle := χ.toHom.comp (toIdele F E)

theorem isHeckeChar_pull (χ : UnitaryHeckeChar E) : IsHeckeChar F E (pull F χ) :=
  ⟨χ.continuous_toHom.comp (Continuous.units_map (toAdele F E).toMonoidHom (continuous_toAdele F E)),
    fun x => (congrArg χ.toHom (toIdele_principal x)).trans (χ.map_principal x)⟩

def heckeEquiv (h : IsCMExt F E σ) :
    UnitaryHeckeChar E ≃ {χ : (AE F E)ˣ →* Circle // IsHeckeChar F E χ} where
  toFun χ := ⟨pull F χ, isHeckeChar_pull χ⟩
  invFun χ := ⟨χ.1.comp (ideleEquiv h).symm.toMulEquiv.toMonoidHom, χ.2.1.comp (ideleEquiv h).symm.continuous,
    fun x => by
      rw [← toIdele_principal (F := F), ← χ.2.2 x]
      exact congrArg χ.1 ((ideleEquiv h).symm_apply_apply _)⟩
  left_inv χ := UnitaryHeckeChar.ext (MonoidHom.ext fun x => congrArg χ.toHom ((ideleEquiv h).apply_symm_apply x))
  right_inv χ := Subtype.ext (MonoidHom.ext fun x => congrArg χ.1 ((ideleEquiv h).symm_apply_apply x))

theorem isHeckeChar_iff (h : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) :
    IsHeckeChar F E χ ↔ ∃! χ' : UnitaryHeckeChar E, pull F χ' = χ := by
  refine ⟨fun hχ => ?_, fun ⟨χ', e, _⟩ => e ▸ isHeckeChar_pull χ'⟩
  have := (heckeEquiv h).bijective.existsUnique ⟨χ, hχ⟩
  simp only [Subtype.ext_iff] at this
  exact this

theorem pull_eq_one_iff (h : IsCMExt F E σ) (χ : UnitaryHeckeChar E) :
    pull F χ = 1 ↔ χ = UnitaryHeckeChar.trivial E :=
  ⟨fun e => (heckeEquiv h).injective (Subtype.ext e), fun e => e ▸ rfl⟩

theorem localIdele_same (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    (localIdele P u).val.2 P = u := by
  classical
  exact Pi.mulSingle_eq_same P _

theorem localIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ≠ P) (u : (P.adicCompletion E)ˣ) :
    (localIdele P u).val.2 Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne hQ _

theorem mix_eq_localIdele {P : HeightOneSpectrum (𝓞 E)} {a : AdeleRing (𝓞 E) E} (ha : IsIndicator {P} a)
    (y : AdeleRing (𝓞 E) E) (u : (P.adicCompletion E)ˣ) (hu : y.2 P = u) :
    a * y + (1 - a) = (localIdele P u).val := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · rw [fst_add, fst_mul, fst_one_sub, ha.1, zero_mul, zero_add, sub_zero]
    rfl
  · rw [ev_add, ev_mul, ev_one_sub]
    by_cases hQ : Q = P
    · subst hQ
      rw [ha.2.1 Q rfl, localIdele_same, hu, one_mul, sub_self, add_zero]
    · rw [ha.2.2 Q hQ, localIdele_ne hQ, zero_mul, zero_add, sub_zero]

theorem toAdele_mix (e y : AE F E) :
    toAdele F E (e * y + (1 - e)) = toAdele F E e * toAdele F E y + (1 - toAdele F E e) := by
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]

theorem valued_eq_iff (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) r) = WithZero.exp (-1 : ℤ) ↔
      r ∈ P.asIdeal ∧ r ∉ P.asIdeal ^ 2 := by
  rw [Formalism.UG.P.levelaf_valued_algebraMap, show P.valuation E (r : E) = P.intValuation r from
    P.valuation_of_algebraMap r, ← P.intValuation_le_pow_iff_mem r 2]
  have h1 := P.intValuation_le_pow_iff_mem r 1
  rw [pow_one] at h1
  rw [← h1]
  by_cases h0 : P.intValuation r = 0
  · rw [h0]
    exact iff_of_false WithZero.exp_ne_zero.symm fun h => h.2 zero_le'
  · rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.exp_le_exp, WithZero.exp_inj]
    omega

variable (h : IsCMExt F E σ)
include h

theorem isUnifIdele_iff (P : HeightOneSpectrum (𝓞 E)) (x : (AE F E)ˣ) : IsUnifIdele σ P x ↔
    ∃ ϖ : (P.adicCompletion E)ˣ, IsUniformiser P ϖ ∧
      (∃ r : 𝓞 E, algebraMap E (P.adicCompletion E) r = ϖ) ∧ toIdele F E x = localIdele P ϖ := by
  constructor
  · rintro ⟨e, f, r, hp, h1, h2, hx⟩
    have hv := (valued_eq_iff P r).2 ⟨h1, h2⟩
    have h0 : algebraMap E (P.adicCompletion E) r ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    refine ⟨Units.mk0 _ h0, hv, ⟨r, rfl⟩, Units.ext ?_⟩
    rw [coe_toIdele, hx, toAdele_mix, toAdele_incA]
    exact mix_eq_localIdele (of_isPrimeIdem h hp).1 _ _ rfl
  · rintro ⟨ϖ, hϖ, ⟨r, hr⟩, hx⟩
    obtain ⟨e, f, hp⟩ := exists_isPrimeIdem h P
    have hv := (valued_eq_iff P r).1 (hr ▸ hϖ)
    refine ⟨e, f, r, hp, hv.1, hv.2, (bijective_toAdele h).1 ?_⟩
    rw [← coe_toIdele, hx, toAdele_mix, toAdele_incA]
    exact (mix_eq_localIdele (of_isPrimeIdem h hp).1 _ _ hr).symm

theorem exists_isUnifIdele (P : HeightOneSpectrum (𝓞 E)) : ∃ x, IsUnifIdele σ P x := by
  obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
  have hv : Valued.v (algebraMap E (P.adicCompletion E) r) = WithZero.exp (-1 : ℤ) := by
    rw [Formalism.UG.P.levelaf_valued_algebraMap, ← hr]
    exact P.valuation_of_algebraMap r
  have h0 : algebraMap E (P.adicCompletion E) r ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨x, hx⟩ := (ideleEquiv h).surjective (localIdele P (Units.mk0 _ h0))
  rw [ideleEquiv_apply] at hx
  exact ⟨x, (isUnifIdele_iff h P x).2 ⟨Units.mk0 _ h0, hv, ⟨r, rfl⟩, hx⟩⟩

theorem isUnramAt_iff (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    IsUnramAt σ (pull F χ) P ↔ χ.IsUnramifiedAt P := by
  constructor
  · rintro ⟨e, f, hp, hχ⟩ u hu
    obtain ⟨x, hx⟩ := (ideleEquiv h).surjective (localIdele P u)
    rw [ideleEquiv_apply] at hx
    have key : ∀ (x : (AE F E)ˣ) (u : (P.adicCompletion E)ˣ), toIdele F E x = localIdele P u →
        Valued.v (u : P.adicCompletion E) = 1 → finPart F E (x : AE F E) ∈ intAE F E := by
      intro x u hx hu
      rw [finPart_mem_intAE_iff, ← coe_toIdele, hx]
      intro Q
      by_cases hQ : Q = P
      · subst hQ
        rw [localIdele_same]
        exact hu.le
      · rw [localIdele_ne hQ]
        exact one_mem _
    have := hχ x ((bijective_toAdele h).1 (by
        rw [toAdele_mix, ← coe_toIdele, hx]
        exact (mix_eq_localIdele (of_isPrimeIdem h hp).1 _ _ (localIdele_same P u)).symm))
      (key x u hx hu) (key x⁻¹ u⁻¹ (by rw [map_inv, map_inv, hx])
        (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]))
    change χ.toHom (localIdele P u) = 1
    rw [← hx]
    exact this
  · intro hχ
    obtain ⟨e, f, hp⟩ := exists_isPrimeIdem h P
    refine ⟨e, f, hp, fun x hx h1 h2 => ?_⟩
    rw [finPart_mem_intAE_iff] at h1 h2
    have e1 : (toAdele F E x).2 P * (toAdele F E (x⁻¹ : (AE F E)ˣ)).2 P = 1 := by
      rw [← ev_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
      rfl
    have e2 := congrArg Valued.v e1
    rw [map_mul, map_one] at e2
    have e3 : toIdele F E x = localIdele P (Units.mkOfMulEqOne _ _ e1) := Units.ext (by
      rw [coe_toIdele]
      conv_lhs => rw [hx, toAdele_mix]
      exact mix_eq_localIdele (of_isPrimeIdem h hp).1 _ _ rfl)
    change χ.toHom (toIdele F E x) = 1
    rw [e3]
    exact hχ _ (eq_one_of_one_le_mul_left (h1 P) (h2 P) e2.ge)

theorem chiAt_eq (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    chiAt σ (pull F χ) P = χ.valueAt P := by
  by_cases hχ : χ.IsUnramifiedAt P
  · have hc : IsUnramAt σ (pull F χ) P ∧ ∃ x, IsUnifIdele σ P x :=
      ⟨(isUnramAt_iff h χ P).2 hχ, exists_isUnifIdele h P⟩
    obtain ⟨ϖ, hϖ, -, e⟩ := (isUnifIdele_iff h P _).1 hc.2.choose_spec
    rw [chiAt, dif_pos hc, χ.valueAt_eq hχ hϖ]
    exact congrArg (fun y => ((χ.toHom y : Circle) : ℂ)) e
  · rw [chiAt, dif_neg fun hc => hχ ((isUnramAt_iff h χ P).1 hc.1), χ.valueAt_of_ramified hχ]

theorem lfac_eq (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    lfac σ (pull F χ) P s = χ.eulerFactor P s := by
  rw [lfac, chiAt_eq h]
  rfl

end Chars

end GlobalTheory.UnitaryHeckeBaseChange
