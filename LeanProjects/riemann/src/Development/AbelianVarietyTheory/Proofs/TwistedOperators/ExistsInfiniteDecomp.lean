import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.QuadSymbol
open scoped TensorProduct

namespace GlobalTheory.TraceClasses

def IsValue {R : Type} [CommRing R] (d x : R) : Prop := ∃ a b, x = a ^ 2 - d * b ^ 2

theorem norm_pi {A ι : Type} [Field A] [Fintype ι] {B : ι → Type} [∀ i, CommRing (B i)]
    [∀ i, Algebra A (B i)] [∀ i, Module.Finite A (B i)] (x : ∀ i, B i) :
    Algebra.norm A x = ∏ i, Algebra.norm A (x i) := by
  classical
  let b := fun i => Module.finBasis A (B i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), Finset.prod_congr rfl
    fun i _ => Algebra.norm_eq_matrix_det (b i) (x i),
    ← ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']
  congr 1
  ext ⟨i, p⟩ ⟨j, q⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, Pi.single_eq_of_ne h]

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem finite_fibre (v : HeightOneSpectrum (𝓞 F)) :
    {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).subset ?_
  rintro _ ⟨w, rfl, rfl⟩
  exact ⟨w.isPrime, ⟨rfl⟩⟩

theorem exists_finite_decomp :
    ∃ ψ : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 F) = v}),
      v.adicCompletion F ⊗[F] K →+* w.1.adicCompletion K,
      (∀ v w x, ψ v w (1 ⊗ₜ x) = algebraMap K _ x) ∧
      (∀ v, Function.Bijective fun y w => ψ v w y) ∧
      ∀ v w a, a ∈ v.adicCompletionIntegers F → ψ v w (a ⊗ₜ 1) ∈ w.1.adicCompletionIntegers K := by
  classical
  refine ⟨fun v w => GlobalTheory.LFun.toCompl w.2, fun v w x => by simp, fun v => ⟨?_, fun z => ?_⟩,
    fun v w a ha => ?_⟩
  · refine (injective_iff_map_eq_zero (RingHom.pi fun w : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 F) = v} =>
      GlobalTheory.LFun.toCompl w.2)).2 fun y hy => ?_
    have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
      (GlobalTheory.AdelicU.evalV_singleFin_self v) y
    have h2 : GlobalTheory.LFun.finAdEquiv F K (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
      FiniteAdeleRing.ext _ fun u => by
        by_cases e : u.under (𝓞 F) = v
        · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
          exact congrFun hy ⟨u, e⟩
        · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
            (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
          rfl
    rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h2, map_zero]
  · have hf := finite_fibre F K v
    obtain ⟨Y, hY⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
      ⟨fun u => if h : u.under (𝓞 F) = v then z ⟨u, h⟩ else 0, by
        refine hf.subset fun u hu => ?_
        by_contra h
        exact hu (by simp only [Set.mem_ofPred_eq] at h; simp [h])⟩
    refine ⟨_, funext fun w => (GlobalTheory.LFun.finAdEquiv_apply w.2 Y).symm.trans ?_⟩
    rw [hY]
    exact dif_pos w.2
  · simpa using GlobalTheory.LFun.complMap_mem w.2 ha

open scoped NumberField.LiesOver in

theorem exists_infinite_decomp :
    ∃ ψ : ∀ (v : InfinitePlace F) (w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}),
      v.Completion ⊗[F] K →+* w.1.Completion,
      (∀ v w x, ψ v w (1 ⊗ₜ x) = algebraMap K _ x) ∧
      ∀ v, Function.Bijective fun y w => ψ v w y := by
  classical
  have hl : ∀ (v : InfinitePlace F) (w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}),
      w.1.LiesOver v := fun v w => ⟨congrArg Subtype.val w.2⟩
  haveI : ∀ w : InfinitePlace K, IsScalarTower F K w.Completion := fun w =>
    .of_algebraMap_eq fun x => by
      apply InfinitePlace.Completion.ext
      rw [InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion,
        UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def]
      rfl
  let φ : ∀ (v : InfinitePlace F) (w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}),
      v.Completion ⊗[F] K →ₐ[v.Completion] w.1.Completion := fun v w =>
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom F K _) fun _ _ => Commute.all _ _
  have h1 : ∀ v w x, φ v w (1 ⊗ₜ x) = algebraMap K _ x := fun v w x => by simp [φ]
  refine ⟨fun v w => φ v w, h1, fun v => ?_⟩
  let f : v.Completion ⊗[F] K →ₗ[v.Completion]
      ∀ w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}, w.1.Completion :=
    LinearMap.pi fun w => (φ v w).toLinearMap
  have hs : Function.Surjective f := by
    letI : NontriviallyNormedField v.Completion :=
      { (inferInstance : NormedField v.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    have hcl : IsClosed (SetLike.coe (LinearMap.range f)) := Submodule.closed_of_finiteDimensional _
    intro z
    have hc : Continuous fun (y : InfiniteAdeleRing K)
        (w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}) => y w.1 :=
      continuous_pi fun w => continuous_apply w.1
    have key : ∀ y : InfiniteAdeleRing K, (fun w : {w : InfinitePlace K // w.comap (algebraMap F K) = v} => y w.1) ∈ SetLike.coe (LinearMap.range f) := fun y =>
      (InfiniteAdeleRing.denseRange_algebraMap K).induction_on y (hcl.preimage hc)
        fun x => ⟨1 ⊗ₜ x, funext fun w => h1 v w x⟩
    have := key fun u => if h : u.comap (algebraMap F K) = v then z ⟨u, h⟩ else 0
    rwa [show (fun w : {w : InfinitePlace K // w.comap (algebraMap F K) = v} => _) = z from
      funext fun w => dif_pos w.2] at this
  haveI : Module.Finite v.Completion
      (∀ w : {w : InfinitePlace K // w.comap (algebraMap F K) = v}, w.1.Completion) :=
    Module.Finite.of_surjective f hs
  haveI : ∀ w : {w : InfinitePlace K // w.comap (algebraMap F K) = v},
      Module.Finite v.Completion w.1.Completion := fun w =>
    Module.Finite.of_surjective (LinearMap.proj (R := v.Completion)
      (φ := fun w : {w : InfinitePlace K // w.comap (algebraMap F K) = v} => w.1.Completion) w)
      (Function.surjective_eval w)
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) ?_).2 hs, hs⟩
  rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
    ← InfinitePlace.sum_inertiaDeg_eq_finrank F K v]
  refine (Finset.sum_subtype _ (fun w => ?_) _).trans
    (Finset.sum_congr rfl fun w _ => InfinitePlace.inertiaDeg_eq_finrank v w.1)
  rw [Set.mem_toFinset]
  exact ⟨fun h => haveI : w.LiesOver v := h; InfinitePlace.LiesOver.comap_eq w v, fun h => hl v ⟨w, h⟩⟩

section Local

variable {F K}

omit [NumberField F] [NumberField K] in

theorem form_iff {A ι : Type} [CommRing A] [Algebra F A] {B : ι → Type} [∀ i, CommRing (B i)]
    [∀ i, Algebra K (B i)] (ψ : ∀ i, A ⊗[F] K →+* B i) (h1 : ∀ i x, ψ i (1 ⊗ₜ x) = algebraMap K _ x)
    (hb : Function.Bijective fun y i => ψ i y) (d : K) (x : A ⊗[F] K) :
    IsValue (1 ⊗ₜ d) x ↔ ∀ i, IsValue (algebraMap K _ d) (ψ i x) := by
  constructor
  · rintro ⟨a, b, rfl⟩ i
    exact ⟨ψ i a, ψ i b, by simp [h1]⟩
  · intro h
    choose a b h using h
    obtain ⟨a, rfl⟩ := hb.2 a
    obtain ⟨b, rfl⟩ := hb.2 b
    exact ⟨a, b, hb.1 (funext fun i => by simp [h1, h])⟩

theorem eta_norm_eq_prod {E L A ι : Type} [Field E] [Field L] [Algebra F E] [Algebra K L] [Field A]
    [Algebra F A] [Fintype ι] {B : ι → Type} [∀ i, Field (B i)]
    [∀ i, Algebra K (B i)] (ψ : ∀ i, A ⊗[F] K →+* B i) (h1 : ∀ i x, ψ i (1 ⊗ₜ x) = algebraMap K _ x)
    (hb : Function.Bijective fun y i => ψ i y) (hc : BaseChangeAt F E K L A)
    (hm : ∀ a b : Aˣ, eta F E A (a * b) = eta F E A a * eta F E A b) (x : (A ⊗[F] K)ˣ) :
    eta F E A (Units.map (Algebra.norm A : A ⊗[F] K →* A) x) =
      ∏ i, eta K L (B i) (Units.map (ψ i : A ⊗[F] K →* B i) x) := by
  letI : ∀ i, Algebra A (B i) := fun i => ((ψ i).comp (algebraMap A _)).toAlgebra
  letI : ∀ i, Algebra F (B i) := fun i => ((algebraMap K (B i)).comp (algebraMap F K)).toAlgebra
  haveI : ∀ i, IsScalarTower F K (B i) := fun i => .of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, IsScalarTower F A (B i) := fun i => .of_algebraMap_eq fun t => by
    change algebraMap K (B i) (algebraMap F K t) = ψ i (algebraMap A _ (algebraMap F A t))
    rw [← h1, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  let f : A ⊗[F] K →ₐ[A] ∀ i, B i := { RingHom.pi ψ with commutes' := fun _ => rfl }
  let e : A ⊗[F] K ≃ₐ[A] ∀ i, B i := AlgEquiv.ofBijective f hb
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : Module.Finite A (∀ i, B i) := Module.Finite.equiv e.toLinearEquiv
  haveI : ∀ i, Module.Finite A (B i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj (R := A) (φ := B) i) (Function.surjective_eval i)
  let η : Aˣ →* ℤˣ := MonoidHom.mk' (eta F E A) hm
  have h2 : Units.map (Algebra.norm A : A ⊗[F] K →* A) x =
      ∏ i, Units.map (Algebra.norm A : B i →* A) (Units.map (ψ i : A ⊗[F] K →* B i) x) := by
    ext
    rw [Units.coe_prod, Units.coe_map, ← Algebra.norm_eq_of_algEquiv e, norm_pi]
    rfl
  rw [h2]
  exact (map_prod η _ _).trans (Finset.prod_congr rfl fun i _ => (hc (B i) _).symm)

end Local

section Global

variable {F K}

theorem finite_not_form {d : K} (hd : d ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ u : (v.adicCompletion F ⊗[F] K)ˣ,
      ((algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] K)).comp
        (v.adicCompletionIntegers F).subtype).IsIntegralElem u ∧
      ((algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] K)).comp
        (v.adicCompletionIntegers F).subtype).IsIntegralElem (u⁻¹ : (v.adicCompletion F ⊗[F] K)ˣ) ∧
      ¬ IsValue (1 ⊗ₜ d) (u : v.adicCompletion F ⊗[F] K)}.Finite := by
  obtain ⟨ψ, h1, hb, hi⟩ := exists_finite_decomp F K
  refine (((GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).union
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 d hd))).image fun w => w.under (𝓞 F)).subset ?_
  rintro v ⟨u, hu, hu', hn⟩
  by_contra hv
  refine hn ((form_iff (ψ v) (h1 v) (hb v) d u).2 fun w => ?_)
  have hw : ¬ (w.1.valuation K 2 ≠ 1 ∨ w.1.valuation K d ≠ 1) := fun h => hv ⟨w.1, h, w.2⟩
  rw [not_or, not_not, not_not] at hw
  have key : ∀ x : K, Valued.v (algebraMap K (w.1.adicCompletion K) x) = w.1.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w.1 x
  have hint : ∀ z, ((algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] K)).comp
      (v.adicCompletionIntegers F).subtype).IsIntegralElem z → Valued.v (ψ v w z) ≤ 1 := by
    rintro z ⟨p, hp, hz⟩
    let g : v.adicCompletionIntegers F →+* w.1.adicCompletionIntegers K :=
      (((ψ v w).comp (algebraMap _ _)).comp (v.adicCompletionIntegers F).subtype).codRestrict _
        fun a => hi v w a a.2
    have : IsIntegral (w.1.adicCompletionIntegers K) (ψ v w z) := by
      refine ⟨p.map g, hp.map g, ?_⟩
      rw [Polynomial.eval₂_map, ← map_zero (ψ v w), ← hz, Polynomial.hom_eval₂]
      rfl
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := w.1.adicCompletion K)).1 this
    rw [← hy]
    exact y.2
  have h3 : Valued.v (ψ v w u) * Valued.v (ψ v w (u⁻¹ : (v.adicCompletion F ⊗[F] K)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  have h4 : Valued.v (ψ v w u) = 1 :=
    le_antisymm (hint _ hu) (h3 ▸ mul_le_of_le_one_right' (hint _ hu'))
  obtain ⟨x, -, y, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K w.1
    (algebraMap K _ d) (ψ v w u)
    (by rw [← map_ofNat (algebraMap K (w.1.adicCompletion K)) 2]; exact (key _).trans hw.1)
    (by rw [key, hw.2]) h4
  exact ⟨x, y, h⟩

theorem finite_not_integral (t : K) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ ((algebraMap (v.adicCompletion F) (v.adicCompletion F ⊗[F] K)).comp
        (v.adicCompletionIntegers F).subtype).IsIntegralElem (1 ⊗ₜ t)}.Finite := by
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ _ _
  have ht : IsIntegral F t := Algebra.IsIntegral.isIntegral t
  have hfin : ∀ a : F, {v : HeightOneSpectrum (𝓞 F) | ¬ v.valuation F a ≤ 1}.Finite := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 a ha)).subset fun v hv h => hv (le_of_eq h)
  refine ((minpoly F t).support.finite_toSet.biUnion fun n _ => hfin ((minpoly F t).coeff n)).subset ?_
  intro v hv
  by_contra hn
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hn
  have hl : (minpoly F t).map (algebraMap F (v.adicCompletion F)) ∈
      Polynomial.lifts (v.adicCompletionIntegers F).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    refine ⟨⟨_, ?_⟩, rfl⟩
    change Valued.v (algebraMap F (v.adicCompletion F) _) ≤ 1
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le ?_
    by_cases h : n ∈ (minpoly F t).support
    · exact hn n h
    · simp [Polynomial.notMem_support_iff.1 h]
  obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl ((minpoly.monic ht).map _)
  refine hv ⟨q, hm, ?_⟩
  rw [← Polynomial.eval₂_map, hq, ← Polynomial.aeval_def, Polynomial.aeval_map_algebraMap]
  exact (Polynomial.aeval_algHom_apply (Algebra.TensorProduct.includeRight :
    K →ₐ[F] v.adicCompletion F ⊗[F] K) t _).trans (by rw [minpoly.aeval, map_zero])

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
  (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {d : K} (h1 : e 1 * e 1 = algebraMap K L d)

include h0 h1

theorem form_of_local (t : Kˣ)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F),
      IsValue (1 ⊗ₜ d) (1 ⊗ₜ (t : K) : v.adicCompletion F ⊗[F] K))
    (hi : ∀ v : InfinitePlace F, IsValue (1 ⊗ₜ d) (1 ⊗ₜ (t : K) : v.Completion ⊗[F] K)) :
    IsValue d (t : K) := by
  obtain ⟨ψ, g1, gb, -⟩ := exists_finite_decomp F K
  obtain ⟨χ, k1, kb⟩ := exists_infinite_decomp F K
  have := (normTheorem K L t).2 ⟨fun w => (mem_normGroup_iff_form e h0 h1).2 (by
      have := (form_iff (ψ _) (g1 _) (gb _) d _).1 (hf _) ⟨w, rfl⟩
      rwa [g1] at this), fun w => (mem_normGroup_iff_form e h0 h1).2 (by
      have := (form_iff (χ _) (k1 _) (kb _) d _).1 (hi _) ⟨w, rfl⟩
      rwa [k1] at this)⟩
  exact (mem_normGroup_iff_form e h0 h1).1 (toUnits_mem_normGroup K this)

theorem exists_global {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra E L] [Algebra F L]
    [IsScalarTower F K L] [IsScalarTower F E L] [Algebra.IsQuadraticExtension F E]
    (hadj : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F ⊗[F] K)ˣ)
    (y : ∀ v : InfinitePlace F, (v.Completion ⊗[F] K)ˣ)
    (hx : {v | ¬ IsValue (1 ⊗ₜ d) (x v : v.adicCompletion F ⊗[F] K)}.Finite) (δ : Fˣ)
    (hf : ∀ v, Units.map (Algebra.norm (v.adicCompletion F) : _ →* _) (x v) / QuadSymbol.toUnits F _ δ ∈
      normGroup F E (v.adicCompletion F))
    (hi : ∀ v, Units.map (Algebra.norm v.Completion : _ →* _) (y v) / QuadSymbol.toUnits F _ δ ∈
      normGroup F E v.Completion) :
    ∃ t : Kˣ, (∀ v, IsValue (1 ⊗ₜ d) ((x v : v.adicCompletion F ⊗[F] K) * (1 ⊗ₜ (t⁻¹ : K)))) ∧
      ∀ v, IsValue (1 ⊗ₜ d) ((y v : v.Completion ⊗[F] K) * (1 ⊗ₜ (t⁻¹ : K))) := by
  classical
  obtain ⟨ψ, g1, gb, -⟩ := exists_finite_decomp F K
  obtain ⟨χ, k1, kb⟩ := exists_infinite_decomp F K
  obtain ⟨bf, bi⟩ := baseChange F E K L hadj
  obtain ⟨mf, mi⟩ := localCharacters F E
  let X : FinFam K := fun w => Units.map (ψ _ ⟨w, rfl⟩ : _ →* _) (x (w.under (𝓞 F)))
  let Y : InfFam K := fun w => Units.map (χ _ ⟨w, rfl⟩ : _ →* _) (y (w.comap (algebraMap F K)))
  have hT : ((fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F)) ⁻¹' hx.toFinset).Finite :=
    hx.toFinset.finite_toSet.preimage' fun v _ => finite_fibre F K v
  have hX : ∀ w, w.under (𝓞 F) ∉ hx.toFinset → X w ∈ normGroup K L _ := fun w hw =>
    (mem_normGroup_iff_form e h0 h1).2 ((form_iff (ψ _) (g1 _) (gb _) d _).1 (by simpa using hw) ⟨w, rfl⟩)
  have hA : AlmostNorm K L X := hT.subset fun w hw => by
    by_contra h
    exact hw (hX w h)
  have hfib : ∀ v, eta F E _ (finDiag F δ v) =
      ∏ w ∈ (finite_fibre F K v).toFinset, eta K L _ (X w) := fun v => by
    haveI : Fintype {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 F) = v} := (finite_fibre F K v).fintype
    rw [Finset.prod_subtype (p := fun w => w.under (𝓞 F) = v) _ (by simp)]
    refine (eta_eq_of_div_mem (hf v)).symm.trans
      ((eta_norm_eq_prod (ψ v) (g1 v) (gb v) (bf v) (mf v) (x v)).trans ?_)
    refine Finset.prod_congr rfl ?_
    rintro ⟨w, rfl⟩ _
    rfl
  have p1 : ∏ᶠ w, eta K L _ (X w) = ∏ᶠ v, eta F E _ (finDiag F δ v) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := hT.toFinset) _ (fun w hw => by
        by_contra h
        exact hw (eta_eq_one_iff.2 (hX w (by simpa using h)))),
      finprod_eq_prod_of_mulSupport_subset (s := hx.toFinset) _ (fun v hv => by
        by_contra h
        refine hv ((hfib v).trans (Finset.prod_eq_one fun w hw => eta_eq_one_iff.2 (hX w ?_)))
        rwa [(Set.Finite.mem_toFinset _).1 hw]),
      ← Finset.prod_fiberwise_of_maps_to (t := hx.toFinset) (g := fun w => w.under (𝓞 F))
        (fun w hw => hT.mem_toFinset.1 hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hfib]
    refine Finset.prod_congr (Finset.ext fun w => ?_) fun _ _ => rfl
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
  have p2 : ∏ w, eta K L _ (Y w) = ∏ v, eta F E _ (infDiag F δ v) := by
    rw [← Finset.prod_fiberwise (g := fun w : InfinitePlace K => w.comap (algebraMap F K))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_subtype (p := fun w : InfinitePlace K => w.comap (algebraMap F K) = v) _ (by simp)]
    refine Eq.trans ?_ ((eta_norm_eq_prod (χ v) (k1 v) (kb v) (bi v) (mi v) (y v)).symm.trans
      (eta_eq_of_div_mem (hi v)))
    refine Finset.prod_congr rfl ?_
    rintro ⟨w, rfl⟩ _
    rfl
  obtain ⟨t, tf, ti⟩ := exists_everywhereNorm_div_of_etaProd_eq_one K L X Y hA (by
    rw [etaProd, p1, p2]
    exact (productFormula F E δ).2)
  refine ⟨t, fun v => (form_iff (ψ v) (g1 v) (gb v) d _).2 ?_,
    fun v => (form_iff (χ v) (k1 v) (kb v) d _).2 ?_⟩
  · rintro ⟨w, rfl⟩
    have := (mem_normGroup_iff_form e h0 h1).1 (tf w)
    simpa [X, finDiag, QuadSymbol.toUnits, g1, div_eq_mul_inv, IsValue] using this
  · rintro ⟨w, rfl⟩
    have := (mem_normGroup_iff_form e h0 h1).1 (ti w)
    simpa [Y, infDiag, QuadSymbol.toUnits, k1, div_eq_mul_inv, IsValue] using this

end Global

end GlobalTheory.TraceClasses
