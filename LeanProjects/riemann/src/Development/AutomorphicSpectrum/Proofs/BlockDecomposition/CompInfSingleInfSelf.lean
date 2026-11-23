import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.NullFr.FieldDec

open scoped TensorProduct
open NumberField IsDedekindDomain

section Abstract

theorem exists_isFieldDec_one (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R] :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → R), IsFieldDec (1 : R) g := by
  classical
  let φ := IsArtinianRing.equivPi R
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hmax : ∀ m : MaximalSpectrum R, m.asIdeal.IsMaximal := fun m => m.isMaximal
  have hnt : ∀ m : MaximalSpectrum R, (1 : R ⧸ m.asIdeal) ≠ 0 := fun m => by
    have := hmax m
    exact one_ne_zero
  have hsing : ∀ (m : MaximalSpectrum R) (x : R), φ.symm (Pi.single m 1) * x = φ.symm (Pi.single m (φ x m)) := by
    intro m x
    apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext n
    by_cases h : n = m
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  refine ⟨MaximalSpectrum R, inferInstance, fun m => φ.symm (Pi.single m 1), ?_, ?_, ?_⟩
  · intro m
    refine ⟨?_, ?_, ?_⟩
    · rw [hsing, AlgEquiv.apply_symm_apply, Pi.single_eq_same]
    · intro h
      have h2 := congrFun ((map_eq_zero_iff φ.symm φ.symm.injective).1 h) m
      rw [Pi.single_eq_same] at h2
      exact hnt m h2
    · intro x hx
      have hx0 : φ x m ≠ 0 := fun h => hx (by rw [hsing, h, Pi.single_zero, map_zero])
      have := hmax m
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hx0
      refine ⟨φ.symm (Pi.single m b), ?_⟩
      rw [hsing, ← map_mul, ← Pi.single_mul, hb]
  · intro m n hmn
    rw [hsing, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne hmn, Pi.single_zero, map_zero]
  · rw [← map_sum, Finset.univ_sum_single]
    exact map_one φ.symm

theorem isFieldDec_sigma {A : Type} [CommRing A] {P : Type} [Fintype P] {u : P → A}
    (horth : ∀ p q, p ≠ q → u p * u q = 0) {ι : P → Type} [∀ p, Fintype (ι p)] {f : ∀ p, ι p → A}
    (hf : ∀ p, IsFieldDec (u p) (f p)) :
    IsFieldDec (∑ p, u p) (fun x : (Σ p, ι p) => f x.1 x.2) := by
  classical
  have hu : ∀ p i, f p i * u p = f p i := fun p i => by
    rw [← (hf p).sum, Finset.mul_sum, Finset.sum_eq_single i]
    · exact (hf p).field i |>.idem
    · exact fun j _ hj => (hf p).orth i j hj.symm
    · exact fun h => absurd (Finset.mem_univ i) h
  refine ⟨fun x => (hf x.1).field x.2, ?_, ?_⟩
  · rintro ⟨p, i⟩ ⟨q, j⟩ h
    by_cases hpq : p = q
    · subst hpq
      exact (hf p).orth i j fun e => h (by rw [e])
    · show f p i * f q j = 0
      rw [← hu p i, ← hu q j]
      calc f p i * u p * (f q j * u q) = f p i * f q j * (u p * u q) := by ring
        _ = 0 := by rw [horth p q hpq, mul_zero]
  · rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun p _ => (hf p).sum

end Abstract

section Local

variable {A k R : Type} [CommRing A] [CommRing R] (s : R →ₙ+* A) (c : A →+* R)

theorem isFieldDec_section (hcs : ∀ y, c (s y) = y) (hmul : ∀ y z, s y * z = s (y * c z)) {ι : Type} [Fintype ι]
    {g : ι → R} (hg : IsFieldDec (1 : R) g) : IsFieldDec (s 1) (fun i => s (g i)) := by
  have hss : ∀ y y', s y * s y' = s (y * y') := fun y y' => by rw [hmul, hcs]
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hss, (hg.field i).idem]
  · intro h
    exact (hg.field i).ne (by rw [← hcs (g i), h, map_zero])
  · intro x hx
    have hx0 : g i * c x ≠ 0 := fun h => hx (by rw [hmul, h, map_zero])
    obtain ⟨y, hy⟩ := (hg.field i).inv (c x) hx0
    refine ⟨s y, ?_⟩
    rw [hmul, hss, hy]
  · intro i j hij
    rw [hss, hg.orth i j hij, map_zero]
  · rw [← map_sum, hg.sum]

theorem nonDiscreteAt_section [TopologicalSpace A] [Field k] [TopologicalSpace k] [(𝓝[≠] (0 : k)).NeBot] [Algebra k R]
    [TopologicalSpace R] [ContinuousSMul k R] (hs : Continuous s) (hcs : ∀ y, c (s y) = y)
    (hmul : ∀ y z, s y * z = s (y * c z)) {g : R} (hg : g * g = g) (h0 : g ≠ 0) : NonDiscreteAt (s g) := by
  intro V hV
  have h1 : Continuous fun a : k => s (a • g) := hs.comp (continuous_id.smul continuous_const)
  have h2 : Tendsto (fun a : k => s (a • g)) (𝓝[≠] 0) (𝓝 0) := by
    have := (h1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  obtain ⟨a, haV, ha⟩ := ((h2.eventually hV).and self_mem_nhdsWithin).exists
  refine ⟨s (a • g), haV, fun h => ?_, ?_⟩
  · have h3 : a • g = 0 := by rw [← hcs (a • g), h, map_zero]
    exact (smul_ne_zero ha h0) h3
  · rw [hmul, hcs, mul_smul_comm, hg]

theorem exists_dec_section [TopologicalSpace A] [Field k] [TopologicalSpace k] [(𝓝[≠] (0 : k)).NeBot] [Algebra k R]
    [TopologicalSpace R] [ContinuousSMul k R] [IsArtinianRing R] [IsReduced R] (hs : Continuous s)
    (hcs : ∀ y, c (s y) = y) (hmul : ∀ y z, s y * z = s (y * c z)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → A), IsFieldDec (s 1) f ∧ ∀ j, NonDiscreteAt (f j) := by
  obtain ⟨ι, _, g, hg⟩ := exists_isFieldDec_one R
  exact ⟨ι, inferInstance, fun i => s (g i), isFieldDec_section s c hcs hmul hg, fun j =>
    nonDiscreteAt_section (k := k) s c hs hcs hmul (hg.field j).idem (hg.field j).ne⟩

end Local

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in

def infJ (w : InfinitePlace F) : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem infJ_mul (w : InfinitePlace F) (a b : w.Completion) : infJ w (a * b) = infJ w a * infJ w b := by
  classical
  refine Prod.ext ?_ (mul_zero _).symm
  exact Pi.single_mul w a b

open Classical in
theorem evInf_infJ_self (w : InfinitePlace F) (a : w.Completion) : evInf F w (infJ w a) = a :=
  Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w a

open Classical in
theorem evInf_infJ_ne {u w : InfinitePlace F} (h : u ≠ w) (a : w.Completion) : evInf F u (infJ w a) = 0 :=
  Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h a

theorem evFin_infJ (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (a : w.Completion) :
    evFin F v (infJ w a) = 0 := rfl

theorem continuous_infJ (w : InfinitePlace F) : Continuous (infJ w) := by
  classical
  exact (continuous_single (A := fun u : InfinitePlace F => u.Completion) w).prodMk continuous_const

variable (E) in

def singleInf (w : InfinitePlace F) : w.Completion ⊗[F] E →ₙ+* AF F ⊗[F] E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (infJ w) (infJ_mul w)

theorem compInf_singleInf_self (w : InfinitePlace F) (y : w.Completion ⊗[F] E) :
    compInf F E w (singleInf E w y) = y :=
  GlobalTheory.AutFunCompare.map_tensNU_self (evInf F w) _ _ (evInf_infJ_self w) y

theorem compInf_singleInf_ne {u w : InfinitePlace F} (h : u ≠ w) (y : w.Completion ⊗[F] E) :
    compInf F E u (singleInf E w y) = 0 :=
  GlobalTheory.AutFunCompare.map_tensNU_zero (evInf F u) _ _ (evInf_infJ_ne h) y

theorem compFin_singleInf (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (y : w.Completion ⊗[F] E) :
    compFin F E v (singleInf E w y) = 0 :=
  GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F v) _ _ (evFin_infJ v w) y

theorem singleInf_mul (w : InfinitePlace F) (y : w.Completion ⊗[F] E) (z : AF F ⊗[F] E) :
    singleInf E w y * z = singleInf E w (y * compInf F E w z) :=
  GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by
    by_cases e : u = w
    · subst e; simp [compInf_singleInf_self]
    · simp [compInf_singleInf_ne e]) fun v => by simp [compFin_singleInf]

theorem singleTens_continuous [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (GlobalTheory.AdelicU.Supp.singleTens E v) :=
  GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))

theorem singleInf_continuous [FiniteDimensional F E] (w : InfinitePlace F) : Continuous (singleInf E w) :=
  GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (continuous_infJ w)

theorem neBot_fin (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField _ _
  exact NormedField.nhdsNE_neBot (0 : Fv F v)

theorem neBot_inf (w : InfinitePlace F) : (𝓝[≠] (0 : w.Completion)).NeBot := by
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_ofNat]
        simp⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)

variable [NumberField E]

theorem finite_of_numberField : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

theorem artinian_tens (k : Type) [Field k] [Algebra F k] : IsArtinianRing (k ⊗[F] E) := by
  have := finite_of_numberField (F := F) (E := E)
  exact IsArtinianRing.of_finite k (k ⊗[F] E)

theorem reduced_tens (k : Type) [Field k] [Algebra F k] : IsReduced (k ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[F] E)

theorem exists_dec_fin (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → AF F ⊗[F] E),
      IsFieldDec (GlobalTheory.AdelicU.Supp.singleTens E v 1) f ∧ ∀ j, NonDiscreteAt (f j) := by
  have := neBot_fin (F := F) v
  have := finite_of_numberField (F := F) (E := E)
  have := artinian_tens (F := F) (E := E) (Fv F v)
  have := reduced_tens (F := F) (E := E) (Fv F v)
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  exact exists_dec_section (k := Fv F v) (GlobalTheory.AdelicU.Supp.singleTens E v) (compFin F E v) (singleTens_continuous v)
    (GlobalTheory.AdelicU.Supp.compFin_singleTens_self v) (GlobalTheory.AdelicU.Supp.singleTens_mul v)

theorem exists_dec_inf (w : InfinitePlace F) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → AF F ⊗[F] E),
      IsFieldDec (singleInf E w 1) f ∧ ∀ j, NonDiscreteAt (f j) := by
  have := neBot_inf (F := F) w
  have := finite_of_numberField (F := F) (E := E)
  have := artinian_tens (F := F) (E := E) w.Completion
  have := reduced_tens (F := F) (E := E) w.Completion
  have : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul w.Completion (w.Completion ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  exact exists_dec_section (k := w.Completion) (singleInf E w) (compInf F E w) (singleInf_continuous w)
    (compInf_singleInf_self w) (singleInf_mul w)

theorem exists_dec_adeles (S : Finset (HeightOneSpectrum (𝓞 F))) {e : AF F ⊗[F] E}
    (h1 : ∀ w, compInf F E w e = 1) (h2 : ∀ v ∈ S, compFin F E v e = 1) (h3 : ∀ v ∉ S, compFin F E v e = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → AF F ⊗[F] E), IsFieldDec e f ∧ ∀ j, NonDiscreteAt (f j) := by
  classical
  let u : InfinitePlace F ⊕ S → AF F ⊗[F] E :=
    Sum.elim (fun w => singleInf E w 1) (fun v => GlobalTheory.AdelicU.Supp.singleTens E v.1 1)
  have hsum : ∑ p, u p = e := by
    refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
    · rw [h1, map_sum, Fintype.sum_sum_type, Finset.sum_eq_single w]
      · simp [u, compInf_singleInf_self]
      · intro b _ hb
        simp [u, compInf_singleInf_ne hb.symm]
      · exact fun h => absurd (Finset.mem_univ w) h
    · rw [map_sum, Fintype.sum_sum_type]
      have hi : ∑ x : InfinitePlace F, compFin F E v (u (Sum.inl x)) = 0 :=
        Finset.sum_eq_zero fun x _ => compFin_singleInf v x _
      rw [hi, zero_add]
      by_cases hv : v ∈ S
      · rw [h2 v hv, Finset.sum_eq_single (⟨v, hv⟩ : S)]
        · simp [u]
        · intro b _ hb
          exact GlobalTheory.AdelicU.Supp.compFin_singleTens_ne (fun e => hb (Subtype.ext e.symm)) _
        · exact fun h => absurd (Finset.mem_univ _) h
      · rw [h3 v hv]
        refine Finset.sum_eq_zero fun b _ => ?_
        exact GlobalTheory.AdelicU.Supp.compFin_singleTens_ne (fun (e : v = b.1) => hv (by rw [e]; exact b.2)) _
  have horth : ∀ p q, p ≠ q → u p * u q = 0 := by
    rintro (w | v) (w' | v') h
    · show singleInf E w 1 * singleInf E w' 1 = 0
      rw [singleInf_mul, compInf_singleInf_ne (fun e => h (by rw [e])), mul_zero, map_zero]
    · show singleInf E w 1 * GlobalTheory.AdelicU.Supp.singleTens E v'.1 1 = 0
      rw [singleInf_mul, GlobalTheory.AdelicU.Supp.compInf_singleTens, mul_zero, map_zero]
    · show GlobalTheory.AdelicU.Supp.singleTens E v.1 1 * singleInf E w' 1 = 0
      rw [GlobalTheory.AdelicU.Supp.singleTens_mul, compFin_singleInf, mul_zero, map_zero]
    · show GlobalTheory.AdelicU.Supp.singleTens E v.1 1 * GlobalTheory.AdelicU.Supp.singleTens E v'.1 1 = 0
      rw [GlobalTheory.AdelicU.Supp.singleTens_mul,
        GlobalTheory.AdelicU.Supp.compFin_singleTens_ne (fun e => h (by rw [Subtype.ext e])), mul_zero, map_zero]
  have hex : ∀ p, ∃ (ι : Type) (_ : Fintype ι) (f : ι → AF F ⊗[F] E),
      IsFieldDec (u p) f ∧ ∀ j, NonDiscreteAt (f j) := by
    rintro (w | v)
    · exact exists_dec_inf w
    · exact exists_dec_fin v.1
  choose ι hι f hf hnd using hex
  refine ⟨Σ p, ι p, inferInstance, fun x => f x.1 x.2, ?_, fun x => hnd x.1 x.2⟩
  rw [← hsum]
  exact isFieldDec_sigma horth hf

end Places

theorem exists_isFieldDec (D : D7) (S : Finset (Pl D)) (e : AE D) (h : IsIdem S e) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → AE D), IsFieldDec e f ∧ ∀ j, NonDiscreteAt (f j) :=
  exists_dec_adeles S h.1 (fun v hv => (h.2 v).trans (if_pos hv)) fun v hv => (h.2 v).trans (if_neg hv)

end GlobalTheory.CompanionTheory.NullFr.FieldDec
