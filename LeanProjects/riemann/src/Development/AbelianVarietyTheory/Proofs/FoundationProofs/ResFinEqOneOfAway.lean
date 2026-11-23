import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions GlobalTheory.HeckeGal
open GlobalTheory.AntiRamConj GlobalTheory.Mem.Chr

namespace GlobalTheory.ToricDistribution

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def liftOpen {B : Type} [CommGroup B] (r : Formalism.ConjugateSelfDual.G E Ω →* B) (hr : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) : Gab E Ω →* B :=
  QuotientGroup.lift _ r fun _ hσ =>
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker r) (r.ker.isClosed_of_isOpen hr) hσ

omit [NumberField E] in
theorem liftOpen_toAb {B : Type} [CommGroup B] (r : Formalism.ConjugateSelfDual.G E Ω →* B) (hr : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G E Ω)))
    (σ : Formalism.ConjugateSelfDual.G E Ω) : liftOpen r hr (toAb E Ω σ) = r σ := rfl

def Corr (art : Ideles E →* Gab E Ω) (r : Formalism.ConjugateSelfDual.G E Ω →* ℂˣ) (χ : HChar E) : Prop :=
  ∀ (x : Ideles E) (σ : Formalism.ConjugateSelfDual.G E Ω), art x = toAb E Ω σ → χ.1 x = r σ

variable {art : Ideles E →* Gab E Ω} {r : Formalism.ConjugateSelfDual.G E Ω →* ℂˣ} {χ : HChar E}

theorem exists_corr (ha : IsGlobalArtin art) (hr : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) : ∃ χ, Corr art r χ := by
  have hc := continuous_of_isOpen_ker' r hr
  refine ⟨⟨(liftAb r hc).comp art, (continuous_liftAb r hc).comp ha.quot.continuous, fun k => ?_⟩, fun x σ h => ?_⟩
  · have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]
  · show liftAb r hc (art x) = _
    rw [h, liftAb_toAb]

theorem Corr.pow (h : Corr art r χ) {m : ℕ} (hm : ∀ σ, r σ ^ m = 1) (x : Ideles E) : χ.1 x ^ m = 1 := by
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  rw [h x σ hσ.symm, hm]

theorem Corr.unr (ha : IsGlobalArtin art) (h : Corr art r χ) {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (hu : ∀ σ ∈ Ine (F := E) A, r σ = 1) : χ.UnrAt v := fun x hx => by
  obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).mp ⟨x, hx, rfl⟩
  exact (h _ σ e.symm).trans (hu σ hσ)

theorem Corr.val (ha : IsGlobalArtin art) (h : Corr art r χ) {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (hu : χ.UnrAt v) {σ : Formalism.ConjugateSelfDual.G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    χ.val v = (r σ)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
  rw [← χ.val_eq hu x hx, ← map_inv]
  exact h _ _ e

end Galois

section FiniteOrder

variable {E : Type} [Field E] [NumberField E] {χ : HChar E} {m : ℕ}

theorem isUnitary_of_pow (hm : m ≠ 0) (h : ∀ x, χ.1 x ^ m = 1) : χ.IsUnitary := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hm

theorem locInf_of_pow [IsTotallyComplex E] (hm : m ≠ 0) (h : ∀ x, χ.1 x ^ m = 1) (w : InfinitePlace E)
    (x : (w.Completion)ˣ) : χ.locInf w x = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (Nat.pos_of_ne_zero hm)
  have hy : e.symm z ^ m = x := e.injective (by rw [map_pow, e.apply_symm_apply, hz])
  have hy0 : e.symm z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm] at hy
    exact x.ne_zero hy.symm
  have e2 : x = Units.mk0 _ hy0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
  rw [e2, map_pow]
  exact h _

theorem inf_of_pow [IsTotallyComplex E] (hm : m ≠ 0) (h : ∀ x, χ.1 x ^ m = 1) (k : Eˣ) : χ.inf k = 1 := by
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => locInf_of_pow hm h w _

theorem normV_eq (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem levelLe_one_of_pow {l n : ℕ} (hl : l.Prime) (h : ∀ x, χ.1 x ^ (l ^ n) = 1) {P : HeightOneSpectrum (𝓞 E)}
    (hP : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal) : χ.LevelLe P 1 := by
  intro x hx hx1
  obtain ⟨a, ha⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  obtain ⟨b, M, hM, hNM⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (show Ideal.absNorm P.asIdeal ≠ 0 from fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)) l hl.ne_one
  have hmem : ((M : ℕ) : 𝓞 E) ∈ P.asIdeal := by
    have h := Ideal.absNorm_mem P.asIdeal
    rw [hNM, Nat.cast_mul, Nat.cast_pow] at h
    exact (P.isPrime.mem_or_mem h).resolve_left fun h' => hP (P.isPrime.mem_of_pow_mem b h')
  have hlt : Valued.v ((M : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (M ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ (l ^ n) = 1 := h _
  have hc : Nat.Coprime (l ^ n) (M ^ a) := Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hM)
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

end FiniteOrder

section Norms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_aboveF {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  simp [aboveF]

theorem prod_absNorm (hu : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∏ P ∈ aboveF (L := E) F v, Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ Module.finrank F E := by
  classical
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hprod := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) (p := v.asIdeal) v.ne_bot
  rw [IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, ← Ideal.absNorm_algebraMap, hprod, map_prod]
  refine Finset.prod_bij (fun P _ => P.asIdeal) (fun P hP => ?_) (fun P _ Q _ h => HeightOneSpectrum.ext h)
    (fun P hP => ?_) (fun P hP => ?_)
  · rw [Set.mem_toFinset]
    obtain rfl := mem_aboveF.1 hP
    exact ⟨P.isPrime, ⟨rfl⟩⟩
  · rw [Set.mem_toFinset] at hP
    obtain ⟨h1, h2⟩ := hP
    exact ⟨⟨P, h1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      mem_aboveF.2 (HeightOneSpectrum.ext h2.over.symm), rfl⟩
  · have := P.isPrime
    have := hu P
    have : (P.asIdeal.under (𝓞 F)).IsMaximal := (P.under (𝓞 F)).isMaximal
    rw [Ideal.ramificationIdx_eq_one_iff.2 (hu P), pow_one]

theorem ordF_up (hu : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal)
    (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ) : ordF P (upF F k) = ordF (P.under (𝓞 F)) k := by
  have := P.isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have : (P.asIdeal.under (𝓞 F)).IsMaximal := (P.under (𝓞 F)).isMaximal
  have h : P.valuation E (algebraMap F E k) = (P.under (𝓞 F)).valuation F k := by
    rw [← HeightOneSpectrum.valuation_liesOver E (P.under (𝓞 F)) P (k : F),
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (P.under (𝓞 F)).ne_bot,
      Ideal.ramificationIdx_eq_one_iff.2 (hu P), pow_one]
  unfold ordF
  rw [← h]
  rfl

open Classical in
theorem aboveF_under (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl c.toRingEquiv v v') : aboveF (L := E) F (v.under (𝓞 F)) = {v, v'} := by
  ext P
  rw [mem_aboveF, under_eq_iff_conjPl c h2 hne v P, Finset.mem_insert, Finset.mem_singleton]
  refine or_congr Iff.rfl ⟨fun h' => (existsUnique_conjPl _ v).unique h' h, ?_⟩
  rintro rfl
  exact h

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.Mem.LocTriv in
theorem ideleMap_local (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    ideleMap F E (Neutral.B1.localIdele F v (atFin v k)) = locF (L := E) F v k := by
  refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun w => ?_))
  · have h : finPartI E (locF (L := E) F v k) = locF (L := E) F v k := by
      rw [locF, map_prod]
      exact Finset.prod_congr rfl fun v _ => Units.ext rfl
    rw [← h]
    exact map_one (infiniteAdeleMap F E)
  · show finiteCompletionMap F E w (ev (w.under (𝓞 F))
      (Neutral.B1.localIdele F v (atFin v k) : AdeleRing (𝓞 F) F)) = ev w _
    rw [locF, Units.coe_prod, map_prod]
    by_cases hw : w.under (𝓞 F) = v
    · rw [Finset.prod_eq_single_of_mem w (mem_aboveF.2 hw) (fun P _ hP => ev_local_ne hP.symm _), ev_local_self]
      subst hw
      rw [ev_local_self]
      exact finiteCompletionMap_coe F E w k
    · rw [ev_local_ne hw, map_one]
      exact (Finset.prod_eq_one fun P hP => ev_local_ne (fun e : w = P => hw (e ▸ mem_aboveF.1 hP)) _).symm

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in

theorem resFin_eq_one_of_away (χ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v ∉ S, ∀ k, χ.resFin v k = 1) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.resFin v k = 1 := by
  have e : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ),
      χ.1 (ideleMap F E (Neutral.B1.localIdele F v (atFin v k))) = χ.resFin v k := fun v k => by
    rw [ideleMap_local, locF, map_prod, HChar.resFin, MonoidHom.finsetProd_apply]
    rfl
  have hc := χ.2.1.comp (continuous_ideleMap F E)
  have key := GlobalTheory.FrobDense.eq_one_of_away (χ.1.comp (ideleMap F E)) hc
    (fun k => (congrArg χ.1 (ideleMap_principalIdele F E k)).trans (χ.2.2 _)) S fun v hv x =>
      (GlobalTheory.Mem.Chr.Determ.denseRange_atFin v).induction_on
        (p := fun x => χ.1.comp (ideleMap F E) (Neutral.B1.localIdele F v x) = 1) x
        (isClosed_eq (hc.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v)) continuous_const)
        fun k => (e v k).trans (h v hv k)
  rw [← e]
  exact DFunLike.congr_fun key _

end Norms

section Anti

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hne : c ≠ 1)
  (hu : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal)

include h2 hne hu

theorem absNorm_split {P P' : HeightOneSpectrum (𝓞 E)} (h : ConjPl c.toRingEquiv P P') (hP : P ≠ P') :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.under (𝓞 F)).asIdeal := by
  classical
  have e := prod_absNorm hu (P.under (𝓞 F))
  rw [aboveF_under c h2 hne h, Finset.prod_pair hP, h2, ← normV_eq P', GlobalTheory.AntiLAdic.normV_conjPl h, normV_eq,
    ← sq] at e
  exact Nat.pow_left_injective two_ne_zero e

theorem absNorm_inert {P : HeightOneSpectrum (𝓞 E)} (h : ConjPl c.toRingEquiv P P) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.under (𝓞 F)).asIdeal ^ 2 := by
  classical
  have e := prod_absNorm hu (P.under (𝓞 F))
  rwa [aboveF_under c h2 hne h, Finset.pair_eq_singleton, Finset.prod_singleton, h2] at e

variable {cc : Ω ≃+* Ω} (hcc : ∀ x : E, cc (algebraMap E Ω x) = algebraMap E Ω (c x)) (hinv : ∀ x, cc (cc x) = x)

include hcc hinv

theorem exists_frob_inert {P : HeightOneSpectrum (𝓞 E)} (h : ConjPl c.toRingEquiv P P) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A P) : ∃ g g' : Formalism.ConjugateSelfDual.G E Ω, (∀ x, g' x = cc (g (cc.symm x))) ∧
      IsFrob (F := E) A (normV P) (g * g') := by
  letI : Algebra F Ω := ((algebraMap E Ω).comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have : IsGalois F E := inferInstance
  obtain ⟨φ, hφA, hφ⟩ := exists_frob_over (F := F) (A := A) (v := P.under (𝓞 F))
    fun x => hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hq : Nat.card (𝓞 F ⧸ (P.under (𝓞 F)).asIdeal) = Ideal.absNorm (P.under (𝓞 F)).asIdeal := normV_eq _
  rw [hq] at hφ
  have hN := absNorm_inert c h2 hne hu h
  have hq1 := GlobalTheory.Mem.WildChar.one_lt_absNorm (P.under (𝓞 F))
  generalize Ideal.absNorm (P.under (𝓞 F)).asIdeal = q at hφ hN hq1
  have hτ : ∀ x : E, φ (algebraMap E Ω x) = algebraMap E Ω (c x) := by
    have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h1 : φ.restrictNormal E = 1
    · exfalso
      haveI := P.isMaximal
      letI := Ideal.Quotient.field P.asIdeal
      haveI : Finite (𝓞 E ⧸ P.asIdeal) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
      letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
      have hd := (FiniteField.forall_pow_eq_one_iff (𝓞 E ⧸ P.asIdeal) (q - 1)).1 fun u => by
        obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 E ⧸ P.asIdeal)
        have h3 := hφ (algebraMap E Ω (x : E)) ((A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A
          (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom)))
        rw [← AlgEquiv.restrictNormal_commutes, h1, AlgEquiv.one_apply, ← map_pow, ← map_sub] at h3
        have h4 := (hA (x - x ^ q)).1 (by simpa using h3)
        rw [← Ideal.Quotient.eq, map_pow, hx] at h4
        have h5 : u ^ q = u := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h4.symm)
        rw [← mul_left_inj u, ← pow_succ, Nat.sub_add_cancel hq1.le, h5, one_mul]
      rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 E ⧸ P.asIdeal) = _ from normV_eq P, hN] at hd
      have := Nat.le_of_dvd (by omega) hd
      have : q < q ^ 2 := by nlinarith
      omega
    · intro x
      rw [← AlgEquiv.restrictNormal_commutes, (hy _ h1).trans (hy c hne).symm]
  have hs : ∀ x, cc.symm x = cc x := fun x => by rw [RingEquiv.symm_apply_eq, hinv]
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x => ⟨c x, by rw [hs, hcc]⟩
  let g : Formalism.ConjugateSelfDual.G E Ω :=
    { cc.trans φ.toRingEquiv with
      commutes' := fun x => by
        show φ (cc (algebraMap E Ω x)) = _
        rw [hcc, hτ, ← hcc, ← hcc, hinv] }
  have hg : ∀ x, (g * GlobalTheory.AntiLAdic.conjHom cc hc g) x = φ (φ x) := fun x => by
    show φ (cc (cc (φ (cc (cc.symm x))))) = _
    rw [hinv, RingEquiv.apply_symm_apply]
  have hd : φ ∈ Dec (F := F) A := hφA
  refine ⟨g, GlobalTheory.AntiLAdic.conjHom cc hc g, fun _ => rfl, ?_, fun x hx => ?_⟩
  · show _ ∈ Dec (F := E) A
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (g * GlobalTheory.AntiLAdic.conjHom cc hc g).surjective x
    have h1 : ((g * GlobalTheory.AntiLAdic.conjHom cc hc g)⁻¹ : Formalism.ConjugateSelfDual.G E Ω) ((g * GlobalTheory.AntiLAdic.conjHom cc hc g) z) = z :=
      (g * GlobalTheory.AntiLAdic.conjHom cc hc g).symm_apply_apply z
    rw [h1, hg, apply_mem_iff_of_mem_Dec hd, apply_mem_iff_of_mem_Dec hd]
  · rw [hg, normV_eq, hN]
    have hx' : A.valuation (φ x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact (apply_mem_iff_of_mem_Dec hd x).2 hx
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx _
    rw [← sub_add_sub_cancel _ (φ x ^ q), sq, pow_mul]
    exact Valuation.map_add_lt _ (hφ _ hx')
      ((GlobalTheory.Mem.WildChar.val_pow_sub_pow_le _ hx' hxq q).trans_lt (hφ x hx))

theorem resFin_of_anti {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {r : Formalism.ConjugateSelfDual.G E Ω →* ℂˣ} {χ : HChar E}
    (h : Corr art r χ) (hr : AntiHom cc r) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.resFin v k = 1 := by
  classical
  have hs : ∀ x, cc.symm x = cc x := fun x => by rw [RingEquiv.symm_apply_eq, hinv]
  have hc : ∀ x : E, ∃ y : E, cc.symm (algebraMap E Ω x) = algebraMap E Ω y := fun x => ⟨c x, by rw [hs, hcc]⟩
  refine resFin_eq_one_of_away χ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset.image (·.under (𝓞 F)))
    (fun v hv k => ?_) v k
  have hun : ∀ P ∈ aboveF (L := E) F v, χ.UnrAt P := fun P hP => by
    by_contra hn
    exact hv (Finset.mem_image.2 ⟨P, by simpa using hn, mem_aboveF.1 hP⟩)
  rw [HChar.resFin_apply, Finset.prod_congr rfl fun P hP => by
    rw [GlobalTheory.HeckeProduct.locK_unr χ (hun P hP), ordF_up hu, mem_aboveF.1 hP], Finset.prod_zpow]
  rcases (aboveF (L := E) F v).eq_empty_or_nonempty with he | ⟨P, hP⟩
  · rw [he, Finset.prod_empty, one_zpow]
  obtain rfl := mem_aboveF.1 hP
  obtain ⟨P', hP'⟩ := (existsUnique_conjPl c.toRingEquiv P).exists
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω P
  rw [aboveF_under c h2 hne hP'] at hun ⊢
  by_cases e : P = P'
  · subst e
    obtain ⟨g, g', hg, hσ⟩ := exists_frob_inert c h2 hne hu hcc hinv hP' hA
    rw [Finset.pair_eq_singleton, Finset.prod_singleton, h.val ha hA (hun P (by simp)) hσ, map_mul, hr g g' hg,
      mul_inv_cancel, inv_one, one_zpow]
  · obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have hA' := GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) hcc hP' hA
    have hσ' := GlobalTheory.AntiLAdic.isFrob_conjHom cc hc hσ
    rw [← GlobalTheory.AntiLAdic.normV_conjPl hP'] at hσ'
    rw [Finset.prod_pair e, h.val ha hA (hun P (by simp)) hσ, h.val ha hA' (hun P' (by simp)) hσ',
      hr σ _ (GlobalTheory.AntiLAdic.conjHom_apply cc hc σ), inv_inv, inv_mul_cancel, one_zpow]

end Anti

end GlobalTheory.ToricDistribution
