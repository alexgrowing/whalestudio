import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit IsUnram)
open Formalism.L2.Host (HChar IsUnitAt IsUnifAt atFin unif unif_spec aboveF upF)
open Neutral.B1 (finiteSingle localIdele)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Idele

variable (F E) in

def infTens : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

variable (F E) in

def finTens : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem tens_ext {x y : AF F ⊗[F] E} (h1 : infTens F E x = infTens F E y) (h2 : finTens F E x = finTens F E y) :
    x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  exact e.injective (Prod.ext ((he x).1.trans (h1.trans (he y).1.symm)) ((he x).2.trans (h2.trans (he y).2.symm)))

theorem infTens_extZero (y : Af F ⊗[F] E) : infTens F E (extZero F E y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => exact TensorProduct.zero_tmul _ _
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem finTens_extZero (y : Af F ⊗[F] E) : finTens F E (extZero F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem coe_locIdele (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    (locIdele F w y : AF F ⊗[F] E) = 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm (Neutral.B1.finiteSingle E w y)) := rfl

theorem infTens_locIdele (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    infTens F E (locIdele F w y) = 1 := by
  rw [coe_locIdele, map_add, map_sub, map_one, infTens_extZero, infTens_extZero, sub_zero, add_zero]

theorem finTens_locIdele (w : HeightOneSpectrum (𝓞 E)) (y : (w.adicCompletion E)ˣ) :
    finAdEquiv F E (finTens F E (locIdele F w y)) = (GlobalTheory.CMVal.single w y : (Af E)ˣ) := by
  rw [coe_locIdele, map_add (finTens F E), map_sub, map_one, finTens_extZero, finTens_extZero, sub_self, zero_add,
    RingEquiv.apply_symm_apply]
  rfl

theorem eq_locIdele {w : HeightOneSpectrum (𝓞 E)} {y : (w.adicCompletion E)ˣ} {x : (AF F ⊗[F] E)ˣ}
    (h1 : infTens F E x = 1) (h2 : finAdEquiv F E (finTens F E x) = (GlobalTheory.CMVal.single w y : (Af E)ˣ)) :
    x = locIdele F w y :=
  Units.ext (tens_ext (h1.trans (infTens_locIdele w y).symm)
    ((finAdEquiv F E).injective (h2.trans (finTens_locIdele w y).symm)))

theorem finSingle_self (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) : Neutral.B1.finiteSingle E w y w = y := by
  classical
  exact Function.update_self (β := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y fun _ => 1

theorem finSingle_ne {w u : HeightOneSpectrum (𝓞 E)} (h : u ≠ w) (y : w.adicCompletion E) :
    Neutral.B1.finiteSingle E w y u = 1 := by
  classical
  exact Function.update_of_ne (β := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) h y fun _ => 1

theorem mem_int_iff (y : Af F ⊗[F] E) :
    y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔
      ∀ P, Valued.v (finAdEquiv F E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv
  have h : ∀ x a, ((toFinAd F E).comp c.symm.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  constructor
  · intro hy
    have : finAdEquiv F E y ∈ Formalism.UG.intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        rw [show finAdEquiv F E (a ⊗ₜ[F] (x : E)) = _ from toFinAd_tmul a (x : E)]
        exact mul_mem (GlobalTheory.AdeleBaseChange.adMap_int ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · intro hy
    have h1 : c y ∈ Formalism.L2.DIV.RInt F E := GlobalTheory.AdeleBaseChange.mem_int_of_map h (by
      change toFinAd F E (c.symm (c y)) ∈ _
      rw [c.symm_apply_apply]
      exact hy)
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg h1
    rw [← c.symm_apply_apply y, e, map_sum]
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, hr i, g i, rfl⟩

theorem continuous_finAdEquiv_symm : Continuous (finAdEquiv F E).symm :=
  GlobalTheory.AdeleBaseChange.continuous_symm_finite F E _ mem_int_iff

theorem continuous_extZero : Continuous (extZero F E) := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine (hc.comp (Continuous.prodMk_right 0)).congr fun y => ?_
  rw [Function.comp_apply, RingEquiv.symm_apply_eq]
  exact Prod.ext ((he _).1.trans (infTens_extZero y)).symm ((he _).2.trans (finTens_extZero y)).symm

theorem continuous_locIdele (w : HeightOneSpectrum (𝓞 E)) : Continuous (locIdele F w) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have h : Continuous fun y : w.adicCompletion E =>
      1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm (Neutral.B1.finiteSingle E w y)) :=
    continuous_const.add (continuous_extZero.comp (continuous_finAdEquiv_symm.comp
      (GlobalTheory.Mem.Chr.Determ.continuous_finSingle w)))
  exact Units.continuous_iff.2 ⟨h.comp Units.continuous_val, h.comp Units.continuous_coe_inv⟩

theorem continuous_locChar {χ : (AF F ⊗[F] E)ˣ →* Circle} (h : Continuous χ) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous fun x => (locChar χ w x : ℂ) := continuous_subtype_val.comp (h.comp (continuous_locIdele w))

theorem finAdEquiv_tmul (a : Af F) (x : E) (w : HeightOneSpectrum (𝓞 E)) :
    finAdEquiv F E (a ⊗ₜ[F] x) w = complMap rfl (a (w.under (𝓞 F))) * algebraMap E _ x := rfl

theorem ideleMap_localIdele (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    ideleMap F E (localIdele F v (atFin v a)) = ∏ w ∈ aboveF (L := E) F v, locIdele F w (atFin w (upF F a)) := by
  refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
  · rw [Units.coe_prod, map_prod, Finset.prod_eq_one fun w _ => infTens_locIdele w _]
    rfl
  · rw [Units.coe_prod, map_prod, map_prod]
    simp only [finTens_locIdele]
    refine Eq.trans ?_ (map_prod (evalV E u) _ _).symm
    change complMap rfl (Neutral.B1.finiteSingle F v (algebraMap F _ (a : F)) (u.under (𝓞 F))) * algebraMap E _ 1 =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.finiteSingle E w (algebraMap E _ (algebraMap F E a)) u
    rw [map_one, mul_one]
    by_cases h : u.under (𝓞 F) = v
    · rw [Finset.prod_eq_single_of_mem u (mem_aboveF.2 h) fun w _ hw => finSingle_ne hw.symm _, finSingle_self]
      subst h
      rw [finSingle_self, complMap_algebraMap]
    · rw [finSingle_ne h, map_one]
      exact (Finset.prod_eq_one fun w hw => finSingle_ne (fun e : u = w => h (e ▸ mem_aboveF.1 hw)) _).symm

end Idele

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.L2.JoinChr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {c : (AE D)ˣ →* Circle}

theorem unrAt_of_unramEverywhere (h : UnramEverywhere D c) (w : HeightOneSpectrum (𝓞 D.host.E)) : UnrAt c w := by
  have key : ∀ y, IsUnitAt w y → finPart D (locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (mem_int_iff _).2 fun P => by
      rw [show finAdEquiv D.host.F D.host.E (finPart D (locIdele D.host.F w y : (AE D)ˣ)) = Neutral.B1.finiteSingle _ w y from
        finTens_locIdele w y]
      by_cases e : P = w
      · subst e
        rw [finSingle_self]
        exact hy.le
      · rw [finSingle_ne e, map_one]
  intro y hy
  have h1 := h _ (infTens_locIdele w y) (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h1).trans (map_one _)

variable {χ : HChar D.host.E}

set_option maxHeartbeats 800000 in

theorem locChar_eq_of_chrEq (h : ChrEq c χ) (w : HeightOneSpectrum (𝓞 D.host.E)) : locChar c w = χ.loc w := by
  obtain ⟨e, he, h0, h1, h2⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D (finAdEquiv D.host.F D.host.E)
    (fun x => (toFinAd_tmul 1 x).trans (by rw [map_one, one_mul])) mem_int_iff (fun a k P n ha => by
      rw [finAdEquiv_tmul, map_one, mul_one, ← complMap_algebraMap (rfl : P.under (𝓞 D.host.F) = _), ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ ha) w
  have key : ∀ k : D.host.Eˣ, locU he.1 k = locIdele D.host.F w (atFin w k) := fun k => by
    refine eq_locIdele ?_ (FiniteAdeleRing.ext _ fun P => ?_)
    · change infPart D (1 + e * (incA D k - 1)) = 1
      rw [RingHom.map_add, RingHom.map_mul, h0, zero_mul, add_zero, RingHom.map_one]
    · have e1 : finAdEquiv D.host.F D.host.E (finPart D (incA D k)) = algebraMap D.host.E _ (k : D.host.E) :=
        (toFinAd_tmul 1 (k : D.host.E)).trans (by rw [map_one, one_mul])
      change finAdEquiv D.host.F D.host.E (finPart D (1 + e * (incA D k - 1))) P =
        Neutral.B1.finiteSingle D.host.E w (algebraMap D.host.E _ (k : D.host.E)) P
      rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, RingEquiv.map_add, RingEquiv.map_mul,
        RingEquiv.map_sub, RingEquiv.map_one, e1]
      change 1 + finAdEquiv D.host.F D.host.E (finPart D e) P * (algebraMap D.host.E _ (k : D.host.E) - 1) = _
      by_cases hP : P = w
      · subst hP
        rw [h1, finSingle_self, one_mul, add_sub_cancel]
      · rw [h2 P hP, finSingle_ne hP, zero_mul, add_zero]
  refine MonoidHom.ext fun x => Units.ext (congrFun ((GlobalTheory.Mem.Chr.Determ.denseRange_atFin w).equalizer
    (continuous_locChar h.1.1 w)
    (Units.continuous_val.comp (χ.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele w))) (funext fun k => ?_)) x)
  have := h.2 w e he k (locU he.1 k) rfl
  rw [key] at this
  exact this

theorem unrAt_iff_of_chrEq (h : ChrEq c χ) (w : HeightOneSpectrum (𝓞 D.host.E)) : UnrAt c w ↔ χ.UnrAt w := by
  rw [UnrAt, locChar_eq_of_chrEq h]
  rfl

theorem val_eq_of_chrEq (h : ChrEq c χ) (w : HeightOneSpectrum (𝓞 D.host.E)) : val c w = χ.val w := by
  rw [val, locChar_eq_of_chrEq h]
  rfl

theorem charFam_eq_of_chrEq (h : ChrEq c χ) : charFam c = heckeFam χ := funext fun w => by
  by_cases hu : χ.UnrAt w
  · rw [charFam_of_unrAt ((unrAt_iff_of_chrEq h w).2 hu), heckeFam_of_unrAt hu, val_eq_of_chrEq h]
  · rw [heckeFam_of_not_unrAt hu]
    exact if_neg (mt (unrAt_iff_of_chrEq h w).1 hu)

theorem charL_eq_of_chrEq (h : ChrEq c χ) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) :
    charL c S = heckeL (above D.host.E S) χ := funext fun s => by
  rw [charL, charFam_eq_of_chrEq h]
  rfl

end Record

section Local

open GlobalTheory.QuadSymbol (normGroup mem_normGroup_iff_form)

variable {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

theorem valued_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valuation_up (h : w.under (𝓞 F) = v) (x : F) :
    w.valuation E (algebraMap F E x) = v.valuation F x ^ w.asIdeal.ramificationIdx (𝓞 F) := by
  subst h
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  rw [← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]

theorem valued_complMap (h : w.under (𝓞 F) = v) {a : Fv F v} (ha : a ≠ 0) :
    Valued.v (complMap h a) = Valued.v a ^ w.asIdeal.ramificationIdx (𝓞 F) := by
  obtain ⟨k, hk⟩ := v.valuation_surjective F (Valued.v a)
  have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hk' := (valued_alg v k).trans hk
  have hk0 : algebraMap F (Fv F v) k ≠ 0 := (Valuation.ne_zero_iff _).1 (hk' ▸ h0)
  have h1 : Valued.v (complMap h (a / algebraMap F _ k)) ≤ 1 :=
    complMap_mem h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_div₀, hk', div_self h0]))
  have h2 : Valued.v (complMap h (algebraMap F _ k / a)) ≤ 1 :=
    complMap_mem h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_div₀, hk', div_self h0]))
  rw [map_div₀, map_div₀, complMap_algebraMap, valued_alg, valuation_up h, hk] at h1 h2
  exact le_antisymm ((div_le_one₀ (zero_lt_iff.2 (pow_ne_zero _ h0))).1 h1)
    ((div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 ha)))).1 h2)

theorem comap_eq_iff : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ↔ w.under (𝓞 F) = v :=
  ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩

theorem isSplit_iff : IsSplit (E := E) v ↔
    ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  simp only [IsSplit, comap_eq_iff]

theorem isUnram_iff : IsUnram (E := E) v ↔
    ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  simp only [IsUnram, comap_eq_iff]

theorem under_eq_of_isInertAt (h : IsInertAt F E v w) : w.under (𝓞 F) = v :=
  HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top)
    (Ideal.map_le_iff_le_comap.1 (le_of_eq h))).symm

theorem eq_of_not_isSplit (hv : ¬ IsSplit (E := E) v) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) : w = w' := by
  by_contra hne
  exact hv (isSplit_iff.2 ⟨w, w', hne, h, h'⟩)

theorem isUnram_of_isInertAt (h : IsInertAt F E v w) : IsUnram (E := E) v := by
  refine isUnram_iff.2 fun u hu => ?_
  obtain rfl := eq_of_not_isSplit (not_isSplit_of_isInertAt h) hu (under_eq_of_isInertAt h)
  have : u.asIdeal.LiesOver v.asIdeal := ⟨hu ▸ rfl⟩
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = u.asIdeal := h
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal _ v.ne_bot]
  by_contra hne
  have := (Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne
  rw [h'] at this
  exact absurd this (not_le_of_gt (Ideal.pow_lt_self _ u.ne_bot u.isPrime.ne_top 2 le_rfl))

theorem exists_conj_basis (h2 : Module.finrank F E = 2) :
    ∃ (σ : E ≃ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), σ ≠ 1 ∧ δ ≠ 0 ∧ b 0 = 1 ∧ σ (b 1) = -b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have : Nontrivial (E ≃ₐ[F] E) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ1⟩ := exists_ne (1 : E ≃ₐ[F] E)
  have hσ2 : σ * σ = 1 := by
    have := pow_card_eq_one' (x := σ)
    rwa [hcard, pow_two] at this
  obtain ⟨δ, b, hδ, hb0, hb, hb1⟩ := GlobalTheory.QuadNormBase.exists_basis F E (σ : E →ₐ[F] E) h2
    (fun x => DFunLike.congr_fun hσ2 x) (by
      by_contra h
      push Not at h
      exact hσ1 (AlgEquiv.ext h))
  exact ⟨σ, δ, b, hσ1, fun h => hδ (h ▸ IsSquare.zero), hb0, hb, hb1⟩

section Basis

variable {σ : E ≃ₐ[F] E} {δ : F} {b : Module.Basis (Fin 2) F E}

theorem isSquare_of_isSplit (h0 : b 0 = 1) (h1 : b 1 * b 1 = algebraMap F E δ) (hv : IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) δ) := by
  obtain ⟨w, w', hne, h, h'⟩ := isSplit_iff.1 hv
  obtain ⟨y, hy⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w' 0)
  have e1 := finAdEquiv_apply h y
  have e2 := finAdEquiv_apply h' y
  rw [hy, finSingle_ne hne] at e1
  rw [hy, finSingle_self] at e2
  generalize Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) y = z at e1 e2
  have h6 := (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z
  simp only [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    h0] at h6
  generalize (Algebra.TensorProduct.basis (Fv F v) b).repr z 0 = p at h6
  generalize (Algebra.TensorProduct.basis (Fv F v) b).repr z 1 = q at h6
  subst h6
  rw [map_add, toCompl_tmul, toCompl_tmul, map_one, mul_one] at e1 e2
  have hq : q ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, add_zero] at e1 e2
    rw [(map_eq_zero _).1 e2.symm, map_zero] at e1
    exact one_ne_zero e1
  refine ⟨p / q, (complMap h').injective ?_⟩
  have hq' : complMap h' q ≠ 0 := (map_ne_zero _).2 hq
  rw [complMap_algebraMap, ← h1, map_mul, map_mul, map_div₀, eq_neg_of_add_eq_zero_left e2.symm]
  field_simp

theorem ramificationIdx_eq_one_of_isSquare (h0 : b 0 = 1) (h1 : b 1 * b 1 = algebraMap F E δ)
    (hs : IsSquare (algebraMap F (Fv F v) δ)) (h : w.under (𝓞 F) = v) : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, algebraMap E (w.adicCompletion E) (b 1) = complMap h s := by
    obtain ⟨s, hs⟩ := hs
    have e := congrArg (complMap h) hs
    rw [complMap_algebraMap, ← h1, map_mul, map_mul] at e
    rcases mul_self_eq_mul_self_iff.1 e with e | e
    · exact ⟨s, e⟩
    · exact ⟨-s, by rw [map_neg, e]⟩
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  obtain ⟨a, ha⟩ : ∃ a, algebraMap E (w.adicCompletion E) π = complMap h a := by
    refine ⟨algebraMap F _ (b.repr π 0) + algebraMap F _ (b.repr π 1) * s, ?_⟩
    conv_lhs => rw [← b.sum_repr π]
    rw [Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul, hs, map_add, map_mul,
      complMap_algebraMap, complMap_algebraMap]
  rw [← valued_alg, ha] at hπ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  rw [valued_complMap h ha0, ← WithZero.exp_log (x := Valued.v a) ((Valuation.ne_zero_iff _).2 ha0), ← WithZero.exp_nsmul,
    WithZero.exp_inj, nsmul_eq_mul] at hπ
  have := Int.eq_one_or_neg_one_of_mul_eq_neg_one hπ
  omega

theorem valuation_form (h2 : Module.finrank F E = 2) (hσ : σ ≠ 1) (hb : σ (b 1) = -b 1)
    (h1 : b 1 * b 1 = algebraMap F E δ) (hv : ¬ IsSplit (E := E) v) (h : w.under (𝓞 F) = v) (p q : F) :
    v.valuation F (p ^ 2 - δ * q ^ 2) ^ w.asIdeal.ramificationIdx (𝓞 F) =
      w.valuation E (algebraMap F E p + algebraMap F E q * b 1) ^ 2 := by
  obtain ⟨u, hu, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl σ.toRingEquiv w
  obtain rfl := eq_of_not_isSplit hv
    (((GlobalTheory.Mem.Chr.under_eq_iff_conjPl σ h2 hσ w u).2 (Or.inr hu)).trans h) h
  have e : u.valuation E (σ (algebraMap F E p + algebraMap F E q * b 1)) = _ := hu _
  rw [← valuation_up h, pow_two (u.valuation E _)]
  nth_rw 1 [← e]
  rw [← map_mul (u.valuation E), map_add σ, map_mul σ, hb, σ.commutes, σ.commutes, map_sub, map_mul, ← h1, map_pow,
    map_pow]
  congr 1
  ring

end Basis

theorem isUnram_of_isSplit (h2 : Module.finrank F E = 2) (hv : IsSplit (E := E) v) : IsUnram (E := E) v := by
  obtain ⟨σ, δ, b, -, -, h0, -, h1⟩ := exists_conj_basis h2
  exact isUnram_iff.2 fun w h => ramificationIdx_eq_one_of_isSquare h0 h1 (isSquare_of_isSplit h0 h1 hv) h

theorem mem_normGroup_of_isSplit (h2 : Module.finrank F E = 2) (hv : IsSplit (E := E) v) (x : (Fv F v)ˣ) :
    x ∈ normGroup F E (Fv F v) := by
  obtain ⟨σ, δ, b, -, hδ, h0, -, h1⟩ := exists_conj_basis h2
  obtain ⟨s, hs⟩ := isSquare_of_isSplit h0 h1 hv
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hδ ((map_eq_zero _).1 (hs.trans (mul_zero _)))
  refine (mem_normGroup_iff_form b h0 h1).2 ⟨(x + 1) / 2, (x - 1) / (2 * s), ?_⟩
  rw [hs]
  field_simp
  ring

open scoped WithZeroTopology in

theorem not_mem_normGroup_of_inert (h2 : Module.finrank F E = 2) (hv : ¬ IsSplit (E := E) v)
    (hu : IsUnram (E := E) v) {x : (Fv F v)ˣ} (hx : IsUnifAt v x) : x ∉ normGroup F E (Fv F v) := by
  obtain ⟨σ, δ, b, hσ, -, h0, hb, h1⟩ := exists_conj_basis h2
  obtain ⟨w, h⟩ := (GlobalTheory.QNorm.places_over F E).2.1 v
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨p, q, e⟩
  have hd := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) v
  have ho : IsOpen ({WithZero.exp (-1 : ℤ)} : Set (WithZero (Multiplicative ℤ))) :=
    WithZeroTopology.isOpen_iff.2 (Or.inl WithZero.exp_ne_zero.symm)
  have hc : Continuous fun z : Fv F v × Fv F v => Valued.v (z.1 ^ 2 - algebraMap F (Fv F v) δ * z.2 ^ 2) :=
    (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective F)).comp (by fun_prop)
  obtain ⟨⟨p', q'⟩, hz⟩ := (hd.prodMap hd).exists_mem_open (ho.preimage hc) ⟨(p, q), by
    change Valued.v (p ^ 2 - algebraMap F (Fv F v) δ * q ^ 2) = _
    rw [← e]
    exact hx⟩
  replace hz : Valued.v (algebraMap F (Fv F v) p' ^ 2 - algebraMap F (Fv F v) δ * algebraMap F (Fv F v) q' ^ 2) =
    WithZero.exp (-1 : ℤ) := hz
  rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, valued_alg] at hz
  have h3 := congrArg WithZero.log (valuation_form h2 hσ hb h1 hv h p' q')
  rw [isUnram_iff.1 hu w h, pow_one, hz, WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at h3
  omega

theorem mem_normGroup_of_isUnram (h2 : Module.finrank F E = 2) (hu : IsUnram (E := E) v) {x : (Fv F v)ˣ}
    (hx : IsUnitAt v x) : x ∈ normGroup F E (Fv F v) := by
  by_cases hv : IsSplit (E := E) v
  · exact mem_normGroup_of_isSplit h2 hv x
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have h := (GlobalTheory.QuadSymbol.localCharacters F E).1 v x (atFin v (unif v))
  rw [GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2 (not_mem_normGroup_of_inert h2 hv hu (unif_spec v)),
    GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2 (not_mem_normGroup_of_inert h2 hv hu (by
      have := unif_spec v
      unfold IsUnifAt at this ⊢
      rw [Units.val_mul, map_mul, hx, one_mul, this]))] at h
  exact GlobalTheory.QuadSymbol.eta_eq_one_iff.1 (by simpa using h.symm)

theorem exists_unit_not_mem_normGroup (h2 : Module.finrank F E = 2) (hu : ¬ IsUnram (E := E) v) :
    ∃ x : (Fv F v)ˣ, IsUnitAt v x ∧ x ∉ normGroup F E (Fv F v) := by
  obtain ⟨σ, δ, b, hσ, hδ, h0, hb, h1⟩ := exists_conj_basis h2
  have hv : ¬ IsSplit (E := E) v := fun h => hu (isUnram_of_isSplit h2 h)
  obtain ⟨w, h, he⟩ : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ w.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by
    simpa only [isUnram_iff, not_forall, exists_prop] using hu
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.QNorm.exists_local_nonnorm F v _ ((map_ne_zero (algebraMap F (Fv F v))).2 hδ)
    fun hs => he (ramificationIdx_eq_one_of_isSquare h0 h1 hs h)
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h3 := valuation_form h2 hσ hb h1 hv h (b.repr π 0) (b.repr π 1)
  have h4 : algebraMap F E (b.repr π 0) + algebraMap F E (b.repr π 1) * b 1 = π := by
    conv_rhs => rw [← b.sum_repr π]
    rw [Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [h4, hπ] at h3
  set N := b.repr π 0 ^ 2 - δ * b.repr π 1 ^ 2 with hN
  have := w.isPrime
  have he0 : 0 < w.asIdeal.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos _ _
  have hN0 : v.valuation F N ≠ 0 := fun h0 => by
    rw [h0, zero_pow he0.ne'] at h3
    exact pow_ne_zero 2 WithZero.exp_ne_zero h3.symm
  have hN1 : v.valuation F N = WithZero.exp (-1 : ℤ) := by
    have h5 := congrArg WithZero.log h3
    rw [WithZero.log_pow, WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul] at h5
    rw [← WithZero.exp_log hN0]
    congr 1
    have h6 : (2 : ℤ) ≤ w.asIdeal.ramificationIdx (𝓞 F) := by omega
    generalize WithZero.log (v.valuation F N) = m at h5
    push_cast at h5
    have h7 : m < 0 := by
      by_contra h8
      nlinarith
    nlinarith
  let n : (Fv F v)ˣ := atFin v (Units.mk0 N ((Valuation.ne_zero_iff _).1 hN0))
  have hn : n ∈ normGroup F E (Fv F v) := (mem_normGroup_iff_form b h0 h1).2
    ⟨algebraMap F _ (b.repr π 0), algebraMap F _ (b.repr π 1), by
      rw [← map_pow (algebraMap F _), ← map_pow (algebraMap F _), ← map_mul, ← map_sub]
      rfl⟩
  have hnv : Valued.v (n : Fv F v) = WithZero.exp (-1 : ℤ) := (valued_alg v N).trans hN1
  refine ⟨Units.mk0 z hz0 * n ^ WithZero.log (Valued.v z), ?_, fun hm => hz ?_⟩
  · unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hnv, ← WithZero.exp_zsmul, Units.val_mk0]
    nth_rw 1 [← WithZero.exp_log (x := Valued.v z) ((Valuation.ne_zero_iff _).2 hz0)]
    rw [← WithZero.exp_add]
    simp
  · exact (mem_normGroup_iff_form b h0 h1).1 ((Subgroup.mul_mem_cancel_right _ (zpow_mem hn _)).1 hm)

end Local

section Eta

open GlobalTheory.QuadSymbol (normGroup)
open GlobalTheory.IdeleNormChar (normSign signToCircle finComp infComp)

variable {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)} {η : (AF F)ˣ →* Circle}

theorem normSign_localIdele [Algebra.IsQuadraticExtension F E] (x : (Fv F v)ˣ) :
    normSign E (localIdele F v x) = GlobalTheory.QuadSymbol.eta F E (Fv F v) x := by
  change (∏ᶠ u : HeightOneSpectrum (𝓞 F), GlobalTheory.QuadSymbol.eta F E _ (finComp (localIdele F v x) u)) *
    ∏ u : InfinitePlace F, GlobalTheory.QuadSymbol.eta F E _ (infComp (localIdele F v x) u) = _
  rw [finprod_eq_single _ v fun u hu => by
      rw [show finComp (localIdele F v x) u = 1 from Units.ext (finSingle_ne hu _)]
      exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (one_mem _),
    Finset.prod_eq_one (f := fun u : InfinitePlace F => GlobalTheory.QuadSymbol.eta F E _ (infComp (localIdele F v x) u))
      fun u _ => GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (by
        rw [show infComp (localIdele F v x) u = 1 from Units.ext rfl]
        exact one_mem _), mul_one,
    show finComp (localIdele F v x) v = x from Units.ext (finSingle_self v _)]

theorem IsEta.eq_normSign [Algebra.IsQuadraticExtension F E] (h : IsEta F E η) :
    η = signToCircle.comp (normSign E) := by
  refine GlobalTheory.IdeleNormChar.eq_signToCircle_comp _ η (fun a ha => ?_) h.2.2.2
  obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h.2.2.1 x, one_mul]
  exact h.2.1 t

theorem IsEta.loc_of_mem (h2 : Module.finrank F E = 2) (h : IsEta F E η) {x : (Fv F v)ˣ}
    (hx : x ∈ normGroup F E (Fv F v)) : (toHChar η h.isHeckeF).loc v x = 1 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  change Circle.toUnits (η (localIdele F v x)) = 1
  rw [h.eq_normSign, MonoidHom.comp_apply, normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hx, map_one, map_one]

theorem IsEta.loc_of_not_mem (h2 : Module.finrank F E = 2) (h : IsEta F E η) {x : (Fv F v)ˣ}
    (hx : x ∉ normGroup F E (Fv F v)) : (toHChar η h.isHeckeF).loc v x = -1 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  change Circle.toUnits (η (localIdele F v x)) = -1
  rw [h.eq_normSign, MonoidHom.comp_apply, normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2 hx]
  exact Units.ext (congrArg (fun z : Circle => (z : ℂ)) (if_neg (by decide) :
    (if (-1 : ℤˣ) = 1 then (1 : Circle) else -1) = -1))

theorem IsEta.unrAt_iff (h2 : Module.finrank F E = 2) (h : IsEta F E η) :
    (toHChar η h.isHeckeF).UnrAt v ↔ IsUnram (E := E) v := by
  refine ⟨fun hu => ?_, fun hu x hx => h.loc_of_mem h2 (mem_normGroup_of_isUnram h2 hu hx)⟩
  by_contra hv
  obtain ⟨x, hx, hn⟩ := exists_unit_not_mem_normGroup h2 hv
  have := congrArg Units.val ((hu x hx).symm.trans (h.loc_of_not_mem h2 hn))
  norm_num at this

theorem IsEta.val_eq (h2 : Module.finrank F E = 2) (h : IsEta F E η) (hu : IsUnram (E := E) v) :
    (toHChar η h.isHeckeF).val v = etaU E v := by
  unfold etaU
  split_ifs with hv
  · exact h.loc_of_mem h2 (mem_normGroup_of_isSplit h2 hv _)
  · exact h.loc_of_not_mem h2 (not_mem_normGroup_of_inert h2 hv hu (unif_spec v))

theorem IsHeckeF.pow (h : IsHeckeF F η) (k : ℕ) : IsHeckeF F (η ^ k) :=
  ⟨h.1.pow k, fun a => by rw [MonoidHom.pow_apply, h.2 a, one_pow]⟩

theorem loc_pow (χ : HChar F) (k : ℕ) (x : (Fv F v)ˣ) : (χ ^ k).loc v x = χ.loc v x ^ k := rfl

variable {μ : (AF F ⊗[F] E)ˣ →* Circle} {k : ℕ}

theorem ResEta.prod_val (h2 : Module.finrank F E = 2) (h : ResEta F E μ k) (hv : IsUnram (E := E) v)
    (hμ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt μ w) :
    ∏ w ∈ aboveF (L := E) F v, val μ w = etaU E v ^ k := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have h1 := congrArg Circle.toUnits (h η hη (localIdele F v (atFin v (unif v))))
  rw [ideleMap_localIdele, map_prod, map_prod, map_pow] at h1
  rw [← hη.val_eq h2 hv]
  refine Eq.trans (Finset.prod_congr rfl fun w hw => ?_) h1
  have hw := mem_aboveF.1 hw
  refine ((hμ w hw).locChar_eq_val ?_).symm
  refine (valued_alg w (algebraMap F E (unif v : Fˣ))).trans ?_
  rw [valuation_up hw, isUnram_iff.1 hv w hw, pow_one, ← valued_alg]
  exact unif_spec v

theorem ResEta.val_mul_val (h2 : Module.finrank F E = 2) (h : ResEta F E μ k) (hne : w ≠ w')
    (hw : w.under (𝓞 F) = v) (hw' : w'.under (𝓞 F) = v) (hu : UnrAt μ w) (hu' : UnrAt μ w') :
    val μ w * val μ w' = 1 := by
  classical
  have hv : IsSplit (E := E) v := isSplit_iff.2 ⟨w, w', hne, hw, hw'⟩
  obtain ⟨σ, -, -, hσ, -⟩ := exists_conj_basis h2
  have hc := ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl σ h2 hσ w w').1 (hw'.trans hw.symm)).resolve_left hne.symm
  have key : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → u = w ∨ u = w' := fun u hu =>
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl σ h2 hσ w u).1 (hu.trans hw.symm)).imp_right fun h1 =>
      (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h1 hc
  have e : aboveF (L := E) F v = {w, w'} := by
    ext u
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨key u, by rintro (rfl | rfl) <;> assumption⟩
  have := h.prod_val h2 (isUnram_of_isSplit h2 hv) fun u hu => by
    rcases key u hu with rfl | rfl <;> assumption
  rwa [e, Finset.prod_pair hne, etaU, if_pos hv, one_pow] at this

theorem ResEta.val_of_isInertAt (h2 : Module.finrank F E = 2) (h : ResEta F E μ k) (hw : IsInertAt F E v w)
    (hu : UnrAt μ w) : val μ w = (-1) ^ k := by
  have hv := not_isSplit_of_isInertAt hw
  have key : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → u = w := fun u hu =>
    eq_of_not_isSplit hv hu (under_eq_of_isInertAt hw)
  have e : aboveF (L := E) F v = {w} := by
    ext u
    rw [mem_aboveF, Finset.mem_singleton]
    exact ⟨key u, fun h => h ▸ under_eq_of_isInertAt hw⟩
  have := h.prod_val h2 (isUnram_of_isInertAt hw) fun u h1 => key u h1 ▸ hu
  rwa [e, Finset.prod_singleton, etaU, if_neg hv] at this

end Eta

end GlobalTheory.LFun

end
