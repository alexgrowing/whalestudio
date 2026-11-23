import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstHecke

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.UnitaryHeckeBaseChange (toAdele adeleEquiv cP)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
theorem cA_eq (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_cA (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  rw [cA_eq, cA_eq]; exact GlobalTheory.UnitaryHeckeBaseChange.cA_cA h z

variable (F) in

def badSet (T : Finset (Pl F)) : Set (Pl E) := {w | w.under (𝓞 F) ∈ T} ∪ {w | w.asIdeal.ramificationIdx ℤ ≠ 1}

theorem finite_badSet (T : Finset (Pl F)) : (badSet F (E := E) T).Finite :=
  Set.Finite.union (by simpa using (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually T.finite_toSet.compl_mem_cofinite)
    (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2

omit [NumberField F] in
theorem splitsFully_of [IsGalois ℚ E] {w : Pl E} (he : w.asIdeal.ramificationIdx ℤ = 1) (hw : (Ideal.absNorm w.asIdeal).Prime) :
    SplitsFully E (w.under (𝓞 F)) := by
  have := w.isPrime
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hw
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under ℤ) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(E/ℚ), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(E/ℚ),
    he, hf, mul_one, mul_one, IsGalois.card_aut_eq_finrank] at k
  rw [SplitsFully, ← k]
  exact congrArg (fun p : Ideal ℤ => (p.primesOver (𝓞 E)).ncard) (Ideal.under_under (B := 𝓞 F) w.asIdeal)

theorem conjPrime_ne (h : IsCMExt F E σ) {w : Pl E} (he : w.asIdeal.ramificationIdx ℤ = 1) (hw : (Ideal.absNorm w.asIdeal).Prime) :
    cP h w ≠ w := fun e => by
  have := w.isPrime
  have : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hw
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 F)) (𝓞 E) Gal(E/F)
  rw [Ideal.ramificationIdx_tower (w.asIdeal.under (𝓞 F)) w.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (w.asIdeal.under (𝓞 F)) w.asIdeal] at hf
  have s : (w.asIdeal.under (𝓞 F)).primesOver (𝓞 E) = {w.asIdeal} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨w.isPrime, ⟨rfl⟩⟩, fun Q ⟨q1, q2⟩ => ?_⟩
    have q3 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := w.asIdeal.under (𝓞 F)) (w.under (𝓞 F)).ne_bot Q
    rcases GlobalTheory.UnitaryHeckeBaseChange.eq_or_eq_cP h (P := w) (Q := ⟨Q, q1, q3⟩) (HeightOneSpectrum.ext q2.over.symm) with r | r
    · exact congrArg HeightOneSpectrum.asIdeal r
    · exact congrArg HeightOneSpectrum.asIdeal (r.trans e)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(E/F), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(E/F),
    Nat.eq_one_of_mul_eq_one_left he, Nat.eq_one_of_mul_eq_one_left hf, IsGalois.card_aut_eq_finrank, h.2.2.1, s,
    Set.ncard_singleton] at k
  omega

theorem exists_split (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (h : IsCMExt F E σ) [IsGalois ℚ E] (T : Finset (Pl F)) :
    ∃ v ∉ T, SplitsFully E v ∧ ∃ (ε : AF F) (e : AE F E), GlobalTheory.Published.IsPlacesIdem ∅ {v} ε ∧ e * e = e ∧
      e * sigR (AF F) σ e = 0 ∧ e + sigR (AF F) σ e = algebraMap (AF F) (AE F E) ε := by
  obtain ⟨w, hw, hp⟩ := exists_prime_norm H (finite_badSet (E := E) T)
  have he : w.asIdeal.ramificationIdx ℤ = 1 := not_not.1 fun x => hw (Or.inr x)
  obtain ⟨e, f, hi⟩ := GlobalTheory.UnitaryHeckeBaseChange.exists_isPrimeIdem h w
  obtain ⟨i1, i2⟩ := GlobalTheory.UnitaryHeckeBaseChange.of_isPrimeIdem h hi
  refine ⟨_, fun x => hw (Or.inl x), splitsFully_of he hp, ?_⟩
  rcases hi with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, -⟩, rfl⟩ | ⟨rfl, -⟩
  · have hv : w.under (𝓞 F) = v := by
      by_contra hv
      exact one_ne_zero ((i2.2.1 w rfl).symm.trans
        ((congrArg (fun z => (toAdele F E z).2 w) h3).trans ((GlobalTheory.UnitaryHeckeBaseChange.place_comp hε).2.2 w hv)))
    obtain ⟨j0, j1, j2⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isPlaceIdem_iff v ε).1 hε
    exact ⟨ε, e, ⟨fun _ x => absurd x (Finset.notMem_empty _), fun u _ => congrFun j0 u,
      fun u x => j1 u ((Finset.mem_singleton.1 x).trans hv), fun u x => j2 u fun y => x (Finset.mem_singleton.2 (y.trans hv.symm))⟩,
      h1, h2, h3⟩
  · exact absurd ((i2.2.1 _ (GlobalTheory.UnitaryHeckeBaseChange.under_cP h w)).symm.trans (i1.2.2 _ (conjPrime_ne h he hp))) one_ne_zero

theorem cA_eIdele (h : IsCMExt F E σ) [IsTotallyComplex E] {z : AE F E} (hz : toAdele F E z = GlobalTheory.IdeleCovolume.eIdele E) :
    cA σ z = z := by
  obtain ⟨_, rfl⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff σ).1 h
  have := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  refine (GlobalTheory.UnitaryHeckeBaseChange.bijective_toAdele h).1 ?_
  rw [cA_eq]
  refine (GlobalTheory.UnitaryHeckeBaseChange.toAdele_cA z).trans ?_
  rw [hz]
  let A := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra
  let c := @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap E E _ _ A
  let ρ : ℝ →+* InfiniteAdeleRing E :=
    (GlobalTheory.CuspRep.infEq E).toRingHom.comp ((Pi.constRingHom _ ℂ).comp Complex.ofRealHom)
  have hρ : Continuous ρ := (GlobalTheory.CuspRep.continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal)
  have k := congrFun (Rat.denseRange_cast.equalizer
    ((@GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap E E _ _ _ _ A).comp hρ) hρ
    (funext fun q => RingHom.congr_fun (RingHom.ext_rat ((c.comp ρ).comp (Rat.castHom ℝ)) (ρ.comp (Rat.castHom ℝ))) q)) (Real.exp 1)
  have e1 : (GlobalTheory.IdeleCovolume.eIdele E : AdeleRing (𝓞 E) E).1 = ρ (Real.exp 1) :=
    (GlobalTheory.CuspRep.infEq E).symm_apply_eq.1 (funext fun w => (GlobalTheory.IdeleCovolume.pInf_eIdele E w).trans (Complex.ofReal_exp 1).symm)
  have e2 : (GlobalTheory.IdeleCovolume.eIdele E : AdeleRing (𝓞 E) E).2 = 1 := GlobalTheory.IdeleCovolume.pFin_eIdele E
  exact Prod.ext ((congrArg c e1).trans (k.trans e1.symm))
    ((congrArg (@GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap E E _ _ _ _ A) e2).trans ((map_one _).trans e2.symm))

theorem at_localIdele (h : IsCMExt F E σ) (w : Pl E) (x : (w.adicCompletion E)ˣ) {z : AE F E}
    (hz : toAdele F E z = Neutral.B1.localIdele E w x) : At (evFin F (w.under (𝓞 F))) (z - 1) := fun a ha => by
  classical
  refine (GlobalTheory.UnitaryHeckeBaseChange.bijective_toAdele h).1 ?_
  rw [Algebra.smul_def, map_mul, map_sub, map_one, hz, map_zero, GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap]
  refine Prod.ext ((congrArg (_ * ·) (sub_self 1)).trans (mul_zero _)) (FiniteAdeleRing.ext _ fun u => ?_)
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E u (a.2 (u.under (𝓞 F))) *
    (Function.update (fun v : Pl E => (1 : v.adicCompletion E)) w x u - 1) = 0
  by_cases hu : u = w
  · subst hu
    rw [show a.2 (u.under (𝓞 F)) = 0 from ha, map_zero, zero_mul]
  · rw [Function.update_of_ne hu, sub_self, mul_zero]

theorem exists_h90_eq_of_normOne (h : IsCMExt F E σ) (u : normOne (cA σ)) : ∃ z, h90 (cA σ) z = u := by
  obtain ⟨_, rfl⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff σ).1 h
  have := h.2.1
  obtain ⟨z, hz⟩ := GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic F E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E) h.2.2.1 (fun e => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    refine InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 ?_)
    refine RingHom.ext fun x => ?_
    have := h.2.2.2 w.embedding x
    rw [e] at this
    exact this.symm) u.1 (by have := mem_normOne.1 u.2; rwa [cA_eq] at this)
  exact ⟨z, hilbertNinetyQuotientHom_eq_iff.2 (by rw [cA_eq]; exact hz.symm)⟩

theorem normOne_mem (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (h : IsCMExt F E σ) [IsGalois ℚ E] (T : Finset (Pl F))
    (N : Subgroup (normOne (cA σ))) (hN : IsClosed (N : Set (normOne (cA σ))))
    (h1 : ∀ u : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((u.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → u ∈ N)
    (h2 : ∀ v ∉ T, SplitsFully E v → ∀ u : normOne (cA σ), At (evFin F v) ((u.1 : AE F E) - 1) → u ∈ N) (u : normOne (cA σ)) :
    u ∈ N := by
  have := h.2.1
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let p : Neutral.B1.Ideles E →* (AE F E)ˣ := Units.map (adeleEquiv h).symm.toRingHom.toMonoidHom
  have hp : ∀ y, toAdele F E (p y) = y := fun y => (adeleEquiv h).apply_symm_apply _
  have hm : ∀ z, h90 (cA σ) z * Units.map (cA σ : AE F E →* AE F E) z = z := fun z => div_mul_cancel _ _
  have hv : ∀ z, (h90 (cA σ) z : AE F E) * cA σ z = z := fun z => congrArg Units.val (hm z)
  let q : (AE F E)ˣ →* normOne (cA σ) := (h90 (cA σ)).codRestrict _ fun z => mem_normOne.2 (z.isUnit.mul_right_cancel (by
    have := congrArg (cA σ) (hv z)
    rw [map_mul, cA_cA h] at this
    rw [mul_assoc, this, hv, one_mul]))
  have cc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have cq : Continuous q := (continuous_id.div' (Continuous.units_map _ cc)).subtype_mk _
  obtain ⟨z, hz⟩ := exists_h90_eq_of_normOne h u
  have := closed_eq_top H (N.comap (q.comp p))
    (hN.preimage (cq.comp (Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_adeleEquiv_symm h))))
    (fun k => h1 _ ⟨k / σ k, div_ne_zero (Units.ne_zero k) ((map_ne_zero σ).2 (Units.ne_zero k)), ?_⟩) ?_ (finite_badSet (E := E) T)
    (fun w hw hn x => h2 _ (fun y => hw (Or.inl y)) (splitsFully_of (not_not.1 fun y => hw (Or.inr y)) hn) _ fun a ha => ?_)
    (Units.map (adeleEquiv h).toRingHom.toMonoidHom z)
  · rw [Subgroup.mem_comap, MonoidHom.comp_apply,
      show p (Units.map (adeleEquiv h).toRingHom.toMonoidHom z) = z from Units.ext ((adeleEquiv h).symm_apply_apply _)] at this
    exact (Subtype.ext hz : q z = u) ▸ this
  · have e : (p (Neutral.B1.diagUnits E k) : AE F E) = inclR (F := F) (AF F) (k : E) :=
      (GlobalTheory.UnitaryHeckeBaseChange.bijective_toAdele h).1 ((hp _).trans (GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA _).symm)
    have k0 : σ (k : E) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero k)
    have := hv (p (Neutral.B1.diagUnits E k))
    rw [e, show cA σ (inclR (F := F) (AF F) (k : E)) = inclR (F := F) (AF F) (σ k) from rfl] at this
    refine ((IsUnit.mk0 (σ (k : E)) k0).map (inclR (F := F) (AF F))).mul_right_cancel (this.trans ?_)
    rw [← map_mul, div_mul_cancel₀ _ k0]
  · have e := hv (p (GlobalTheory.IdeleCovolume.eIdele E))
    rw [cA_eIdele h (hp _)] at e
    have : q (p (GlobalTheory.IdeleCovolume.eIdele E)) = 1 :=
      Subtype.ext (Units.ext ((Units.isUnit _).mul_right_cancel (e.trans (one_mul _).symm)))
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, this]
    exact one_mem N
  · set y := p (Neutral.B1.localIdele E w x)
    have a1 : a • ((y : AE F E) - 1) = 0 := at_localIdele h w x (hp _) a ha
    have a2 := congrArg (cA σ) a1
    rw [map_smul, map_sub, map_one, map_zero] at a2
    refine ((Units.isUnit y).map (cA σ)).mul_right_cancel ?_
    rw [smul_mul_assoc, sub_mul, zero_mul, one_mul]
    rw [show ((((q.comp p) (Neutral.B1.localIdele E w x)).1 : (AE F E)ˣ) : AE F E) * cA σ y = y from hv y,
      show (y : AE F E) - cA σ y = (y - 1) - (cA σ y - 1) by ring, smul_sub, a1, a2, sub_self]

end GlobalTheory.ThK.Dbl

end
