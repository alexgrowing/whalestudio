import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapEqOfContinuousAdicCompletionIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKerStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.LocDegOne

theorem val_div_sub_one_le₁ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le₁ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E']
    (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E') (hi : Continuous i)
    (hloc : ∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x))
    (art : Ideles E →* Gab E Ω) (art' : Ideles E' →* Gab E' Ω') (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    (ρ : Gab E' Ω' →* Gab E Ω) (hρc : Continuous ρ)
    (hρ : ∀ (τ : G E' Ω') (σ : G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (toAb E' Ω' τ) = toAb E Ω σ)
    (x : (w.adicCompletion E)ˣ) :
    ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x))) = art (localIdele E w x) := by
  classical
  have hw' := GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso E E' w w' i hi hloc
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : E'ˣ, art' (diagUnits E' k) = 1 := fun k => by
    have hk : diagUnits E' k ∈ art'.ker := by
      rw [ha'.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hiE : ∀ y ∈ infConn E, art y = 1 := fun y hy => by
    have hk : y ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  have hiK : ∀ y ∈ infConn E', art' y = 1 := fun y hy => by
    have hk : y ∈ art'.ker := by
      rw [ha'.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)))) = χ (art (localIdele E w x)) by
    have h2 : χ (ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x))) / art (localIdele E w x)) = 1 := by
      rw [_root_.map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles E' →* Gab E Ω ⧸ U := χ.comp (ρ.comp art')
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles E')) = (ρ.comp art') ⁻¹' U := by
    ext y; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext y; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles E')) := by
    rw [hker1]; exact hU.preimage (hρc.comp ha'.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  let f1 : (w.adicCompletion E)ˣ →* Gab E Ω ⧸ U :=
    ψ1.comp ((localIdele E' w').comp (Units.map i.toRingHom.toMonoidHom))
  let f2 : (w.adicCompletion E)ˣ →* Gab E Ω ⧸ U := ψ2.comp (localIdele E w)
  have hf1 : IsOpen (f1.ker : Set (w.adicCompletion E)ˣ) := by
    have e : (f1.ker : Set (w.adicCompletion E)ˣ) =
        ((localIdele E' w').comp (Units.map i.toRingHom.toMonoidHom)) ⁻¹' (ψ1.ker : Set (Ideles E')) := by
      ext y; simp only [f1, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho1.preimage ((GlobalTheory.Mem.UnrAe.continuous_localIdele w').comp (Continuous.units_map _ hi))
  have hf2 : IsOpen (f2.ker : Set (w.adicCompletion E)ˣ) := by
    have e : (f2.ker : Set (w.adicCompletion E)ˣ) = (localIdele E w) ⁻¹' (ψ2.ker : Set (Ideles E)) := by
      ext y; simp only [f2, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho2.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele w)
  show f1 x = f2 x
  refine GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker E w _ f1 f2 hf1 hf2 (fun c => ?_) x
  let y : E'ˣ := Units.map (algebraMap E E').toMonoidHom c
  have hc1 : f1 (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom c) = ψ1 (locUnit E' w' y) := by
    simp only [f1, MonoidHom.comp_apply, locUnit_apply]
    congr 2
    ext
    simp [y, hloc]
  rw [hc1]
  change _ = ψ2 (locUnit E w c)

  let NK : E'ˣ →* Eˣ := Units.map (Algebra.norm E (S := E'))
  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E ψ2.ker ho2 {w}
  have hwSE : w ∈ SE := hvS (Finset.mem_singleton_self w)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.PlacesOver.places_over_finset E E' SE
  have hWT : w' ∈ TSK := (hTSK w').mpr ⟨w, hwSE, hw'⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E' ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' v' ME
  obtain ⟨ML, hML⟩ := GlobalTheory.T.norm_close_to_component_localDegreeOne E E' w w' i hi hloc ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (w'.valuation E' (y : E'))).natAbs
  let P0 : ℕ := MK + M'' + ML + 1
  obtain ⟨a, hap, hapos⟩ := GlobalTheory.T.exists_totallyPositive_approx_at_finite_places E' TSK (fun u => if u = w' then (y : E') else 1) (P0 + m)
  have haW : w'.valuation E' (a - y) ≤ WithZero.exp (-((P0 : ℤ) + m)) := by
    have := hap w' hWT
    rw [if_pos rfl] at this
    exact val_le_of_le₁ w' this (by push_cast; omega)
  have hz : w'.valuation E' (a / y - 1) ≤ WithZero.exp (-(P0 : ℤ)) :=
    val_div_sub_one_le₁ w' y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : E'ˣ := Units.mk0 a ha0
  let zu : E'ˣ := au / y
  have hzu : (zu : E') = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]
  have hoth : ∀ u ∈ TSK, u ≠ w' → u.valuation E' (a - 1) ≤ WithZero.exp (-(P0 : ℤ)) := fun u hu hne => by
    have := hap u hu
    rw [if_neg hne] at this
    exact val_le_of_le₁ u this (by push_cast; omega)

  have F1 : ψ1 (locUnit E' w' au) = ψ1 (locUnit E' w' y) := by
    have hm : locUnit E' w' zu ∈ ψ1.ker := hSKc w' (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le₁ w' hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E w (NK au)) = ψ2 (locUnit E w c) := by
    have hn : w.valuation E (Algebra.norm E a / (c : E) - 1) ≤ WithZero.exp (-(ME : ℤ)) := by
      refine hML (c : E) a c.ne_zero (fun u hu hne => ?_) ?_
      · exact val_le_of_le₁ u (hoth u ((hTSK u).mpr ⟨w, hwSE, hu⟩) hne) (by push_cast; omega)
      · have e : algebraMap E E' (c : E) = (y : E') := rfl
        rw [e]; exact val_le_of_le₁ w' hz (by push_cast; omega)
    let q : Eˣ := NK au / c
    have hq : (q : E) = Algebra.norm E a / (c : E) := by simp [q, NK, au]
    have hm : locUnit E w q ∈ ψ2.ker := hSc w hwSE q (by rw [hq]; exact hn)
    have e : NK au = c * q := by simp [q]
    rw [e, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ u ∈ TSK, u ≠ w' → ψ1 (locUnit E' u au) = 1 := fun u hu hne =>
    MonoidHom.mem_ker.mp (hSKc u (hTS hu) au (val_le_of_le₁ u (hoth u hu hne) (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ w → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : E') fun u hu => ?_
    have huT : u ∈ TSK := (hTSK u).mpr ⟨v', hv', hu⟩
    have huW : u ≠ w' := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hu.symm.trans hw'))
    exact val_le_of_le₁ u (hoth u huT huW) (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ z, IsUnitAt v' z → ψ2 (localIdele E v' z) = 1 := fun v' hv' z hz =>
    MonoidHom.mem_ker.mp (hSu v' hv' z hz)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (u : HeightOneSpectrum (𝓞 E'))
      (hu : u.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v'.asIdeal) =>
    GlobalTheory.T.artin_transport_algClosure_equiv E Ω E' Ω' φ hφ art art' ha ha' ρ hρ (Gab E Ω ⧸ U) χ v' u hu (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E E' (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' u hu => (hchi v' hv' u hu).1) (fun v' hv' u hu => (hchi v' hv' u hu).2) au

  have hPK : (∏ u ∈ TK, ψ1 (locUnit E' u au)) * ψ1 (locUnit E' w' au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK u).mp h2
      exact hTK1 u h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive E' (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) (fun z hz => by simp [ψ1, hiK z hz])
      au (fun φ => hapos φ) (TK ∪ TSK) fun u hu => by
        rw [Finset.mem_union, not_or] at hu
        exact hTK2 u hu.1 fun v' hv' e => hu.2 ((hTSK u).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem w' hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E w (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (fun z hz => by simp [ψ2, hiE z hz])
      (NK au) (fun φ => GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero E E' a ha0 hapos φ) (TE ∪ SE) fun v' hv' => by
        rw [Finset.mem_union, not_or] at hv'
        exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem w hwSE F4] at h
    exact h
  have key : ψ1 (locUnit E' w' au) = ψ2 (locUnit E w (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  rw [← F1, key, F2]

theorem artin_of_placeIso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (σ : Weil h) (σ' : Weil h') (x : (w.adicCompletion E)ˣ), WeilRel φ σ σ' → art' (Neutral.B1.localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)) = GlobalTheory.HeckeGal.toAb E' Ω' σ' → art (Neutral.B1.localIdele E w x) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hPI art art' ha ha' σ σ' x hW hx
  letI : Algebra E E' := j.toAlgebra
  obtain ⟨ρ, hρc, hρ⟩ := GlobalTheory.T.exists_abelianizedGalois_hom_of_closureIso E Ω E' Ω' φ j hPI.ext
  have key := res_art_eq_art E Ω E' Ω' φ hPI.ext w w' i hPI.cont hPI.loc art art' ha ha' ρ hρc hρ x
  have hσ : ρ (toAb E' Ω' σ') = toAb E Ω σ := hρ σ' σ hW
  rw [← key, hx, hσ]

end GlobalTheory.LocDegOne

end
