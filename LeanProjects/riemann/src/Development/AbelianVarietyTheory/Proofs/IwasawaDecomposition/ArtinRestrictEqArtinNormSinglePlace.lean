import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrullStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnitsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTargetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplexStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  intro E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ
  classical
  haveI : IsTotallyComplex K := GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex E K
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let r : G K Ω →* Gab E Ω := (toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)
  have hr : Continuous r := QuotientGroup.continuous_mk.comp (GlobalTheory.T.continuous_restrictScalarsHom' E Ω K)
  let ρ : Gab K Ω →* Gab E Ω := liftAb r hr
  have hρ : ∀ σ : G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E) := fun σ => rfl
  have hρc : Continuous ρ := continuous_liftAb r hr
  let NK : Kˣ →* Eˣ := Units.map (Algebra.norm E (S := K))
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : Kˣ, artK (diagUnits K k) = 1 := fun k => by
    have hk : diagUnits K k ∈ artK.ker := by
      rw [haK.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))
  rw [← hρ, hτ]
  change ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))
  rw [← div_eq_one]
  refine GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by
    have h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1 := by
      rw [map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles K →* Gab E Ω ⧸ U := χ.comp (ρ.comp artK)
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles K)) = (ρ.comp artK) ⁻¹' U := by
    ext x; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext x; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles K)) := by
    rw [hker1]; exact hU.preimage (hρc.comp haK.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units E ψ2.ker ho2 {v}
  have hvSE : v ∈ SE := hvS (Finset.mem_singleton_self v)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.T.exists_finset_places_over_finset_places E K SE
  have hWT : W ∈ TSK := (hTSK W).mpr ⟨v, hvSE, hW⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units K ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.T.norm_close_to_one_of_close_above_place E K v' ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (W.valuation K (y : K))).natAbs
  obtain ⟨a, ha'⟩ := GlobalTheory.T.exists_approx_finite_places_numberField_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)
  have haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m)) := by
    have := ha' W hWT
    rw [if_pos rfl] at this
    exact val_le_of_le W this (by push_cast; omega)
  have hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ)) :=
    val_div_sub_one_le W y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : Kˣ := Units.mk0 a ha0
  let zu : Kˣ := au / y
  have hzu : (zu : K) = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]

  have F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y) := by
    have hm : locUnit K W zu ∈ ψ1.ker := hSKc W (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le W hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y)) := by
    have hm : locUnit E v (NK zu) ∈ ψ2.ker := hSc v hvSE (NK zu) (by
      refine hM' v (zu : K) fun w hw => ?_
      rw [hWu w hw, hzu]
      exact val_le_of_le W hz (by
        have : M' v ≤ M'' := Finset.le_sup hvSE
        push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1 := fun w hw hne => by
    have := ha' w hw
    rw [if_neg hne] at this
    exact MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : K) fun w hw => ?_
    have hwT : w ∈ TSK := (hTSK w).mpr ⟨v', hv', hw⟩
    have hwW : w ≠ W := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hw.symm.trans hW))
    have := ha' w hwT
    rw [if_neg hwW] at this
    exact val_le_of_le w this (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ x, IsUnitAt v' x → ψ2 (localIdele E v' x) = 1 := fun v' hv' x hx =>
    MonoidHom.mem_ker.mp (hSu v' hv' x hx)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K))
      (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) =>
    GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au

  have hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK w).mp h2
      exact hTK1 w h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by
      rw [Finset.mem_union, not_or] at hw
      refine hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by
      rw [Finset.mem_union, not_or] at hv'
      exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4] at h
    exact h
  have key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))
  rw [← F1, key, F2]

end GlobalTheory.NormCompat
