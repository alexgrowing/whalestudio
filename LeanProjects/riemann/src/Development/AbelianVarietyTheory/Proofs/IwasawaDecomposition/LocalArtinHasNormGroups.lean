import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionEmbeddingCompatibleClosuresStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocNormGrp

section Norm

open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem valuation_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem valuation_le_of_exponent_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_congr_mem {K : Type} [Field K] [NumberField K] (W : HeightOneSpectrum (𝓞 K))
    (V : Subgroup (W.adicCompletion K)ˣ) (hV : IsOpen (V : Set (W.adicCompletion K)ˣ)) :
    ∃ M : ℕ, ∀ z : Kˣ, W.valuation K ((z : K) - 1) ≤ WithZero.exp (-(M : ℤ)) →
      Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom z ∈ V := by
  have h1 := hV.mem_nhds V.one_mem
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨s, hs, hsV⟩ := h1
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).2 γ.ne_zero
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun z hz => hsV (hγ ?_)⟩
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  have e : ((Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom z : (W.adicCompletion K)ˣ) :
      W.adicCompletion K) - (1 : (W.adicCompletion K)ˣ) = algebraMap K (W.adicCompletion K) ((z : K) - 1) := by simp
  rw [e]
  have e2 : Valued.v (algebraMap K (W.adicCompletion K) ((z : K) - 1)) = W.valuation K ((z : K) - 1) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' W _
  rw [e2]
  refine hz.trans_lt ?_
  rw [← WithZero.exp_log hc0, WithZero.exp_lt_exp, WithZero.log_exp]
  omega

theorem res_art_eq_art_norm (E E' Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Algebra E' Ω] [IsAlgClosure E' Ω] [Algebra E E']
    (hφ : ∀ x, RingEquiv.refl Ω (algebraMap E Ω x) = algebraMap E' Ω (algebraMap E E' x))
    (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E'))
    (hw' : w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal)
    (N : (w'.adicCompletion E')ˣ →* (w.adicCompletion E)ˣ) (hN : Continuous N)
    (hNg : ∀ z : E'ˣ, N (Units.map (algebraMap E' (w'.adicCompletion E')).toMonoidHom z) =
      Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.map (Algebra.norm E (S := E')) z))
    (art : Ideles E →* Gab E Ω) (art' : Ideles E' →* Gab E' Ω) (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    (ρ : Gab E' Ω →* Gab E Ω) (hρc : Continuous ρ)
    (hρ : ∀ (τ : G E' Ω) (σ : G E Ω), (∀ z, RingEquiv.refl Ω (σ z) = τ (RingEquiv.refl Ω z)) →
      ρ (toAb E' Ω τ) = toAb E Ω σ)
    (x : (w'.adicCompletion E')ˣ) :
    ρ (art' (localIdele E' w' x)) = art (localIdele E w (N x)) := by
  classical
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
  suffices h : χ (ρ (art' (localIdele E' w' x))) = χ (art (localIdele E w (N x))) by
    have h2 : χ (ρ (art' (localIdele E' w' x)) / art (localIdele E w (N x))) = 1 := by
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

  let f1 : (w'.adicCompletion E')ˣ →* Gab E Ω ⧸ U := ψ1.comp (localIdele E' w')
  let f2 : (w'.adicCompletion E')ˣ →* Gab E Ω ⧸ U := ψ2.comp ((localIdele E w).comp N)
  have hf1 : IsOpen (f1.ker : Set (w'.adicCompletion E')ˣ) := by
    have e : (f1.ker : Set (w'.adicCompletion E')ˣ) = (localIdele E' w') ⁻¹' (ψ1.ker : Set (Ideles E')) := by
      ext y; simp only [f1, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho1.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele w')
  have hf2 : IsOpen (f2.ker : Set (w'.adicCompletion E')ˣ) := by
    have e : (f2.ker : Set (w'.adicCompletion E')ˣ) = ((localIdele E w).comp N) ⁻¹' (ψ2.ker : Set (Ideles E)) := by
      ext y; simp only [f2, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho2.preimage ((GlobalTheory.Mem.UnrAe.continuous_localIdele w).comp hN)
  show f1 x = f2 x
  refine GlobalTheory.units_adicCompletion_hom_ext E' w' _ f1 f2 hf1 hf2 (fun y => ?_) x
  let NK : E'ˣ →* Eˣ := Units.map (Algebra.norm E (S := E'))
  have hf2g : ∀ z : E'ˣ, f2 (Units.map (algebraMap E' (w'.adicCompletion E')).toMonoidHom z) =
      ψ2 (locUnit E w (NK z)) := fun z => by
    simp only [f2, MonoidHom.comp_apply, locUnit_apply, hNg, NK]
  rw [hf2g]
  change ψ1 (locUnit E' w' y) = _

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E ψ2.ker ho2 {w}
  have hwSE : w ∈ SE := hvS (Finset.mem_singleton_self w)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.PlacesOver.places_over_finset E E' SE
  have hWT : w' ∈ TSK := (hTSK w').mpr ⟨w, hwSE, hw'⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E' ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' v' ME
  obtain ⟨ML, hML⟩ := exists_congr_mem w' f2.ker hf2
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (w'.valuation E' (y : E'))).natAbs
  let P0 : ℕ := MK + M'' + ML + 1
  obtain ⟨a, hap, hapos⟩ := GlobalTheory.FinPlaceApproxPos.approxpos_target E' TSK (fun u => if u = w' then (y : E') else 1) (P0 + m)
  have haW : w'.valuation E' (a - y) ≤ WithZero.exp (-((P0 : ℤ) + m)) := by
    have := hap w' hWT
    rw [if_pos rfl] at this
    exact valuation_le_of_exponent_le w' this (by push_cast; omega)
  have hz : w'.valuation E' (a / y - 1) ≤ WithZero.exp (-(P0 : ℤ)) :=
    valuation_div_sub_one_le w' y.ne_zero le_rfl haW
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
    exact valuation_le_of_exponent_le u this (by push_cast; omega)

  have F1 : ψ1 (locUnit E' w' au) = ψ1 (locUnit E' w' y) := by
    have hm : locUnit E' w' zu ∈ ψ1.ker := hSKc w' (hTS hWT) zu (by
      rw [hzu]; exact valuation_le_of_exponent_le w' hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E w (NK au)) = ψ2 (locUnit E w (NK y)) := by
    have hm : ψ2 (locUnit E w (NK zu)) = 1 := by
      rw [← hf2g]
      exact hML zu (by rw [hzu]; exact valuation_le_of_exponent_le w' hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, hm, mul_one]

  have F3 : ∀ u ∈ TSK, u ≠ w' → ψ1 (locUnit E' u au) = 1 := fun u hu hne =>
    MonoidHom.mem_ker.mp (hSKc u (hTS hu) au (valuation_le_of_exponent_le u (hoth u hu hne) (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ w → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : E') fun u hu => ?_
    have huT : u ∈ TSK := (hTSK u).mpr ⟨v', hv', hu⟩
    have huW : u ≠ w' := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hu.symm.trans hw'))
    exact valuation_le_of_exponent_le u (hoth u huT huW) (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ z, IsUnitAt v' z → ψ2 (localIdele E v' z) = 1 := fun v' hv' z hz =>
    MonoidHom.mem_ker.mp (hSu v' hv' z hz)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (u : HeightOneSpectrum (𝓞 E'))
      (hu : u.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v'.asIdeal) =>
    GlobalTheory.T.artin_transport_algClosure_equiv E Ω E' Ω (RingEquiv.refl Ω) hφ art art' ha ha' ρ hρ (Gab E Ω ⧸ U) χ v' u hu (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E E' (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' u hu => (hchi v' hv' u hu).1) (fun v' hv' u hu => (hchi v' hv' u hu).2) au

  have hPK : (∏ u ∈ TK, ψ1 (locUnit E' u au)) * ψ1 (locUnit E' w' au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK u).mp h2
      exact hTK1 u h1 v' hv' e
    have h := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E' (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) (fun z hz => by simp [ψ1, hiK z hz])
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
    have h := GlobalTheory.ProdLocUnitPos.prod_locUnit_eq_one_of_pos E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (fun z hz => by simp [ψ2, hiE z hz])
      (NK au) (fun φ => GlobalTheory.norm_pos_of_totallyPositive E E' a ha0 hapos φ) (TE ∪ SE) fun v' hv' => by
        rw [Finset.mem_union, not_or] at hv'
        exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem w hwSE F4] at h
    exact h
  have key : ψ1 (locUnit E' w' au) = ψ2 (locUnit E w (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  rw [← F1, key, F2]

theorem art_norm_eq_res : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (artK : Neutral.B1.Ideles K →* GlobalTheory.HeckeGal.Gab K Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin artK → ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)), W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ (N : (W.adicCompletion K)ˣ →* (v.adicCompletion E)ˣ), Continuous N → (∀ z : Kˣ, N (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom z) = Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom (Units.map (Algebra.norm E (S := K)) z)) → ∀ (y : (W.adicCompletion K)ˣ) (τ : G K Ω) (σ : G E Ω), (∀ z, σ z = τ z) → artK (Neutral.B1.localIdele K W y) = GlobalTheory.HeckeGal.toAb K Ω τ → art (Neutral.B1.localIdele E v (N y)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ art artK ha haK v W hW N hN hNg y τ σ hσ hy
  have hφ : ∀ x, RingEquiv.refl Ω (algebraMap E Ω x) = algebraMap K Ω (algebraMap E K x) :=
    fun x => IsScalarTower.algebraMap_apply E K Ω x
  obtain ⟨ρ, hρc, hρ⟩ := GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv E Ω K Ω (RingEquiv.refl Ω) (algebraMap E K) hφ
  rw [← res_art_eq_art_norm E K Ω hφ v W hW N hN hNg art artK ha haK ρ hρc hρ y, hy]
  exact hρ τ σ hσ

end Norm

theorem art_range_weil : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ τ : Weil h, ∃ y : (w.adicCompletion E)ˣ, art (Neutral.B1.localIdele E w y) = GlobalTheory.HeckeGal.toAb E Ω τ) ∧ ∀ y : (w.adicCompletion E)ˣ, ∃ τ : Weil h, art (Neutral.B1.localIdele E w y) = GlobalTheory.HeckeGal.toAb E Ω τ := by
  intro E Ω _ _ _ _ _ A w h art ha
  constructor
  · intro τ
    obtain ⟨ϖ, -, hϖ⟩ := (ha.frob w A h _).2 ⟨_, isFrob_frob (h := h), rfl⟩
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) τ
    obtain ⟨u, -, hu⟩ := (ha.ine w A h _).2 ⟨t, t.2, rfl⟩
    refine ⟨ϖ ^ (-deg τ) * u, ?_⟩
    rw [map_mul, map_mul, map_zpow, map_zpow, hϖ, hu, _root_.map_inv, _root_.inv_zpow', neg_neg, ← map_zpow, ← map_mul]
    conv_rhs => rw [ht]
    rfl
  · intro y
    obtain ⟨k, hk⟩ := Formalism.L2.Host.exists_unif w
    set ϖ := Formalism.L2.Host.atFin w k
    obtain ⟨φ, hφ, hϖ⟩ := (ha.frob w A h _).1 ⟨ϖ, hk, rfl⟩
    have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    let n : ℤ := WithZero.log (Valued.v (y : w.adicCompletion E))
    have hu : Formalism.L2.Host.IsUnitAt w (y * ϖ ^ n) := by
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hk
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hk, ← WithZero.exp_log hy0,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp [n]
    obtain ⟨t, ht, hte⟩ := (ha.ine w A h _).1 ⟨_, hu, rfl⟩
    refine ⟨⟨t, Ine_le_Weil h ht⟩ * ⟨φ, mem_Weil_of_isFrob h hφ⟩ ^ n, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, map_mul, map_zpow, hte, map_mul, map_mul, map_zpow, map_zpow, ← hϖ,
      _root_.map_inv, _root_.inv_zpow, inv_mul_cancel_right]

theorem exists_fixing_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), Neutral.B1.IsFiniteAbelian (w.adicCompletion E) L → ∃ H : Subgroup (Weil h), H.FiniteIndex ∧ IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} ∧ (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → (σ ∈ H ↔ ∀ z ∈ L, g z = z)) ∧ ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → a.ker ≤ H := by
  intro E Ω _ _ _ _ _ A w h ι hι L hL
  obtain ⟨θ, hθ, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
  haveI := hL.finiteDimensional
  haveI := hL.isGalois
  let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
  let r : Weil h →* (L ≃ₐ[w.adicCompletion E] L) := (AlgEquiv.restrictNormalHom L).comp ψ
  have hr : ∀ σ, σ ∈ r.ker ↔ ψ σ ∈ L.fixingSubgroup := fun σ => by
    rw [← IntermediateField.restrictNormalHom_ker]; rfl
  have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ r.ker} := by
    have e : {σ : Ine (F := E) A | ineIncl h σ ∈ r.ker} =
        (fun σ : Ine (F := E) A => θ (Subgroup.inclusion (Ine_le_Dec A) σ)) ⁻¹' (L.fixingSubgroup : Set (GalLoc w)) :=
      Set.ext fun σ => hr _
    rw [e]
    exact L.fixingSubgroup_isOpen.preimage (hθ.comp (continuous_subtype_val.subtype_mk _))
  refine ⟨r.ker, inferInstance, hop, fun σ g hg => ?_, fun a ha σ hσ => ?_⟩
  · have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
      have := hl (θ.symm g)
      rw [θ.apply_symm_apply] at this
      exact Subtype.ext (this.eq hg)
    have e2 : ψ σ = g := by
      show θ _ = g
      rw [← e, θ.apply_symm_apply]
    rw [hr, e2, IntermediateField.mem_fixingSubgroup_iff]
  · letI : CommGroup (L ≃ₐ[w.adicCompletion E] L) :=
      { (inferInstance : Group (L ≃ₐ[w.adicCompletion E] L)) with mul_comm := hL.comm }
    by_contra hne
    obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[w.adicCompletion E] L) ℂ
      (a := r σ) hne
    have hs : WeilDeligne.IsSmooth (χ.comp r) := by
      refine Subgroup.isOpen_mono (H₁ := r.ker.comap (ineIncl h)) (H₂ := (χ.comp r).ker.comap (ineIncl h))
        (Subgroup.comap_mono fun s hs => ?_) hop
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one]
    obtain ⟨χ', -, e⟩ := ha.factor _ hs
    apply hχ
    have : χ (r σ) = χ' (a σ) := DFunLike.congr_fun e σ
    rw [MonoidHom.mem_ker.1 hσ, map_one] at this
    exact this

theorem exists_place {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] [Algebra E L] [IsScalarTower E L Ω] : ∃ v : HeightOneSpectrum (𝓞 L), IsPlaceOver A v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := fun x => by
    have h1 : IsIntegral ℤ (algebraMap L Ω x) := x.2.map (algebraMap L Ω).toIntAlgHom
    have h2 : IsIntegral A (algebraMap L Ω x) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hy ▸ y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  have hf : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω x) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h0 => ?_⟩, hf⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have h3 := (hf (algebraMap (𝓞 E) (𝓞 L) x)).1 (by
    have := (h x).2 hx
    rwa [IsScalarTower.algebraMap_apply E L Ω] at this)
  rw [h0, Ideal.mem_bot] at h3
  exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L) (by simpa using h3))

theorem hasNormGroups_of_isLocalArtin : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocEmb A w ι → IsLocalArtin h a → HasNormGroups h ι a := by
  intro hG hC E Ω _ _ _ _ _ A w h ι a hι ha L hL σ g hg
  obtain ⟨H, hfin, hop, hH, hker⟩ := exists_fixing_subgroup E Ω A w h ι hι L hL
  obtain ⟨K, hK, hloc, hHK⟩ := GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup E Ω A w h H hfin hop
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  obtain ⟨W, h'⟩ := exists_place h K
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb K Ω A W h'
  obtain ⟨f, b, hf, hb1, hb2, hfE, -, -, -, hNc, hNg⟩ := GlobalTheory.T.local_embeddings_tower_compatible E K Ω A w W h h' hloc ι ι' hι hι'
  letI := f.toAlgebra
  have hLeq := GlobalTheory.T.local_embedding_weil_action_finite_extension E K Ω A w h ι hι L hL.finiteDimensional fun s g' hg' => (hH s g' hg').symm.trans (hHK s)
  have hN := GlobalTheory.T.completion_embedding_compatible_closures E K w W (fun x : K => ι (algebraMap K Ω x)) f b hf hb1
    (fun x => by rw [hb2, ι'.commutes, IsScalarTower.algebraMap_apply K (W.adicCompletion K)]) hfE
  rw [← hLeq] at hN
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨artK, hartK⟩ := hG K Ω
  let N := Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)
  have key := art_norm_eq_res E K Ω art artK hart hartK w W (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h') N
    (Continuous.units_map _ hNc) fun z => Units.ext (hNg z)
  have key' : ∀ (y : (W.adicCompletion K)ˣ) (τ : Weil h') (s : Weil h), (∀ z, (s : G E Ω) z = (τ : G K Ω) z) →
      artK (Neutral.B1.localIdele K W y) = GlobalTheory.HeckeGal.toAb K Ω τ → N y = a s := fun y τ s hs hy =>
    GlobalTheory.T.globalArtin_localIdele_injective hC E Ω art hart w ((key y τ s hs hy).trans (ha.glob art hart s).symm)
  obtain ⟨h1, h2⟩ := art_range_weil K Ω A W h' artK hartK
  rw [← hH σ g hg, hN]
  constructor
  · intro hσ
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_weil_of_fixes' E K Ω A w W h h' σ ((hHK σ).1 hσ)
    obtain ⟨y, hy⟩ := h1 τ
    exact ⟨y, key' y τ σ hτ hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨τ, hτ⟩ := h2 y
    let s := GlobalTheory.WeilRestrict.resWeil h h' τ
    have hs : s ∈ H := (hHK s).2 fun x => (τ : G K Ω).commutes x
    have e : a s = a σ := (key' y τ s (fun _ => rfl) hτ).symm.trans hy
    have hm : s⁻¹ * σ ∈ H := hker a ha (by rw [MonoidHom.mem_ker, map_mul, _root_.map_inv, e, inv_mul_cancel])
    simpa using H.mul_mem hs hm

end GlobalTheory.LocNormGrp

end
