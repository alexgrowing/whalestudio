import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.PlaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalFieldStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open PositivityTheory.Rg.Tf.Geo
open scoped Classical NNReal ENNReal Pointwise

section Local

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k']
  [IsModuleTopology k k']

private theorem cont_norm : Continuous (Algebra.norm k : k' → k) := by
  let b := Module.finBasis k k'
  have e : (Algebra.norm k : k' → k) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [e]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have hl : Continuous ((b.coord i).comp (LinearMap.mulRight k (b j))) :=
    IsModuleTopology.continuous_of_linearMap _
  refine hl.congr fun x => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul]

private theorem nabs_norm [CharZero k] (x : k'ˣ) :
    GlobalTheory.SplitWeil.nabs k (Units.map (Algebra.norm k : k' →* k) x) = GlobalTheory.SplitWeil.nabs k' x := by
  borelize k'
  unfold GlobalTheory.SplitWeil.nabs
  congr 1
  symm
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : k')
  let μ : Measure k' := Measure.addHaar
  have h0 : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨0, mem_interior_iff_mem_nhds.mpr hK0⟩).ne'
  have hf : μ K ≠ ∞ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hf ?_
  let T : k' ≃ₗ[k] k' := DistribMulAction.toLinearEquiv k k' x⁻¹
  have hT := GlobalTheory.T.map_linearEquiv_addHaar_localField k k' μ T
  have hdet : LinearEquiv.det T = (Units.map (Algebra.norm k : k' →* k) x)⁻¹ := by
    ext
    simp only [LinearEquiv.coe_det, T, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_apply,
      Units.val_inv_eq_inv_val, map_inv₀]
    have hl : (↑(DistribMulAction.toLinearEquiv k k' x⁻¹) : k' →ₗ[k] k') =
        LinearMap.mul k k' ↑x⁻¹ := by
      ext y
      simp [Units.smul_def]
    rw [hl]
    apply eq_inv_of_mul_eq_one_left
    rw [← LinearMap.det_comp]
    have hc : (LinearMap.mul k k' ↑x⁻¹).comp (Algebra.lmul k k' ↑x) = LinearMap.id := by
      ext y
      simp
    rw [hc, LinearMap.det_id]
  have hm : MeasurableSet K := hK.isClosed.measurableSet
  have hTc : Continuous T := IsModuleTopology.continuous_of_linearMap (T : k' →ₗ[k] k')
  have e : Measure.map T μ K = (((distribHaarChar k) (LinearEquiv.det T))⁻¹ • μ) K := by
    rw [hT]
  rw [Measure.map_apply hTc.measurable hm, hdet, map_inv, inv_inv] at e
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  rw [← e]
  congr 1
  ext y
  simp [T, Set.mem_smul_set_iff_inv_smul_mem]

private theorem prod_aut [IsGalois k k'] {M : Type*} [CommMonoid M] (s : k' ≃ₐ[k] k') (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    (f : (k' ≃ₐ[k] k') → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank k k'), f (s ^ i) := by
  have ho : orderOf s = Module.finrank k k' :=
    (orderOf_eq_card_of_forall_mem_zpowers hs).trans (IsGalois.card_aut_eq_finrank k k')
  calc ∏ τ, f τ = ∏ τ ∈ (Finset.range (orderOf s)).image (fun i => s ^ i), f τ := by
        rw [IsCyclic.image_range_orderOf hs]
    _ = ∏ i ∈ Finset.range (orderOf s), f (s ^ i) :=
        Finset.prod_image (fun i hi j hj h =>
          pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) h)
    _ = _ := by rw [ho]

private theorem iter_aut (s : k' ≃ₐ[k] k') (i : ℕ) (x : k') :
    (⇑(s : k' ≃+* k'))^[i] x = (s ^ i) x := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]
    rfl

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  subst h
  have ev : ∀ (u : HeightOneSpectrum (𝓞 E)) (x : E),
      Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
    fun u x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have key : ∀ x : E, Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    rw [galEquiv_algebraMap, ev, ev]
    exact valuation_smul σ w x
  by_cases hy : y = 0
  · simp [hy]
  have hy' : galEquiv v σ w (σ • w) rfl y ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy)
  have h2 := (continuous_galEquiv v σ w (σ • w) rfl).continuousAt.preimage_mem_nhds
    (Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy'))
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap E w).inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : Valued.v (algebraMap E (w.adicCompletion E) x) = Valued.v y := hx.1
  have e2 : Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (galEquiv v σ w (σ • w) rfl y) := hx.2
  rw [← e2, key, e1]

private theorem galFin_eq (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hfix : w.1 = σ • w.1)
    (y : CompletionsOver E v) : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [galFin, galOf, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgEquiv.symm_apply_apply]
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul]
    simp only [Pi.mul_apply, map_mul, Pi.algebraMap_apply, AlgHom.id_apply, AlgEquiv.commutes,
      galEquiv_algebraMap]
    rfl
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply] at ha hb ⊢
    rw [ha, hb]

end Global

open scoped Valued in
theorem UpperTheory.Gal.Join.locGal :
    UpperTheory.Gal.Join.LocGal := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hns
  obtain ⟨-, -, -, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  have hw : ∀ u : PlacesOver E v, u = w := huniq v hns w
  obtain ⟨A, hval, hfin, hgal, s, hs, hrk, hinc, hgf, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  have hA : A = algebraCompletion v w.1 := Algebra.algebra_ext _ _ fun x => (hinc x).symm
  subst hA
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have hse : ∀ z, s z = galEquiv v σ w.1 w.1 hfix z := fun z => by
    have h1 := hgf (Pi.single w z)
    rw [galFin_eq σ w hfix, Pi.single_eq_same] at h1
    exact h1.symm
  have hvs : ∀ z, Valued.v (s z) = Valued.v z := fun z => by
    rw [hse]
    exact val_gal v σ w.1 w.1 hfix z
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : IsModuleTopology (v.adicCompletion F) (w.1.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  refine ⟨(s : _ ≃+* _), Units.map (Algebra.norm (v.adicCompletion F) : w.1.adicCompletion E →* _), fun n g => ?_,
    ⟨⟨fun x => ?_, ?_, fun x => ?_⟩, fun x => ?_, ?_, fun x => ?_⟩, fun x => rfl⟩
  · exact Units.ext (Matrix.ext fun a b => hgf _)
  · exact le_antisymm ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).le)
      ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).ge)
  · exact hp.pos
  · rw [iter_aut, ← hrk, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  · change algebraMap _ _ (Algebra.norm (v.adicCompletion F) (x : w.1.adicCompletion E)) = _
    rw [Algebra.norm_eq_prod_automorphisms, prod_aut s hs, hrk]
    exact Finset.prod_congr rfl fun i _ => (iter_aut s i _).symm
  · exact Continuous.units_map _ cont_norm
  · exact nabs_norm x
