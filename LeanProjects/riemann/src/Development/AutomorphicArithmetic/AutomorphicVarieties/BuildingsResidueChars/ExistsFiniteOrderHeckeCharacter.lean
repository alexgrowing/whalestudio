import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem pow_one_of_profinite {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (φ : G →* ℂˣ) (hφ : Continuous φ) : ∃ n : ℕ, 0 < n ∧ ∀ g, φ g ^ n = 1 := by
  have ho : IsOpen (φ.ker : Set G) := by
    refine isOpen_ker_of_noSmallSubgroups (fun W hW => ?_) GroundTheory.Global.Complex.units_noSmallSubgroups φ hφ
    obtain ⟨U, hU, hUo, h1⟩ := mem_nhds_iff.1 hW
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1
    exact ⟨H.toOpenSubgroup, hH.trans hU⟩
  haveI : Finite (G ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨φ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun g => ?_⟩
  rw [← map_pow]
  exact Subgroup.pow_index_mem φ.ker g

private theorem exists_circle {C G : Type} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (φ : G →* ℂˣ) (hφ : Continuous φ) (p : C →* G) (hp : Continuous p) :
    ∃ c : C →ₜ* Circle, IsOfFinOrder c ∧ ∀ x, (c x : ℂ) = (φ (p x) : ℂ) := by
  obtain ⟨n, hn, h⟩ := pow_one_of_profinite φ hφ
  have h' : ∀ g, (φ g : ℂ) ^ n = 1 := fun g => by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hu : ∀ g, ‖(φ g : ℂ)‖ = 1 := fun g => by
    have := congrArg norm (h' g)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  let c : C →ₜ* Circle :=
    { toFun := fun x => ⟨(φ (p x) : ℂ), by simp [Submonoid.unitSphere, hu]⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [map_mul, Units.val_mul]
        rfl
      continuous_toFun := by
        refine Continuous.subtype_mk (f := fun x => (φ (p x) : ℂ)) ?_ _
        exact Units.continuous_val.comp (hφ.comp hp) }
  refine ⟨c, isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩, fun _ => rfl⟩
  ext x
  rw [ContinuousMonoidHom.pow_apply, Circle.coe_pow]
  exact h' _

open RationalIdeles in
theorem UpperTheory.exists_finite_order_hecke_character :
    ∀ χ : HChar ℚ, ∃ c : HeckeCharacter ℚ, IsOfFinOrder c ∧ ∀ u : Ad3.Pl, IsUnram (χ.loc u * (localChar c u)⁻¹) := by
  intro χ
  haveI : ∀ p : Nat.Primes, Fact p.1.Prime := fun p => ⟨p.2⟩
  haveI : TotallyDisconnectedSpace (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 ℚ), TotallyDisconnectedSpace (v.adicCompletionIntegers ℚ)ˣ := fun v => by
      haveI : TotallyDisconnectedSpace (v.adicCompletion ℚ) := inferInstance
      haveI : TotallyDisconnectedSpace (v.adicCompletionIntegers ℚ) := inferInstance
      exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
        (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
    infer_instance
  let s : (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) →* IdeleGroup ℚ :=
    positiveSubgroup.subtype.comp (positiveSubgroupEquiv.symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _))
  have hs : Continuous s :=
    continuous_subtype_val.comp (positiveSubgroupEquiv.symm.continuous.comp (continuous_const.prodMk continuous_id))
  let p : IdeleClassGroup ℚ →* (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :=
    (MonoidHom.snd _ _).comp (positiveSubgroupEquiv.toMulEquiv.toMonoidHom.comp
      positiveSubgroupEquivIdeleClassGroup.symm.toMulEquiv.toMonoidHom)
  have hp : Continuous p :=
    continuous_snd.comp (positiveSubgroupEquiv.continuous.comp positiveSubgroupEquivIdeleClassGroup.symm.continuous)
  have hsp : ∀ y : positiveSubgroup, realPart (y : IdeleGroup ℚ) = 1 → s (p (IdeleClassGroup.mk ℚ y)) = y := by
    intro y hy
    have h1 : p (IdeleClassGroup.mk ℚ y) = (positiveSubgroupEquiv y).2 := by
      rw [← positiveSubgroupEquivIdeleClassGroup_apply]
      exact congrArg (fun z => (positiveSubgroupEquiv z).2) (positiveSubgroupEquivIdeleClassGroup.symm_apply_apply y)
    have h2 : positiveSubgroupEquiv y = (1, (positiveSubgroupEquiv y).2) := Prod.ext (Subtype.ext hy) rfl
    rw [h1]
    change ((positiveSubgroupEquiv.symm (1, (positiveSubgroupEquiv y).2) : positiveSubgroup) : IdeleGroup ℚ) = y
    rw [← h2, ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨c, hc, hcx⟩ := exists_circle ((χ.1 : IdeleGroup ℚ →* ℂˣ).comp s) (χ.2.1.comp hs) p hp
  refine ⟨c, hc, fun u x hx => ?_⟩
  have hmem : x ∈ (Submonoid.ofClass (u.adicCompletionIntegers ℚ)).units := by
    have hv : Valued.v (x : u.adicCompletion ℚ) = 1 := by
      have he : (ValuativeRel.valuation (u.adicCompletion ℚ)).IsEquiv (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))) := by
        haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))
        exact ValuativeRel.isEquiv _ _
      exact he.eq_one_iff_eq_one.1 hx
    refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have hy := DirichletHecke.finiteEmbedding_mem_positiveSubgroup (DirichletHecke.norm_padicRingEquiv_eq_one hmem)
  have h3 := hsp ⟨_, hy⟩ (DirichletHecke.realPart_finiteEmbedding u x)
  have h4 := hcx (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding u x))
  rw [MonoidHom.comp_apply, h3] at h4
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  exact Units.ext h4.symm
