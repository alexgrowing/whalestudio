import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.HopfExpansion

section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem setInt_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → E) (y : G) {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T) (h : ∀ x, x ∈ S ↔ y * x ∈ T) :
    ∫ x in S, f (y * x) ∂m = ∫ x in T, f x ∂m := by
  rw [← integral_indicator hS, ← integral_indicator hT, ← integral_mul_left_eq_self (T.indicator f) y]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((h x).1 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((h x).2 h'))]

private theorem avg (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (u v : H) :
    ∫ j in (J : Set G), ⟪u, π j v⟫_ℂ ∂m = ⟪u, prj W v⟫_ℂ := by
  have hmeas : MeasurableSet (J : Set G) := hJo.measurableSet
  have hint : IntegrableOn (fun j => π j v) (J : Set G) m :=
    (π.continuous_orbit v).continuousOn.integrableOn_compact' hJ hmeas
  have hcl : IsClosed (W : Set H) := by
    have : (W : Set H) = ⋂ j ∈ J, {v | π j v = v} := by
      ext v
      simp [hW]
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (π j).continuous continuous_id
  have hA : (∫ j in (J : Set G), π j v ∂m) ∈ W := by
    rw [hW]
    intro j₀ hj₀
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    have := setInt_shift m (fun j => π j v) j₀ hmeas hmeas (fun x => by
      simp [Subgroup.mul_mem_cancel_left J hj₀])
    simpa [UnitaryRep.map_mul_apply] using this
  have hin : ∀ w ∈ W, ⟪w, ∫ j in (J : Set G), π j v ∂m⟫_ℂ = ⟪w, v⟫_ℂ := by
    intro w hw
    rw [← integral_inner hint w]
    have : ∀ j ∈ (J : Set G), ⟪w, π j v⟫_ℂ = ⟪w, v⟫_ℂ := by
      intro j hj
      rw [UnitaryRep.inner_map_right, (hW w).1 hw _ (J.inv_mem hj)]
    rw [setIntegral_congr_fun hmeas this]
    simp [Measure.real, hm]
  have hP : prj W v = ∫ j in (J : Set G), π j v ∂m := by
    change W.topologicalClosure.starProjection v = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hA) ?_
    intro w hw
    rw [hcl.submodule_topologicalClosure_eq] at hw
    rw [inner_sub_left, ← inner_conj_symm, ← inner_conj_symm _ w, hin w hw]
    simp
  rw [hP, integral_inner hint u]

private theorem main (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (x : G) (u v : H) :
    ⟪u, (∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}, π c.out) (prj W v)⟫_ℂ =
      ∫ g, Set.indicator {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} 1 g * ⟪u, π g v⟫_ℂ ∂m := by
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJo
  set S : Set (G ⧸ J) := {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} with hSdef
  have hSfin : S.Finite := by
    have e : S = (fun k : G => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hJ.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete
  set D : Set G := {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} with hDdef
  let P : G ⧸ J → Set G := fun c => QuotientGroup.mk ⁻¹' {c}
  have hPo : ∀ c, IsOpen (P c) := fun c => (isOpen_discrete {c}).preimage QuotientGroup.continuous_mk
  have hPmem : ∀ (c : G ⧸ J) (h : G), h ∈ (J : Set G) ↔ c.out * h ∈ P c := by
    intro c h
    have : (QuotientGroup.mk (c.out * h) : G ⧸ J) = c ↔ h ∈ J := by
      conv_lhs => rhs; rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simp
    exact this.symm
  have hD : D = ⋃ c ∈ hSfin.toFinset, P c := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨QuotientGroup.mk (a * x), ⟨a, ha, rfl⟩, ?_⟩
      change (QuotientGroup.mk (a * x * b) : G ⧸ J) = QuotientGroup.mk (a * x)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using J.inv_mem hb
    · rintro ⟨c, ⟨k, hk, rfl⟩, hg⟩
      have hg' : (QuotientGroup.mk g : G ⧸ J) = QuotientGroup.mk (k * x) := hg
      have := QuotientGroup.eq.1 hg'.symm
      exact ⟨k, hk, _, this, by group⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact Finset.measurableSet_biUnion _ fun c _ => (hPo c).measurableSet
  have hcont : Continuous fun g => ⟪u, π g v⟫_ℂ := continuous_const.inner (π.continuous_orbit v)
  have hPint : ∀ c, IntegrableOn (fun g => ⟪u, π g v⟫_ℂ) (P c) m := by
    intro c
    have e : P c = (fun h => c.out * h) '' (J : Set G) := by
      ext g
      constructor
      · intro hg
        refine ⟨c.out⁻¹ * g, (hPmem c _).2 (by simpa using hg), by simp⟩
      · rintro ⟨h, hh, rfl⟩
        exact (hPmem c h).1 hh
    have hc : IsCompact (P c) := by
      rw [e]
      exact hJ.image (continuous_const.mul continuous_id)
    exact hcont.continuousOn.integrableOn_compact' hc (hPo c).measurableSet
  have hind : (fun g => D.indicator (1 : G → ℂ) g * ⟪u, π g v⟫_ℂ) = D.indicator fun g => ⟪u, π g v⟫_ℂ := by
    ext g
    by_cases hg : g ∈ D <;> simp [hg]
  rw [hind, integral_indicator hDm, hD, integral_biUnion_finset _ (fun c _ => (hPo c).measurableSet) ?_
    (fun c _ => hPint c), finsum_mem_eq_finite_toFinset_sum _ hSfin, ContinuousLinearMap.sum_apply, inner_sum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← setInt_shift m (fun g => ⟪u, π g v⟫_ℂ) c.out hJo.measurableSet (hPo c).measurableSet (hPmem c)]
    rw [UnitaryRep.inner_map_right, ← avg π m J hJ hJo hm W hW]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [UnitaryRep.map_mul_apply]
    exact (UnitaryRep.inner_map_right π _ _ _).symm
  · intro c _ d _ hcd
    refine Set.disjoint_left.2 fun g hg hg' => hcd ?_
    exact (hg : _ = c).symm.trans hg'

end
end UpperTheory.ConvolutionTheory.C.HopfExpansion

theorem UpperTheory.ConvolutionTheory.C.hopOloc :
    UpperTheory.ConvolutionTheory.C.HopOloc := by
  intro K _ _ n μ _ w _ _ m _ J x hJ hm u v
  let φ : Gw n w →* normOneGL K n := (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)
  have hφ : Continuous φ := MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne K n) μ).compHom φ hφ
  have hπ : ∀ x, π x = rhoL μ w x := fun _ => rfl
  have hW : ∀ v, v ∈ fixL μ w J ↔ ∀ j ∈ J, π j v = v := by
    intro v
    simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
    constructor
    · intro h j hj
      simpa [hπ, rhoL] using h _ ⟨j, hj, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      simpa [hπ, rhoL] using h j hj
  exact HopfExpansion.main π m J hJ.1 hJ.2 hm (fixL μ w J) hW x u v
