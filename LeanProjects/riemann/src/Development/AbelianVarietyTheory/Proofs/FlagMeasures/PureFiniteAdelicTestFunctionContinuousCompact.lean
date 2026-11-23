import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.PureFinite

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

include b in
theorem continuous_projV_fin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X) := by
  have h : Continuous (evalV F v) :=
    RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  haveI : IsTopologicalRing (Af F) := inferInstance
  have h2 : Continuous (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) :=
    continuous_map_tens b (evalV F v) h
  exact continuous_pi fun a => continuous_pi fun i =>
    h2.comp ((continuous_apply i).comp (continuous_apply a))

theorem projV_add (v : HeightOneSpectrum (𝓞 F)) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X + Y) = projV v X + projV v Y := by
  funext a i
  simp [projV, map_add]

theorem latV_add (v : HeightOneSpectrum (𝓞 F)) {Y Z : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV b v) (hZ : Z ∈ latV b v) : Y + Z ∈ latV b v := by
  intro a i k
  simp only [Pi.add_apply, map_add, Finsupp.add_apply]
  exact add_mem (hY a i k) (hZ a i k)

variable (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem continuous_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hev : (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v Y)) =ᶠ[nhds X]
      fun Y => ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    filter_upwards [hUo.mem_nhds hXU] with Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  exact (continuous_finset_prod _ fun v _ =>
    (hSB v).1.continuous.comp (continuous_projV_fin b v)).continuousAt

theorem hasCompactSupport_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    HasCompactSupport (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  let D : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun i j k v =>
      ((fun Z : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Z i j) k) '' tsupport (Φv v)) ∪
        (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i j k v, IsCompact (D i j k v) := fun i j k v =>
    ((hSB v).2.isCompact.image ((continuous_crd b (Fv F v) k).comp
      ((continuous_apply j).comp (continuous_apply i)))).union
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i j k, ∀ᶠ v in Filter.cofinite,
      D i j k v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i j k
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (Φv v) ⊆ latV b v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (isClopen_latV b v n M).isClosed
    exact hsub hZ i j k
  let Bf : Fin n → Fin M → Fin d → Set (Af F) := fun i j k => {x | ∀ v, x v ∈ D i j k v}
  have hBf : ∀ i j k, IsCompact (Bf i j k) := fun i j k => isCompact_finBox (hD i j k) (hDe i j k)
  let Box : Set (Fin n → Fin M → Fin d → Af F) :=
    Set.pi univ fun i => Set.pi univ fun j => Set.pi univ fun k => Bf i j k
  have hbox : IsCompact Box := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_univ_pi fun k => hBf i j k
  let L : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  refine HasCompactSupport.intro (hbox.image hL) fun X hX => ?_
  by_contra h
  apply hX
  have hv := factor_ne_zero b Φv hae X h
  refine ⟨fun i j k => crd b (Af F) (X i j) k, ?_, ?_⟩
  · simp only [Box, Set.mem_pi, Set.mem_univ, true_implies]
    intro i j k v
    refine Or.inl ⟨projV v X, subset_tsupport _ (hv v), ?_⟩
    exact crd_projV b X v i j k
  · funext i j
    exact (eq_sum_crd b (Af F) (X i j)).symm

end GlobalTheory.PureFinite

namespace GlobalTheory

theorem isPureFin_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  intro F E _ _ _ _ _ d M n b Φf Φv h
  obtain ⟨hSB, hae, hprod⟩ := h
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  subst e
  exact ⟨PureFinite.continuous_finprod b Φv hSB hae, PureFinite.hasCompactSupport_finprod b Φv hSB hae⟩

end GlobalTheory
