import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullySplitPrimesDensityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOfDensityOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
import Development.AutomorphicArithmetic.DivisorFrames.EqTopOfFiniteCircleSup
import Development.AutomorphicArithmetic.DivisorFrames.FiniteAdeleUnitsOpenSubgroupBasis
import Development.AutomorphicArithmetic.DivisorFrames.AdeleUnitsPolarCircles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

private theorem ideles_eq_top (E : Type) [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (M : Subgroup (AdeleRing (𝓞 E) E)ˣ) (hM : IsClosed (M : Set (AdeleRing (𝓞 E) E)ˣ))
    (hχ : ∀ μ : (AdeleRing (𝓞 E) E)ˣ →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1)
    (hr : ∀ r : (AdeleRing (𝓞 E) E)ˣ, (r : AdeleRing (𝓞 E) E).2 = 1 →
      (∀ w : InfinitePlace E,
        (InfinitePlace.Completion.extensionEmbedding w ((r : AdeleRing (𝓞 E) E).1 w)).im = 0) → r ∈ M) :
    M = ⊤ := by
  obtain ⟨c, hc, hpol⟩ := UpperTheory.adele_units_polar_circles E hE
  refine UpperTheory.eq_top_of_finite_circle_sup _ M hM hχ _ Finset.univ c hc fun W hW => ?_
  let q : (AdeleRing (𝓞 E) E)ˣ →* (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  let j : (FiniteAdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hq : Continuous q := Continuous.units_map _ continuous_snd
  have hj : Continuous j := Continuous.units_map _ (Continuous.prodMk_right (1 : InfiniteAdeleRing E))
  obtain ⟨U, hU⟩ := UpperTheory.finiteAdele_units_open_subgroup_basis E (j ⁻¹' W) (hj.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  refine ⟨U.comap q hq, fun o ho => ⟨o * (j (q o))⁻¹, ?_, j (q o), hU ho, by simp⟩⟩
  have h1 : q (o * (j (q o))⁻¹) = 1 := by
    have : q (j (q o)) = q o := Units.ext rfl
    rw [map_mul, map_inv, this, mul_inv_cancel]
  obtain ⟨r, hr1, hr2, hr3⟩ := hpol (o * (j (q o))⁻¹) (congrArg Units.val h1)
  have := mul_mem (Subgroup.mem_sup_left (T := ⨆ i ∈ Finset.univ, (c i).range) (hr r hr1 hr2))
    (Subgroup.mem_sup_right (S := M) (by simpa using hr3 : r⁻¹ * (o * (j (q o))⁻¹) ∈ _))
  rwa [mul_inv_cancel_left] at this

open GlobalTheory.UnitaryHeckeBaseChange in

private theorem cA_eq_of_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (y : AE F E) (h2 : (toAdele F E y).2 = 1)
    (h1 : ∀ w : InfinitePlace E,
      (InfinitePlace.Completion.extensionEmbedding w ((toAdele F E y).1 w)).im = 0) : cA σ y = y := by
  obtain ⟨_, rfl⟩ := (isCMExt_iff σ).1 h
  apply (bijective_toAdele h).1
  refine (toAdele_cA y).trans (Prod.ext (funext fun w => ?_) ?_)
  · apply (InfinitePlace.Completion.extensionEmbedding w).injective
    have hw := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
    have key := congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer
      (g := fun a => InfinitePlace.Completion.extensionEmbedding w
        (@GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap E E _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra a w))
      (h := fun a => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (a w)))
      (hw.comp ((continuous_apply w).comp
        (@continuous_infiniteAdeleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra)))
      (Complex.continuous_conj.comp (hw.comp (continuous_apply w)))
      (funext fun k => by
        have e := congrFun (congrArg Prod.fst (adeleConj_algebraMap (F := F) k)) w
        refine (congrArg (InfinitePlace.Completion.extensionEmbedding w) e).trans ?_
        refine (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ _)).trans ?_
        refine (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj F E w.embedding k).trans ?_
        exact congrArg (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)).symm))
      (toAdele F E y).1
    exact key.trans (Complex.conj_eq_iff_im.2 (h1 w))
  · exact ((congrArg (@GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra) h2).trans (map_one _)).trans h2.symm

open GlobalTheory.UnitaryHeckeBaseChange in

private theorem at_of_local {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) (y : AE F E)
    (hy : toAdele F E y = HeckeValGen.localIdele E P x) : At (evFin F (P.under (𝓞 F))) (y - 1) := by
  intro u hu
  apply (bijective_toAdele h).1
  rw [Algebra.smul_def, map_mul, map_sub, map_one, map_zero, hy]
  erw [toAdele_algebraMap]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change _ * ((1 : InfiniteAdeleRing E) - 1) = 0
    rw [sub_self, mul_zero]
  · by_cases hQ : Q = P
    · subst hQ
      change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E Q (evFin F (Q.under (𝓞 F)) u) * _ = 0
      rw [hu, map_zero, zero_mul]
    · have e := localIdele_ne hQ x
      change _ * (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E) : AdeleRing (𝓞 E) E).2 Q - 1) = 0
      rw [e, sub_self, mul_zero]

private noncomputable def quo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (AE F E)ˣ →* GlobalTheory.NormOneIdele.N1 F E σ :=
  MonoidHom.codRestrict (MonoidHom.id _ / Units.map (cA σ : AE F E →* AE F E)) _ fun y => by
    have hc : ∀ z, cA σ (cA σ z) = z := GlobalTheory.UnitaryHeckeBaseChange.cA_cA h
    rw [GlobalTheory.NormOneIdele.mem_normOneIdeles]
    change ((y : AE F E) * cA σ (y⁻¹ : (AE F E)ˣ)) * cA σ ((y : AE F E) * cA σ (y⁻¹ : (AE F E)ˣ)) = 1
    rw [map_mul, hc]
    calc _ = ((y : AE F E) * (y⁻¹ : (AE F E)ˣ)) * cA σ ((y : AE F E) * (y⁻¹ : (AE F E)ˣ)) := by
          rw [map_mul]; ring
      _ = 1 := by rw [Units.mul_inv, map_one, mul_one]

private theorem quo_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (y : (AE F E)ˣ) :
    ((quo h y : (AE F E)ˣ) : AE F E) = y * cA σ (y⁻¹ : (AE F E)ˣ) := rfl

private theorem continuous_quo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Continuous (quo h) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hc : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ : AE F E →ₐ[AF F] AE F E).toLinearMap
  exact (continuous_id.div' (Continuous.units_map (cA σ : AE F E →* AE F E) hc)).subtype_mk _

private theorem surjective_quo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Surjective (quo h) := by
  intro u
  obtain ⟨_, rfl⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff σ).1 h
  have hs : ∀ z : AE F E, GlobalTheory.AdLat.sg (AdeleRing (𝓞 F) F) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E) z =
      cA (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E : E →ₐ[F] E) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul a b => rfl
  obtain ⟨x, hx⟩ := GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic F E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E) h.2.2.1
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_ne_one F E) (u.1 : AE F E) (by rw [hs]; exact GlobalTheory.NormOneIdele.mem_normOneIdeles.1 u.2)
  rw [hs] at hx
  refine ⟨x, Subtype.ext (Units.ext ?_)⟩
  refine (quo_val h x).trans ((congrArg (· * _) hx).trans ?_)
  rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

theorem _root_.GlobalTheory.T.norm_one_character_split_places : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → IsGalois ℚ E → ∀ (T : Finset (Pl F)) (ψ : GlobalTheory.NormOneIdele.N1 F E σ → ℂ), Continuous ψ →
    (∀ γ z : GlobalTheory.NormOneIdele.N1 F E σ, (∃ e : E, ((γ : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) e) → ψ (γ * z) = ψ z) →
    (∀ v : Pl F, v ∉ T → SplitsFully E v → ∀ z k : GlobalTheory.NormOneIdele.N1 F E σ,
      At (evFin F v) (((k : (AE F E)ˣ) : AE F E) - 1) → ψ (z * k) = ψ z) →
    ∀ z z', ψ z = ψ z' := by
  intro _ F E _ _ _ _ _ σ h hG T ψ hψ hrat hloc
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let Θ := GlobalTheory.UnitaryHeckeBaseChange.ideleEquiv h
  let φ : (AdeleRing (𝓞 E) E)ˣ →* GlobalTheory.NormOneIdele.N1 F E σ := (quo h).comp Θ.symm.toMulEquiv.toMonoidHom
  have hφ : Continuous φ := (continuous_quo h).comp Θ.symm.continuous
  have hΘ : ∀ x, GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (Θ.symm x : (AE F E)ˣ) = x := fun x =>
    congrArg Units.val (Θ.apply_symm_apply x)
  let M : Subgroup (AdeleRing (𝓞 E) E)ˣ :=
    { carrier := {g | ∀ z, ψ (z * φ g) = ψ z}
      one_mem' := fun z => by rw [map_one, mul_one]
      mul_mem' := fun {a b} ha hb z => by rw [map_mul, ← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha z => by rw [← ha (z * φ a⁻¹), map_inv, inv_mul_cancel_right] }
  have hM : IsClosed (M : Set (AdeleRing (𝓞 E) E)ˣ) := by
    have : (M : Set (AdeleRing (𝓞 E) E)ˣ) = ⋂ z, {g | ψ (z * φ g) = ψ z} := by
      ext g; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_iInter fun z => isClosed_eq (hψ.comp (continuous_const.mul hφ)) continuous_const
  have hdiag : ∀ k : Eˣ, HeckeValGen.diagUnits E k ∈ M := fun k z => by
    rw [mul_comm]
    refine hrat _ z ⟨k * σ (k⁻¹ : Eˣ), ?_⟩
    have e : Θ.symm (HeckeValGen.diagUnits E k) = Units.map (HeckeCharacterZeroLocus.ThmBIn.incA F E).toMonoidHom k :=
      Θ.symm_apply_eq.2 (GlobalTheory.UnitaryHeckeBaseChange.toIdele_principal k).symm
    have e' : φ (HeckeValGen.diagUnits E k) = quo h (Units.map (HeckeCharacterZeroLocus.ThmBIn.incA F E).toMonoidHom k) :=
      congrArg (quo h) e
    rw [e', quo_val, map_mul]
    rfl
  have hfin : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ T → SplitsFully E (P.under (𝓞 F)) →
      ∀ x, HeckeValGen.localIdele E P x ∈ M := fun P h1 h2 x z => by
    refine hloc _ h1 h2 z _ fun u hu => ?_
    have a1 := at_of_local h P x _ (hΘ _) u hu
    have a2 := at_of_local h P x⁻¹ _ (hΘ _) u hu
    rw [map_inv, map_inv] at a2
    have a3 := congrArg (cA σ) a2
    rw [map_smul, map_sub, map_one, map_zero] at a3
    have e : φ (HeckeValGen.localIdele E P x) = quo h (Θ.symm (HeckeValGen.localIdele E P x)) := rfl
    rw [e, quo_val]
    generalize cA σ _ = b at a3 ⊢
    generalize Units.val (Θ.symm (HeckeValGen.localIdele E P x)) = a at a1 ⊢
    rw [show a * b - 1 = (a - 1) * b + (b - 1) by ring, smul_add, ← smul_mul_assoc, a1, a3, zero_mul, add_zero]
  have htop : M = ⊤ := by
    refine ideles_eq_top E h.2.1 M hM (fun μ hμ hμM => ?_) fun r h1 h2 z => ?_
    · have := GlobalTheory.DensityOneTriv.trivialOfDensityOne E (Circle.toUnits.comp μ)
        ⟨(Units.continuous_iff.2 ⟨continuous_subtype_val.comp hμ,
            (continuous_subtype_val.comp hμ.inv).congr fun x => rfl⟩), fun k => by
          rw [MonoidHom.comp_apply, hμM _ (hdiag k), map_one]⟩
        (fun x => Circle.norm_coe (μ x)) _ (GlobalTheory.DensitySplit.hasDirichletDensity_splitsFully F E hG T)
        fun P hP => GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters.valueOneAt_of_trivAt fun x => by
          rw [MonoidHom.comp_apply, hμM _ (hfin P hP.1 hP.2 x), map_one]
      ext x
      simpa using congrArg Units.val (DFunLike.congr_fun this x)
    · have e : φ r = 1 := by
        refine Subtype.ext (Units.ext ?_)
        have e1 := cA_eq_of_real h (Θ.symm r : (AE F E)ˣ) (by rw [hΘ]; exact h1) (by rw [hΘ]; exact h2)
        have e2 : φ r = quo h (Θ.symm r) := rfl
        rw [e2, quo_val, ← e1, ← map_mul, Units.mul_inv, map_one]
        rfl
      rw [e, mul_one]
  have hone : ∀ z, ψ z = ψ 1 := fun z => by
    obtain ⟨y, rfl⟩ := surjective_quo h z
    have := (htop ▸ Subgroup.mem_top (Θ y) : Θ y ∈ M) 1
    rw [one_mul] at this
    rw [← this]
    exact congrArg (fun t => ψ (quo h t)) (Θ.symm_apply_apply y).symm
  exact fun z z' => (hone z).trans (hone z').symm
