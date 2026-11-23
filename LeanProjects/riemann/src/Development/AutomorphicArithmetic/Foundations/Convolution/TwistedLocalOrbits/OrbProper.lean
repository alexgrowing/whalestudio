import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem inj {k E : Type} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} (δ δ' : GL (Fin n) E) (h : IsTwRegSemisimple σ δ)
    (e : (normGL σ δ' : Matrix (Fin n) (Fin n) E).charpoly = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly) :
    TwConjugate (sigmaGL σ) δ δ' := by
  have hn : ∀ x : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) x = normGL σ x := fun x => by
    unfold UpperTheory.ConvolutionTheory.D.nm normGL twNorm
    congr 2
    funext i
    rw [← sigmaGL_pow]
    rfl
  obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ (UpperTheory.ConvolutionTheory.D.galField k E σ hσ) n δ δ' (by rw [hn]; exact h) (by rw [hn, hn]; exact e)
  exact ⟨x, hx⟩

private theorem openOrbit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (θ : Monoid.End G) (hθ : Continuous θ) (δ : G) (hc : IsClosed {δ' | TwConjugate θ δ δ'})
    (C : Set G) (hC : IsCompact C) :
    ∃ D : Set G, IsCompact D ∧ ∀ x, twConj θ x δ ∈ C → ∃ t ∈ twCent θ δ, ∃ d ∈ D, x = t * d := by
  have hm : ∀ a b y, twConj θ (a * b) y = twConj θ b (twConj θ a y) := fun a b y => by
    simp only [twConj, map_mul]; group
  have h1 : ∀ y, twConj θ 1 y = y := fun y => by simp [twConj]
  let X := {δ' // δ' ∈ {δ' | TwConjugate θ δ δ'}}
  letI : MulAction G X :=
    { smul := fun g y => ⟨twConj θ g⁻¹ y.1, by
        obtain ⟨a, ha⟩ := y.2
        exact ⟨a * g⁻¹, by rw [hm, ← ha]⟩⟩
      one_smul := fun y => Subtype.ext (by change twConj θ 1⁻¹ y.1 = y.1; rw [inv_one, h1])
      mul_smul := fun a b y => Subtype.ext (by
        change twConj θ (a * b)⁻¹ y.1 = twConj θ a⁻¹ (twConj θ b⁻¹ y.1)
        rw [mul_inv_rev, hm]) }
  have hs : ∀ (g : G) (y : X), (g • y).1 = twConj θ g⁻¹ y.1 := fun _ _ => rfl
  haveI : ContinuousSMul G X := ⟨Continuous.subtype_mk (by
    simp only [twConj]
    exact ((continuous_fst.inv.inv).mul (continuous_subtype_val.comp continuous_snd)).mul (hθ.comp continuous_fst.inv)) _⟩
  let x₀ : X := ⟨δ, 1, (h1 δ).symm⟩
  have hx : ∀ y : X, ∃ g : G, g • x₀ = y := fun y => by
    obtain ⟨a, ha⟩ := y.2
    exact ⟨a⁻¹, Subtype.ext (by rw [hs, inv_inv]; exact ha.symm)⟩
  haveI : MulAction.IsPretransitive G X := ⟨fun y z => by
    obtain ⟨a, rfl⟩ := hx y
    obtain ⟨b, rfl⟩ := hx z
    exact ⟨b * a⁻¹, by rw [smul_smul, inv_mul_cancel_right]⟩⟩
  haveI : LocallyCompactSpace X := hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have ho := isOpenMap_smul_of_sigmaCompact (G := G) x₀
  have hK : IsCompact (Subtype.val ⁻¹' C : Set X) := hc.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  choose N hN hN' using fun g : G => exists_compact_mem_nhds g
  obtain ⟨s, hs'⟩ := hK.elim_finite_subcover (fun g : G => (fun a : G => a • x₀) '' interior (N g))
    (fun g => ho _ isOpen_interior) fun y _ => by
      obtain ⟨g, rfl⟩ := hx y
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hN' g), rfl⟩
  refine ⟨(⋃ g ∈ s, N g)⁻¹, (s.isCompact_biUnion fun g _ => hN g).inv, fun x hxC => ?_⟩
  have := hs' (show (x⁻¹ • x₀ : X) ∈ Subtype.val ⁻¹' C by
    rw [Set.mem_preimage, hs, inv_inv]; exact hxC)
  simp only [Set.mem_iUnion] at this
  obtain ⟨g, hg, a, ha, e⟩ := this
  have e' : twConj θ a⁻¹ δ = twConj θ x δ := by
    have := congrArg Subtype.val e
    simpa only [hs, inv_inv] using this
  refine ⟨x * a, ?_, a⁻¹, ?_, by group⟩
  · change twConj θ (x * a) δ = δ
    rw [hm, ← e', ← hm, inv_mul_cancel, h1]
  · rw [Set.mem_inv, inv_inv]
    exact Set.mem_biUnion hg (interior_subset ha)

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.ConvolutionTheory.Loc.orbProper :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) (δ : GL (Fin n) E), IsTwRegSemisimple σ δ → ∀ C : Set (GL (Fin n) E), IsCompact C →
        ∃ D : Set (GL (Fin n) E), IsCompact D ∧ ∀ x, twConj (sigmaGL σ) x δ ∈ C → ∃ t ∈ twCent (sigmaGL σ) δ, ∃ d ∈ D, x = t * d := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ hδ C hC
  obtain ⟨i1, i2, i3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have hc := ((UpperTheory.V.Z.Tf.Orb.extCont k E).2.2 n).2
  have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hN : ∀ m, Continuous (twNorm (sigmaGL σ : Monoid.End (GL (Fin n) E)) m) := fun m => by
    induction m with
    | zero => exact continuous_const.congr fun x => (twNorm_zero _ x).symm
    | succ m ih =>
      refine (ih.mul (hc (σ ^ m))).congr fun x => ?_
      rw [twNorm_succ, sigmaGL_pow]
      rfl
  refine openOrbit _ (hc σ) δ ?_ C hC
  have e : {δ' | TwConjugate (sigmaGL σ) δ δ'} = ⋂ i, {δ' : GL (Fin n) E | (normGL σ δ' : Matrix (Fin n) (Fin n) E).charpoly.coeff i =
      (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly.coeff i} := by
    ext δ'
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨?_, fun h => inj σ hσ δ δ' hδ (Polynomial.ext h)⟩
    rintro ⟨g, rfl⟩ i
    rw [normGL, twNorm_twConj_of_pow_eq_one _ hl, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    rfl
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq ((contCoeff n i).comp (Units.continuous_val.comp (hN _))) continuous_const
