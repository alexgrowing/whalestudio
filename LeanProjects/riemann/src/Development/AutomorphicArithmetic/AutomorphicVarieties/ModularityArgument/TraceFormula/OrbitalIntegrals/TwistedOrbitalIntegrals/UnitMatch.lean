import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

private theorem ind_comp {X Y M : Type} [Zero M] [One M] (u : X → Y) (A : Set Y) :
    (fun x => A.indicator (1 : Y → M) (u x)) = (u ⁻¹' A).indicator 1 := by
  funext x
  by_cases h : u x ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ u ⁻¹' A from h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ u ⁻¹' A from h)]

theorem UpperTheory.V.Z.Tf.Orb.unitMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotReal → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.UnitMatch := by
  intro hT hC hCC hTw hH hQ hU hB k E _ _ _ _ _ _ _ _ _ _ _ _ _ hur σ hσ n _ _ _ _ μE μk hE hk vE vk
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  obtain ⟨h1, h2⟩ := hB k E hur σ hσ n μE μk hE hk vE vk
  have hk' : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), IsRegSemisimple γ → μγ.IsHaarMeasure →
      orbIntegralC μk γ μγ (unitFnC k) = ((orbIntegral μk γ μγ (unitFn k)).toReal : ℂ) := fun γ μγ hγ hμ => by
    obtain ⟨c1, c2⟩ := cent_facts hCC hγ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μγ hμ
    unfold orbIntegralC orbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g), ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g)]
    exact hQ _ μk _ μγ _ (((hU k n).1.preimage ((continuous_inv.mul continuous_const).mul continuous_id)).measurableSet)
  refine ⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hm => ?_, fun γ μγ hγ hn hμ => ?_⟩
  · have hγ : IsRegSemisimple γ := by
      have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
          (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
        rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
        rfl
      have := hδ
      unfold IsTwRegSemisimple at this
      rw [e] at this
      exact (Polynomial.separable_map _).1 this
    obtain ⟨c1, c2⟩ := hTw k E σ hσ n δ hδ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μδ hμδ
    rw [hk' γ μγ hγ hμγ, ← h1 δ γ h μδ μγ hδ hN hμδ hμγ hm]
    unfold twOrbIntegralC twOrbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ), ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ)]
    exact hQ _ μE _ μδ _ (((hU E n).1.preimage ((continuous_inv.mul continuous_const).mul hσc)).measurableSet)
  · rw [hk' γ μγ hγ hμ, h2 γ μγ hγ hn hμ]
    simp
