import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem affineMap_hasFDerivAt (hTri : UpperTheory.Gal.W2.TriCharpoly) {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (R : V →ₗ[ℂ] W) (c : V × W) (G : V × W → V × W)
    (hG : ∀ v, G v = (T v.1, Θ v.2 + R v.1) + c) (v₀ : V × W) :
    ∃ G' : (V × W) →L[ℂ] (V × W), HasFDerivAt G G' v₀ ∧
      (G' : (V × W) →ₗ[ℂ] (V × W)).charpoly = T.charpoly * Θ.charpoly := by
  unfold UpperTheory.Gal.W2.TriCharpoly at hTri
  let Gl : (V × W) →ₗ[ℂ] (V × W) :=
    LinearMap.prod (T ∘ₗ LinearMap.fst ℂ V W) (Θ ∘ₗ LinearMap.snd ℂ V W + R ∘ₗ LinearMap.fst ℂ V W)
  let G' : (V × W) →L[ℂ] (V × W) := LinearMap.toContinuousLinearMap Gl
  refine ⟨G', ?_, ?_⟩
  · have hfun : G = fun v => G' v + c := by
      funext v
      rw [hG v]
      rfl
    rw [hfun]
    exact G'.hasFDerivAt.add_const c
  · have hc : (G' : (V × W) →ₗ[ℂ] (V × W)) = Gl := rfl
    rw [hc]
    exact hTri V W T Θ R Gl (fun v w => rfl)

theorem UpperTheory.Gal.W2.locTan_of :
    UpperTheory.Gal.W2.TanChart → UpperTheory.Gal.W2.PerNear → UpperTheory.Gal.W2.BaseImm → UpperTheory.Gal.W2.PtHol → UpperTheory.Gal.W2.PtImm → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.TriCharpoly → UpperTheory.Gal.W2.LocTan := by
  intro hTan hPer hBase hHol hImm hFib hCorr hTri
  unfold UpperTheory.Gal.W2.TanChart at hTan
  unfold UpperTheory.Gal.W2.PerNear at hPer
  unfold UpperTheory.Gal.W2.BaseImm at hBase
  unfold UpperTheory.Gal.W2.PtHol at hHol
  unfold UpperTheory.Gal.W2.PtImm at hImm
  unfold UpperTheory.Gal.W2.PtFibre at hFib
  unfold UpperTheory.Gal.W2.CorrChart at hCorr
  unfold UpperTheory.Gal.W2.LocTan
  intro O _ bar g ρ D X s A _ S d hsm k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP₀ hM co hco ga H hfix T hT L hL z₀ hz₀ y hy At hAt
  have hCsp : ∀ b, co b ∈ Csp bar ρ M₀ := by
    intro b
    have hco' := hco
    unfold IsCoordC at hco'
    rw [← hco'.2]
    exact LinearMap.mem_range_self co b
  obtain ⟨B0, hB0o, h0B0, hB0⟩ := hPer O bar g ρ D P₀ M₀ hP₀ hM d co hCsp
  have hB0' := hB0
  unfold PELU.IsHolPeriods at hB0'
  choose x hx using hz₀
  let sec : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Sp ℂ ⟶ (KS.pow A k).left) :=
    fun bz => S.pt k (perC P₀ (co bz.1)) bz.2
  let R : (Fin d → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ) :=
    { toFun := fun b j => -(co (T b) *ᵥ star (P₀ (x j)))
      map_add' := by
        intro a b
        funext j
        simp only [map_add, Matrix.add_mulVec, Pi.add_apply, neg_add]
      map_smul' := by
        intro c b
        funext j
        simp [Matrix.smul_mulVec] }
  let c : (Fin d → ℂ) × (Fin k → Fin g → ℂ) := (0, fun j => -(P₀ (x j)))
  let G : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Fin d → ℂ) × (Fin k → Fin g → ℂ) :=
    fun v => (T v.1, fibMap H L v.2 - fun j => perC P₀ (co (T v.1)) (x j))
  have hG : ∀ v, G v = (T v.1, fibMap H L v.2 + R v.1) + c := by
    intro v
    refine Prod.ext ?_ ?_
    · show T v.1 = T v.1 + 0
      rw [add_zero]
    · funext j
      show fibMap H L v.2 j - perC P₀ (co (T v.1)) (x j) =
        fibMap H L v.2 j + -(co (T v.1) *ᵥ star (P₀ (x j))) + -(P₀ (x j))
      rw [perC_apply]
      abel
  obtain ⟨G', hG'd, hG'c⟩ := affineMap_hasFDerivAt hTri T (fibMap H L) R c G hG ((0 : Fin d → ℂ), z₀)
  have hfix0 : G ((0 : Fin d → ℂ), z₀) = ((0 : Fin d → ℂ), z₀) := by
    refine Prod.ext (map_zero T) ?_
    funext j
    show fibMap H L z₀ j - perC P₀ (co (T 0)) (x j) = z₀ j
    rw [map_zero T, map_zero co, perC_zero, hx j, sub_sub_cancel]
  have hsec0 : (y : Sp ℂ ⟶ (KS.pow A k).left) = sec ((0 : Fin d → ℂ), z₀) := by
    show _ = S.pt k (perC P₀ (co 0)) z₀
    rw [map_zero co, perC_zero]
    exact hy
  have hev : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), sec v ≫ c₂ = sec (G v) ≫ c₁ := by
    have hTc : Continuous (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1) :=
      (LinearMap.continuous_of_finiteDimensional T).comp continuous_fst
    have hT0 : Filter.Tendsto (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1)
        (𝓝 ((0 : Fin d → ℂ), z₀)) (𝓝 0) := by
      have := hTc.tendsto ((0 : Fin d → ℂ), z₀)
      simpa using this
    have h1 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), v.1 ∈ B0 :=
      (continuous_fst.tendsto ((0 : Fin d → ℂ), z₀)).eventually (hB0o.eventually_mem h0B0)
    have h2 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), T v.1 ∈ B0 :=
      hT0.eventually (hB0o.eventually_mem h0B0)
    filter_upwards [h1, h2] with v hv1 hv2
    obtain ⟨b, z⟩ := v
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hv1
    have hPTb : PELU.IsPeriod D ρ (perC P₀ (co (T b))) := hB0'.1 (T b) hv2
    have hPTb' : PELU.IsPeriod D ρ (perC P₀ (H * co b * (H.map star)⁻¹)) := by
      rw [← hT b]
      exact hPTb
    have step := hCorr O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP₀ hM ga H hfix L hL (co b) hPb hPTb' z
    show S.pt k (perC P₀ (co b)) z ≫ c₂ =
      S.pt k (perC P₀ (co (T b))) (fibMap H L z - fun j => perC P₀ (co (T b)) (x j)) ≫ c₁
    rw [step, ← hT b]
    congr 1
    refine ((hFib O bar g ρ D X s A S k _ hPTb).2.2.2.1 _ _).mpr ?_
    intro j
    refine ⟨x j, ?_⟩
    simp [hT b]
  have hflat := hImm O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) 0 hB0o h0B0 hB0
    (hBase O bar g ρ D X s A S d hsm P₀ M₀ hP₀ hM co hco) z₀
  have hhol := hHol O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) hB0o hB0
  have hsecs : ∀ v ∈ B0 ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)),
      sec v ≫ ((KS.pow A k).hom ≫ s) = spMap (RingHom.id ℂ) := by
    rintro ⟨b, z⟩ ⟨hb, -⟩
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hb
    show S.pt k (perC P₀ (co b)) z ≫ ((KS.pow A k).hom ≫ s) = _
    rw [← Category.assoc, (hFib O bar g ρ D X s A S k _ hPb).1 z, S.ov _ hPb]
  have hfr : Module.finrank ℂ ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) = d + k * g := by
    simp [Module.finrank_pi_fintype]
  have key := hTan ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) (d + k * g) hfr Z (KS.pow A k).left sZ
    ((KS.pow A k).hom ≫ s) c₁ c₂ h₁ h₂ (B0 ×ˢ Set.univ) sec ((0 : Fin d → ℂ), z₀)
    (hB0o.prod isOpen_univ) ⟨h0B0, trivial⟩ hhol hsecs hflat G G' hG'd hfix0 hev y hsec0 At hAt
  rw [key, hG'c]
