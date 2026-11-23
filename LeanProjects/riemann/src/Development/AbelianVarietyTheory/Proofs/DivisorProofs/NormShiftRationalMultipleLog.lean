import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricFinitelyManyPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

theorem const_rat : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ), Norms V L₁ f a l → Norms V L₂ f a (fun v e y => l v e y + c v) → ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  intro F _ _ Y V L₁ L₂ f a l c h₁ h₂ v
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  obtain ⟨y⟩ := ValGroup.nonempty_algPt Y
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨r₁, -, hu₁, -, hf₁⟩ := h₁
  obtain ⟨r₂, -, hu₂, -, hf₂⟩ := h₂
  have chart (B : HermLB V.p) : ∃ i, yt (IsLocalRing.closedPoint e.O) ∈ B.B.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (B.isLB.cover.ge (Set.mem_univ _))
  obtain ⟨i, hi⟩ := chart L₁
  obtain ⟨i', hi'⟩ := chart L₂
  have k₁ := hf₁ v e y z yt (fun _ => i) hz hyt (hU _ hi)
  have k₂ := hf₂ v e y z yt (fun _ => i') hz hyt (hU _ hi')
  have hx : ∀ (B : HermLB V.p) (j : B.B.ι), yt (IsLocalRing.closedPoint e.O) ∈ B.B.U j →
      below z ∈ (B.B.pull V.j).U (fun _ => j) := by
    intro B j hj
    have h1 : (spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ yt ⁻¹ᵁ B.B.U j := hU _ hj trivial
    have h2 : (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ B.B.U j := by
      rw [← hyt]; exact h1
    exact Set.mem_iInter.2 fun _ => h2
  have hb : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have n₁ := (Base.valAt_zpow z (hb ▸ hu₁ (fun _ => i) (below z) (hx L₁ i hi))).1
  have n₂ := (Base.valAt_zpow z (hb ▸ hu₂ (fun _ => i') (below z) (hx L₂ i' hi'))).1
  have key : c v = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1)) * ((r₂ fun _ => i' : V.G.functionFieldˣ) : V.G.functionField)) /
      TrueGeo.valAt z (V.φ (f (below y.1)) * ((r₁ fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))) := by
    rw [map_div₀, Real.log_div (e.w.ne_zero n₂) (e.w.ne_zero n₁), ← k₁]
    simp only at k₂
    linarith
  obtain ⟨m, q, hm, hq⟩ := GlobalTheory.ExtValueGroup.log_w_rat F v e _ (div_ne_zero n₂ n₁)
  exact ⟨m, q, hm, by rw [key]; exact hq⟩
