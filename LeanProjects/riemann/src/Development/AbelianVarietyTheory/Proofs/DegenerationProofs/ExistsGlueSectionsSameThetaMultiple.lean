import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
