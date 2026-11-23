import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.GenTop

theorem appLE_fromSpecResidueField {X : Scheme.{0}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h = X.evaluation U x hx ≫ (Scheme.ΓSpecIso _).inv := by
  have h' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U) := h
  have e : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  have := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ le_rfl h'
  rw [appLE_of_eq e U ⊤ h (h'.trans le_rfl), ← this, ← Scheme.Hom.app_eq_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.germ_residue, Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pullRatio_SpecMap_fromSpec {N : ℕ} (i : Fin (N + 1)) {R : CommRingCat.{0}}
    (ψ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ R)
    (h : ⊤ ≤ (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    pullRatio (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⊤ i h j =
      (Scheme.ΓSpecIso R).inv (ψ (ratio ℤ N i j)) := by
  have h1 : (isAffineOpen_chart ℤ N i).fromSpec.appLE (chart ℤ N i) ⊤
      (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (isAffineOpen_chart ℤ N i).fromSpec
    (chart ℤ N i) ⊤ ⊤ (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge le_rfl
  unfold pullRatio
  rw [← h3, h1]
  have := congrArg (fun q => q.hom (ratio ℤ N i j)) (Scheme.ΓSpecIso_inv_naturality ψ)
  exact this.symm

theorem surjective_of_factor {X : Scheme.{0}} (x : X) {F : Type} [Field F]
    (ι : CommRingCat.of F ⟶ X.residueField x) (G : Spec (.of F) ⟶ X)
    (h : Spec.map ι ≫ G = X.fromSpecResidueField x) : Function.Surjective ι.hom := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective G
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hz : z = x := by
    have e := congrArg (fun f : Spec (X.residueField x) ⟶ X => f default) h
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hz
  rw [← Category.assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (φ ≫ ι) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecResidueField _), Spec.map_id, Category.id_comp]
    exact h
  have h3 : φ ≫ ι = 𝟙 _ := Spec.map_injective h2
  intro a
  refine ⟨φ.hom a, ?_⟩
  have := congrArg (fun q => q.hom a) h3
  simpa using this

theorem blockFnField_ptCoord_eq_top (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n)
    [CharZero ((MP ℤ m n).residueField x)] : blockFnField (ptCoord x) = ⊤ := by
  have hone : ∀ k, ptCoord x ⟨k, ptChart x k⟩ = 1 := fun k => by
    simp only [ptCoord, pullRatio_self, map_one]
  have hmem : ∀ p, ptCoord x p ∈ blockFnField (ptCoord x) := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, by rw [hone, div_one]⟩
  let F := blockFnField (ptCoord x)
  let r : ∀ k, Fin (n k + 1) → F := fun k j => ⟨ptCoord x ⟨k, j⟩, hmem _⟩
  have hr : ∀ k, r k (ptChart x k) = 1 := fun k => Subtype.ext (hone k)
  let ρ : ∀ k, Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k)) ⟶ CommRingCat.of F := fun k =>
    CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k))) (S := F)
      (chartLift (ptChart x k) (Int.castRingHom F) (r k))
  let g : ∀ k, Spec (CommRingCat.of F) ⟶ projectiveSpace ℤ (n k) := fun k =>
    Spec.map (ρ k) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec
  let G : Spec (CommRingCat.of F) ⟶ MP ℤ m n :=
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (Spec.map (CommRingCat.ofHom (Int.castRingHom F))) g
      (fun _ => specZIsTerminal.hom_ext _ _)
  let ι : CommRingCat.of F ⟶ (MP ℤ m n).residueField x := CommRingCat.ofHom F.val.toRingHom
  have key : Spec.map ι ≫ G = (MP ℤ m n).fromSpecResidueField x := by
    refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
    rw [Category.assoc, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr]
    have hx := mem_ptChart x k
    have h₂' : ⊤ ≤ (MP ℤ m n).fromSpecResidueField x ⁻¹ᵁ blockChart n k (ptChart x k) := fun s _ => by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hx
    have e1 : Spec.map ι ≫ g k = Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    have h₁ : ⊤ ≤ (Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec) ⁻¹ᵁ
        chart ℤ (n k) (ptChart x k) := by
      rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
      exact le_top
    rw [e1]
    refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ =>
      ⟨⊤, trivial, ptChart x k, h₁, by rw [Scheme.Hom.comp_preimage]; exact h₂', fun j => ?_⟩
    rw [pullRatio_SpecMap_fromSpec]
    have e2 := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl)
      (j := j) ((MP ℤ m n).fromSpecResidueField x) h₂'
    refine Eq.trans ?_ e2
    rw [appLE_fromSpecResidueField x hx]
    show _ = (Scheme.ΓSpecIso _).inv (ptCoord x ⟨k, j⟩)
    congr 1
    show F.val (chartLift (ptChart x k) (Int.castRingHom F) (r k) (ratio ℤ (n k) (ptChart x k) j)) = _
    rw [chartLift_ratio _ _ (hr k)]
    rfl
  have hs := surjective_of_factor x ι G key
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

end GlobalTheory.CompanionTheory.MPDict.GenTop
