import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.SecPullIso

variable {Y Z : Scheme.{0}}

theorem mem_bo_res {U V : Z.Opens} (h : V ≤ U) (a : Γ(Z, U)) (x : Z) :
    x ∈ Z.basicOpen (resG Z h a) ↔ x ∈ V ∧ x ∈ Z.basicOpen a := by
  have : Z.basicOpen (resG Z h a) = V ⊓ Z.basicOpen a := Z.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_bo_appLE (f : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(Z, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ Z.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ Z.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_bo_mul {U : Z.Opens} (a b : Γ(Z, U)) (x : Z) :
    x ∈ Z.basicOpen (a * b) ↔ x ∈ Z.basicOpen a ∧ x ∈ Z.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem secOn_pull_of_iso : ∀ (X X' : Scheme.{0}) (F : X' ⟶ X) (L : LB X) (L' : LB X') (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (V : X.Opens) (θ : ∀ j, Γ(X, V ⊓ L.U j)), θ ∈ secOn L V → ∀ (W : X'.Opens), W ≤ F ⁻¹ᵁ V →
    ∃ θ' : (∀ i, Γ(X', W ⊓ L'.U i)), θ' ∈ secOn L' W ∧ ∀ (g : X') (i : L'.ι) (j : L.ι), g ∈ W → g ∈ L'.U i → F g ∈ L.U j →
      (g ∈ X'.basicOpen (θ' i) ↔ F g ∈ X.basicOpen (θ j)) := by
  intro X X' F L L' w hw hL hL' V θ hθ W hW
  have hP : (L.pull F).IsLB := Semi.LB.isLB_pull hL F
  let e := GlobalTheory.LB.isoOfGen hL' hP w hw
  let s0 : Γ(GlobalTheory.LB.toMod (L.pull F), W) := (GlobalTheory.LB.toMod (L.pull F)).presheaf.map (homOfLE hW).op
    (GlobalTheory.LB.pullSec L F V (GlobalTheory.LB.mkSec θ hθ))
  let s' : Γ(GlobalTheory.LB.toMod L', W) := e.inv.app W s0
  have hs : e.hom.app W s' = s0 := by
    have := congrArg (fun q => q.app W s0) e.inv_hom_id
    exact this
  refine ⟨GlobalTheory.LB.coord s', GlobalTheory.LB.coord_mem s', fun g i j hg hi hj => ?_⟩
  have hgp : g ∈ (L.pull F).U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
  have hgO : g ∈ W ⊓ (L.pull F).U (fun _ => j) ⊓ L'.U i := ⟨⟨hg, hgp⟩, hi⟩
  have key := GlobalTheory.LB.coord_isoOfGen_hom_app hL' hP w hw s' (fun _ => j) i
    (W := W ⊓ (L.pull F).U (fun _ => j) ⊓ L'.U i) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  rw [hs] at key
  have hl : g ∈ X'.basicOpen (resG X' (inf_le_left : W ⊓ (L.pull F).U (fun _ => j) ⊓ L'.U i ≤ W ⊓ (L.pull F).U (fun _ => j))
      (GlobalTheory.LB.coord s0 (fun _ => j))) ↔ F g ∈ X.basicOpen (θ j) := by
    change g ∈ X'.basicOpen (resG X' _ (resG X' _ ((F.appLE _ _ _).hom (θ j)))) ↔ _
    rw [mem_bo_res, mem_bo_res, mem_bo_appLE]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hgO, ⟨hg, hgp⟩, ⟨hW hg, hgp⟩, h⟩⟩
  rw [← hl, key, mem_bo_mul, mem_bo_res, mem_bo_res]
  have hu : ∀ u : Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U i)ˣ, g ∈ X'.basicOpen (u : Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U i)) := fun u => by
    rw [X'.basicOpen_of_isUnit u.isUnit]
    exact ⟨hgp, hi⟩
  exact ⟨fun h => ⟨⟨hgO, hu _⟩, hgO, h⟩, fun h => h.2.2⟩

end GlobalTheory.SecPullIso
