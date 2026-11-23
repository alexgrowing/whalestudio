import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem gs_appLE {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (hz : f z ∈ V) (x : Γ(X, U)) :
    gs f z V ((g.appLE U V h).hom x) = gs (f ≫ g) z U x := by
  have e : (g.appLE U V h).hom x = (Y.presheaf.map (homOfLE h).op).hom ((g.app U).hom x) := rfl
  rw [e, gs_res f z h hz, gs_pull f g z U (h hz)]

theorem exists_sec_of_genIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (π : X₁ ⟶ Y), π ≫ f₁ = 𝟙 X₁ → f₁ ≫ π = 𝟙 Y → ∀ (k : ℕ) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), ∃ σ' : SecM (𝟙 X₁) L₁ k, (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h1 h2 π hπ hπ' k s
  let ε : Fin 1 → ℤ := fun _ => (k : ℤ)
  let u := isoInv (ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε)
  have hu : u.IsGen := isoInv_isGen (ReciprocityTheory.ChartRestriction.G.DVR.flatIso_isGen L₁ L₂ f₁ f₂ w hw ε)
  let t := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hu (LB.isLB_linComb h1 (fun _ : Fin 1 => f₁) ε) (LB.isLB_linComb h2 (fun _ : Fin 1 => f₂) ε)
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t, ?_⟩
  intro y i j hy2 hy1

  have hyA : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) := Set.mem_iInter.2 fun _ => hy1
  have hyB : y ∈ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := Set.mem_iInter.2 fun _ => hy2
  have hyAB : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) ⊓ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := ⟨hyA, hyB⟩
  have hyw : y ∈ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hy2, Set.mem_iInter.2 fun _ => hy1⟩

  have s1 : gs f₁ y _ ((ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t).f fun _ => j) =
      gs (𝟙 Y) y _ (t.f fun _ => j) := by
    show gs f₁ y _ ((π.appLE _ _ _).hom _) = _
    rw [gs_appLE f₁ π y _ (show f₁ y ∈ _ from Set.mem_iInter.2 fun _ => by simpa using hy1), hπ']

  have s2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) := by
    rw [← ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hu _ _ (fun _ => j) (fun _ => i)]
    exact (gs_res (𝟙 Y) y inf_le_left hyAB _).symm

  have s3 : gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) =
      ((gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j))) ^ (-(k : ℤ))).val * gs (𝟙 Y) y _ (s.f fun _ => i) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand
    rw [gs_mul (𝟙 Y) y _ hyAB, gs_unit (𝟙 Y) y _ hyAB, gs_res (𝟙 Y) y inf_le_right hyAB]
    congr 2
    rw [map_inv, gm_res (𝟙 Y) y _ hyAB]
    show (gm (𝟙 Y) y _ (res _ ((ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε).s ((fun _ => j), (fun _ => i))))⁻¹)⁻¹ = _
    have hyBA : y ∈ ((LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).div (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε)).U ((fun _ => i), (fun _ => j)) := ⟨hyB, hyA⟩
    have hyAB' : y ∈ ((LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).div (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε)).U ((fun _ => j), (fun _ => i)) := hyAB
    rw [map_inv, inv_inv]
    erw [gm_res (𝟙 Y) y _ hyBA]
    show gm (𝟙 Y) y _ (∏ q : Fin 1, res (ReciprocityTheory.ChartRestriction.G.DVR.flat_le L₁ L₂ f₁ f₂ ((fun _ => j), (fun _ => i)) q) (w.s (fun _ => i, fun _ => j)) ^ (-ε q)) = _
    rw [Fin.prod_univ_one]
    erw [map_zpow, gm_res (𝟙 Y) y _ hyAB']
    rfl
  rw [s1, s2, s3, gs_unit (𝟙 Y) y _ hyw, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.SecThroughIso
