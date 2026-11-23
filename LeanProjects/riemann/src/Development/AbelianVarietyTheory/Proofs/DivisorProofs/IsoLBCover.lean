import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixUniq

open GlobalTheory.HomFixMat

theorem psi_unique {Rg : Type} [CommRing Rg] {A : Over (Sp Rg)} [GrpObj A] {X : Scheme.{0}} (ψ ψ₂ : X ⟶ (topS Rg ⊗ A).left)
    (h : ψ ≫ (snd (topS Rg) A).left = ψ₂ ≫ (snd (topS Rg) A).left) : ψ = ψ₂ := by
  haveI : Mono (topS Rg).hom := by
    show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  have e : ψ ≫ (fst (topS Rg) A).left = ψ₂ ≫ (fst (topS Rg) A).left := by
    rw [← cancel_mono (topS Rg).hom]
    simp only [Category.assoc, Over.w]
    rw [← Over.w (snd (topS Rg) A), ← Category.assoc, h, Category.assoc]
  exact pullback.hom_ext e h

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

variable (L : LB A.left) (M : LB B.left) in

def RigEq (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R]
    (t : Sp R ⟶ Sp Rg) {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) : Prop :=
  ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k

theorem isoLB_cover {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left}
    {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB) (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)}
    (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (x : A'.left) :
    ∃ p, x ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := by
  have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
  obtain ⟨iM, hiM⟩ := hc M hM ((((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)).base x)
  obtain ⟨iL, hiL⟩ := hc L hL (((ψA ≫ (snd (topS Rg) A).left)).base x)
  exact ⟨(fun _ => iM, fun _ => iL), Set.mem_iInter.2 fun _ => hiM, Set.mem_iInter.2 fun _ => hiL⟩

end GlobalTheory.HomFixUniq
