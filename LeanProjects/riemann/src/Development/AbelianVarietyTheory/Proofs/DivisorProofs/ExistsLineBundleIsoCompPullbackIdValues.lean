import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
