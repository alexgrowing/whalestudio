import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace DeRhamVectorExtension

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsNilpotent (p : R) → ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
    IsAbelianScheme A → ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (e : Family p)

def Family.Natural : Prop :=
  ∀ ⦃R R' : Type⦄ [CommRing R] [CommRing R'] (hR : IsNilpotent (p : R)) (hR' : IsNilpotent (p : R'))
    ⦃A : Over (Sp R)⦄ [GrpObj A] ⦃A' : Over (Sp R')⦄ [GrpObj A']
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    ⦃G : PDivGroup p R⦄ ⦃G' : PDivGroup p R'⦄ (t : G.TorsionTower A) (t' : G'.TorsionTower A')
    ⦃σ : R →+* R'⦄ ⦃φ : A'.left ⟶ A.left⦄
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A),
    e hR' hA' t' (m.pull c) = (t'.semiHom t m).rig (e hR hA t c)

def Family.Filtered : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A),
    (PrimitiveSubmodule A).map (e hR hA t).toLinearMap = LinearMap.range G.rigOfOmega

def Family.Tangent : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A)
    (h : HdR A) (v : epsR R ⟶ A),
    IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie ((e hR hA t).symm.dualMap h)) v

end DeRhamVectorExtension

def DeRhamVectorExtension : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ e : DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent

namespace DeRhamVectorExtension

variable {p : ℕ} {e : Family p} {R : Type} [CommRing R] (hR : IsNilpotent (p : R))
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
  {G H : PDivGroup p R} (t : G.TorsionTower A) (u : H.TorsionTower B)

variable (e) in

def Family.lie : HdR A ≃ₗ[R] G.LieUniv := (e hR hA t).symm.dualMap

theorem Family.lie_apply (h : HdR A) (c : primDR A) : e.lie hR hA t h (e hR hA t c) = h c :=
  congrArg h ((e hR hA t).symm_apply_apply c)

theorem Family.Filtered.mem_Fil_iff (he : e.Filtered) (h : HdR A) :
    h ∈ Fil A ↔ G.lieUnivToLie (e.lie hR hA t h) = 0 := by
  have k := he hR hA t
  rw [Fil, Submodule.mem_dualAnnihilator]
  refine ⟨fun H ↦ LinearMap.ext fun w ↦ ?_, fun H c hc ↦ ?_⟩
  · obtain ⟨c, hc, hw⟩ := k.ge ⟨w, rfl⟩
    exact (congrArg (e.lie hR hA t h) hw.symm).trans ((e.lie_apply hR hA t h c).trans (H c hc))
  · obtain ⟨w, hw⟩ := k.le ⟨c, hc, rfl⟩
    exact (e.lie_apply hR hA t h c).symm.trans
      ((congrArg (e.lie hR hA t h) hw.symm).trans (LinearMap.congr_fun H w))

variable [Fact p.Prime]

theorem Family.Natural.primPull (he : e.Natural) (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    e hR hA t (primPull (dp0 R) (𝟙 _) f c) = PDivGroup.rigExtMap (t.map u f) (e hR hB u c) := by
  have k := he hR hR hB hA u t (PDiv.grpMor_of_hom f) c
  rw [← PDivGroup.SemiHom.ofHom_rig]
  exact k

theorem Family.Natural.lie_push (he : e.Natural) (f : A ⟶ B) [IsMonHom f] (h : HdR A) :
    e.lie hR hB u (push (dp0 R) (𝟙 _) f h) = PDivGroup.lieUnivMap (t.map u f) (e.lie hR hA t h) :=
  LinearMap.ext fun x ↦ by
    obtain ⟨c, rfl⟩ := (e hR hB u).surjective x
    rw [Family.lie_apply, push_apply, ← e.lie_apply hR hA t, he.primPull hR hA hB t u]
    rfl

end DeRhamVectorExtension

end GlobalTheory.Published
