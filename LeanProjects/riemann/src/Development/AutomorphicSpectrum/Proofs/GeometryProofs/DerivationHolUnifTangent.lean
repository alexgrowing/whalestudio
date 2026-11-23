import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer

theorem ev_pull {C : Type} [CommRing C] {Y Y' : Scheme.{0}} (x : Sp C ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens)
    (h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (f : Γ(Y', U)) :
    ev x (ψ ⁻¹ᵁ U) h' (ψ.app U f) = ev (x ≫ ψ) U h f := by
  simp only [ev, RingHom.comp_apply, Scheme.Hom.comp_appLE, CommRingCat.hom_comp]

theorem valAt'_pull {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (ψ ⁻¹ᵁ U) (ψ.app U f) = valAt' (x ≫ ψ) U f := by
  by_cases h : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dif_pos h, dif_pos h']
    exact ev_pull x ψ U h h' f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U) := h
    rw [valAt', valAt', dif_neg h, dif_neg h']

theorem tr_eq_pull {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A]
    {z : Sp ℂ ⟶ Sp R} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G)
    (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v' : epsR ℂ ⟶ A)
    (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) :
    tr v₀ (a.left ≫ φ) = ((toUnit (epsR ℂ) ≫ a) * v').left ≫ φ := by
  have hb : (a.left ≫ φ) ≫ G.hom = z := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w a]
    exact Category.id_comp z
  let J : Over.mk ((epsR ℂ).hom ≫ z) ⟶ epsAt ((a.left ≫ φ) ≫ G.hom) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (a.left ≫ φ) ≫ G.hom = (epsR ℂ).hom ≫ z
      rw [hb, Category.id_comp]
      rfl)
  let P := piE ((a.left ≫ φ) ≫ G.hom) ≫ (Over.homMk (a.left ≫ φ) rfl : Over.mk ((a.left ≫ φ) ≫ G.hom) ⟶ G)
  let Q := rhoE ((a.left ≫ φ) ≫ G.hom) ≫ v₀
  have e := h.2 (epsR ℂ) (toUnit (epsR ℂ) ≫ a) v' (J ≫ P) (J ≫ Q) ?_ ?_
  · rw [← MonObj.comp_mul] at e
    have e' : (J ≫ (P * Q)).left = (P * Q).left := Category.id_comp _
    rw [← e, e']
    rfl
  · have hu : (toUnit (epsR ℂ)).left = (epsR ℂ).hom := (Over.w (toUnit (epsR ℂ))).symm ▸ (Category.comp_id _).symm
    show 𝟙 _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ a.left ≫ φ = (toUnit (epsR ℂ) ≫ a).left ≫ φ
    rw [Over.comp_left, hu, Category.id_comp, Category.assoc]
    rfl
  · show 𝟙 _ ≫ spMap (dualMap (bmap ((a.left ≫ φ) ≫ G.hom))) ≫ v₀.left = v'.left ≫ φ
    rw [hb, Category.id_comp, hv]

theorem fderiv_valAt_eq_der (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left)
    (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ)
    (v' : epsR ℂ ⟶ A) (hv : v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left) (hd : u.IsDiff c v')
    (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ)
    (hw : ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V) :
    fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c =
      valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  let t : A ⟶ A := (toUnit A ≫ u.ex w) * 𝟙 A
  have hE : v' ≫ t = (toUnit (epsR ℂ) ≫ u.ex w) * v' := by
    have e : v' ≫ toUnit A = toUnit (epsR ℂ) := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e]
  have ht : ∀ x, u.ex x ≫ t = u.ex (w + x) := by
    intro x
    have e : u.ex x ≫ toUnit A = 𝟙 _ := toUnit_unique _ _
    simp only [t, MonObj.comp_mul, Category.comp_id, ← Category.assoc, e, Category.id_comp, u.ex_add]
  have htr : tr v₀ ((u.ex w).left ≫ φ) = v'.left ≫ t.left ≫ φ := by
    rw [tr_eq_pull h v₀ (u.ex w) v' hv, ← hE, Over.comp_left, Category.assoc]
  have hT := tr_top v₀ hv₀ _ V hw
  have hU : ⊤ ≤ v'.left ⁻¹ᵁ ((t.left ≫ φ) ⁻¹ᵁ V) := by
    have h2 := hT
    rw [htr] at h2
    exact h2
  have key := hd ((t.left ≫ φ) ⁻¹ᵁ V) hU ((t.left ≫ φ).app V f)
  have hF : (fun x => valAt' (u.ex x).left ((t.left ≫ φ) ⁻¹ᵁ V) ((t.left ≫ φ).app V f)) =
      fun x => (fun x => valAt' ((u.ex x).left ≫ φ) V f) (w + x) := by
    funext x
    rw [valAt'_pull, ← Category.assoc, ← Over.comp_left, ht]
  have hG := fderiv_comp_add_left (𝕜 := ℂ) (f := fun x => valAt' ((u.ex x).left ≫ φ) V f) (x := 0) w
  rw [add_zero] at hG
  rw [hF, hG] at key
  rw [← key, valAt', dif_pos hw]
  have e1 := snd_ev_tr v₀ hv₀ hV ((u.ex w).left ≫ φ) hw hT f
  have hT' : ⊤ ≤ (v'.left ≫ t.left ≫ φ) ⁻¹ᵁ V := hU
  have e2 : ev (v'.left ≫ t.left ≫ φ) V hT' f = ev (tr v₀ ((u.ex w).left ≫ φ)) V hT f :=
    congrArg (fun m => m f) (ev_congr htr.symm V hT' hT)
  have e3 := ev_pull v'.left (t.left ≫ φ) V hT' hU f
  exact (congrArg TrivSqZeroExt.snd (e3.trans e2)).trans e1

end GlobalTheory.CompanionTheory.Ar.InvDer
