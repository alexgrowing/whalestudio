import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLift

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n m : ℕ} (h : n = m)
    {w : Fin m → (epsR R ⟶ G)} (hw : IsLieBasis w) : IsLieBasis (fun j : Fin n => w (j.cast h)) := by
  subst h
  simpa using hw

theorem dual_eq_id {K : Type} [Field K] (F : DualNumber K →+* DualNumber K)
    (h₁ : ∀ a, F (algebraMap K _ a) = algebraMap K _ (RingHom.id K a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = RingHom.id _ := by
  let Fa : DualNumber K →ₐ[K] DualNumber K := { F with commutes' := h₁ }
  have : Fa = AlgHom.id K _ := DualNumber.algHom_ext h₂
  exact RingHom.ext fun z => congrArg (fun q : DualNumber K →ₐ[K] DualNumber K => q z) this

theorem main : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  intro K _ G _ _ L σ σ' x x' hg' y y' M hx hx' hM
  obtain ⟨φ, he, ψ, F, hφ, hψ, hmaps, hsec, hF₁, hF₂, hxv⟩ := hx
  obtain ⟨φ', -, -, F', hφ', -, -, -, hF₁', hF₂', hxv'⟩ := hx'
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  have e' : spMap (RingHom.id (DualNumber K)) = 𝟙 (Sp (DualNumber K)) := Spec.map_id _
  have hF := dual_eq_id F hF₁ hF₂
  have hF' := dual_eq_id F' hF₁' hF₂'
  subst hF hF'
  have eD : spMap (Formalism.L2.Pj.dualMap (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Formalism.L2.Pj.dualMap]
  have eR : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Chart.dualMapR]

  have hw : ∀ i, (y' i).left ≫ G.hom = (epsR K).hom ≫ spMap (RingHom.id K) := fun i => by
    rw [e, Category.comp_id]; exact Over.w (y' i)
  let v : Fin x.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (hφ.1.lift (y' i).left (epsR K).hom (hw i))
    (hφ.1.lift_snd _ _ _)
  have hvφ : ∀ i, (v i).left ≫ φ = (y' i).left := fun i => hφ.1.lift_fst _ _ _

  let χ : x.P.A.left ⟶ x'.P.A.left := hφ'.1.lift φ x.P.A.hom hφ.1.w
  have hχ : χ ≫ φ' = φ := hφ'.1.lift_fst _ _ _
  have hχ' : χ ≫ x'.P.A.hom = x.P.A.hom ≫ spMap (RingHom.id K) := by
    rw [hφ'.1.lift_snd, e, Category.comp_id]
  have hn : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ spMap (RingHom.id K)) (χ ≫ φ') := by
    rw [hχ, e, Category.comp_id, ← e]; exact hφ
  have hC : IsGrpPullback x.P.A x'.P.A (spMap (RingHom.id K)) χ := IsGrpPullback.cancel hφ' hn hχ'
  have := x'.P.isAb.smooth
  have hvχ : ∀ j, (v j).left ≫ χ = spMap (Chart.dualMapR (RingHom.id K)) ≫ (x'.v (j.cast hg'.symm)).left := by
    intro j
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hχ, hvφ, eR, Category.id_comp, hxv', e', Category.id_comp]
      simp
    · rw [Category.assoc, hχ', ← Category.assoc, Over.w (v j), eR, Category.id_comp, Over.w (x'.v _), e,
        Category.comp_id]
  have hv : IsLieBasis v := Chart.isLieBasis_baseChange (RingHom.id K) hC
    (isLieBasis_cast hg'.symm x'.basis) hvχ
  refine ⟨v, hv, fun i => ?_, φ, he, ψ, RingHom.id _, hφ, hψ, hmaps, hsec, hF₁, hF₂, fun i => ?_⟩
  · have h' : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ 𝟙 (Sp K)) φ := by rw [Category.comp_id]; exact hφ
    exact GlobalTheory.LamT.isLieComb_of_two_pullbacks (RingHom.id K) rfl (grpPullback_self G) h' rfl (hM i)
      (fun j => by rw [hxv, eD, e', Category.comp_id]; rfl)
      (by rw [hvφ, eD, Category.comp_id, Category.id_comp])
  · rw [hvφ, e', Category.id_comp]

end GlobalTheory.LieLift
