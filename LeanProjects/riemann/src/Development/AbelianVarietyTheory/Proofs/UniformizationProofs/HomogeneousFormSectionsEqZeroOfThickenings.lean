import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormVan

variable {X X' Z : Scheme.{0}}

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem gs_zero (r : Z ⟶ X) (z : Z) (U : X.Opens) : gs r z U 0 = 0 := by
  by_cases h : r z ∈ U
  · rw [gs_eq r z U h, map_zero, map_zero]
  · exact dif_neg h

theorem sval_zeroSec (M : LB X) (π : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J : (Z ⟶ X) → M.ι) :
    sval (zeroSec (M.pull π)) r z J = 0 := gs_zero r z _

theorem exists_pull_id {M : LB X} (τ : LB.Sec M) : ∃ s : LB.Sec (M.pull (𝟙 X)),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (s.f j) = gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) := by
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : PUnit → M.ι), r z ∈ M.U (j PUnit.unit) →
      gs r z ((M.pull (𝟙 X)).U j) (rs X (le j) (τ.f (j PUnit.unit))) =
        gs r z (M.U (j PUnit.unit)) (τ.f (j PUnit.unit)) :=
    fun Z r z j hj => gs_res r z (le j) (mem_pull.2 hj) _
  refine ⟨⟨fun j => rs X (le j) (τ.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, v⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j hm.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
      (congrArg Units.val (gm_pull_g M (𝟙 X) (𝟙 X) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 X) y _ hy _).trans (v _ _ y j' hm.2)))).symm)
  rw [Category.id_comp]
  exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (τ.compat _ _)).trans
    ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))

theorem eval₂Hom_scale {κ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : κ → A)
    {P : MvPolynomial κ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂Hom φ (fun j => c * x j) P = c ^ e * MvPolynomial.eval₂Hom φ x P := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hP (MvPolynomial.mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def formSec {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {N : LB X} {κ : Type} (σ : κ → LB.Sec N)
    {d : ℕ} {F : MvPolynomial κ R} (hF : F.IsHomogeneous d) : LB.Sec (pw N d) where
  f := fun k => MvPolynomial.eval₂Hom (cst p (N.U k)) (fun j => (σ j).f k) F
  compat := fun i j => by
    have c : ∀ {U V : X.Opens} (h : V ≤ U), (rs X h).comp (cst p U) = cst p V :=
      fun h => RingHom.ext (rs_cst p h)
    change rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (MvPolynomial.eval₂Hom _ _ F) =
      (N.g i j ^ (d : ℤ)).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (MvPolynomial.eval₂Hom _ _ F)
    rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom, c, c, zpow_natCast, Units.val_pow_eq_pow_val,
      ← eval₂Hom_scale _ _ _ hF]
    congr 2
    exact funext fun a => (σ a).compat i j

theorem sec_eq_zero (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (hI : IsAdicComplete I R)
    (Y : Over (Spec (CommRingCat.of R))) (hs : Smooth Y.hom) (hp : IsProjBy Y.hom) (M : LB Y.left) (hM : M.IsLB)
    (τ : LB.Sec M) (h : ∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : M.ι),
      pullback.fst Y.hom (thick R I e) z ∈ M.U k → gs (pullback.fst Y.hom (thick R I e)) z (M.U k) (τ.f k) = 0)
    (k : M.ι) : τ.f k = 0 := by
  obtain ⟨s, hv⟩ := exists_pull_id τ
  have e : s = zeroSec _ := (GlobalTheory.SecAlg.existsUnique_sec R I hI Y hs hp M hM (fun _ => zeroSec _)
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)).unique
    (fun e z J hJ => by
      have hm : (fstG I e Y).left z ∈ M.U (J ((fstG I e Y).left ≫ 𝟙 _)) := hJ ((fstG I e Y).left ≫ 𝟙 _)
      exact (hv _ _ z _ hm).trans ((h e z _ hm).trans (sval_zeroSec _ _ _ z J).symm))
    (fun e z J _ => (sval_zeroSec _ _ _ z J).trans (sval_zeroSec _ _ _ z J).symm)
  refine fn_ext fun y hy => ?_
  rw [← hv _ (𝟙 _) y (fun _ => k) hy, e, gs_zero]
  exact gs_zero _ _ _

theorem form_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (N : LB Y.left) (κ : Type) (σ : κ → LB.Sec N) (d : ℕ) (F : MvPolynomial κ R), N.IsLB → F.IsHomogeneous d → (∀ (e : ℕ) (z : (thickObj R I e Y).left) (k : N.ι), pullback.fst Y.hom (thick R I e) z ∈ N.U k → gs (pullback.fst Y.hom (thick R I e)) z (N.U k) (MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F) = 0) → ∀ k, MvPolynomial.eval₂Hom (cst Y.hom (N.U k)) (fun j => (σ j).f k) F = 0 :=
  fun R _ _ I hI Y hs hp N _ σ d _ hN hF h k =>
    sec_eq_zero R I hI Y hs hp (pw N d) (isLB_pw hN d) (formSec Y.hom σ hF) h k

end GlobalTheory.FormVan
