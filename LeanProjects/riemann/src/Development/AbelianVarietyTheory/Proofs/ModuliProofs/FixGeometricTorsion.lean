import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompatOfLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.TUniq

namespace GlobalTheory.TUniq

theorem fix_geometric_torsion {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g k J b s) (θ : t.A ⟶ t.A) [IsMonHom θ] (hpt : ∀ i, t.pt i ≫ θ = t.pt i)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ t.A) (hy : y ^ k = 1) : y ≫ θ = y := by
  obtain ⟨c, rfl, -⟩ := t.bij K x y hy
  let F : (Over.mk x ⟶ t.A) →* (Over.mk x ⟶ t.A) := IsMonHom.monoidHom θ (Over.mk x)
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => (map_pow F _ _).trans (congrArg (· ^ (c i).val) ?_))
  show (_ ≫ t.pt i) ≫ θ = _
  rw [Category.assoc, hpt]

theorem tObj_rigid : Out.Laws → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (f : S ⟶ S'), 3 ≤ k → ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A f φ → IsGrpPullback t.A t'.A f φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  intro hL o _ g k J b S S' s s' t t' f hk φ φ' hφ hφ' hl hl' hpt
  obtain ⟨θ, hθ, e⟩ := grpPullback_iso hφ hφ'
  have hη : ∀ i, t.pt i ≫ θ.hom = t.pt i := fun i => by
    apply Over.OverMorphism.ext
    apply hφ'.1.hom_ext
    · rw [Over.comp_left, Category.assoc, e]
      exact hpt i
    · rw [Over.w, Over.w]
  have h₁ : LBIso (t.L.pull θ.hom.left) (t'.L.pull φ) :=
    LBIso.chartPull (chartPullPull t.L _ θ.hom.left rfl) (chartPullSame t'.L _ _ _ θ.hom.left fun _ => e.symm) hl'
  obtain ⟨w, hw⟩ : LBIso t.L (t.L.pull θ.hom.left) :=
    LBIso.trans t.isLB (pull_isLB t'.isLB φ) (pull_isLB t.isLB _) hl h₁.symm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    simpa using b.unit.map ((Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ s.appTop).hom
  have := t.ab.comm
  have := t.ab.smooth
  have : Etale (Out.mulA t.A k).left := GrpTangent.etale_id_pow t.A hku
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL t.pol k hk θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t.A k θ.hom (fix_geometric_torsion t θ.hom hη))
    obtain ⟨u, hu⟩ := gen_of_iso ((isGen_iff w).1 hw) (t.A.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut t.L _ _ _ _ fun n => ?_) u hu
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← e, h, Over.id_left, Category.id_comp]

end GlobalTheory.TUniq
