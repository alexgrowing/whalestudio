import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.TanLift

open MonObj in

theorem exists_isTangent_lift {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] {x : Sp R ⟶ X}
    {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left} (h : IsPullback φ G'.hom t.G.hom x)
    (hu : η[G'].left ≫ φ = x ≫ η[t.G].left) {v : Sp (DualNumber R) ⟶ t.G.left} (hv : Formalism.L2.Pj.IsTanAtG t x v) :
    ∃ p : epsR R ⟶ G', IsTangent p ∧ p.left ≫ φ = v := by
  let p : epsR R ⟶ G' := Over.homMk (h.lift v (epsR R).hom hv.1) (h.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h.lift_fst _ _ _
  refine ⟨p, h.hom_ext ?_ ?_, hp⟩
  · rw [Category.assoc, hp, hu, hv.2]
    simp [Hom.one_def]
  · rw [Category.assoc, Over.w p, Over.w η[G']]
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1

theorem exists_lift : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → ∀ (y₀ : Sp ℂ ⟶ T) (d : (PPAS.ofPolAV Q).RiemannData y₀) (v₀ : Sp (DualNumber ℂ) ⟶ s.T.Z.t.G.left), Formalism.L2.Pj.IsTanAtG s.T.Z.t (y₀ ≫ b) v₀ → ∃ (w : Fin Q.g → ℂ) (v : epsR ℂ ⟶ d.B), IsTangent v ∧ d.u.IsDiff w v ∧ v.left ≫ d.φ ≫ θ = v₀ := by
  intro D A N j S κ s T b Q θ hθ y₀ d v₀ hv
  have h₁ := LieVB.unitSec_comp hθ
  have h₂ := LieVB.unitSec_comp d.isPull
  obtain ⟨v, hT, hp⟩ := exists_isTangent_lift s.T.Z.t (φ := d.φ ≫ θ) (d.isPull.1.paste_horiz hθ.1)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ θ) h₂)).trans
      ((Category.assoc _ _ _).trans ((congrArg (y₀ ≫ ·) h₁).trans (Category.assoc _ _ _).symm))) hv
  obtain ⟨w, hw, -⟩ := (GlobalTheory.UnifTangent.riemannData_tangent T _ y₀ d).1 v hT
  exact ⟨w, v, hT, hw, hp⟩

end GlobalTheory.TanLift
