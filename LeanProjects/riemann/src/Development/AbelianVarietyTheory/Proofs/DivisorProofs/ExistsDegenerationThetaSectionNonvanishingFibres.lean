import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.DegTheta

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (z : Γ(X, U)) :
    resG X h (resG X h' z) = resG X (h.trans h') z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (z : Γ(X, U)) : resG X h z = z := by
  change (X.presheaf.map (homOfLE h).op).hom z = z
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

theorem basicOpen_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (z : Γ(X, U)) :
    X.basicOpen (resG X h z) = V ⊓ X.basicOpen z :=
  Scheme.basicOpen_res X z (homOfLE h).op

def secOfSecOn {X : Scheme.{0}} {L : LB X} {V : X.Opens} (hV : ∀ x : X, x ∈ V) (θ : ∀ i, Γ(X, V ⊓ L.U i))
    (hθ : θ ∈ secOn L V) : L.Sec where
  f i := resG X (le_inf (fun x _ => hV x) le_rfl) (θ i)
  compat i j := by
    have e := congrArg (resG X (le_inf (le_inf (fun x _ => hV x) inf_le_left) inf_le_right : L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
    simp only [map_mul, resG_resG] at e
    change resG X _ (resG X _ (θ i)) = _ * resG X _ (resG X _ (θ j))
    rw [resG_resG, resG_resG, e, resG_self]

end GlobalTheory.DegTheta

namespace GlobalTheory.DegTheta

theorem exists_sec_nonvanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), ∃ th : D.P.L.Sec, (∀ s : Sp R, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i) := by
  intro R _ _ _ _ D F _ _ N ν
  obtain ⟨V, θ, hxV, hθ, H⟩ := GlobalTheory.SecFamily.exists_secOn_nonvanishing GlobalTheory.abelianSchemeLaws_all.1 (Sp R) D.P
    (IsLocalRing.closedPoint R)
  have hVtop : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hxV
  have hV : ∀ a : D.P.A.left, a ∈ D.P.A.hom ⁻¹ᵁ V := fun a => by rw [hVtop]; trivial
  let θ' : D.P.L.Sec := secOfSecOn hV θ hθ
  obtain ⟨r, hr⟩ := ν.th_gen (DVR.toH0 θ')
  refine ⟨DVR.secOfH0 ν.th, fun s => ?_, fun i h => ?_⟩
  · obtain ⟨a, i, has, ha⟩ := H s (by rw [hVtop]; trivial)
    refine ⟨a, has, ?_⟩
    have haU : a ∈ D.P.L.U i := (D.P.A.left.basicOpen_le (θ i) ha).2
    have e := hr (fun _ => i)
    have h1 : a ∈ D.P.A.left.basicOpen ((DVR.toH0 θ').f (fun _ => i)) := by
      have eq1 : (DVR.toH0 θ').f (fun _ => i) = resG _ ((DVR.h0_le (fun _ => i)).trans
          (le_inf (fun x _ => hV x) le_rfl)) (θ i) := resG_resG _ _ _
      rw [eq1]
      exact (basicOpen_resG _ (θ i)).ge ⟨DVR.chart_le_weighted_chart_single i haU, ha⟩
    rw [e, Scheme.basicOpen_mul] at h1
    have h2 : a ∈ D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f i) := by
      have eq2 : (DVR.secOfH0 ν.th).f i = resG _ (DVR.chart_le_weighted_chart_single i) (ν.th.f (fun _ => i)) := rfl
      rw [eq2]
      exact (basicOpen_resG (DVR.chart_le_weighted_chart_single i) _).ge ⟨haU, h1.2⟩
    exact (le_iSup (fun k => D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f k)) i) h2
  · exact ((resG_resG h (DVR.chart_le_weighted_chart_single i) _).trans (resG_self _ _)).symm

end GlobalTheory.DegTheta
