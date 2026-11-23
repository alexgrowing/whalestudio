import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ValuesSubfield
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_numOf_th {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) :
    ∃ (N₁ : NumD F) (ν₁ : NumOf D F N₁), ν₁.J = ν.J ∧ ν₁.th = th :=
  ⟨{ N with th := fun x => sF th (ν.eA x).left ν.J / rigVal ν },
    { ν with th := th, th_gen := hth, th_eq := fun _ => div_mul_cancel₀ _ (vF_ne_zero ν.good _ _) }, rfl, rfl⟩

theorem exists_values_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  intro hG R _ _ D he hb F F' _ _ _ _ f hf N' ν'
  obtain ⟨N₀, ν₀, h₀⟩ := ValuesExist.exists_numOf D F hG he hb ν'.th ν'.th_gen (fun ψ => ν'.J (spMap f ≫ ψ))
    fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F) (spMap f (IsLocalRing.closedPoint F')) z) ▸
      ν'.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F'))
  obtain ⟨N, ν, h₁, h₂⟩ := exists_numOf_th ν₀ ν'.th ν'.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := fun ψ => by rw [h₁, h₀]
  refine ⟨N, ν, numHom f hf ν ν' hJ h₂.symm, eX_numHom f hf ν ν' hJ h₂.symm, fun k p p' c c' h hc hc' => ?_⟩
  obtain rfl := (qkExt_iff hb f hf p p').1 h
  exact numHom_rel f hf ν ν' hJ h₂.symm hc hc'

end GlobalTheory.ValuesSubfield
