import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagQ

variable {ι : Type} [Fintype ι] {N : ℕ} {Y : Var ℚ}

def genMat (j : Y.X ⟶ Fl ι N) : ι → GL (Fin N) Y.Fn :=
  (exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) N Prod.fst Prod.snd Y.Fn ((ratOf Y).pt ≫ j)).choose

theorem flagPt_genMat (j : Y.X ⟶ Fl ι N) :
    (ratOf Y).pt ≫ j = flagPt Prod.fst Prod.snd (genMat j) :=
  (exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) N Prod.fst Prod.snd Y.Fn ((ratOf Y).pt ≫ j)).choose_spec

def genFrame (j : Y.X ⟶ Fl ι N) : Mat (fun _ : ι => N) Y.Fn := fun τ => (genMat j τ).1.transpose

def IsFrame (j : Y.X ⟶ Fl ι N) (y : Y.X) (A : Mat (fun _ : ι => N) Y.Fn) : Prop :=
  Par 0 ((ratOf Y).O y).toSubring A ∧ Par (fun _ => N) ⊤ (A * (genFrame j)⁻¹)

def ptQ : Sp ℚ ⟶ PSpace ℚ 0 :=
  GlobalTheory.ProjSpace.pt (RingHom.id ℚ) (fun _ => 1) (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

def toPt (Y : Var ℚ) : Y.X ⟶ (proj ℚ 0).X := Y.str ≫ ptQ ≫ @inv _ _ _ _ (proj ℚ 0).ι (isIso_proj_ι ℚ 0)

def triv (ι : Type) (N : ℕ) : Fr (ratOf (proj ℚ 0)) (fun _ : ι => N) 0 :=
  Fr.ofBasis _ 0 1 fun _ => by simp

end GlobalTheory.FlagQ
