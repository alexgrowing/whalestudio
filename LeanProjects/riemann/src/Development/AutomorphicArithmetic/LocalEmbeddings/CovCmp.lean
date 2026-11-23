import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.CovCmp

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def CRead (V : Mean4O.Cover Y) (v : HeightOneSpectrum (𝓞 F)) (L : LB V.X) (s : L.ι → V.X.functionFieldˣ)
    (l : TrueGeo.Ext v → AlgPt Y → ℝ) : Prop :=
  IsRatSec L s ∧ ∃ W : Y.X.Opens, genericPoint Y.X ∈ W ∧
    ∀ (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) (i : L.ι),
      below y.1 ∈ W → z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.U i →
      UnitAt (below (z ≫ V.j)) (s i : V.X.functionField) →
      Real.log (e.w (TrueGeo.valAt (z ≫ V.j) (s i : V.X.functionField))) = l e y

theorem cRead_of_gReads (Q : TrueGeo.Model Y) [IsIntegral Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X)
    {v : HeightOneSpectrum (𝓞 F)} {L : LB Q.X} {s : L.ι → Q.X.functionFieldˣ} {l : TrueGeo.Ext v → AlgPt Y → ℝ}
    (h : GReads Q v L s l) : CRead (Mean4O.Cover.ofModel Q hQ) v L s l := by
  obtain ⟨h₁, W, hW, h₂⟩ := h
  refine ⟨h₁, W, hW, fun e y z yt i a₁ a₂ a₃ a₄ _ => ?_⟩
  obtain rfl : z = y.1 := (Category.comp_id _).symm.trans a₂
  exact (h₂ e y yt i a₁ a₃ a₄).2

def pullSec {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : X ⟶ Z) (hg : g (genericPoint X) ⤳ genericPoint Z)
    {N : LB Z} (s : N.ι → Z.functionFieldˣ) : (N.pull g).ι → X.functionFieldˣ :=
  fun J => Units.map (SmallSec.fnMap g hg).toMonoidHom (s (J PUnit.unit))

theorem isRatSec_pullSec {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : X ⟶ Z)
    (hg : g (genericPoint X) ⤳ genericPoint Z) {N : LB Z} {s : N.ι → Z.functionFieldˣ} (hs : IsRatSec N s) :
    IsRatSec (N.pull g) (pullSec g hg s) := by
  intro J K h
  have le : (N.pull g).U J ⊓ (N.pull g).U K ≤ g ⁻¹ᵁ (N.U (J PUnit.unit) ⊓ N.U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hgg : (N.pull g).g J K = res le (pullU g _ (N.g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  have hZ : genericPoint Z ∈ N.U (J PUnit.unit) ⊓ N.U (K PUnit.unit) :=
    gen_mem (x := g (genericPoint X)) (le h)
  have e : fnOf _ h (res le (pullU g _ (N.g (J PUnit.unit) (K PUnit.unit)))).val =
      SmallSec.fnMap g hg (fnOf _ hZ (N.g (J PUnit.unit) (K PUnit.unit)).val) :=
    (fnOf_resG le h _).trans (SmallSec.fnMap_fnOf g hg hZ (le h) _).symm
  rw [hgg, e]
  simp only [pullSec, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [hs _ _ hZ, map_mul]

end GlobalTheory.CovCmp

end
