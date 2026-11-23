import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TriFrame

theorem isIso_of_isSubbundle_comp : ∀ (X : Scheme.{0}) [IsIntegral X] (G G' E : X.Modules) (n : ℕ) (i : G ⟶ E) (a : G' ⟶ G), IsVB G n → IsVB G' n → Mono i → IsSubbundle (a ≫ i) → IsIso a := by
  intro X _ G G' E n i a hG hG' hi hs
  have := hs.mono
  have : Mono a := mono_of_mono a i
  have := hG.isFiniteQC
  have := hG'.isFiniteQC
  have : QCoh.IsFiniteQC (cokernel a) := inferInstance
  have hS := shortExact_cokernel_comp a i
  have hm := hS.mono_f
  have htf : IsTorsionFree (cokernel a) :=
    @IsTorsionFree.of_mono X (cokernel (a ≫ i)) (cokernel a) _ hs.isSaturated
      (kernelCokernelCompSequence.snakeInput a i).L₃.f hm
  have h0 := genRank_cokernel a
  rw [hG.genRank_eq, hG'.genRank_eq] at h0
  have hz : IsZero (cokernel a) := htf.isZero (by omega)
  have : Epi a := Preadditive.epi_of_isZero_cokernel a hz
  exact isIso_of_mono_of_epi a

end GlobalTheory.TriFrame
