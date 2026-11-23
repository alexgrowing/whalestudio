import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdelesStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem idem_glue_mul {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] {e : R} (hee : e * e = e)
    {x y x' y' : Matrix m m R} (h1 : x * x' = 1) (h2 : y * y' = 1) :
    ((1 - e) • x + e • y) * ((1 - e) • x' + e • y') = 1 := by
  have hce : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have hec : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hcc : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hec, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, h2, hce, hec, hcc, hee, zero_smul,
    add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def idemGlue {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (e : R) (hee : e * e = e)
    (x y : GL m R) : GL m R :=
  ⟨(1 - e) • (x : Matrix m m R) + e • (y : Matrix m m R),
    (1 - e) • ((x⁻¹ : GL m R) : Matrix m m R) + e • ((y⁻¹ : GL m R) : Matrix m m R),
    idem_glue_mul hee (Units.mul_inv x) (Units.mul_inv y), idem_glue_mul hee (Units.inv_mul x) (Units.inv_mul y)⟩

theorem bc_idemGlue_of_zero {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 0) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ x := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((x : Matrix m m R) i j)
  rw [map_add, map_mul, map_mul, map_sub, map_one, h, sub_zero, one_mul, zero_mul, add_zero]

theorem bc_idemGlue_of_one {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 1) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ y := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((y : Matrix m m R) i j)
  rw [map_add, map_mul, map_mul, map_sub, map_one, h, sub_self, zero_mul, one_mul, zero_add]

theorem isLatticeFrame_idemGlue {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {e : AF F ⊗[F] E} (hee : e * e = e) {x : GL (Fin n) (AF F ⊗[F] E)}
    (hx : IsLatticeFrame L x) (y : GL (Fin n) (AF F ⊗[F] E)) (he : ∀ v, compFin F E v e = 0) :
    IsLatticeFrame L (idemGlue e hee x y) := by
  intro v z
  rw [bc_idemGlue_of_zero hee x y _ (he v)]
  exact hx v z

theorem exists_isLatticeFrame_bc_eq (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) :
    ∃ b : GL (Fin A.rank) (AE D), IsLatticeFrame (frameLat A) b ∧
      ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a := by
  obtain ⟨b₀, hb₀, -⟩ :=
    Frames.exists_isLatticeFrame_isMajorantFrame (isCMExt_host D) (isHermND_gram A) (frameLat A)
  obtain ⟨e, hee, -, hfin, hinf, -, -⟩ := GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles D
  exact ⟨idemGlue e hee b₀ a, isLatticeFrame_idemGlue hee hb₀ a hfin, fun w => bc_idemGlue_of_one hee b₀ a _ (hinf w)⟩

end GlobalTheory.StdUnn
