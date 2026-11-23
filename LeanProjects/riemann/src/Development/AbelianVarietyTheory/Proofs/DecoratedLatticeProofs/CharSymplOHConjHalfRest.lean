import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfCocycle

variable {D : D7} {S T : HSp D}

theorem comm4 {R : Type} [CommRing R] (c a h H : R) : c * (a * h * H) = c * a * H * h := by ring

theorem split_half {E R : Type} [Field E] [CharZero E] [CommRing R] (f : E →+* R) (x k : R) :
    x * k = x * (k * f ((2 : ℕ) : E)⁻¹) + x * (k * f ((2 : ℕ) : E)⁻¹) := by
  have h : f ((2 : ℕ) : E)⁻¹ * (1 + 1) = 1 := by
    rw [← map_one f, ← map_add, ← map_mul]
    congr 1
    norm_num
  linear_combination (-(x * k)) * h

theorem half_add {F R : Type} [Field F] [CharZero F] [CommRing R] (g : F →+* R) (t : R) :
    g (1 / 2) * (t + t) = t := by
  have h : g (1 / 2) * (1 + 1) = 1 := by
    rw [← map_one g, ← map_add, ← map_mul]
    congr 1
    norm_num
  linear_combination t * h

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  have h := GlobalTheory.LatVacSign.hO_smul_smul 1 a x y
  rwa [one_smul, one_mul] at h

theorem hO_nsmul_right (n : ℕ) (x y : WO S T) : hO S T x (n • y) = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hO_nsmul_left (n : ℕ) (x y : WO S T) : hO S T (n • x) y = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

set_option maxHeartbeats 1000000 in

theorem char_symplOH_conjHalf_rest : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : ℕ), 0 < c → ∀ (Y Z : WO S T), c • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → Z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → e • Y = c • (e • Z) → ψ (symplOH S T (cA D e • Y) ((1 - cA D e) • Y)) = 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e SS he h2 c hc Y Z hY hZ heq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D (cA D e) = e := GlobalTheory.LatVac.cA_cA e
  have hP : ∀ PP ∈ SS, ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_ofNat]
    exact h2 PP hPP
  have hint : finPart D (e * incA D ((2 : ℕ) : D.host.E)⁻¹) ∈ intAE D :=
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.DatumFourier.idem_div_int he two_ne_zero hP)
  have hZ' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint Z hZ
  have hcA2 : cA D (incA D ((2 : ℕ) : D.host.E)⁻¹) = incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    change incA D (star ((2 : ℕ) : D.host.E)⁻¹) = _
    rw [star_inv₀, star_natCast]
  have k1 : hO S T (cA D e • Y) ((1 - cA D e) • Y) = (c : AE D) * cA D e * hO S T Y Z := by
    have a1 := GlobalTheory.LatVacSign.hO_smul_smul (cA D e) (1 - cA D e) Y Y
    have a2 := hO_smul_right e Y Y
    rw [heq, hO_nsmul_right, hO_smul_right] at a2
    rw [a1, map_sub, map_one, hcc]
    have : cA D e * (1 - e) = cA D e := by
      rw [mul_sub, mul_one, mul_comm, hec, sub_zero]
    rw [this, mul_assoc, ← a2]
  have k2 : hO S T (c • Y) ((e * incA D ((2 : ℕ) : D.host.E)⁻¹) • Z) =
      (c : AE D) * cA D e * hO S T Y Z * incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    rw [hO_nsmul_left, hO_smul_right, map_mul, hcA2]
    exact comm4 _ _ _ _
  rw [symplOH, symplO, k1, split_half (incA D) (incA D D.host.xi0) ((c : AE D) * cA D e * hO S T Y Z), map_add,
    half_add (algebraMap D.host.F (AF D.host.F)), ← k2]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hY hZ'

end GlobalTheory.ConjHalfCocycle

end
