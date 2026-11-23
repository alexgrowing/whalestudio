import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.LabConv

theorem isCuspOf_of_hasCuspLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  intro g _ L t ht hζ htL d V P hd hcusp hlab
  subst htL
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := hlab
  rw [Fintype.card_fin] at hdeg
  have hPl : GlobalTheory.GLq.IsPrimeLab d P := ⟨hm, hi, Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX, hdeg⟩
  refine ⟨hPl, hcusp, ?_⟩
  intro x hx y hy z hz
  have hd0 : 0 < d := hd
  have hcpl : GlobalTheory.GLq.IsPrimeLab d (y : GlobalTheory.GLq.Mt g d).charpoly := by
    refine ⟨Matrix.charpoly_monic _, hy, ?_, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩
    intro h0
    have hdet := Matrix.det_eq_sign_charpoly_coeff (y : GlobalTheory.GLq.Mt g d)
    rw [h0, mul_zero] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit y) |>.ne_zero hdet
  have hz1 : z ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hcpl hz
  have hx1 : x ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hPl hx
  have hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd0]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (g ^ d - 1) := ⟨by
    have := Nat.one_lt_pow hd0.ne' (Fact.out : g.Prime).one_lt
    omega⟩
  obtain ⟨m, -, hmz⟩ := hprim.eq_pow_of_pow_eq_one hz1
  have hax : aeval x P = 0 := GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem hm.ne_zero hx
  have haz : aeval z (y : GlobalTheory.GLq.Mt g d).charpoly = 0 :=
    GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem (Matrix.charpoly_monic _).ne_zero hz
  have hmz' : (Formalism.L2.NT.convC L.teich ht L.gen hζ).gen (Fintype.card (Fin d)) ^ m = z := by
    rw [Fintype.card_fin]; exact hmz
  have e := hval x hax y hy z haz m hmz'
  simp only [Fintype.card_fin, ZMod.card] at e
  have htx : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  show LinearMap.trace ℂ V (V.ρ y) = _
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmz, ← pow_mul, GlobalTheory.GLq.LabelUnique.thetaOf_gen_pow L d hd0 x htx]
  rfl

end GlobalTheory.SerCmp.LabConv
