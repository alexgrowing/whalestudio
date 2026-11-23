import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf

noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

def IsLogA (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) : Prop :=
  ∀ n : ℕ, y - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (Reformulated.AutPerF.BdRPlus l (OC l)) ((-1) ^ (i + 1) / i) *
    (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
      (WittVector.teichmuller l ε) - 1) ^ i ∈ RingHom.ker (Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l)) ^ n

theorem mem_ker_pow_iff_of_equiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (c : A ≃+* B) (f : A →+* C) (g : B →+* C) (h : ∀ y, g (c y) = f y) (n : ℕ) (y : A) :
    y ∈ RingHom.ker f ^ n ↔ c y ∈ RingHom.ker g ^ n := by
  have hk : RingHom.ker g = (RingHom.ker f).map c := by
    ext z
    obtain ⟨x, rfl⟩ := c.surjective z
    rw [Ideal.apply_mem_of_equiv_iff, RingHom.mem_ker, RingHom.mem_ker, h]
  rw [hk, ← Ideal.map_pow, Ideal.apply_mem_of_equiv_iff]

theorem ringEquiv_algebraMap_rat {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (c : A ≃+* B) (q : ℚ) : c (algebraMap ℚ A q) = algebraMap ℚ B q :=
  RingHom.congr_fun (RingHom.ext_rat (c.toRingHom.comp (algebraMap ℚ A)) (algebraMap ℚ B)) q

theorem isLogA_iff_of_compat (c : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l)
    (ha : ∀ a : Reformulated.AutPerF.Ainf l (OC l), c (algebraMap _ _ a) = Formalism.Per6.aD l a)
    (hθ : ∀ y, Formalism.Per6.θD l (c y) = Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y)
    (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (c y) := by
  refine forall_congr' fun n => ?_
  rw [mem_ker_pow_iff_of_equiv c _ _ hθ, map_sub, map_sum]
  simp only [map_mul, map_pow, map_sub, map_one, ringEquiv_algebraMap_rat, ha]

end Cmp6
