import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.GenModelXi

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable (D : D7)

def HfS (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by intro c a b; simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_div_assoc', Finset.mul_sum]; simp only [Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by intro c a b; simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [mul_div_assoc', Finset.mul_sum]; simp only [Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
          fun _ _ => by ring)

def Bridge : Prop :=
  ∀ (D : D7) (T : Tor D) (N N' : ℕ),
    IsHerm (HfS D T N N') ∧
    (∀ (x : VC D N N') (G : VC D N N' → ℂ), U D T x G = opU (HfS D T N N') x G) ∧
    (∀ (La₁ La₂ : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ),
      Iop D T La₁ La₂ G = inter (HfS D T N N') (al D T) La₁ La₂ G) ∧
    (∀ La' : AddSubgroup (VC D N N'), ThSp D T La' ⊆ (fixedBy (HfS D T N N') (al D T) La' : Set _)) ∧
    ∀ La' : AddSubgroup (VC D N N'), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La' → IsSemiChar (HfS D T N N') La' (al D T)

abbrev Pair (N N' : ℕ) : Type :=
  Submodule (𝓞 D.host.E) (Fin N → D.host.E) × Submodule (𝓞 D.host.E) (Fin N' → D.host.E)

def HalvesRec : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₀ L₀' →
    ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), SplitP D P →
    ∀ s : Finset (Pair D N N'), (∀ q ∈ s, admitted D N N' q.1 q.2 ∧ EqOff D P q.1 L₀ ∧ EqOff D P q.2 L₀') →
      ∃ (A B : AddSubgroup (VC D N N')) (φ : A → Matrix (Fin N') (Fin N) (EP D P)),
        IsSemiChar (HfS D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) ∧
        IsSemiChar (HfS D (tor0 D cc δ) N N') B (al D (tor0 D cc δ)) ∧
        GoodLat (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A B (La D (tor0 D cc δ) L₀ L₀') ∧
        ∀ q ∈ s, GoodLat (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A B (La D (tor0 D cc δ) q.1 q.2) ∧
          relIdx (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) q.1 q.2) ≠ 0 ∧
          (∀ a : A, (a : VC D N N') ∈ La D (tor0 D cc δ) q.1 q.2 ↔ φ a ∈ (YP D P q.1 q.2 : Set _)) ∧
          volP (YP D P L₀ L₀') (YP D P q.1 q.2) = volA A (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) q.1 q.2)

def ModelXiNZ : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₀ L₀' →
    ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), SplitP D P →
    ∀ th ∈ Th D (tor0 D cc δ) L₀ L₀',
    ∃ Xi : (Matrix (Fin N') (Fin N) (EP D P) → ℂ) →ₗ[ℂ] (VC D N N' → ℂ),
      Xi (Set.indicator (YP D P L₀ L₀' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) = th ∧
      ∀ L L', admitted D N N' L L' → EqOff D P L L₀ → EqOff D P L' L₀' →
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L L') th =
          fun z => (((Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')))⁻¹ : ℝ) : ℂ) *
            Xi (Set.indicator (YP D P L L' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) z

def DiscrNZ : Prop := ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → discr (lamOf D cc 1) ≠ 0

end Formalism.L2.PairingIndexBounds.Rec
