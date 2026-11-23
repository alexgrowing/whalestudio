import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CommPhase

theorem kap_add (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.kap D T x (y + z) = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Formalism.MainNotions.TaylorLogMetric.kap D T x z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.kap, GlobalTheory.NormSum.VacMove.hf_add_right, Complex.add_im, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem kap_eq_one_of_int (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (m : ℤ)
    (h : (Hf D T x y).im = m) : Formalism.MainNotions.TaylorLogMetric.kap D T x y = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.kap, h]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem chars : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  intro D δ hc 𝔪 a d x hx
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)
  have hint : ∀ y ∈ La0 D (tor0 D ⊤ δ) a d, ∃ m : ℤ, (Hf D (tor0 D ⊤ δ) x y).im = m :=
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _ k0).2.2.1 x hx
  set Lp := La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)
  set S := (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf Lp
  have hwd : ∀ u v : Lp, (QuotientAddGroup.leftRel S) u v →
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d) := by
    intro u v huv
    rw [QuotientAddGroup.leftRel_apply] at huv
    have hm : ((-u + v : Lp) : VC D a d) ∈ La0 D (tor0 D ⊤ δ) a d := AddSubgroup.mem_addSubgroupOf.mp huv
    obtain ⟨m, hm⟩ := hint _ hm
    have h1 := kap_eq_one_of_int D (tor0 D ⊤ δ) x _ m hm
    have hv : (v : VC D a d) = (u : VC D a d) + ((-u + v : Lp) : VC D a d) := by
      push_cast; abel
    rw [hv, kap_add, h1, mul_one]
  let χ : AddChar (Lp ⧸ S) ℂ :=
    { toFun := fun q => Quotient.liftOn' q (fun y : Lp => Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d)) hwd
      map_zero_eq_one' := by
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((0 : Lp) : VC D a d) = 1
        exact kap_eq_one_of_int D (tor0 D ⊤ δ) x _ 0 (by simp [Hf])
      map_add_eq_mul' := by
        intro q r
        induction q using QuotientAddGroup.induction_on
        induction r using QuotientAddGroup.induction_on
        rename_i u v
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((u + v : Lp) : VC D a d) =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) * Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d)
        push_cast
        exact kap_add _ _ _ _ _ }
  exact ⟨χ, fun y => rfl⟩

end GlobalTheory.CommPhase
