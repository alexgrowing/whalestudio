import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ext_cmp {z₁ z₂ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ w, GlobalTheory.HeckeRowsCompare.cmp D w z₁ = GlobalTheory.HeckeRowsCompare.cmp D w z₂) : z₁ = z₂ := by
  refine (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E)).ext_elem fun i => ?_
  refine FiniteAdeleRing.ext _ fun w => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (h w)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, GlobalTheory.HeckeRowsCompare.repr_map] at e
  exact e

theorem mul_comm_of_locAt (V : Formalism.BasicNotions.TH.HSp D) {v v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ≠ v') {x y : Bridge.Gf V}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v' y) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ext_cmp
  intro w
  have hm : ∀ a b : Bridge.Gf V,
      GlobalTheory.HeckeRowsCompare.cmp D w ((a * b : Bridge.Gf V).1.1 i j) =
        ((a.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w)) * (b.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w))) i j := by
    intro a b
    rw [← Matrix.map_mul]
    rfl
  show GlobalTheory.HeckeRowsCompare.cmp D w ((x * y : Bridge.Gf V).1.1 i j) = GlobalTheory.HeckeRowsCompare.cmp D w ((y * x : Bridge.Gf V).1.1 i j)
  rw [hm, hm]
  by_cases hw : w = v
  · subst hw
    have h1 : y.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hy w hv
    rw [h1, mul_one, one_mul]
  · have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hx w hw
    rw [h1, mul_one, one_mul]

theorem mul_comm_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ)
    (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x →
      isLocEnv V pl ok i' y → x * y = y * x := by
  intro D V Pl0 pl ok i i' x y hv hx hy
  exact mul_comm_of_locAt V hv
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx))
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ y ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i' y).2.1 hy))

end GlobalTheory.LocComm

end
