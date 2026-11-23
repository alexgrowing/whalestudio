import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjSplit

theorem sigR_incA (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  simp [cA, sigR, incA, inclR]

def ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram) : GA D V :=
  ⟨Formalism.UG.bc (incA D) γ, by
    show Formalism.UG.cT _ _ * _ * _ = _
    have hc : Formalism.UG.cT (cA D) ((γ : Matrix _ _ D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR_incA]
    have := congrArg (fun M => M.map (incA D)) hγ
    simp only [Matrix.map_mul] at this
    simpa [Formalism.UG.bc, JR, hc] using this⟩

theorem finE_ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    (Formalism.IndefR.Lev.finE V (ratPt D V γ hγ)).1 = γ.1.map (eToEAf D) := by
  ext i j
  change Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E
    (Algebra.TensorProduct.map (AlgHom.snd (↥D.host.F) (Ainf ↥D.host.F) (Af ↥D.host.F)) (AlgHom.id (↥D.host.F) D.host.E)
      (Algebra.TensorProduct.includeRight (γ.1 i j))) = _
  simp [eToEAf]

theorem mt_mul (D : D7) (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_mul_inv (D : D7) (V : HSp D) (a : GA D V) : mt V a * mt V a⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel]; simp [Formalism.L2.Theta.mt]

theorem suppAt_conj {D : D7} {V : HSp D} {e : AE D} {h : GA D V} (hs : SuppAt e V h) (g : GA D V) :
    SuppAt e V (g * h * g⁻¹) := by
  have hm : (e + cA D e) • (mt V h - 1) = mt V h - 1 := Matrix.ext fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hs i j
  have key : mt V (g * h * g⁻¹) - 1 = mt V g * (mt V h - 1) * mt V g⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have hm' : (e + cA D e) • (mt V (g * h * g⁻¹) - 1) = mt V (g * h * g⁻¹) - 1 := by
    rw [key, ← Matrix.smul_mul, ← Matrix.mul_smul, hm]
  intro i j
  have := congrFun (congrFun hm' i) j
  rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem finE_ratPt_units (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    Formalism.IndefR.Lev.finE V (ratPt D V γ hγ) = Formalism.UG.bc (eToEAf D) γ :=
  Units.ext (finE_ratPt D V γ hγ)

theorem conj_supp : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  intro D V S γ h hγ hh ⟨P, e, he, hs, hoff⟩
  refine ⟨ratPt D V γ hγ * h * (ratPt D V γ hγ)⁻¹, ?_, ⟨P, e, he, suppAt_conj hs _, hoff⟩, ?_⟩
  · exact (MonoidHom.normal_ker (infHom V)).conj_mem h hh _
  · rw [map_mul, map_mul, map_inv, finE_ratPt_units, Units.val_mul, Units.val_mul, ← map_inv]
    rfl

end GlobalTheory.ConjSplit
