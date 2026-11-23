import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTwAn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem isGL_int_of_bdd {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∉ Pr.vGs)
    (hc : GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ) (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k)
    (hg : IsGL ι a g)
    (hb : ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) :
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  obtain ⟨e, -, he⟩ := hg
  have hb' : TwBdd (Pr := Pr) j P a := hb
  have hi : (g⁻¹ : GL _ k).val = GlobalTheory.SymBridge.toLoc ι e e a.symm.toLinearMap := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [he, Model.toLoc_mul, LinearEquiv.comp_symm, Model.toLoc_eq]
    simp
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · rw [hi]
    show ι (a.symm (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [hc.int]
    exact twAn_bdd_inv hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)
  · rw [he, Matrix.smul_apply, hc.unif]
    show ι ((qOf P : ℕ) : X.E) ^ j • ι (a (Pi.single (e s) 1) (e r)) ∈ 𝒪[k]
    rw [smul_eq_mul, ← map_pow, ← map_mul, hc.int]
    exact twAn_bdd_q hP hb' (Pi.single (e s) 1) (fun l => twAn_single_int (e s) l) (e r)

end GlobalTheory.TwBridge
