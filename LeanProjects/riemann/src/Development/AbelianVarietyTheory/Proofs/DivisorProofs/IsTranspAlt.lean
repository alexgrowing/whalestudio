import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff

noncomputable section

namespace GlobalTheory.ThKAdm

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

structure IsTransp (B : Base F E) (W : Spc F E d) (L : Subgroup (UA σ W.J)) (I : Formalism.MainNotions.S.AutInst) (g : ℕ)
    (e : I.GA →* UA σ W.J) : Prop where
  surj : Function.Surjective e
  cont : Continuous e
  rat : ∀ γ ∈ I.GFset, e γ ∈ ratU σ W.J
  lev : ∀ k ∈ I.Kg g, e (1, k) ∈ L
  kinf : ∀ k : GlobalTheory.Dec.Kinf I, e (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1) ∈ KInf σ W B.emb
  real : ∀ x : I.Ginf, e (x, 1) ∈ UAt σ W (evI F)
  frame : ∃ (ι : InfinitePlace I.F ≃ InfinitePlace F) (Q : InfinitePlace I.F → Matrix (Fin d) (Fin I.n) ℂ)
    (Q' : InfinitePlace I.F → Matrix (Fin I.n) (Fin d) ℂ), (∀ v, Q' v * Q v = 1 ∧ Q v * Q' v = 1) ∧
    ∀ (x : I.Ginf) v, (mat (e (x, 1))).map (piInf (B.emb (ι v))) = Q v * Formalism.MainNotions.S.uMat (x v) * Q' v

end GlobalTheory.ThKAdm

end
