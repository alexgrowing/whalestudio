import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsLatRepL {nS nT : ℕ} (σ : E →ₐ[F] E) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (hc : HeisClosedF σ JS JT ξ₀ ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)) : Prop where
  hw : w + sgOF σ w = 1
  sd : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} = ⊤
  fin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0
  op : ∀ p x v, Om p (opFF hc w x v) = opFF hc w (rhoFF σ JS JT p x) (Om p v)
  sd' : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))
  vac : ∀ p e, Fixes (opFF hc w) (latF F E nS nT Λ) e →
    Om p e = normOp lam (opFF hc w) (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) e
  good : GoodNorm (sgOF σ) lam
  lev : ∀ x : XFF F E nS nT, ∃ N : ℕ, 0 < N ∧ ∀ l ∈ latF F E nS nT Λ,
    ψ (symplOHF σ JS JT ξ₀ (x : WOF F E nS nT) (N • (l : WOF F E nS nT))) = 1
  near : ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ
  near' : ∀ (x : XFF F E nS nT) (N : ℕ), 0 < N → ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l
  splitStab : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ

end UpperTheory.TP.W

end
