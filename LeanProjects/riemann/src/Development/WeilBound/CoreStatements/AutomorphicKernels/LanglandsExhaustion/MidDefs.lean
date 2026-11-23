import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section Tensor

variable {G H V V' W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

def extL {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ')
    (σ : Representation ℂ H W) : (extTensor ρ σ).IntertwiningMap (extTensor ρ' σ) where
  toLinearMap := f.toLinearMap.rTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

def extR (σ : Representation ℂ H W) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : (extTensor σ ρ).IntertwiningMap (extTensor σ ρ') where
  toLinearMap := f.toLinearMap.lTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Ind

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def ind₂Map (e : a ⊕ b ≃ n) {ρ : Representation ℂ (GL a k × GL b k) V}
    {ρ' : Representation ℂ (GL a k × GL b k) V'} (f : ρ.IntertwiningMap ρ') :
    (ind₂ e ρ).IntertwiningMap (ind₂ e ρ') :=
  parIndMap (two e) (compMap f _)

end Ind

variable {nA nB m m' N : ℕ} {VA VB V V' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def T3 (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) (τ : Representation ℂ (GL (Fin m) k) V) :=
  ind₂ (stdSum h1) (extTensor PA (ind₂ (stdSum h2) (extTensor τ PB)))

def tripleProductMap (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) V'} (f : τ.IntertwiningMap τ') :
    (T3 h2 h1 PA PB τ).IntertwiningMap (T3 h2 h1 PA PB τ') :=
  ind₂Map _ (extR PA (ind₂Map _ (extL f PB)))

end PositivityTheory.Exh

end
