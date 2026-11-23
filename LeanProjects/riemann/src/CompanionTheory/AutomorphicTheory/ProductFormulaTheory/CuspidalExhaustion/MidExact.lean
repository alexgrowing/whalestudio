import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.MidDefs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import BuildAid.D1

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

section TensorExact

variable {G H V₁ V₂ V₃ W : Type} [Group G] [Group H] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
  [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup W] [Module ℂ W]
  {τ₁ : Representation ℂ G V₁} {τ₂ : Representation ℂ G V₂} {τ₃ : Representation ℂ G V₃}

theorem extL_exact (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (σ : Representation ℂ H W)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extL f σ) ∧ Function.Exact (extL f σ) (extL g σ) :=
  ⟨Module.Flat.rTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.rTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

theorem extR_exact (σ : Representation ℂ H W) (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extR σ f) ∧ Function.Exact (extR σ f) (extR σ g) :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.lTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

end TensorExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section IndExact

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
  {ρ₁ : Representation ℂ (GL a k × GL b k) V₁} {ρ₂ : Representation ℂ (GL a k × GL b k) V₂}
  {ρ₃ : Representation ℂ (GL a k × GL b k) V₃}

theorem ind₂Map_exact (e : a ⊕ b ≃ n) (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (ind₂Map (k := k) e f) ∧ Function.Exact (ind₂Map (k := k) e f) (ind₂Map (k := k) e g) := by
  refine ⟨GlobalTheory.ParIndExact.parIndMap_injective _ _ hf, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · exact GlobalTheory.ParIndExact.parIndMap_exact _ (compMap f _) (compMap g _) hf
      (fun v hv => by obtain ⟨u, hu⟩ := (hfg v).1 hv; exact ⟨u, hu⟩) y hy
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hfg.apply_apply_eq_zero (u.1.1 x)

end IndExact

variable {nA nB m m' N : ℕ} {VA VB V₁ V₂ V₃ : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

set_option maxHeartbeats 1000000 in

theorem tripleProductMap_injective (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ₁ : Representation ℂ (GL (Fin m) k) V₁}
    {τ₂ : Representation ℂ (GL (Fin m) k) V₂} {τ₃ : Representation ℂ (GL (Fin m) k) V₃}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    Function.Injective (tripleProductMap h2 h1 PA PB f) ∧ Function.Exact (tripleProductMap h2 h1 PA PB f) (tripleProductMap h2 h1 PA PB g) := by
  have s1 := extL_exact (G := GL (Fin m) k) (H := GL (Fin nB) k) f g PB hf hfg
  have s2 := ind₂Map_exact (k := k) (stdSum h2) (extL f PB) (extL g PB) s1.1 s1.2
  have s3 := extR_exact (G := GL (Fin m') k) (H := GL (Fin nA) k) PA (ind₂Map (k := k) (stdSum h2) (extL f PB))
    (ind₂Map (k := k) (stdSum h2) (extL g PB)) s2.1 s2.2
  exact ind₂Map_exact (k := k) (stdSum h1) (extR PA (ind₂Map (k := k) (stdSum h2) (extL f PB)))
    (extR PA (ind₂Map (k := k) (stdSum h2) (extL g PB))) s3.1 s3.2

end CompanionTheory.Exh

end
