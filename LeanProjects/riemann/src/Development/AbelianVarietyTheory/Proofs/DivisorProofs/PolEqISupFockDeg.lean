import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (k : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})
    (fun _ N => N ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) k

theorem fockDeg_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    fockDeg M ψ τ 0 = Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀} := rfl

theorem fockDeg_succ (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ (k + 1) = fockDeg M ψ τ k ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
      ActsD (evI F) (M.heisLine ψ u) f f₁} := rfl

def lowDegInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : ℕ :=
  sInf {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}

def lowPartInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Submodule ℂ P :=
  (fockDeg M B.ψ B.emb (lowDegInf B M p)).map p

theorem fockDeg_mono (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Monotone (fockDeg M ψ τ) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem fockDeg_le_pol (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ k ≤ M.Pol ψ τ := by
  induction k with
  | zero => exact Submodule.span_le.2 fun f hf => Submodule.mem_sInf.2 fun N hN => hN.1 f hf
  | succ k ih =>
    refine sup_le ih (Submodule.span_le.2 ?_)
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 (ih hf) N hN) f₁ hd

theorem pol_eq_iSup_fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = ⨆ k, fockDeg M ψ τ k := by
  refine le_antisymm (sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ hd => ?_⟩) (iSup_le (fockDeg_le_pol M ψ τ))
  · exact Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hf₀)
  · obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M ψ τ).directed_le).1 hf
    exact Submodule.mem_iSup_of_mem (k + 1)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, f, hk, hd⟩))

theorem lowPartInf_ne_bot (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (h : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0) : lowPartInf B M p ≠ ⊥ := by
  obtain ⟨f, hf, hp⟩ := h
  rw [pol_eq_iSup_fockDeg] at hf
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M B.ψ B.emb).directed_le).1 hf
  have hne : {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}.Nonempty := ⟨k, f, hk, hp⟩
  obtain ⟨g, hg, hpg⟩ := Nat.sInf_mem hne
  intro hbot
  exact hpg ((Submodule.eq_bot_iff _).1 hbot (p g) ⟨g, hg, rfl⟩)

end GlobalTheory.IndLine
