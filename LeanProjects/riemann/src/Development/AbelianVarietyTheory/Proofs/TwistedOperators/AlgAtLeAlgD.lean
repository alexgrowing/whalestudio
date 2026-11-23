import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf

noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def algAt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = M.vac v) ∧ Φ = pure f φ}

variable (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)

theorem algAt_mono {T T' : Finset (Pl F)} (h : T ⊆ T') : algAt M ψ emb T ≤ algAt M ψ emb T' := by
  refine Submodule.span_mono ?_
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨f, φ, hf, hφ, fun v hv' => hv v fun h' => hv' (h h'), rfl⟩

theorem exists_algAt {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb)
    (T₀ : Finset (Pl F)) : ∃ T, T₀ ⊆ T ∧ Φ ∈ algAt M ψ emb T := by
  classical
  induction hΦ using Submodule.span_induction generalizing T₀ with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hco, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hco
    refine ⟨T₀ ∪ hfin.toFinset, Finset.subset_union_left, Submodule.subset_span ⟨f, φ, hf, hφ, fun v hv => ?_, rfl⟩⟩
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne))
  | zero => exact ⟨T₀, subset_rfl, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    obtain ⟨T₂, h₂, hy₂⟩ := hy T₁
    exact ⟨T₂, h₁.trans h₂, add_mem (algAt_mono M ψ emb h₂ hx₁) hy₂⟩
  | smul c x _ hx =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    exact ⟨T₁, h₁, Submodule.smul_mem _ c hx₁⟩

end GlobalTheory.HoweGlobal

end
