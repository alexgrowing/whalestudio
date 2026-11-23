import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

noncomputable section

namespace PI.LPI

theorem prV_tmul' {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

theorem prV_mem_tensInt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  have hle : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (v.adicCompletion F) (intOE E)
        (v.adicCompletionIntegers F).toSubring).comap (prV (E := E) v) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · change prV (E := E) v ((x : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inl ⟨x, rfl⟩)
    · change prV (E := E) v ((1 : E) ⊗ₜ[F] (a : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inr ⟨⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩, rfl⟩)
  exact hle hs

theorem plDown : PLDown := by
  intro F E _ _ _ _ _ n Lb v y hy
  have hy' : y ∈ Submodule.span (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      ((fun x : Fin n → E => fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ''
        (Lb : Set (Fin n → E))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨l, hl, rfl⟩
  | zero =>
    convert (latV v Lb).zero_mem using 1
    funext j
    simp
  | add x y _ _ hx hy =>
    have h : (fun j => prV (E := E) v ((x + y) j)) =
        (fun j => prV (E := E) v (x j)) + (fun j => prV (E := E) v (y j)) := by
      funext j; simp
    rw [h]
    exact add_mem hx hy
  | smul s x _ hx =>
    have h : (fun j => prV (E := E) v ((s • x) j)) =
        (⟨prV (E := E) v s, prV_mem_tensInt (E := E) v s s.2⟩ :
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) •
          (fun j => prV (E := E) v (x j)) := by
      funext j
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j) = prV (E := E) v s * prV (E := E) v (x j)
      exact map_mul _ _ _
    rw [h]
    exact Submodule.smul_mem _ _ hx

end PI.LPI
