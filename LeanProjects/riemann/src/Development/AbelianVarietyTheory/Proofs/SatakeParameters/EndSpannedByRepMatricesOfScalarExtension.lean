import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_endSpanned_map {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ}
    (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L))
    (h : EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))))) :
    EndSpanned τ U := by
  classical
  intro φ
  set UE := Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))) with hUE
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm

  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  set Y : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' (U.subtype ∘ₗ φ ∘ₗ p) with hY
  have hYv : ∀ v : Fin a → L, Y.mulVec v = (φ (p v) : Fin a → L) := by
    intro v
    rw [hY, LinearMap.toMatrix'_mulVec]
    rfl
  have hYU : ∀ w : U, Y.mulVec (w : Fin a → L) = (φ w : Fin a → L) := by
    intro w
    rw [hYv]
    have : p (w : Fin a → L) = w := by
      have := LinearMap.congr_fun hp w
      simpa using this
    rw [this]
  have hYE : ∀ x ∈ UE, (Y.map f).mulVec x ∈ UE := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap, hYv]
      exact Submodule.subset_span ⟨_, (φ (p v)).2, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact UE.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact UE.smul_mem c hx
  let ψ : UE →ₗ[E] UE := (Matrix.mulVecLin (Y.map f)).restrict hYE
  obtain ⟨XE, hXE, hXEw⟩ := h ψ

  let d := Module.finrank L U
  let b := Module.finBasis L U
  let Φ : Matrix (Fin a) (Fin a) L →ₗ[L] (Fin a × Fin d → L) :=
    { toFun := fun M ik => (M.mulVec (b ik.2 : Fin a → L)) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  let ΦE : Matrix (Fin a) (Fin a) E →ₗ[E] (Fin a × Fin d → E) :=
    { toFun := fun M ik => (M.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  set R := Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) with hR
  set RE := Set.range fun g => ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) with hRE
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  have hΦE : ∀ M : Matrix (Fin a) (Fin a) L, ΦE (M.map f) = f ∘ Φ M := by
    intro M
    funext ik
    show ((M.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((M.mulVec (b ik.2 : Fin a → L)) ik.1)
    rw [hmap]; rfl
  set t : Fin a × Fin d → L := fun ik => (φ (b ik.2) : Fin a → L) ik.1 with ht
  have hXt : ΦE XE = f ∘ t := by
    funext ik
    have hmem : f ∘ (b ik.2 : Fin a → L) ∈ UE := Submodule.subset_span ⟨_, (b ik.2).2, rfl⟩
    have := hXEw ⟨_, hmem⟩
    show (XE.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((φ (b ik.2) : Fin a → L) ik.1)
    rw [this]
    show ((Y.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = _
    rw [hmap, hYU]
    rfl
  have hEspan : f ∘ t ∈ Submodule.span E ((fun v => f ∘ v) '' (Φ '' R)) := by
    rw [← hXt]
    have h1 : ΦE XE ∈ Submodule.map ΦE (Submodule.span E RE) := Submodule.mem_map_of_mem hXE
    rw [Submodule.map_span] at h1
    convert h1 using 2
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, hΦE _⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, (hΦE _).symm⟩
  have hLspan := mem_span_of_map_mem_span f (Φ '' R) t hEspan
  rw [← Submodule.map_span] at hLspan
  obtain ⟨X, hX, hXt'⟩ := hLspan
  refine ⟨X, hX, fun w => ?_⟩
  have hb : ∀ k, X.mulVec (b k : Fin a → L) = (φ (b k) : Fin a → L) := by
    intro k
    funext i
    exact congrFun hXt' (i, k)
  have hext : (Matrix.mulVecLin X) ∘ₗ U.subtype = U.subtype ∘ₗ φ := b.ext fun k => by
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Submodule.subtype_apply]
    exact hb k
  exact LinearMap.congr_fun hext w

end GlobalTheory.SplitField
