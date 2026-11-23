import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section ULim

variable {ι R : Type} [CommRing R] (F : Filter ι) (I : ℕ → Ideal R)
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def uNull : Submodule R (∀ i, M i) where
  carrier := {p | ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i))}
  add_mem' ha hb j := ((ha j).and (hb j)).mono fun _ h => add_mem h.1 h.2
  zero_mem' _ := Eventually.of_forall fun _ => zero_mem _
  smul_mem' c _ h j := (h j).mono fun _ h => Submodule.smul_mem _ c h

variable {F I M} in
theorem mem_uNull {p : ∀ i, M i} :
    p ∈ uNull F I M ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := Iff.rfl

abbrev ULim : Type := (∀ i, M i) ⧸ uNull F I M

def ULim.mk : (∀ i, M i) →ₗ[R] ULim F I M := (uNull F I M).mkQ

theorem ULim.mk_surjective : Function.Surjective (ULim.mk F I M) := Submodule.mkQ_surjective _

variable {F I M} in
theorem ULim.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F I M p = 0 ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := by
  show (uNull F I M).mkQ p = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

variable {I M} in

def ULim.map {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) : ULim F I M →ₗ[R] ULim F I' M' :=
  Submodule.mapQ _ _ (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) fun p hp j =>
    (hp j).mono fun i hi => by
      have h1 : f i (p i) ∈ Submodule.map (f i) (I j • ⊤ : Submodule R (M i)) := ⟨_, hi, rfl⟩
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono (h j) le_top h1

variable {I M} in
theorem ULim.map_mk {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) (p : ∀ i, M i) :
    ULim.map F h f (ULim.mk F I M p) = ULim.mk F I' M' fun i => f i (p i) := rfl

def ULim.scal (r : ι → R) : ULim F I M →ₗ[R] ULim F I M :=
  ULim.map F (fun _ => le_rfl) fun i => r i • LinearMap.id

theorem ULim.scal_const (r : R) (x : ULim F I M) : ULim.scal F I M (fun _ => r) x = r • x := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
  rfl

variable (R) in

abbrev UProd : Type := ULim F (fun _ => (⊥ : Ideal R)) M

variable {F M} in
theorem UProd.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F (fun _ => (⊥ : Ideal R)) M p = 0 ↔ ∀ᶠ i in F, p i = 0 := by
  rw [ULim.mk_eq_zero]
  simp

theorem UProd.pure_bijective (i₀ : ι) :
    ∃ e : UProd R (pure i₀) M →ₗ[R] M i₀, Function.Bijective e ∧ ∀ p, e (ULim.mk _ _ M p) = p i₀ := by
  refine ⟨Submodule.liftQ _ (LinearMap.proj i₀) fun p hp => ?_, ⟨?_, ?_⟩, fun _ => rfl⟩
  · simpa using hp 0
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ M x
    exact UProd.mk_eq_zero.2 hx
  · classical
    intro m
    exact ⟨ULim.mk _ _ M (Pi.single i₀ m), by
      show (Pi.single i₀ m : ∀ i, M i) i₀ = m
      simp⟩

end ULim

section QReg

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def QRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (J : Ideal R) (a : ℕ) : Prop :=
  ∀ c : GlobalTheory.MonoDeg σ a → M,
    ∑ α, GlobalTheory.monoVal y α.1 • c α ∈ ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ ((Ideal.span (Set.range y) ⊔ J) • ⊤ : Submodule R M)

theorem isQuasiRegularSeq_iff_qRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) :
    GlobalTheory.IsQuasiRegularSeq M y ↔ ∀ a, QRegAt M y ⊥ a := by
  unfold GlobalTheory.IsQuasiRegularSeq QRegAt
  simp only [sup_bot_eq]

theorem qRegAt_top (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (a : ℕ) : QRegAt M y ⊤ a :=
  fun _ _ _ => by simp

end QReg

end UpperTheory.V.AlgebraTools
