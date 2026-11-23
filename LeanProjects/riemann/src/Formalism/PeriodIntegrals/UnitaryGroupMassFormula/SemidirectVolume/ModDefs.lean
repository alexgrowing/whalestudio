import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ConjInvOfExists

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r)

def Wsub : AddSubgroup (Fin M → R ⊗[F] E) where
  carrier := {w | (∀ a, hR R σ J (ratV (F := F) R (P.e a)) w = 0) ∧
    (∀ a, hR R σ J (ratV (F := F) R (P.f a)) w = 0) ∧ hR R σ J (ratV (F := F) R P.z) w = 0}
  zero_mem' := by
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;> simp [hR, Formalism.UG.hform]
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have hadd : ∀ u x y : Fin M → R ⊗[F] E, hR R σ J u (x + y) = hR R σ J u x + hR R σ J u y :=
      fun u x y => (PG.Dat.hL (datR R σ J P (1 : F)) u).map_add x y
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [hadd, hx1, hy1, add_zero]
    · rw [hadd, hx2, hy2, add_zero]
    · rw [hadd, hx3, hy3, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : ∀ u : Fin M → R ⊗[F] E, hR R σ J u (-x) = -hR R σ J u x := fun u => by
      simp [hR, Formalism.UG.hform, Finset.sum_neg_distrib]
    refine ⟨fun a => ?_, fun a => ?_, ?_⟩
    · rw [hneg, hx1, neg_zero]
    · rw [hneg, hx2, neg_zero]
    · rw [hneg, hx3, neg_zero]

def Sk (r : ℕ) : AddSubgroup (Fin r → Fin r → R ⊗[F] E) where
  carrier := {c | ∀ a b, c a b + sigR R σ (c b a) = 0}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro x y hx hy a b
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [add_add_add_comm, hx a b, hy a b, add_zero]
  neg_mem' := by
    intro x hx a b
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, map_neg] at *
    rw [← neg_add, hx a b, neg_zero]

def betaM (w w' : Fin r → Fin M → R ⊗[F] E) : Fin r → Fin r → R ⊗[F] E := fun a b =>
  inclR (F := F) R (1 / 2 : E) * (hR R σ J (w' a) (w b) - hR R σ J (w a) (w' b))

end Gen

def HeisenbergCoordinates : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∃ Φ : FrameUnipotentSubgroup (AF F) σ J P ≃ₜ ((Fin r → Wsub (AF F) σ J P) × Sk (AF F) σ r),
      (∀ n₀ n : FrameUnipotentSubgroup (AF F) σ J P,
        (fun a => ((Φ (n₀ * n)).1 a : Fin M → AF F ⊗[F] E)) =
          (fun a => ((Φ n₀).1 a : Fin M → AF F ⊗[F] E) + ((Φ n).1 a : Fin M → AF F ⊗[F] E)) ∧
        ((Φ (n₀ * n)).2 : Fin r → Fin r → AF F ⊗[F] E) =
          ((Φ n₀).2 : Fin r → Fin r → AF F ⊗[F] E) + ((Φ n).2 : Fin r → Fin r → AF F ⊗[F] E) +
            betaM (AF F) σ J (fun a => ((Φ n₀).1 a : Fin M → AF F ⊗[F] E))
              (fun a => ((Φ n).1 a : Fin M → AF F ⊗[F] E))) ∧
      (∀ h ∈ Hsub (AF F) σ J P, ∀ n n' : FrameUnipotentSubgroup (AF F) σ J P,
        (n' : HA (AF F) σ J) = h * n * h⁻¹ →
        (∀ a, ((Φ n').1 a : Fin M → AF F ⊗[F] E) = lin (AF F) σ J h ((Φ n).1 a)) ∧
          (Φ n').2 = (Φ n).2)

theorem lin_mem_Wsub {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
    {P : Frame E M r} {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ Wsub R σ J P) : lin R σ J h w ∈ Wsub R σ J P := by
  have hS := heisenberg_le_stabilizer R σ J P hh
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · rw [← stabilizer_fixes_frame_vector R σ J P hS a, hR_lin]; exact h1 a
  · have := hh
    rw [Hsub, mem_stabT] at this
    have hf := this (Fin.natAdd (r + 1) a)
    rw [tupH_f] at hf
    rw [← hf, hR_lin]; exact h2 a
  · rw [← stabilizer_fixes_normal_vector hS, hR_lin]; exact h3

def actW {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
    {P : Frame E M r} {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : Wsub R σ J P) :
    Wsub R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wsub hh w.2⟩

def WMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ (h : HA (AF F) σ J) (hh : h ∈ Hsub (AF F) σ J P) (μ : Measure (Wsub (AF F) σ J P)),
      μ.IsAddHaarMeasure → μ.map (actW hh) = μ

end PI.VolSemiDirect.W.Md
