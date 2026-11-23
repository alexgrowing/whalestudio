import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

def conjF (G : HTGroup p) : G.F →ₐ[ℚ] G.F :=
  ((IsCMField.complexConj G.F : G.F →+* G.F)).toRatAlgHom

def rhoL (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    ℚ_[p] ⊗[ℚ] algF P →ₐ[ℚ_[p]] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
  (G.locW w).comp (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p])
    ((algF P).val : algF P →+* G.C).toRatAlgHom)

def inclF (G : HTGroup p) (P : Pair G) : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] algF P :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (algebraMap G.F (algF P)).toRatAlgHom

variable {G : HTGroup p} {P : Pair G}

theorem rhoL_tmul (w : Fin G.m) (a : ℚ_[p]) (x : algF P) :
    rhoL G P w (a ⊗ₜ x) = algebraMap ℚ_[p] _ a * G.rho w (x : G.C) := by
  simp [rhoL, HTGroup.locW, Algebra.TensorProduct.lift_tmul]
  rfl

theorem rhoL_one_tmul (w : Fin G.m) (x : algF P) :
    rhoL G P w ((1 : ℚ_[p]) ⊗ₜ x) = G.rho w (x : G.C) := by
  rw [rhoL_tmul, map_one, one_mul]

theorem algebraMap_injective (G : HTGroup p) (P : Pair G) :
    Function.Injective (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] algF P)) := by
  intro a b h
  have hL : Function.Injective (algebraMap ℚ (algF P)) := (algebraMap ℚ (algF P)).injective
  apply Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ_[p]) (A := ℚ_[p]) (B := algF P) hL
  simpa [Algebra.TensorProduct.algebraMap_apply] using h

theorem mem_simT_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {x : Aˣ} :
    x ∈ GlobalTheory.LKTorus.simT k c ↔ ∃ t : kˣ, (x : A) * c x = algebraMap k A t := Iff.rfl

section Phi

variable (G P) (c : algF P →ₐ[ℚ] algF P)

def nuP : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* ℚ_[p]ˣ where
  toFun s := Classical.choose (mem_simT_iff.1 s.2)
  map_one' := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (1 : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).2)]
    simp [Algebra.TensorProduct.one_def]
  map_mul' s t := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (s * t).2), Units.val_mul, map_mul,
      ← Classical.choose_spec (mem_simT_iff.1 s.2), ← Classical.choose_spec (mem_simT_iff.1 t.2)]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    ring

variable {G P c}

def gamL (P : Pair G) : algF P := ⟨(P.γ : G.C), Algebra.subset_adjoin rfl⟩

theorem rhoL_comm (w : Fin G.m) (y : ℚ_[p] ⊗[ℚ] algF P) :
    G.rho w (P.γ : G.C) * rhoL G P w y = rhoL G P w y * G.rho w (P.γ : G.C) := by
  have h : G.rho w (P.γ : G.C) = rhoL G P w ((1 : ℚ_[p]) ⊗ₜ gamL P) := (rhoL_one_tmul w (gamL P)).symm
  rw [h, ← map_mul, ← map_mul, mul_comm]

variable (G P c)

def phiG : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* Gp G :=
  (nuP G P c).prod (MonoidHom.pi fun w =>
    (Units.map ((rhoL G P w).toRingHom.toMonoidHom)).comp (GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).subtype)

theorem phiG_mem (s : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)) :
    phiG G P c s ∈ Subgroup.centralizer {P.atP} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Prod.ext (mul_comm _ _) (funext fun w => Units.ext ?_)
  exact (rhoL_comm w _).symm

def phiP : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* Subgroup.centralizer {P.atP} :=
  (phiG G P c).codRestrict _ (phiG_mem G P c)

end Phi

end GlobalTheory.CentAtP
