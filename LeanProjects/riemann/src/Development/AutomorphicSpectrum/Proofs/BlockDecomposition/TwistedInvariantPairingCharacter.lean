import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
