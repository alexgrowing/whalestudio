import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace CompanionTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  have h : ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s : ℂ) := rfl
  rw [h, ← Complex.ofReal_cpow (by unfold nabs; positivity), Complex.conj_ofReal]

end ConjDual

open ConjDual in
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, hsym, hpos, hinv⟩ := hu

  have key : ∀ (g : GL (Fin n) k) (x v : V), B (ρ g⁻¹ x) v = B x (ρ g v) := by
    intro g x v
    have := hinv g (ρ g⁻¹ x) v
    rw [← this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

  have hsm : ∀ v : V, (B.flip v : Module.Dual ℂ V) ∈ smoothPart ρ.dual := by
    intro v
    let H₁ : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    let H₂ : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ρ.dual g (B.flip v) = B.flip v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by
          show ρ.dual 1 (B.flip v) = B.flip v
          rw [map_one, Module.End.one_apply]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : H₁ ≤ H₂ := by
      intro g hg
      show ρ.dual g (B.flip v) = B.flip v
      ext x
      have hg' : ρ g v = v := hg
      rw [Representation.dual_apply]
      show B (ρ g⁻¹ x) v = B x v
      rw [key, hg']
    exact Subgroup.isOpen_mono hle (hs v)
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual := LinearMap.codRestrict (smoothPart ρ.dual) B.flip hsm
  have hφ : ∀ v x, ((φ v : smoothPart ρ.dual) : Module.Dual ℂ V) x = B x v := fun _ _ => rfl
  have heq : ∀ g v, φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    apply Subtype.ext
    ext x
    rw [hφ, contra_apply, hφ, key]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h1 := hpos v hne
    have h2 : B v v = 0 := by
      have := congrArg (fun l : smoothPart ρ.dual => (l : Module.Dual ℂ V) v) hv
      simpa [hφ] using this
    rw [h2] at h1
    simp at h1
  have hsurj : Function.Surjective φ := by
    have hci : (contra ρ).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra irrAdm' ρ hs hi
    let U : Subrepresentation (contra ρ) :=
      { toSubmodule := LinearMap.range φ
        apply_mem_toSubmodule := by
          rintro g _ ⟨v, rfl⟩
          exact ⟨ρ g v, heq g v⟩ }
    have : Nontrivial V := by
      by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      obtain ⟨a, b, hab⟩ := hi.exists_pair_ne
      apply hab
      apply Subrepresentation.ext
      have : ∀ S : Subrepresentation ρ, S.toSubmodule = ⊤ := fun S => by
        ext x; simp [Subsingleton.elim x 0]
      rw [this a, this b]
    rcases hci.eq_bot_or_eq_top U with hU | hU
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have : φ v ∈ U.toSubmodule := ⟨v, rfl⟩
      rw [hU] at this
      have h0 : φ v = 0 := (Submodule.mem_bot ℂ).1 this
      exact hv (hinj (by rw [h0, map_zero]))
    · intro l
      have : l ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
      exact this
  refine ⟨φ, ⟨hinj, hsurj⟩, fun g v => ?_⟩
  show φ (((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) • ρ g v) =
    ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) • contra ρ g (φ v)
  rw [LinearMap.map_smulₛₗ, conj_chi, heq]

end CompanionTheory.RgGu.NR

end
