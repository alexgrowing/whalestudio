import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.LevZZero

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

theorem translate_apply (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (f : IndSp (stdBlocks d hd) ρ) (u : GL (Fin N) k) :
    (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * u) =
      (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l (f.1.1 (pm k (wOpen d hd) * (a⁻¹ * u * a))) := by
  have hx : pm k (wOpen d hd) * u * a =
      leviEmb k (stdBlocks d hd) l * (pm k (wOpen d hd) * (a⁻¹ * u * a)) := by
    rw [← hl]
    group
  have hf := f.1.2 ⟨leviEmb k (stdBlocks d hd) l, leviEmb_mem_parab k _ l⟩ (pm k (wOpen d hd) * (a⁻¹ * u * a))
  change f.1.1 (pm k (wOpen d hd) * u * a) = _
  rw [hx]
  refine hf.trans ?_
  rw [MonoidHom.comp_apply, leviProj_leviEmb]
  rfl

theorem translate_mem_openFns (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    {f : IndSp (stdBlocks d hd) ρ} (hf : f ∈ openFns d hd ρ) :
    parInd (stdBlocks d hd) ρ a f ∈ openFns d hd ρ := by
  have hf' : ∀ g : GL (Fin N) k, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd) := hf
  show ∀ g : GL (Fin N) k, (parInd (stdBlocks d hd) ρ a f).1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
  intro g hg
  obtain ⟨p, hp, n, hn, hpn⟩ := hf' (g * a) hg
  refine ⟨p * (leviEmb k (stdBlocks d hd) l)⁻¹,
    (parab k _).mul_mem hp ((parab k _).inv_mem (leviEmb_mem_parab k _ l)), a * n * a⁻¹, haB n hn, ?_⟩
  have hg' : g = p * pm k (wOpen d hd) * n * a⁻¹ := by
    rw [← hpn]
    group
  rw [hg', ← hl]
  group

end General

section Two

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem modExp_two_one (r m : ℕ) : modExp (fun a => Fin (dd r m a)) 1 = -(r : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two, dd]

theorem nabs_pow (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by
  simp [nabs, map_pow]

theorem deltaHalf_levZ (r m : ℕ) (z : kˣ) :
    (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k z ^ (-((m * r : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  have h0 : levZ k r m z 0 = 1 := by simp [levZ] <;> rfl
  have h1 : levZ k r m z 1 = GeneralLinearGroup.scalar (Fin (dd r m 1)) z := by simp [levZ]
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (dd r m 1)) z) = z ^ m := by
    rw [GeneralLinearGroup.det_scalar]
    simp [dd]
  have key : (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 0)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 0 : ℂ) / 2)) *
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 1)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 1 : ℂ) / 2)) := by
    simp only [deltaHalf, Fin.prod_univ_two, MonoidHom.finset_prod_apply, Units.val_mul]
    rfl
  rw [key, h0, h1, hdet, map_one, modExp_two_one, nabs_pow]
  have hx : 0 ≤ nabs k z := by simp [nabs]
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  rw [hn1]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hexp : (((-(r : ℤ) : ℤ) : ℂ) / 2) = (((-(r : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_cpow (pow_nonneg hx m), ← Real.rpow_natCast_mul hx]
  congr 2
  push_cast
  ring

end Two

end PositivityTheory.RgUd.CellA
