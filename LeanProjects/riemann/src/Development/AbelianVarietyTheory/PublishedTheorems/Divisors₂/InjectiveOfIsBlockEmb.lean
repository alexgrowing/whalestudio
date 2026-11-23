import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviBlockCentreFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.StdPar.BlockCentreModel

theorem iff_isBlockEmb : GlobalTheory.Published.LeviBlockCentreFinite ↔
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ → ∀ g₀ : GAd σ J,
        ∀ f : GlobalTheory.CuspRep.Sm E d, (∀ x, f.1 x = φ (ι x * g₀)) →
          FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (GlobalTheory.CuspRep.Sm E d) => z f) '' GlobalTheory.CuspRep.Zalg E d)) :=
  ⟨fun H F E _ _ _ _ _ _ σ h n J hJ r X Y hW K hK S l d hl ι hι => H F E σ h n J hJ r X Y hW K hK S l d hl ι _ _ rfl rfl hι,
    fun H F E _ _ _ _ _ _ σ h n J hJ r X Y hW K hK S l d hl ι _ _ e e' hι => by
      subst e e'
      exact H F E σ h n J hJ r X Y hW K hK S l d hl ι hι⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

example : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem injective_of_isBlockEmb (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {l d : ℕ} {hl : l + d ≤ r}
    {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J} (hι : GlobalTheory.BlockForms.IsBlockEmb σ J X Y hl ι) : Function.Injective ι := by
  obtain ⟨Φ, j, -, -, -, -, e⟩ := hι
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 := e g
  rw [hg, map_one, Units.val_one, add_assoc, left_eq_add] at h1
  set Xb := GlobalTheory.BlockForms.blkCols hl X
  set Yb := GlobalTheory.BlockForms.blkCols hl Y
  have yx' : cT (σ : E →+* E) Yb * J * Xb = 1 := Matrix.ext fun a b =>
    (congrFun (congrFun (yx h hJ hW) ⟨l + a.val, by omega⟩) ⟨l + b.val, by omega⟩).trans (by simp [Matrix.one_apply, Fin.ext_iff])
  have xx' : cT (σ : E →+* E) Xb * J * Xb = 0 := Matrix.ext fun a b =>
    congrFun (congrFun hW.xx ⟨l + a.val, by omega⟩) ⟨l + b.val, by omega⟩
  have a1 : adMat F (cT (σ : E →+* E) Yb * J) * adMat F Xb = 1 := by
    rw [← Matrix.map_mul, yx', Matrix.map_one _ (map_zero _) (map_one _)]
  have a2 : adMat F (cT (σ : E →+* E) Xb * J) * adMat F Xb = 0 := by
    rw [← Matrix.map_mul, xx', Matrix.map_zero _ (map_zero _)]
  have h2 := congrArg (fun M => adMat F (cT (σ : E →+* E) Yb * J) * (M * adMat F Xb)) h1
  simp only [Matrix.add_mul, Matrix.mul_assoc (_ * _) (adMat F _) (adMat F Xb), a1, a2, Matrix.mul_one, Matrix.mul_zero, add_zero,
    Matrix.zero_mul, ← Matrix.mul_assoc _ (adMat F Xb), Matrix.one_mul] at h2
  have h3 : g.1.map Φ.symm = 1 := (sub_eq_zero.1 h2)
  refine Units.ext (Matrix.ext fun a b => Φ.symm.injective ?_)
  refine (congrFun (congrFun h3 a) b).trans ?_
  simp [Matrix.one_apply, apply_ite Φ.symm]

theorem hypotheses_inhabited : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E)
    (_ : IsTotallyComplex E) (_ : Algebra F E) (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (X Y : Matrix (Fin 2) (Fin 1) E)
    (K : Subgroup (GAd σ J)) (S : Finset (Fin 1)) (hl : 0 + 1 ≤ 1) (ι : GlobalTheory.CuspRep.GA E 1 →* GAd σ J) (φ : GAd σ J → ℂ)
    (f : GlobalTheory.CuspRep.Sm E 1), IsCMExt F E σ ∧ IsHermND σ J ∧ IsWittFrame σ J X Y ∧ IsMaxCpt σ J K ∧
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y hl ι ∧ Function.Injective ι ∧
      (∀ j : Fin 1, 0 ≤ j.val → j.val + 1 < 0 + 1 → j ∉ S) ∧ (∃ k ∈ S, k.val + 1 = 0 + 1) ∧
      IsAutOn σ J X Y S K φ ∧ (∀ g₀ x, f.1 x = φ (ι x * g₀)) ∧ f ≠ 0 := by
  haveI : IsCMField (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩
  have h := isCMExt_of_isCMField (CyclotomicField 4 ℚ)
  have hJ : IsHermND (IsCMField.complexConj (CyclotomicField 4 ℚ) : _ →ₐ[maximalRealSubfield (CyclotomicField 4 ℚ)] _)
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (CyclotomicField 4 ℚ)) :=
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩
  obtain ⟨K, hK⟩ := exists_isMaxCpt h hJ
  obtain ⟨ι, hι⟩ := GlobalTheory.BlockFormsEmb.exists_blockEmb _ _ _ h 2 _ hJ 1 _ _ isWittFrame_plane 0 1 le_rfl
  refine ⟨_, _, _, _, _, _, inferInstance, _, _, _, _, _, K, Finset.univ, le_rfl, ι, fun _ => 1,
    ⟨fun _ => 1, fun g => contDiffOn_const.congr (f := fun _ => (1 : ℂ)) fun x hx => ?_⟩, h, hJ, isWittFrame_plane, hK, hι,
    injective_of_isBlockEmb h hJ isWittFrame_plane hι, fun j _ hj => by omega, ⟨0, Finset.mem_univ _, rfl⟩,
    isAutOn_const _ _ _ _ _ K 1, fun _ _ => rfl, fun e => one_ne_zero (congrFun (congrArg Subtype.val e) 1)⟩
  have hx' : IsUnit (Matrix.of x) := hx
  simp [GlobalTheory.CuspRep.chart, hx']

end GlobalTheory.StdPar.BlockCentreModel

end
