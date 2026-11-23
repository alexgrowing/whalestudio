import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.Inhab NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

section Conj

variable (V : Type) [AddCommGroup V] [Module ℂ V]

def cj (v : V) : V :=
  (Module.Basis.ofVectorSpace ℂ V).repr.symm
    (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _))

theorem cj_add (v w : V) : cj V (v + w) = cj V v + cj V w := by
  unfold cj
  rw [map_add, Finsupp.mapRange_add (fun a b => map_add (starRingEnd ℂ) a b), map_add]

theorem cj_smul (c : ℂ) (v : V) : cj V (c • v) = star c • cj V v := by
  unfold cj
  have : (c • (Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) =
      star c • ((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) := by
    ext i
    simp
  rw [LinearEquiv.map_smul (Module.Basis.ofVectorSpace ℂ V).repr c v, this, LinearEquiv.map_smul]

theorem cj_cj (v : V) : cj V (cj V v) = v := by
  unfold cj
  rw [LinearEquiv.apply_symm_apply]
  have : (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _)).mapRange
      (starRingEnd ℂ) (map_zero _) = (Module.Basis.ofVectorSpace ℂ V).repr v := by
    ext i
    simp
  rw [this, LinearEquiv.symm_apply_apply]

end Conj

variable (D : D7)

abbrev HR : Type := lp (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2

abbrev HC : Type := lp (fun u : D.what₂.Word => D.what₂.Mu u) 2

abbrev HF : Type := HR D × HC D

def petH (a b : HF D) : ℂ := inner ℂ a.1 b.1 + inner ℂ a.2 b.2

def rowI (μ : D.what₂.Tup) (j : ℕ) : D.what₂.Mult μ j →ₗ[ℂ] HF D :=
  (LinearMap.inl ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩)

def rowP (μ : D.what₂.Tup) (j : ℕ) : HF D →ₗ[ℂ] D.what₂.Mult μ j :=
  (lp.evalₗ (𝕜 := ℂ) (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩).comp
    (LinearMap.fst ℂ (HR D) (HC D))

def colI (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] HF D :=
  (LinearMap.inr ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun u : D.what₂.Word => D.what₂.Mu u) 2 u)

theorem component_inclusion (μ j) (x : D.what₂.Mult μ j) : rowP D μ j (rowI D μ j x) = x :=
  lp.single_apply_self (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x

theorem pet_rowI (μ j) (x : D.what₂.Mult μ j) (b : HF D) : petH D (rowI D μ j x) b = inner ℂ x (rowP D μ j b) := by
  show inner ℂ (lp.single (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x) b.1 +
    inner ℂ (0 : HC D) b.2 = _
  rw [inner_zero_left, add_zero]
  exact lp.inner_single_left (G := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) ⟨μ, j⟩ x b.1

theorem pet_colI (u) (x y : D.what₂.Mu u) : petH D (colI D u x) (colI D u y) = inner ℂ x y := by
  show inner ℂ (0 : HR D) 0 + inner ℂ (lp.single 2 u x) (lp.single 2 u y) = _
  rw [inner_zero_left, zero_add, lp.inner_single_left (G := fun u : D.what₂.Word => D.what₂.Mu u) u x]
  rw [lp.single_apply_self]

def toTop {M : Type} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] HF D) : M →ₗ[ℂ] (⊤ : Submodule ℂ (HF D)) :=
  f.codRestrict ⊤ fun _ => Submodule.mem_top

def thetaFull : ThetaX D where
  AF := fun _ => HF D
  cusp := fun _ => ⊤
  pet := fun _ F G => petH D F G
  pet_add_left := fun _ F F' G => by
    simp only [petH, Prod.fst_add, Prod.snd_add, inner_add_left]; ring
  pet_smul_left := fun _ c F G => by
    simp only [petH, Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_add]; rfl
  pet_right := fun _ F => ⟨fun G G' => by
      simp only [petH, Submodule.coe_add, Prod.fst_add, Prod.snd_add, inner_add_right]; ring,
    fun c G => by
      simp only [petH, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul, mul_add]⟩
  pet_symm := fun _ F G => by
    simp only [petH, star_add]
    rw [← starRingEnd_apply, ← starRingEnd_apply, inner_conj_symm, inner_conj_symm]
  pet_pos := fun _ F hF => by
    have h1 : (F : HF D) ≠ 0 := fun h => hF (Subtype.ext h)
    have e : (petH D (F : HF D) F).re = ‖(F : HF D).1‖ ^ 2 + ‖(F : HF D).2‖ ^ 2 := by
      simp only [petH, Complex.add_re]
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
    show 0 < (petH D (F : HF D) F).re
    rw [e]
    rcases (not_and_or.mp fun h : (F : HF D).1 = 0 ∧ (F : HF D).2 = 0 => h1 (Prod.ext h.1 h.2)) with h | h
    · have := norm_pos_iff.mpr h; positivity
    · have := norm_pos_iff.mpr h; positivity
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => HF D →ₗ[ℂ] HF D
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ _ _ _ => LinearMap.lcomp ℂ (HF D) (⊤ : Submodule ℂ (HF D)).subtype
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := fun t j _ => (tow D t).Ys j
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ => cj (HF D)
  conjAF_add := fun _ => cj_add _
  conjAF_smul := fun _ => cj_smul _
  conjAF_conjAF := fun _ => cj_cj _
  conjAF_cusp := fun _ _ _ => Submodule.mem_top
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ _ _ => 0
  Bper_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ _ _ => 0
  Btop_right := fun _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Btop_add_left := fun _ _ _ _ _ _ => by simp
  Btop_smul_left := fun _ _ _ _ _ _ => by simp
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun u _ _ => toTop D (colI D u)
  rowAF := fun μ j => toTop D (rowI D μ j)
  PhiY := fun μ j => (rowI D μ j).comp ((D.what₂.io μ j).comp (rowP D μ (j + 1)))
  PhiYup := fun _ _ => 0
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaFull_mY (μ : D.what₂.Tup) (j : ℕ) : (((thetaFull D).mY μ j : ℝ) : ℂ) = 1 := Complex.ofReal_one

theorem thetaFull_row : (thetaFull D).TieRowIsom := fun μ j _ x y => by
  unfold ThetaX.petY
  rw [thetaFull_mY, one_mul]
  exact (pet_rowI D μ j x (rowI D μ j y)).trans (by rw [component_inclusion])

theorem thetaFull_io : (thetaFull D).TieIo := fun μ j _ y x => by
  unfold ThetaX.petY ThetaX.dnY
  rw [thetaFull_mY, thetaFull_mY, one_mul, one_smul]
  show petH D (rowI D μ j (D.what₂.io μ j (rowP D μ (j + 1) (rowI D μ (j + 1) y)))) (rowI D μ j x) = _
  rw [component_inclusion, pet_rowI, component_inclusion]

theorem thetaFull_colIsom (u μ j) (x y : D.what₂.Mu u) :
    (thetaFull D).pet _ (((thetaFull D).colAF u μ j x : (thetaFull D).cusp _) : (thetaFull D).AF _)
      ((thetaFull D).colAF u μ j y) = inner ℂ x y := pet_colI D u x y

theorem theta_exists : ∃ X : ThetaX D, X.TieRowIsom ∧ X.TieIo :=
  ⟨thetaFull D, thetaFull_row D, thetaFull_io D⟩

end Formalism.BasicNotions.Examples₂.NZ
