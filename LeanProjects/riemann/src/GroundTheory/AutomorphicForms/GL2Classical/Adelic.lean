import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.ExistsIntOfMemIntegralFiniteAdeles
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean

open NumberField IsDedekindDomain Matrix CongruenceSubgroup
open GroundTheory.Global
open scoped MatrixGroups

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

def toReal : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)

@[simp]
theorem toReal_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (toReal γ : Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) :=
  rfl

theorem det_toReal (γ : GL (Fin 2) ℚ) : (toReal γ).det.val = ((γ.det.val : ℚ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact ((Rat.castHom ℝ).map_det (γ : Matrix (Fin 2) (Fin 2) ℚ)).symm

def realInf : GL (Fin 2) ℝ →* InfiniteAdelicGL ℚ 2 :=
  Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.symm.toRingHom

def realEmb : GL (Fin 2) ℝ →* AdelicGL ℚ 2 :=
  (prodEquiv ℚ 2).symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp realInf)

theorem prodEquiv_realEmb (h : GL (Fin 2) ℝ) : prodEquiv ℚ 2 (realEmb h) = (realInf h, 1) :=
  (prodEquiv ℚ 2).apply_symm_apply _

theorem realInf_injective : Function.Injective realInf := fun x y hxy => by
  refine Units.ext (Matrix.ext fun a b => ?_)
  have := congrArg (fun g : InfiniteAdelicGL ℚ 2 =>
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) hxy
  exact RationalIdeles.realEquiv.symm.injective this

theorem realEmb_injective : Function.Injective realEmb := fun x y hxy => by
  have := congrArg (fun g => (prodEquiv ℚ 2 g).1) hxy
  simp only [prodEquiv_realEmb] at this
  exact realInf_injective this

theorem realEmb_mul_finEmb_comm (h : GL (Fin 2) ℝ) (y : FiniteAdelicGL ℚ 2) :
    realEmb h * finEmb ℚ 2 y = finEmb ℚ 2 y * realEmb h := by
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]

def realPart (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map RationalIdeles.realEquiv.toRingHom (prodEquiv ℚ 2 g).1

theorem realInf_realPart (g : AdelicGL ℚ 2) : realInf (realPart g) = (prodEquiv ℚ 2 g).1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  exact RationalIdeles.realEquiv.symm_apply_apply _

theorem realEmb_realPart_mul_finEmb (g : AdelicGL ℚ 2) :
    realEmb (realPart g) * finEmb ℚ 2 (prodEquiv ℚ 2 g).2 = g := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul,
    realInf_realPart]

theorem diagonal_eq (γ : GL (Fin 2) ℚ) :
    diagonal ℚ 2 γ = realEmb (toReal γ) * finEmb ℚ 2 (finiteDiagonal ℚ 2 γ) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (Units.ext (Matrix.ext fun a b => ?_))
  · change (algebraMap ℚ (InfiniteAdeleRing ℚ)) (γ a b) =
      RationalIdeles.realEquiv.symm (((γ : Matrix (Fin 2) (Fin 2) ℚ) a b : ℚ) : ℝ)
    exact RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (InfiniteAdeleRing ℚ))
      (RationalIdeles.realEquiv.symm.toRingHom.comp (Rat.castHom ℝ))) _
  · rfl

theorem diagonal_mul_realEmb_mul_finEmb (δ γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ)
    (u : FiniteAdelicGL ℚ 2) :
    diagonal ℚ 2 δ * realEmb h * finEmb ℚ 2 u =
      diagonal ℚ 2 (δ * γ) * realEmb ((toReal γ)⁻¹ * h) *
        finEmb ℚ 2 ((finiteDiagonal ℚ 2 γ)⁻¹ * u) := by
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
    Prod.inv_mk, mul_one, one_mul, inv_one]
  refine Prod.ext ?_ ?_ <;> simp only [] <;> group

variable (N : ℕ) [NeZero N]

theorem finiteDiagonal_mem_Gamma0Level_of_int {γ : GL (Fin 2) ℚ} (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ i j, (A i j : ℚ) = γ i j) (hB : ∀ i j, (B i j : ℚ) = (γ⁻¹ : GL (Fin 2) ℚ) i j)
    (hN : (N : ℤ) ∣ A 1 0) : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N := by
  refine ⟨(mem_integralFiniteGL_iff ℚ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · rw [finiteDiagonal_apply, ← hA, map_intCast]
    exact intCast_mem_integralFiniteAdeles _
  · rw [← map_inv, finiteDiagonal_apply, ← hB, map_intCast]
    exact intCast_mem_integralFiniteAdeles _
  · obtain ⟨m, hm⟩ := hN
    refine ⟨(m : 𝔸f), intCast_mem_integralFiniteAdeles m, ?_⟩
    change algebraMap ℚ 𝔸f (γ 1 0) = _
    rw [← hA, hm, Int.cast_mul, map_mul, map_intCast, map_intCast, Int.cast_natCast]

@[simp]
theorem mapGL_apply (σ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) :=
  rfl

theorem toReal_mapGL (σ : SL(2, ℤ)) :
    toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ) = Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) : ℝ) = ((σ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)
  exact Rat.cast_intCast _

theorem finiteDiagonal_mapGL_mem_Gamma0Level {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) :
    finiteDiagonal ℚ 2 (Matrix.SpecialLinearGroup.mapGL ℚ σ) ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N (σ : Matrix (Fin 2) (Fin 2) ℤ)
    ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (fun i j => rfl) (fun i j => ?_) ?_
  · rw [← map_inv]
    rfl
  · rw [Gamma0_mem] at hσ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hσ

theorem exists_mem_Gamma0_of_mem {γ : GL (Fin 2) ℚ} (hγ : finiteDiagonal ℚ 2 γ ∈ Gamma0Level N)
    (hdet : 0 < (γ.det.val : ℚ)) :
    ∃ σ ∈ Gamma0 N, Matrix.SpecialLinearGroup.mapGL ℚ σ = γ := by
  obtain ⟨A, hA, hN, hd⟩ := exists_int_of_finiteDiagonal_mem N hγ
  have hdetA : ((A.det : ℤ) : ℚ) = γ.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have e : (Int.castRingHom ℚ).mapMatrix A = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      exact hA i j
    rw [← e, ← RingHom.map_det]
    rfl
  have h1 : A.det = 1 := by
    rcases hd with h | h
    · exact h
    · rw [h] at hdetA
      rw [← hdetA] at hdet
      norm_num at hdet
  refine ⟨(⟨A, h1⟩ : SL(2, ℤ)), ?_, Units.ext (Matrix.ext fun i j => hA i j)⟩
  exact Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hN)

def epsilon : GL (Fin 2) ℚ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem epsilon_inv : epsilon⁻¹ = epsilon :=
  inv_eq_of_mul_eq_one_right (Units.ext (by simp [epsilon, Matrix.one_fin_two]))

theorem det_toReal_epsilon : (toReal epsilon).det.val = -1 := by
  rw [det_toReal, Matrix.GeneralLinearGroup.val_det_apply]
  simp [epsilon, Matrix.det_fin_two_of]

theorem finiteDiagonal_epsilon_mem : finiteDiagonal ℚ 2 epsilon ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N !![-1, 0; 0, 1] !![-1, 0; 0, 1] ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [epsilon]
  · intro i j
    rw [epsilon_inv]
    fin_cases i <;> fin_cases j <;> simp [epsilon]
  · simp

theorem exists_decomposition (g : AdelicGL ℚ 2) :
    ∃ γ : GL (Fin 2) ℚ, ∃ h : GL (Fin 2) ℝ, 0 < h.det.val ∧ ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u := by
  obtain ⟨δ, u, hu, hy⟩ := exists_eq_finiteDiagonal_mul N (prodEquiv ℚ 2 g).2
  have hg : g = diagonal ℚ 2 δ * realEmb ((toReal δ)⁻¹ * realPart g) * finEmb ℚ 2 u := by
    conv_lhs => rw [← realEmb_realPart_mul_finEmb g, hy]
    apply (prodEquiv ℚ 2).injective
    simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
      Prod.inv_mk, inv_one, mul_one, one_mul]
    rw [Prod.mk.injEq]
    exact ⟨by group, by group⟩
  set x := (toReal δ)⁻¹ * realPart g
  by_cases hx : 0 < x.det.val
  · exact ⟨δ, x, hx, u, hu, hg⟩
  · refine ⟨δ * epsilon, (toReal epsilon)⁻¹ * x, ?_, (finiteDiagonal ℚ 2 epsilon)⁻¹ * u,
      mul_mem (inv_mem (finiteDiagonal_epsilon_mem N)) hu,
      hg.trans (diagonal_mul_realEmb_mul_finEmb δ epsilon x u)⟩
    have hne : x.det.val ≠ 0 := x.det.ne_zero
    have hneg : x.det.val < 0 := lt_of_le_of_ne (not_lt.1 hx) hne
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal_epsilon]
    linarith

end GL2Classical

end

end GroundTheory.Automorphic
