import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapE

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

section Comm

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem sgl_mul_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (a : w.adicCompletion F) (b : w'.adicCompletion F) :
    sgl F w a * sgl F w' b = 0 := by
  apply adele_ext
  intro v
  rw [map_mul (evalV F v), map_zero]
  by_cases hv : v = w
  · subst hv; rw [sgl_apply_ne F w' b h, mul_zero]
  · rw [sgl_apply_ne F w a hv, zero_mul]

theorem iE_mul_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (x : E ⊗[F] w.adicCompletion F)
    (y : E ⊗[F] w'.adicCompletion F) : iE F E w x * iE F E w' y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_zero]
  | tmul e a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, add_zero]
    | tmul e' a' =>
      rw [iE_tmul, iE_tmul, Algebra.TensorProduct.tmul_mul_tmul, sgl_mul_ne F h, TensorProduct.tmul_zero]

theorem mapE_mul_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (X : Matrix n n (E ⊗[F] w.adicCompletion F))
    (Y : Matrix n n (E ⊗[F] w'.adicCompletion F)) : mapE F E w X * mapE F E w' Y = 0 := by
  ext a b
  simp only [mapE, Matrix.mul_apply, Matrix.map_apply, iE_mul_ne F E h, Finset.sum_const_zero, Matrix.zero_apply]

theorem eps_smul_mapE_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (Y : Matrix n n (E ⊗[F] w'.adicCompletion F)) :
    epsW F E w • mapE F E w' Y = 0 := by
  ext a b
  simp only [mapE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, epsW, iE_mul_ne F E h, Matrix.zero_apply]

theorem compl_smul_mapE_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (Y : Matrix n n (E ⊗[F] w'.adicCompletion F)) :
    (1 - epsW F E w) • mapE F E w' Y = mapE F E w' Y := by
  rw [sub_smul, one_smul, eps_smul_mapE_ne F E h, sub_zero]

theorem sec_comm {w w' : HeightOneSpectrum (𝓞 F)} (h : w ≠ w') (X : GL n (E ⊗[F] w.adicCompletion F))
    (Y : GL n (E ⊗[F] w'.adicCompletion F)) : Commute (sec F E w X) (sec F E w' Y) := by
  apply Units.ext
  show (sec F E w X : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * (sec F E w' Y : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
    (sec F E w' Y : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * (sec F E w X : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  rw [sec_val, sec_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, mapE_mul_ne F E h, mapE_mul_ne F E h.symm, compl_smul_mapE_ne F E h, compl_smul_mapE_ne F E h.symm, add_zero]
  rw [mul_comm (1 - epsW F E w) (1 - epsW F E w')]
  abel

end Comm

section Family

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σE : E →ₐ[F] E) (J : Matrix n n E)

def secU (w : HeightOneSpectrum (𝓞 F)) : UPts σE J (w.adicCompletion F) →* UPts σE J (FiniteAdeleRing (𝓞 F) F) :=
  ((sec F E w).comp (UPts σE J (w.adicCompletion F)).subtype).codRestrict _ (fun X => sec_mem_UPts F E w σE J X.2)

theorem secU_val (w : HeightOneSpectrum (𝓞 F)) (X : UPts σE J (w.adicCompletion F)) :
    (secU F E σE J w X : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = sec F E w (X : GL n (E ⊗[F] w.adicCompletion F)) := rfl

variable {κ : Type} [Fintype κ] [DecidableEq κ] (S : κ → HeightOneSpectrum (𝓞 F)) (hS : Function.Injective S)

def secAll : (∀ v : κ, UPts σE J ((S v).adicCompletion F)) →* UPts σE J (FiniteAdeleRing (𝓞 F) F) :=
  MonoidHom.noncommPiCoprod (fun v => secU F E σE J (S v)) (by
    intro a b hab X Y
    apply Subtype.ext
    exact sec_comm F E (fun h => hab (hS h)) _ _)

theorem secAll_single (v : κ) (X : UPts σE J ((S v).adicCompletion F)) :
    secAll F E σE J S hS (Pi.mulSingle v X) = secU F E σE J (S v) X :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem bc_secAll_same (v : κ) (X : ∀ v : κ, UPts σE J ((S v).adicCompletion F)) :
    bc (prV (E := E) (S v)) (secAll F E σE J S hS X : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (X v : GL n (E ⊗[F] (S v).adicCompletion F)) := by
  have key : ((bc (prV (E := E) (S v))).comp ((UPts σE J (FiniteAdeleRing (𝓞 F) F)).subtype.comp (secAll F E σE J S hS))) =
      (UPts σE J ((S v).adicCompletion F)).subtype.comp (Pi.evalMonoidHom _ v) := by
    apply MonoidHom.pi_ext
    intro i x
    simp only [MonoidHom.comp_apply, secAll_single, Pi.evalMonoidHom_apply, Subgroup.subtype_apply, secU_val]
    by_cases h : i = v
    · subst h
      rw [bc_sec_same, Pi.mulSingle_eq_same]
    · rw [bc_sec_ne F E (S i) _ (fun hh => h (hS hh).symm), Pi.mulSingle_eq_of_ne (Ne.symm h)]
      rfl
  exact DFunLike.congr_fun key X

theorem bc_secAll_off (w' : HeightOneSpectrum (𝓞 F)) (hw : ∀ v, w' ≠ S v) (X : ∀ v : κ, UPts σE J ((S v).adicCompletion F)) :
    bc (prV (E := E) w') (secAll F E σE J S hS X : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 := by
  have key : ((bc (prV (E := E) w')).comp ((UPts σE J (FiniteAdeleRing (𝓞 F) F)).subtype.comp (secAll F E σE J S hS))) = 1 := by
    apply MonoidHom.pi_ext
    intro i x
    simp only [MonoidHom.comp_apply, secAll_single, Subgroup.subtype_apply, secU_val, MonoidHom.one_apply]
    exact bc_sec_ne F E (S i) _ (hw i)
  exact DFunLike.congr_fun key X

end Family

end Formalism.L2.G
