import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Lift

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }

@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl

end Lift

section Level

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']

def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, (f.two_cobOne b.1).symm.trans ((congrArg f.two b.2).trans (map_zero _))⟩
  map_add' _ _ := Subtype.ext (map_add f.lin _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)

@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl

theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb

theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ

variable (R A) in

def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp

@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit R φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ

variable [IsCocomm R A] [IsCocomm R' A']

variable (R A) in

def levelRel : A →ₗ[R] symCocycles R A × Cot R A :=
  ((cobOne R A).codRestrict _ fun _ => cobOne_mem _).prod (AugCot.d (counitAlgHom R A))

variable (R A) in

abbrev LevelRig : Type := (symCocycles R A × Cot R A) ⧸ LinearMap.range (levelRel R A)

omit [IsCocomm R A] [IsCocomm R' A'] in

def SemiBialgHom.levelPair (f : SemiBialgHom σ A A') :
    symCocycles R A × Cot R A →ₛₗ[σ] symCocycles R' A' × Cot R' A' where
  toFun x := (⟨f.two x.1.1, f.two_mem x.1.2⟩, f.cot x.2)
  map_add' _ _ := Prod.ext (Subtype.ext (map_add f.two _ _)) (map_add f.cot _ _)
  map_smul' _ _ := Prod.ext (Subtype.ext (map_smulₛₗ f.two _ _)) (map_smulₛₗ f.cot _ _)

def SemiBialgHom.levelRig (f : SemiBialgHom σ A A') : LevelRig R A →ₛₗ[σ] LevelRig R' A' :=
  Submodule.mapQ _ _ f.levelPair (by
    rintro _ ⟨b, rfl⟩
    exact ⟨f b, Prod.ext (Subtype.ext (f.two_cobOne b).symm) (f.cot_d b).symm⟩)

@[simp] theorem SemiBialgHom.levelRig_mk (f : SemiBialgHom σ A A')
    (x : symCocycles R A × Cot R A) :
    f.levelRig (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.levelPair x) := rfl

end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n

@[simp] theorem resOne_zero (a : G.A 1) : G.resOne 0 a = a := rfl

@[simp] theorem resOne_succ (n : ℕ) (a : G.A (n + 2)) :
    G.resOne (n + 1) a = G.resOne n (G.res (n + 1) a) := rfl

theorem resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))

theorem resOne_funs (B : G.funs) (n : ℕ) : G.resOne n (B.1 (n + 1)) = B.1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, B.2, ih]

theorem resOne_mulBy (n : ℕ) (a : G.A (n + 1)) :
    G.resOne n (mulBy R _ p a) = algebraMap R _ (counit a) := by
  have h := G.mulBy_pow_self 1 (G.resOne n a)
  rw [pow_one, CoalgHomClass.counit_comp_apply] at h
  rw [map_mulBy, h]

theorem resOne_mulP (n : ℕ) (a : G.A n) :
    G.resOne n (G.mulP n a) = algebraMap R _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, resOne_mulBy, CoalgHomClass.counit_comp_apply]

def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)

theorem transl_apply (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl

theorem transl_res (n : ℕ) (a : G.A (n + 2)) :
    G.transl n (G.res (n + 1) a) =
      (G.res (n + 1) : G.A (n + 2) →ₗ[R] G.A (n + 1)).rTensor _ (G.transl (n + 1) a) := by
  rw [transl_apply, transl_apply, ← pullTwo_comul]
  generalize comul (R := R) a = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

theorem transl_mulP (n : ℕ) (a : G.A n) : G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ 1 := by
  rw [transl_apply, ← pullTwo_comul]
  conv_rhs => rw [← (TensorProduct.rid R _).apply_symm_apply a, TensorProduct.rid_symm_apply,
    ← Coalgebra.lTensor_counit_comul]
  generalize comul (R := R) a = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul x y => simp [resOne_mulP, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem pullbackTwo_mulP_injective (n : ℕ) : Function.Injective (pullbackTwo (G.mulP n)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n) (Test.mulP_injective G n)

theorem res_eq_zero_of_cobOne_eq_zero (hp : (p : R) = 0) (n : ℕ) {b : G.A (n + 1)}
    (hb : cobOne R _ b = 0) : G.res n b = 0 :=
  Test.mulP_injective G n (by
    rw [mulP_res, (mulBy_of_cobOne_eq_zero hb p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul,
      map_zero])

theorem eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 :=
  Subtype.ext (funext fun n => (B.2 n).symm.trans (G.res_eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun c : G.cocycles => c.1 (n + 1)) hB)))

theorem rigOfOmega_injective_of_eq_zero (hp : (p : R) = 0) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero hp (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

theorem omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]

def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)

theorem primLie_apply (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega)
    (φ : CartierDual R (G.A 1)) (h : w.1 1 = dUnit R φ) : G.primLie b w = φ b.1 :=
  (congrArg (primTangent R (G.A 1) b) h).trans (primTangent_d b φ)

def cocyclesLevel (n : ℕ) : G.cocycles →ₗ[R] symCocycles R (G.A n) :=
  (LinearMap.proj n ∘ₗ G.cocycles.subtype).codRestrict _ fun c => (c.2 n).1

def rigLevel (n : ℕ) : G.RigExt →ₗ[R] LevelRig R (G.A n) :=
  Submodule.mapQ _ _ ((G.cocyclesLevel n).prodMap (G.omegaLevel n)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b.1 n, rfl⟩)

@[simp] theorem rigLevel_mk (n : ℕ) (c : G.cocycles) (w : G.omega) :
    G.rigLevel n (G.rigMk (c, w)) = Submodule.Quotient.mk (⟨c.1 n, (c.2 n).1⟩, w.1 n) := rfl

end PDivGroup

end GlobalTheory
