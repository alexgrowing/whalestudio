import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped nonZeroDivisors

namespace UpperTheory.V.Tower

section Norm

variable (K : Type) {K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

def idNorm : (Ideal (𝓞 K'))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I := ⟨Ideal.relNorm (𝓞 K) I.1, mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero I.2 (Ideal.relNorm_eq_bot_iff.1 h)⟩
  map_one' := Subtype.ext (map_one (Ideal.relNorm (𝓞 K)))
  map_mul' I J := Subtype.ext (map_mul (Ideal.relNorm (𝓞 K)) I.1 J.1)

theorem ideal_norm_class_congr {I J : (Ideal (𝓞 K'))⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idNorm K I) = ClassGroup.mk0 (idNorm K J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, h⟩ := h
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 K') x, Algebra.intNorm (𝓞 K) (𝓞 K') y, fun h => hx (Algebra.intNorm_eq_zero.1 h),
    fun h => hy (Algebra.intNorm_eq_zero.1 h), ?_⟩
  have := congrArg (Ideal.relNorm (𝓞 K)) h
  rw [map_mul, map_mul, Ideal.relNorm_singleton, Ideal.relNorm_singleton] at this
  exact this

private def nFun (c : ClassGroup (𝓞 K')) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (idNorm K (ClassGroup.mk0_surjective c).choose)

private theorem norm_function_mk (I : (Ideal (𝓞 K'))⁰) : nFun K (ClassGroup.mk0 I) = ClassGroup.mk0 (idNorm K I) :=
  ideal_norm_class_congr K (ClassGroup.mk0_surjective _).choose_spec

def clNorm : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K) :=
  MonoidHom.mk' (nFun K) fun a b => by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, norm_function_mk, norm_function_mk, norm_function_mk, map_mul, map_mul]

theorem class_norm_mk (I : (Ideal (𝓞 K'))⁰) : clNorm K (ClassGroup.mk0 I) = ClassGroup.mk0 (idNorm K I) := norm_function_mk K I

end Norm

section Lim

variable (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

omit [IsAlgClosure L Ω] in
theorem Fn_le_succ (n : ℕ) : Fn L Ω l n ≤ Fn L Ω l (n + 1) := by
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have h0 : ∀ m : ℕ, (Polynomial.X ^ l ^ m - 1 : Polynomial L) ≠ 0 := fun m =>
    Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos m) 1
  rw [Polynomial.mem_rootSet_of_ne (h0 _)] at hx ⊢
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at hx ⊢
  rw [pow_succ, pow_mul, hx, one_pow]

def normStep (n : ℕ) : ClassGroup (𝓞 (Fn L Ω l (n + 1))) →* ClassGroup (𝓞 (Fn L Ω l n)) :=
  letI : Algebra (Fn L Ω l n) (Fn L Ω l (n + 1)) := (IntermediateField.inclusion (Fn_le_succ l L Ω n)).toRingHom.toAlgebra
  clNorm (Fn L Ω l n)

def ClLim : Subgroup (∀ n, ClassGroup (𝓞 (Fn L Ω l n))) where
  carrier := {a | ∀ n, normStep l L Ω n (a (n + 1)) = a n}
  one_mem' n := map_one _
  mul_mem' {a b} ha hb n := by rw [Pi.mul_apply, Pi.mul_apply, map_mul, ha n, hb n]
  inv_mem' {a} ha n := by rw [Pi.inv_apply, Pi.inv_apply, map_inv, ha n]

def ALim : Subgroup (∀ n, ClassGroup (𝓞 (Fn L Ω l n))) :=
  ClLim l L Ω ⊓ Subgroup.pi Set.univ fun n => CommGroup.primaryComponent (ClassGroup (𝓞 (Fn L Ω l n))) l

variable (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

theorem galOf_Fn (n : ℕ) : galOf k (Fn L Ω l n) Ω = levU l (galOf k L Ω) n :=
  haveI := (fnCyc L Ω l n).1
  galOfCyc k Ω l n L (Fn L Ω l n)

theorem cycU_le_Fn (n : ℕ) : cycU l (galOf k L Ω) ≤ galOf k (Fn L Ω l n) Ω :=
  (galOf_Fn l L Ω k n).symm ▸ cycU_le_levU l _ n

abbrev pullN (n : ℕ) : (ClassGroup (𝓞 (Fn L Ω l n)) → QZ l) →ₗ[ℤ_[l]] (cycU l (galOf k L Ω) → QZ l) :=
  clPull (Fn L Ω l n) (cycU_le_Fn l L Ω k n) ℤ_[l] (QZ l)

end Lim

section Desc

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

def ClAnn (K : Type) [Field K] [NumberField K] [Algebra K Ω] {ι : Type} [Fintype ι] (s : ι → G k Ω) (b : ι → ℤ) : Prop :=
  ∃ τ : ι → K ≃+* K, (∀ i, IsLift (τ i) (s i).toRingEquiv) ∧ ∀ c : ClassGroup (𝓞 K), ∏ i, clMap (τ i) c ^ b i = 1

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω]

def IsDesc {l : ℕ} [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal]
    (Φ : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e) : Prop :=
  ∀ (x : Sha D e) (u : Uinf L Ω l) (u' : cycU l U), u'.1 = galEmb k L Ω u.1 → (Φ x).1.1 u' = resInf D e x.1 u

def shaAct {l : ℕ} [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (τ : L ≃+* L) : Module.End ℤ_[l] (Sha D e) :=
  (galoisActionOnCohomology D e τ).restrict fun _ hx => galois_action_preserves_sha D e τ hx

variable [Normal k L]

abbrev resG : G k Ω →* (L ≃ₐ[k] L) := AlgEquiv.restrictNormalHom L

def descHom {M : Type} [Monoid M] (π : G k Ω →* M) (h : ∀ g ∈ galOf k L Ω, π g = 1) : (L ≃ₐ[k] L) →* M where
  toFun σ := π ((galQuot k L Ω).1 σ).choose
  map_one' := h _ ((galQuot k L Ω).2.1.le ((galQuot k L Ω).1 1).choose_spec)
  map_mul' σ τ := by
    have h1 := ((galQuot k L Ω).1 σ).choose_spec
    have h2 := ((galQuot k L Ω).1 τ).choose_spec
    have h3 := ((galQuot k L Ω).1 (σ * τ)).choose_spec
    generalize ((galQuot k L Ω).1 σ).choose = a at h1 ⊢
    generalize ((galQuot k L Ω).1 τ).choose = b at h2 ⊢
    generalize ((galQuot k L Ω).1 (σ * τ)).choose = c at h3 ⊢
    have : (a * b)⁻¹ * c ∈ galOf k L Ω := by
      rw [← (galQuot k L Ω).2.1, MonoidHom.mem_ker, map_mul, map_inv, map_mul, h1, h2, h3, inv_mul_cancel]
    rw [← map_mul, ← mul_one (π (a * b)), ← h _ this, ← map_mul, mul_inv_cancel_left]

theorem descHom_res {M : Type} [Monoid M] (π : G k Ω →* M) (h : ∀ g ∈ galOf k L Ω, π g = 1) (g : G k Ω) :
    descHom L π h (resG L g) = π g := by
  have h1 := ((galQuot k L Ω).1 (resG L g)).choose_spec
  show π ((galQuot k L Ω).1 (resG L g)).choose = π g
  generalize ((galQuot k L Ω).1 (resG L g)).choose = a at h1 ⊢
  have : a⁻¹ * g ∈ galOf k L Ω := by
    rw [← (galQuot k L Ω).2.1, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  rw [← mul_one (π a), ← h _ this, ← map_mul, mul_inv_cancel_left]

variable (k Ω) (l : ℕ) [Fact l.Prime] (N : ℕ)

abbrev YL (e : ℤ) : Type := Ye l N (galOf k L Ω) (galOf k L Ω) e

def yGal (e : ℤ) : Representation ℤ_[l] (L ≃ₐ[k] L) (YL k Ω L l N e) :=
  descHom L (yRep l N (galOf k L Ω) (galOf k L Ω) e) fun g hg => LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    exact Representation.Coinvariants.mk_self_apply _ (⟨g, hg⟩ : galOf k L Ω) x

theorem yGal_res (e : ℤ) (g : G k Ω) : yGal k Ω L l N e (resG L g) = yRep l N (galOf k L Ω) (galOf k L Ω) e g :=
  descHom_res L _ _ g

abbrev YLSign (e : ℤ) (c : L ≃ₐ[k] L) (s : ℤ_[l]) : Type :=
  YL k Ω L l N e ⧸ LinearMap.range (yGal k Ω L l N e c - s • (1 : Module.End ℤ_[l] (YL k Ω L l N e)))

def TwLimit (e : ℤ) (z : MonoidAlgebra ℤ_[l] (L ≃ₐ[k] L)) : Prop :=
  ∀ r n₀ : ℕ, ∃ n, n₀ ≤ n ∧ ∃ (ι : Type) (_ : Fintype ι) (s : ι → G k Ω) (b : ι → ℤ) (w : MonoidAlgebra ℤ_[l] (L ≃ₐ[k] L)),
    ClAnn (Fn L Ω l n) s b ∧
    ∑ i, MonoidAlgebra.single (resG L (s i)) ((b i : ℤ_[l]) * ((cycZ k Ω l (s i) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])) =
      z + (l : ℤ_[l]) ^ r • w

theorem twLimit_zero (e : ℤ) : TwLimit k Ω L l e 0 := fun _ n₀ =>
  ⟨n₀, le_rfl, Empty, inferInstance, Empty.elim, Empty.elim, 0, ⟨Empty.elim, fun i => i.elim, fun _ => by simp⟩, by simp⟩

end Desc

end UpperTheory.V.Tower

end
