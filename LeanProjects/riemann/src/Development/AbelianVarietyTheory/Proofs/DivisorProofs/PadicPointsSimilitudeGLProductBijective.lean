import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMapInjectivity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivExtendingPadicAlgCl

open GlobalTheory.LKTrip
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKTrip.HTGroup.LocPBij

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem starT_starT (x : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (starT G.star ℚ_[p] x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem starT_algebraMap (a : ℚ_[p]) :
    (starT G.star ℚ_[p] (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a)).unop = algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) a := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
    MulOpposite.unop_one]

theorem starT_mul (x y : ℚ_[p] ⊗[ℚ] G.C) :
    (starT G.star ℚ_[p] (x * y)).unop = (starT G.star ℚ_[p] y).unop * (starT G.star ℚ_[p] x).unop := by
  rw [map_mul, MulOpposite.unop_mul]

def starL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C where
  toFun x := (starT G.star ℚ_[p] x).unop
  map_add' x y := by rw [map_add, MulOpposite.unop_add]
  map_smul' a x := by
    rw [Algebra.smul_def, starT_mul, starT_algebraMap, RingHom.id_apply, Algebra.smul_def]
    exact (Algebra.commutes _ _).symm

def psiL : ℚ_[p] ⊗[ℚ] G.C →ₗ[ℚ_[p]]
    ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :=
  LinearMap.prod (LinearMap.pi fun i => (G.locW i).toLinearMap)
    ((LinearMap.pi fun i => (G.locW i).toLinearMap).comp (starL G))

theorem psiL_injective : Function.Injective (psiL G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact GlobalTheory.HTGroupLocInj.locW_inj G x (fun i => congrFun (congrArg Prod.fst hx) i)
    (fun i => congrFun (congrArg Prod.snd hx) i)

theorem finrank_eq : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) = Module.finrank ℚ_[p]
    (((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i))) := by
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_prod,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_matrix, Fintype.card_fin]
  rw [← HTGroup.two_mul_sum_finrank_Fw p G, ← Finset.mul_sum]
  ring

theorem psiL_bijective : Function.Bijective (psiL G) := by
  haveI : ∀ i, FiniteDimensional ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => inferInstance
  exact ⟨psiL_injective G,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq G)).1 (psiL_injective G)⟩

end GlobalTheory.LKTrip.HTGroup.LocPBij

theorem GlobalTheory.LKTrip.HTGroup.bijective_locP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  intro p _ G
  have key : ∀ d : ℚ_[p] ⊗[ℚ] G.C, (starT G.star ℚ_[p] d).unop = d → (∀ i, G.locW i d = 0) → d = 0 :=
    fun d hd h0 => GlobalTheory.HTGroupLocInj.locW_inj G d h0 (fun i => by rw [hd]; exact h0 i)
  constructor
  · rintro ⟨⟨x, c⟩, hx⟩ ⟨⟨y, d⟩, hy⟩ h
    have hx' : (x : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := hx
    have hy' : (y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] y).unop = algebraMap ℚ_[p] _ (d : ℚ_[p]) := hy
    have hc : c = d := congrArg Prod.fst h
    subst hc
    have hu := fun i => congrFun (congrArg Prod.snd h) i
    have sx : (starT G.star ℚ_[p] x).unop = ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hx', ← mul_assoc, Units.inv_mul, one_mul]
    have sy : (starT G.star ℚ_[p] y).unop = ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← hy', ← mul_assoc, Units.inv_mul, one_mul]
    have hw : ∀ i, G.locW i x = G.locW i y := fun i => congrArg Units.val (hu i)
    have hwi : ∀ i, G.locW i ((x⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) = G.locW i ((y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) := by
      intro i
      have := congrArg (fun u => ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ˣ) : Matrix (Fin G.n) (Fin G.n) (G.Fw i))) (hu i)
      exact this
    have hxy : x = y := by
      apply Units.ext
      apply GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_injective G
      refine Prod.ext (funext hw) (funext fun i => ?_)
      show G.locW i (starT G.star ℚ_[p] x).unop = G.locW i (starT G.star ℚ_[p] y).unop
      rw [sx, sy, map_mul, map_mul, hwi]
    subst hxy
    rfl
  · rintro ⟨c, a⟩
    obtain ⟨x, hx⟩ := (GlobalTheory.LKTrip.HTGroup.LocPBij.psiL_bijective G).2
      (fun i => ((a i : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)),
       fun i => algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)))
    have h1 : ∀ i, G.locW i x = a i := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (c : ℚ_[p]) *
        (((a i)⁻¹ : GL (Fin G.n) (G.Fw i)) : Matrix (Fin G.n) (Fin G.n) (G.Fw i)) := fun i => congrFun (congrArg Prod.snd hx) i
    have hyy := GlobalTheory.LKTrip.HTGroup.LocPBij.starT_starT G x
    have hxy : x * (starT G.star ℚ_[p] x).unop = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, Algebra.left_comm, Units.mul_inv, mul_one, sub_self]
    have hyx : (starT G.star ℚ_[p] x).unop * x = algebraMap ℚ_[p] _ (c : ℚ_[p]) := by
      rw [← sub_eq_zero]
      apply key
      · rw [map_sub, MulOpposite.unop_sub, GlobalTheory.LKTrip.HTGroup.LocPBij.starT_mul, hyy,
          GlobalTheory.LKTrip.HTGroup.LocPBij.starT_algebraMap]
      · intro i
        rw [map_sub, map_mul, h1, h2, AlgHom.commutes, mul_assoc, Units.inv_mul, mul_one, sub_self]
    let u : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨x, algebraMap ℚ_[p] _ ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * (starT G.star ℚ_[p] x).unop,
      by rw [Algebra.left_comm, hxy, ← map_mul, Units.inv_mul, map_one],
      by rw [mul_assoc, hyx, ← map_mul, Units.inv_mul, map_one]⟩
    refine ⟨⟨(u, c), hxy⟩, Prod.ext rfl (funext fun i => Units.ext (h1 i))⟩
