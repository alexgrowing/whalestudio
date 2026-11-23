import Mathlib

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open PowerSeries

section EvF

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ)

def Zp : Polynomial O := (1 + Polynomial.X) ^ (p ^ m) - 1

def Zs : PowerSeries O := (1 + PowerSeries.X) ^ (p ^ m) - 1

theorem Zs_coe : ((Zp (O := O) p m : Polynomial O) : PowerSeries O) = Zs p m := by
  simp [Zp, Zs]

theorem X_add_one_monic : (Polynomial.X + 1 : Polynomial O).Monic := by
  simpa using Polynomial.monic_X_add_C (1 : O)

theorem pow_natDegree' : ((1 + Polynomial.X : Polynomial O) ^ (p ^ m)).natDegree = p ^ m := by
  have h1 : (1 + Polynomial.X : Polynomial O).Monic := by rw [add_comm]; exact X_add_one_monic
  have h2 : (1 + Polynomial.X : Polynomial O).natDegree = 1 := by
    rw [add_comm]; simpa using Polynomial.natDegree_X_add_C (1 : O)
  rw [h1.natDegree_pow, h2, mul_one]

theorem Zp_monic : (Zp (O := O) p m).Monic := by
  have h1 : (1 + Polynomial.X : Polynomial O).Monic := by rw [add_comm]; exact X_add_one_monic
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  have h2 := h1.pow (p ^ m)
  unfold Zp
  apply h2.sub_of_left
  rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree h2.ne_zero, pow_natDegree']
  first
  | exact_mod_cast hpm
  | exact WithBot.coe_lt_coe.mpr hpm

private theorem algHom_coe_polynomial_eq_of_X_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (φ ψ : PowerSeries A →ₐ[A] B) (h : φ PowerSeries.X = ψ PowerSeries.X) (r : Polynomial A) :
    φ (r : PowerSeries A) = ψ (r : PowerSeries A) := by
  first
  | (have e := Polynomial.algHom_ext (f := φ.comp (Polynomial.coeToPowerSeries.algHom A))
        (g := ψ.comp (Polynomial.coeToPowerSeries.algHom A)) (by simpa using h)
     simpa using AlgHom.congr_fun e r)
  | (have hC : ∀ a : A, φ ((Polynomial.C a : Polynomial A) : PowerSeries A) =
          ψ ((Polynomial.C a : Polynomial A) : PowerSeries A) := by
        intro a
        have e : ((Polynomial.C a : Polynomial A) : PowerSeries A) = algebraMap A (PowerSeries A) a := by
          first
          | rw [Polynomial.coe_C, PowerSeries.algebraMap_eq]
          | simp [PowerSeries.algebraMap_eq]
        rw [e, AlgHom.commutes, AlgHom.commutes]
     refine Polynomial.induction_on r (fun a => hC a) (fun p q hp hq => ?_) (fun n a _ => ?_)
     · rw [Polynomial.coe_add, map_add, map_add, hp, hq]
     · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_mul, map_pow,
         map_pow, h, hC])

theorem Zp_natDegree : (Zp (O := O) p m).natDegree = p ^ m := by
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  unfold Zp
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, pow_natDegree']
  rw [Polynomial.natDegree_one, pow_natDegree']; exact hpm

variable (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
include hlm

theorem Zs_res : PowerSeries.map (IsLocalRing.residue O) (Zs p m) = PowerSeries.X ^ (p ^ m) := by
  have hpp : p.Prime := Fact.out
  have hp : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff ((p : ℕ) : O)).mpr hlm
    simpa using h
  haveI hk : CharP (IsLocalRing.ResidueField O) p := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hpp).mpr hp
    | exact CharP.charP_of_prime_eq_zero hpp hp
    | (have h1 : ringChar (IsLocalRing.ResidueField O) ∣ p := ringChar.dvd hp
       rcases (Nat.dvd_prime hpp).mp h1 with h2 | h2
       · exact absurd h2 CharP.ringChar_ne_one
       · exact ringChar.of_eq h2)
  haveI : CharP (PowerSeries (IsLocalRing.ResidueField O)) p := by
    first
    | infer_instance
    | exact charP_of_injective_algebraMap' (IsLocalRing.ResidueField O) p
  simp only [Zs, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  first
  | (rw [add_pow_char_pow]; simp)
  | (rw [add_pow_expChar_pow]; simp)

theorem Zs_res_ne : PowerSeries.map (IsLocalRing.residue O) (Zs p m) ≠ 0 := by
  rw [Zs_res p m hlm]; exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem Zs_order : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (Zs p m)).order.toNat =
    p ^ m := by
  have h : (PowerSeries.map (IsLocalRing.residue O) (Zs p m)).order.toNat = p ^ m := by
    first
    | rw [Zs_res p m hlm, PowerSeries.order_X_pow, ENat.toNat_coe]
    | simp [Zs_res p m hlm]
  exact h

variable {F : Type} [CommRing F] [Algebra O F]

def evP (x : F) (f : PowerSeries O) : F := Polynomial.aeval x (f %ʷ Zs p m)

omit hlm in
theorem evalWeierstrassMod_def (x : F) (f : PowerSeries O) : evP p m x f = Polynomial.aeval x (f %ʷ Zs p m) := rfl

theorem evalWeierstrassMod_eq_aeval_of_eq {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (f q : PowerSeries O)
    (r : Polynomial O) (h : f = Zs p m * q + (r : PowerSeries O)) :
    evP p m x f = Polynomial.aeval x r := by
  have hne := Zs_res_ne p m hlm
  have hW := f.isWeierstrassDivision_weierstrassDiv_weierstrassMod hne
  have hP := Zp_monic (O := O) p m
  have hord : (PowerSeries.map (IsLocalRing.residue O) (Zs p m)).order.toNat = p ^ m := by
    first
    | rw [Zs_res p m hlm, PowerSeries.order_X_pow, ENat.toNat_coe]
    | simp [Zs_res p m hlm]
  rw [evalWeierstrassMod_def]
  generalize hq0 : f /ʷ Zs p m = q0 at hW
  generalize hr0 : f %ʷ Zs p m = r0 at hW ⊢
  have h2 := hW.eq_mul_add
  have e1 : ((r0 - r : Polynomial O) : PowerSeries O) = Zs p m * (q - q0) := by
    rw [Polynomial.coe_sub]; linear_combination h - h2
  have hdiv : (((r0 - r) %ₘ Zp p m + Zp p m * ((r0 - r) /ₘ Zp p m) : Polynomial O) :
      PowerSeries O) = ((r0 - r : Polynomial O) : PowerSeries O) := by
    first
    | rw [Polynomial.modByMonic_add_div _ _ hP]
    | rw [Polynomial.modByMonic_add_div (r0 - r) (Zp p m)]
    | rw [Polynomial.modByMonic_add_div (r0 - r) hP]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Zs_coe] at hdiv
  have H1 : PowerSeries.IsWeierstrassDivision (((r0 - r) %ₘ Zp p m : Polynomial O) : PowerSeries O)
      (Zs p m) (q - q0 - (((r0 - r) /ₘ Zp p m : Polynomial O) : PowerSeries O)) 0 := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.coe_zero, add_zero]; linear_combination hdiv + e1
  have H2 : PowerSeries.IsWeierstrassDivision (((r0 - r) %ₘ Zp p m : Polynomial O) : PowerSeries O)
      (Zs p m) 0 ((r0 - r) %ₘ Zp p m) := by
    refine ⟨?_, ?_⟩
    · first
      | rw [Zs_order p m hlm]
      | rw [hord]
      calc ((r0 - r) %ₘ Zp p m).degree < (Zp (O := O) p m).degree :=
            Polynomial.degree_modByMonic_lt _ hP
        _ = ((p ^ m : ℕ) : WithBot ℕ) := by
            rw [Polynomial.degree_eq_natDegree hP.ne_zero, Zp_natDegree]
    · rw [mul_zero, zero_add]
  have hb : (r0 - r) %ₘ Zp p m = 0 := by
    first
    | exact (PowerSeries.IsWeierstrassDivision.elim hne H1 H2).2.symm
    | exact (H1.elim hne H2).2.symm
    | exact (H2.eq_weierstrassDiv_weierstrassMod hne).2.trans (H1.eq_weierstrassDiv_weierstrassMod hne).2.symm
  have hdvd : Zp p m ∣ r0 - r := (Polynomial.modByMonic_eq_zero_iff_dvd hP).mp hb
  have h3 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hx
  rw [map_sub, sub_eq_zero] at h3
  exact h3

def evR {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) : PowerSeries O →ₐ[O] F where
  toFun := evP p m x
  map_one' := by
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx 1 0 1 (by simp)]; simp
  map_mul' f g := by
    obtain ⟨qf, hf⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
      ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
    obtain ⟨qg, hg⟩ : ∃ q, g = Zs p m * q + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
      ⟨_, (g.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
    have key : f * g = Zs p m * (qf * (Zs p m * qg + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O)) +
        ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) * qg) +
        (((f %ʷ Zs p m) * (g %ʷ Zs p m) : Polynomial O) : PowerSeries O) := by
      calc f * g = (Zs p m * qf + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O)) *
            (Zs p m * qg + ((g %ʷ Zs p m : Polynomial O) : PowerSeries O)) := by rw [← hf, ← hg]
        _ = _ := by rw [Polynomial.coe_mul]; ring
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx (f * g) _ _ key, map_mul]
    rfl
  map_zero' := by
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx 0 0 0 (by simp)]; simp
  map_add' f g := by
    have hf := (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add
    have hg := (g.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx (f + g) (f /ʷ Zs p m + g /ʷ Zs p m) ((f %ʷ Zs p m) + (g %ʷ Zs p m)) ?_,
      map_add]
    · rfl
    · conv_lhs => rw [hf, hg]
      rw [Polynomial.coe_add]
      ring
  commutes' o := by
    show evP p m x (algebraMap O (PowerSeries O) o) = algebraMap O F o
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx _ 0 (Polynomial.C o) (by simp [PowerSeries.algebraMap_eq])]
    simp

theorem evR_apply {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (f : PowerSeries O) :
    evR p m hlm hx f = evP p m x f := rfl

theorem evR_coe {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (r : Polynomial O) :
    evR p m hlm hx (r : PowerSeries O) = Polynomial.aeval x r := by
  rw [evR_apply]
  exact evalWeierstrassMod_eq_aeval_of_eq p m hlm hx _ 0 r (by rw [mul_zero, zero_add])

theorem evR_X {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) :
    evR p m hlm hx PowerSeries.X = x := by
  have h := evR_coe p m hlm hx (Polynomial.X : Polynomial O)
  rwa [Polynomial.coe_X, Polynomial.aeval_X] at h

theorem evR_Zs {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) :
    evR p m hlm hx (Zs p m) = 0 := by
  have h := evR_coe p m hlm hx (Zp (O := O) p m)
  rwa [Zs_coe, hx] at h

theorem evR_subst {x y : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hy : Polynomial.aeval y (Zp (O := O) p m) = 0) (u : PowerSeries O)
    (hu : PowerSeries.constantCoeff u = 0) (huy : evR p m hlm hx u = y) (f : PowerSeries O) :
    evR p m hlm hx (PowerSeries.subst u f) = evR p m hlm hy f := by
  have hu' : PowerSeries.HasSubst u := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hu
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hu
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PowerSeries O →ₐ[O] F,
      ∀ g, evR p m hlm hx (PowerSeries.subst u g) = ψ g :=
    ⟨(evR p m hlm hx).comp (PowerSeries.substAlgHom hu'), fun g => by
      first
      | rfl
      | rw [AlgHom.comp_apply, PowerSeries.coe_substAlgHom]
      | simp [PowerSeries.coe_substAlgHom]⟩
  have hX : ψ PowerSeries.X = evR p m hlm hy PowerSeries.X := by
    rw [← hψ, PowerSeries.subst_X hu', huy, evR_X]
  have hpoly := algHom_coe_polynomial_eq_of_X_eq ψ (evR p m hlm hy) hX
  have hS : ψ (Zs p m) = 0 := by
    rw [← Zs_coe, hpoly, evR_coe, hy]
  obtain ⟨q, r, hf⟩ : ∃ (q : PowerSeries O) (r : Polynomial O),
      f = Zs p m * q + (r : PowerSeries O) :=
    ⟨_, _, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod
      (Zs_res_ne p m hlm)).eq_mul_add⟩
  rw [hψ, hf, map_add, map_add, map_mul, map_mul, hS, evR_Zs p m hlm hy, hpoly]
  simp

end EvF

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
