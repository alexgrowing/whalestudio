import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

variable {p : ℕ} [Fact p.Prime]

def InT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β y : G.C) (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R (z.1 : R ⊗[ℚ] G.C)).unop =
      algebraMap R (R ⊗[ℚ] G.C) (z.2 : R) * inC G R β ∧
    Commute (z.1 : R ⊗[ℚ] G.C) (inC G R y)

def psiAway (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
  (MulAut.conj x).toMonoidHom.prodMap (MonoidHom.id _)

def psiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gr G 1 :=
  (inclG G 1).comp ((MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _)))

@[simp] theorem psiAway_apply (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :
    psiAway G x z = (x * z.1 * x⁻¹, z.2) := rfl

def dg (D : Type) [Ring D] [Algebra ℚ D] (p : ℕ) [Fact p.Prime] :
    Dˣ × ℚˣ →* ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
  ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] AfP p ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).prod
    ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] ℚ_[p] ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom))

theorem toAfF_eq_psiAway (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) :
    ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x ((dg G.C p (y : G.Cˣ × ℚˣ)).1) := rfl

theorem formGroupToPadicPointsDegreeOne_eq_unitaryPoints (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    toP1 G β y = psiP G ((dg G.C p (y : G.Cˣ × ℚˣ)).2) := by
  simp only [toP1, psiP, MonoidHom.comp_apply]
  congr 1
  refine Prod.ext rfl (funext fun w => Units.ext ?_)
  change G.rho w _ = G.locW w ((1 : ℚ_[p]) ⊗ₜ _)
  change _ = (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) * (G.rho w).toRatAlgHom _
  rw [map_one, one_mul]
  rfl

theorem form_mul_inv {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β : D) (a e : Dˣ) (α η : ℚˣ)
    (ha : (a : D) * β * (σ a).unop = algebraMap ℚ D α * β) (he : (e : D) * β * (σ e).unop = algebraMap ℚ D η * β) :
    ((a * e⁻¹ : Dˣ) : D) * β * (σ ((a * e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((α * η⁻¹ : ℚˣ) : ℚ) * β := by
  have hs : (σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hs' : (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (e : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have hη : algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ D (η : ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * β := by
    calc ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop
        = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * (((e⁻¹ : Dˣ) : D) * (algebraMap ℚ D (η : ℚ) * β) *
            (σ ((e⁻¹ : Dˣ) : D)).unop) := by
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
          rw [show (η : ℚ) * ((η⁻¹ : ℚˣ) : ℚ) = 1 by simp, one_smul]
      _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((((e⁻¹ : Dˣ) : D) * e) * β *
            ((σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop)) := by
          rw [← he]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs, one_mul, mul_one]
  have hsm : (σ ((a * e⁻¹ : Dˣ) : D)).unop = (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  rw [hsm, Units.val_mul, Units.val_mul, map_mul]
  calc (a : D) * ((e⁻¹ : Dˣ) : D) * β * ((σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop)
      = (a : D) * (((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop) * (σ (a : D)).unop := by
        simp only [mul_assoc]
    _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((a : D) * β * (σ (a : D)).unop) := by
        rw [key, ← mul_assoc (a : D), ← Algebra.commutes ((η⁻¹ : ℚˣ) : ℚ) (a : D)]; simp only [mul_assoc]
    _ = _ := by
        rw [ha, ← mul_assoc, ← map_mul, mul_comm ((η⁻¹ : ℚˣ) : ℚ), map_mul]

theorem conj_back {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x g : Sˣ)
    (t c : A) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hg : (g : S) * (σ g).unop = algebraMap A S c) :
    ((x⁻¹ * g * x : Sˣ) : S) * b * (σ ((x⁻¹ * g * x : Sˣ) : S)).unop = algebraMap A S c * b := by
  have h1 : (σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = algebraMap A S t * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ (x : S)).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by rw [hx, ← Algebra.commutes, mul_assoc]
  have hσ : (σ ((x⁻¹ * g * x : Sˣ) : S)).unop =
      (σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop := by
    simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [hσ]
  calc ((x⁻¹ * g * x : Sˣ) : S) * b * ((σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)
      = ((x⁻¹ : Sˣ) : S) * ((g : S) * ((x : S) * b * (σ (x : S)).unop) * (σ (g : S)).unop) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = ((x⁻¹ : Sˣ) : S) * (algebraMap A S t * ((g : S) * (σ (g : S)).unop)) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        rw [hx, ← Algebra.commutes t (g : S)]; simp only [mul_assoc]
    _ = algebraMap A S (c * t) * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
        rw [hg, ← map_mul, ← Algebra.commutes, mul_assoc, mul_comm t c]
    _ = algebraMap A S c * b := by rw [hb, map_mul, mul_assoc]

theorem inT_psiAway_inv_of_commute : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y₀ : grp G β) (c : G.GAf), c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c →
    InT G (AfP p) β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (psiAway G x⁻¹ (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
  intro p _ G β x t hx y₀ c hc
  have hxx : ((x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) = x := inv_inv x
  refine ⟨?_, ?_⟩
  · have hg : (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (starT G.star (AfP p) (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
          AfP p ⊗[ℚ] G.C)).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) := c.2
    have h := conj_back (starT G.star (AfP p)) (inC G (AfP p) β) x _ (t : AfP p) _ hx hg
    simp only [psiAway_apply, hxx]
    exact h
  · have hU := congrArg (fun g : G.GAf => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)) hc
    simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
    rw [toAfF_eq_psiAway, psiAway_apply] at hU
    simp only [psiAway_apply, hxx]
    set c1 := (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    set Y := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).1.1
    have hUU : (x⁻¹ * c1 * x) * Y = Y * (x⁻¹ * c1 * x) := by
      calc (x⁻¹ * c1 * x) * Y = x⁻¹ * (c1 * (x * Y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * Y * x⁻¹) * c1) * x := by rw [hU]
        _ = Y * (x⁻¹ * c1 * x) := by group
    exact congrArg Units.val hUU

end GlobalTheory.TorCls
