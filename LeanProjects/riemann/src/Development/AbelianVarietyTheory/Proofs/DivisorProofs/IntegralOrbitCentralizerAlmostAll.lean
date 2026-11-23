import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarPreservesIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMeanValueNonnegative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrderCentralizerStable
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.KottAlmost

section Generic

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

def shU (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : Aˣ where
  val := (σ u).unop
  inv := (σ ((u⁻¹ : Aˣ) : A)).unop
  val_inv := by rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  inv_val := by rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem shU_inv_val (σ : A →+* Aᵐᵒᵖ) (u : Aˣ) : (((shU σ u)⁻¹ : Aˣ) : A) = (σ ((u⁻¹ : Aˣ) : A)).unop := rfl

theorem sh_mul (σ : A →+* Aᵐᵒᵖ) (a b : A) : (σ (a * b)).unop = (σ b).unop * (σ a).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem comm_sh (σ : A →+* Aᵐᵒᵖ) (a : A) (y : Aˣ) (cy : Kˣ)
    (hy : (y : A) * (σ y).unop = algebraMap K A cy) (ha : a * y = y * a) :
    (σ a).unop * y = y * (σ a).unop := by
  have hsy : (σ y).unop = ((y⁻¹ : Aˣ) : A) * algebraMap K A cy := by
    rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
  have h := congrArg (fun z => (σ z).unop) ha
  simp only [sh_mul] at h
  rw [hsy] at h
  have h' : (((y⁻¹ : Aˣ) : A) * (σ a).unop) * algebraMap K A cy =
      ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * algebraMap K A cy := by
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, h]; simp only [mul_assoc]
  have hk : IsUnit (algebraMap K A cy) := cy.isUnit.map (algebraMap K A)
  have h'' := hk.mul_right_cancel h'
  calc (σ a).unop * y = y * (((y⁻¹ : Aˣ) : A) * (σ a).unop) * y := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = y * ((σ a).unop * ((y⁻¹ : Aˣ) : A)) * y := by rw [h'']
    _ = y * (σ a).unop := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

end Generic

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

section Step

variable {K A : Type} [CommRing K] [Ring A] [Algebra K A]

theorem step (σ : A →+* Aᵐᵒᵖ) (hinv : ∀ a, (σ (σ a).unop).unop = a)
    (I : A → Prop) (J : K → Prop) (hJ1 : J 1)
    (h1 : ∀ a b, I a → I b → I (a * b)) (h2 : ∀ a, I a → I (σ a).unop)
    (γ : uGroup (A := K) σ)
    (h3 : ∀ g : Aˣ, I ((g⁻¹ * (γ : Aˣ × Kˣ).1 * g : Aˣ) : A) → I ((g⁻¹ * (γ : Aˣ × Kˣ).1⁻¹ * g : Aˣ) : A) →
      ∃ e : Aˣ, e * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * e ∧ I ((e⁻¹ * g : Aˣ) : A) ∧ I ((g⁻¹ * e : Aˣ) : A))
    (h4 : ∀ s : Aˣ, s * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * s → I (s : A) → I ((s⁻¹ : Aˣ) : A) →
      (σ s).unop = s → ∃ t : Aˣ, t * (γ : Aˣ × Kˣ).1 = (γ : Aˣ × Kˣ).1 * t ∧ I (t : A) ∧ I ((t⁻¹ : Aˣ) : A) ∧
        (t : A) * (σ t).unop = s)
    (g : uGroup (A := K) σ)
    (hg : I (((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1 : A) ∧
      I (((((g⁻¹ * γ * g : uGroup (A := K) σ) : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A)) :
    ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id _) γ, ∃ d : uGroup (A := K) σ,
      (I ((d : Aˣ × Kˣ).1 : A) ∧ I ((((d : Aˣ × Kˣ).1)⁻¹ : Aˣ) : A) ∧ J ((d : Aˣ × Kˣ).2 : K) ∧
        J ((((d : Aˣ × Kˣ).2)⁻¹ : Kˣ) : K)) ∧ g = c * d := by
  obtain ⟨⟨g1, cg⟩, hgm⟩ := g
  obtain ⟨⟨y, cy⟩, hym⟩ := γ
  have hgm' : (g1 : A) * (σ g1).unop = algebraMap K A cg := hgm
  have hym' : (y : A) * (σ y).unop = algebraMap K A cy := hym
  have hg1 : I ((g1⁻¹ * y * g1 : Aˣ) : A) := hg.1
  have hg2 : I ((g1⁻¹ * y⁻¹ * g1 : Aˣ) : A) := by
    have e : (g1⁻¹ * y * g1 : Aˣ)⁻¹ = g1⁻¹ * y⁻¹ * g1 := by group
    rw [← e]; exact hg.2
  obtain ⟨e, he, hu1, hu2⟩ := h3 g1 hg1 hg2
  obtain ⟨u, hu⟩ : ∃ u : Aˣ, u = e⁻¹ * g1 := ⟨_, rfl⟩
  rw [← hu] at hu1
  have hu2' : I ((u⁻¹ : Aˣ) : A) := by
    have : u⁻¹ = g1⁻¹ * e := by rw [hu]; group
    rw [this]; exact hu2
  obtain ⟨s, hs⟩ : ∃ s : Aˣ, s = u * shU σ u := ⟨_, rfl⟩
  have hsv : (s : A) = (u : A) * (σ u).unop := by rw [hs]; rfl
  have hsI : I (s : A) := by rw [hsv]; exact h1 _ _ hu1 (h2 _ hu1)
  have hsI' : I ((s⁻¹ : Aˣ) : A) := by
    rw [hs, _root_.mul_inv_rev, Units.val_mul, shU_inv_val]
    exact h1 _ _ (h2 _ hu2') hu2'
  have hss : (σ s).unop = s := by
    rw [hsv, sh_mul, hinv]
  have hsval : (s : A) = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop := by
    rw [hsv, hu, Units.val_mul, sh_mul, ← hgm']
    simp only [mul_assoc]
  have hey : ((e⁻¹ : Aˣ) : A) * y = y * ((e⁻¹ : Aˣ) : A) := by
    have : e⁻¹ * y = y * e⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, he, mul_inv_cancel_right]
    exact congrArg Units.val this
  have hby := comm_sh σ ((e⁻¹ : Aˣ) : A) y cy hym' hey
  have hsy : s * y = y * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsval]
    calc ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop * y
        = ((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (y * (σ ((e⁻¹ : Aˣ) : A)).unop) := by rw [mul_assoc, hby]
      _ = ((e⁻¹ : Aˣ) : A) * (y * algebraMap K A cg) * (σ ((e⁻¹ : Aˣ) : A)).unop := by
          rw [mul_assoc ((e⁻¹ : Aˣ) : A), ← mul_assoc (algebraMap K A cg), Algebra.commutes]; simp only [mul_assoc]
      _ = (y : A) * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) := by
          rw [← mul_assoc ((e⁻¹ : Aˣ) : A) (y : A), hey]; simp only [mul_assoc]
  obtain ⟨t, ht, htI, htI', hts⟩ := h4 s hsy hsI hsI' hss
  have hcm : ((e * t : Aˣ) : A) * (σ ((e * t : Aˣ) : A)).unop = algebraMap K A cg := by
    rw [Units.val_mul, sh_mul]
    calc (e : A) * t * ((σ t).unop * (σ e).unop) = e * (t * (σ t).unop) * (σ e).unop := by
          simp only [mul_assoc]
      _ = e * (((e⁻¹ : Aˣ) : A) * algebraMap K A cg * (σ ((e⁻¹ : Aˣ) : A)).unop) * (σ e).unop := by
          rw [hts, hsval]
      _ = algebraMap K A cg * ((σ ((e⁻¹ : Aˣ) : A)).unop * (σ e).unop) := by
          simp only [← mul_assoc, Units.mul_inv, one_mul]
      _ = _ := by rw [← sh_mul, Units.mul_inv, map_one, MulOpposite.unop_one, mul_one]
  have hdm : ((t⁻¹ * u : Aˣ) : A) * (σ ((t⁻¹ * u : Aˣ) : A)).unop = algebraMap K A ((1 : Kˣ) : K) := by
    rw [Units.val_mul, sh_mul, Units.val_one, map_one]
    calc ((t⁻¹ : Aˣ) : A) * u * ((σ u).unop * (σ ((t⁻¹ : Aˣ) : A)).unop)
        = ((t⁻¹ : Aˣ) : A) * ((u : A) * (σ u).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by simp only [mul_assoc]
      _ = ((t⁻¹ : Aˣ) : A) * ((t : A) * (σ t).unop) * (σ ((t⁻¹ : Aˣ) : A)).unop := by
          rw [hts, hsv]
      _ = 1 := by
          rw [← mul_assoc, Units.inv_mul, one_mul, ← sh_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  refine ⟨⟨(e * t, cg), hcm⟩, ?_, ⟨(t⁻¹ * u, 1), hdm⟩, ⟨h1 _ _ htI' hu1, ?_, hJ1, by rw [inv_one]; exact hJ1⟩, ?_⟩
  · apply Subtype.ext; apply Prod.ext
    · show e * t * y = y * (e * t)
      rw [mul_assoc, ht, ← mul_assoc, he, mul_assoc]
    · show cg * cy = cy * cg
      exact mul_comm _ _
  · show I (((t⁻¹ * u)⁻¹ : Aˣ) : A)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    exact h1 _ _ hu2' htI
  · apply Subtype.ext; apply Prod.ext
    · show g1 = e * t * (t⁻¹ * u)
      rw [hu]; group
    · show cg = cg * 1
      rw [mul_one]

end Step

end GlobalTheory.OrbFinAf.KottAlmost

namespace GlobalTheory.OrbFinAf.KottAlmost

theorem starT_starT {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R a).unop).unop = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => rw [starT_tmul, starT_tmul, G.star_star]
  | add a b ha hb => rw [map_add, MulOpposite.unop_add, map_add, MulOpposite.unop_add, ha, hb]

end GlobalTheory.OrbFinAf.KottAlmost
