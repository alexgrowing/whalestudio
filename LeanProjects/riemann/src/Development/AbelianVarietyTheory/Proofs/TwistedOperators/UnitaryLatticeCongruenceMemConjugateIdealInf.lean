import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongSelfDual

section Ideals

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem oToS_coe (a : 𝓞 E) : ((Formalism.L2.DIV.oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) := rfl

theorem idS_inf_le (𝔪 𝔫 : Ideal (𝓞 E)) :
    Formalism.L2.DIV.idS F 𝔪 ⊓ Formalism.L2.DIV.idS F 𝔫 ≤ Formalism.L2.DIV.idS F (𝔪 ⊓ 𝔫) := by
  intro x hx
  by_cases hd : 𝔪 ⊔ 𝔫 = ⊥
  · have h1 : 𝔪 = ⊥ := eq_bot_iff.2 (hd ▸ le_sup_left)
    have h2 : 𝔫 = ⊥ := eq_bot_iff.2 (hd ▸ le_sup_right)
    subst h1 h2
    simpa using hx.1
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
  obtain ⟨𝔠, h𝔠⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have key : Ideal.span {a} * (𝔪 ⊓ 𝔫) = 𝔪 * 𝔫 * 𝔠 := by
    rw [h𝔠, mul_comm (𝔪 ⊔ 𝔫) 𝔠, mul_assoc, Ideal.sup_mul_inf, mul_comm]
  have h1 : Formalism.L2.DIV.oToS F E a * x ∈
      Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 := by
    have hfa : Formalism.L2.DIV.oToS F E a ∈ (Formalism.L2.DIV.idS F 𝔪 ⊔ Formalism.L2.DIV.idS F 𝔫) * Formalism.L2.DIV.idS F 𝔠 := by
      have h0 : a ∈ (𝔪 ⊔ 𝔫) * 𝔠 := h𝔠 ▸ Ideal.mem_span_singleton_self a
      have h3 := Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS F E) h0
      unfold Formalism.L2.DIV.idS
      rwa [Ideal.map_mul, Ideal.map_sup] at h3
    have hle : (Formalism.L2.DIV.idS F 𝔪 ⊔ Formalism.L2.DIV.idS F 𝔫) * Formalism.L2.DIV.idS F 𝔠 * Ideal.span {x} ≤
        Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 := by
      rw [mul_right_comm, Ideal.sup_mul]
      refine Ideal.mul_mono (sup_le (Ideal.mul_mono le_rfl ((Ideal.span_singleton_le_iff_mem _).2 hx.2)) ?_) le_rfl
      rw [mul_comm (Formalism.L2.DIV.idS F 𝔪)]
      exact Ideal.mul_mono le_rfl ((Ideal.span_singleton_le_iff_mem _).2 hx.1)
    exact hle (Ideal.mul_mem_mul hfa (Ideal.mem_span_singleton_self x))
  have h2 : Formalism.L2.DIV.idS F 𝔪 * Formalism.L2.DIV.idS F 𝔫 * Formalism.L2.DIV.idS F 𝔠 =
      Ideal.span {Formalism.L2.DIV.oToS F E a} * Formalism.L2.DIV.idS F (𝔪 ⊓ 𝔫) := by
    unfold Formalism.L2.DIV.idS
    rw [← Ideal.map_mul, ← Ideal.map_mul, ← key, Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  rw [h2, Ideal.mem_span_singleton_mul] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  have hu : IsUnit ((Formalism.L2.DIV.oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    rw [oToS_coe]
    have ha1 : algebraMap (𝓞 E) E a ≠ 0 := by
      intro h0; apply ha0; exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h0
    exact (Ne.isUnit ha1).map _
  have hzx' : z = x := by
    apply Subtype.ext
    have h3 := congrArg (fun t : Formalism.L2.Herm.intAf F E => (t : E ⊗[F] Formalism.L2.Herm.Af F)) hzx
    simp only [Subring.coe_mul] at h3
    exact hu.mul_left_cancel h3
  exact hzx' ▸ hz

theorem inId_inf {𝔪 𝔫 : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (h1 : GlobalTheory.FrameIdeal.InId 𝔪 x)
    (h2 : GlobalTheory.FrameIdeal.InId 𝔫 x) : GlobalTheory.FrameIdeal.InId (𝔪 ⊓ 𝔫) x := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, hts⟩ := h2
  obtain rfl : t = s := Subtype.ext hts
  exact ⟨t, idS_inf_le 𝔪 𝔫 ⟨hs, ht⟩, rfl⟩

theorem inId_neg {I : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (h : GlobalTheory.FrameIdeal.InId I x) :
    GlobalTheory.FrameIdeal.InId I (-x) := by
  have := GlobalTheory.FrameIdeal.inId_mul (t := -1) (neg_mem (one_mem _)) h
  rwa [neg_one_mul] at this

end Ideals

section Forms

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_dot (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform τ J x y = (fun i => τ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform τ J (x - y) z = Formalism.UG.hform τ J x z - Formalism.UG.hform τ J y z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (τ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform τ J x (y - z) = Formalism.UG.hform τ J x y - Formalism.UG.hform τ J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_unitary (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT τ B * J * B = J)
    (x y : Fin n → A) : Formalism.UG.hform τ J (B *ᵥ x) (B *ᵥ y) = Formalism.UG.hform τ J x y := by
  rw [GlobalTheory.DualCompletion.hform_mulVec_left, Matrix.mulVec_mulVec, h, hform_dot]
  rfl

theorem hform_mulVec_right (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (a c : Fin n → A) :
    Formalism.UG.hform τ J a (B *ᵥ c) = ∑ k, Formalism.UG.hform τ J a (fun i => B i k) * c k := by
  simp only [hform_dot, Matrix.dotProduct_mulVec]
  rfl

end Forms

variable {D : D7}

local notation "σA" => Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
local notation "ιA" => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)

theorem conjI_eq (𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SW.conjI 𝔪 = D.host.conj • 𝔪 := by
  show _ = 𝔪.map (MulSemiringAction.toRingHom _ _ D.host.conj)
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [hab]
    show (D.host.conj (b : D.host.E)) = star (b : D.host.E)
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    show (D.host.conj (b : D.host.E)) = star (b : D.host.E)
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem inId_hform {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (Lev.EAf D)} (hfr : Formalism.L2.DIV.IsFrame β Λ) {𝔪 : Ideal (𝓞 D.host.E)}
    {a b : Fin V.rank → Lev.EAf D} (ha : a ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hb : b ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) :
    GlobalTheory.FrameIdeal.InId (F := D.host.F) 𝔪 (Formalism.UG.hform σA (V.gram.map ιA) a b) := by
  have hc := (GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr 𝔪 b).1 hb
  have e : b = β.1 *ᵥ ((β⁻¹).1 *ᵥ b) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e, hform_mulVec_right]
  refine GlobalTheory.FrameIdeal.inId_sum _ fun k => GlobalTheory.FrameIdeal.inId_mul ?_ (hc k)
  have hk := GlobalTheory.FrameIdeal.col_mem_hatL hfr k
  rw [Matrix.mulVec_single_one] at hk
  exact GlobalTheory.GramFrame.pair_hatL V.gram Λ (GlobalTheory.FrameIdeal.selfDual_pair hsd) _ _ ha hk

set_option maxHeartbeats 1000000 in

theorem congLev_conj : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (g : GL (Fin V.rank) (Lev.EAf D)), g ∈ congLev D.sp.cm V.gram Λ 𝔪 → g ∈ congLev D.sp.cm V.gram Λ (𝔪 ⊓ D.host.conj • 𝔪) := by
  intro D V Λ hsd 𝔪 g hg
  rw [GlobalTheory.ChiGrid.mem_congLev] at hg ⊢
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨β, hfr⟩ : ∃ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ :=
    GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hsd.1.fg hsd.1.span_eq_top
  refine ⟨g1, g2, fun y hy => ?_⟩
  have hm := g3 y hy
  have hU : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) g.1 *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * g.1 =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := g1
  have hc : g.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.SW.conjI 𝔪 • Λ) := by
    rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr]
    refine (GlobalTheory.FrameIdeal.key_iff hsd hfr 𝔪 _).2 fun j => ?_
    have hx : (β.1)ᵀ j ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
      have h0 := GlobalTheory.FrameIdeal.col_mem_hatL (D := D) (β := β) (Λ := Λ) hfr j
      rwa [Matrix.mulVec_single_one] at h0
    have e : Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (g.1 *ᵥ y - y) (fun c => β.1 c j) =
        -Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
          (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) (g.1 *ᵥ y)
          (g.1 *ᵥ (β.1)ᵀ j - (β.1)ᵀ j) := by
      rw [hform_sub_left, hform_sub_right, hform_unitary _ _ _ hU]
      have : (fun c => β.1 c j) = (β.1)ᵀ j := rfl
      rw [this]; ring
    rw [e]
    exact inId_neg (inId_hform hsd hfr ((g2 y).1 hy) (g3 _ hx))
  rw [conjI_eq] at hc
  rw [GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hfr] at hm hc ⊢
  exact fun i => inId_inf (hm i) (hc i)

end GlobalTheory.CongSelfDual
