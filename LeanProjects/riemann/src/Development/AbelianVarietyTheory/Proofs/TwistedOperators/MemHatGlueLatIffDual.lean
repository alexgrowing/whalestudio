import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

section Flat

variable {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_surj (V : HSp D) (x : Fin V.rank → D.host.E) : ∃ y : V.V, vA V y = fun i => inc D (x i) :=
  ⟨(Formalism.L2.Herm.crd V).symm x, funext fun i => by simp [vA]⟩

theorem eq_sum_vA_frame (x : Fin X.rank → EAf D) : x = ∑ i, x i • vA X (X.frame i) := by
  funext k
  have : ∀ i, vA X (X.frame i) k = if i = k then 1 else 0 := fun i => by
    change inc D (X.frame.repr (X.frame i) k) = _
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp [Finset.sum_apply, this]

theorem adelic_induction {p : (Fin X.rank → EAf D) → Prop} (h1 : ∀ x : X.V, p (vA X x)) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsm : ∀ (a : EAf D) x, p x → p (a • x)) (x : Fin X.rank → EAf D) : p x := by
  rw [eq_sum_vA_frame x]
  exact Finset.sum_induction _ p hadd h0 fun i _ => hsm _ _ (h1 _)

theorem hA_zero_left (V : HSp D) (y : Fin V.rank → EAf D) : hA V 0 y = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_zero_right (V : HSp D) (y : Fin V.rank → EAf D) : hA V y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mA_mA (h : HSpace.IsIsomEmb X Y ι) (x x' : Fin X.rank → EAf D) :
    hA Y (mA Y X ι *ᵥ x) (mA Y X ι *ᵥ x') = hA X x x' := by
  induction x using adelic_induction with
  | h1 x =>
    induction x' using adelic_induction with
    | h1 x' => rw [mA_mulVec_vA, mA_mulVec_vA, hA_vA, hA_vA, HSpace.hD, HSpace.hD, h]
    | h0 => rw [mulVec_zero, hA_zero_right, hA_zero_right]
    | hadd a b ha hb => rw [mulVec_add, hA_add_right, hA_add_right, ha, hb]
    | hsm c a ha => rw [mulVec_smul, hA_smul_right, hA_smul_right, ha]
  | h0 => rw [mulVec_zero, hA_zero_left, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, hA_add_left, ha, hb]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, hA_smul_left, ha]

theorem hA_mA_vA (h : IsLine Y X ι z u) (x : Fin X.rank → EAf D) : hA Y (mA Y X ι *ᵥ x) (vA Y z) = 0 := by
  induction x using adelic_induction with
  | h1 x => rw [mA_mulVec_vA, hA_vA, h.2.1, RingHom.map_zero]
  | h0 => rw [mulVec_zero, hA_zero_left]
  | hadd a b ha hb => rw [mulVec_add, hA_add_left, ha, hb, add_zero]
  | hsm c a ha => rw [mulVec_smul, hA_smul_left, ha, mul_zero]

theorem hA_flat (h : IsLine Y X ι z u) (x x' : Fin X.rank → EAf D) (a a' : EAf D) :
    hA Y (mA Y X ι *ᵥ x + a • vA Y z) (mA Y X ι *ᵥ x' + a' • vA Y z) = hA X x x' - a * cjA D a' * inc D (Tu D u) := by
  have h1 : hA Y (vA Y z) (mA Y X ι *ᵥ x') = 0 := by rw [← cjA_hA, hA_mA_vA h, RingHom.map_zero]
  rw [hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
    hA_mA_mA h.1, hA_mA_vA h, h1, hA_vA, h.2.2, RingHom.map_neg]
  ring

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← RingHom.map_mul, inv_mul_cancel₀ (Tu_ne_zero u), RingHom.map_one]

theorem cjA_inc_Tu (u : D.what₂.Word) : cjA D (inc D (Tu D u)) = inc D (Tu D u) := by rw [cjA_inc, star_natCast]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc, star_inv₀, star_natCast]

theorem inc_Tu_mem (u : D.what₂.Word) : inc D (Tu D u) ∈ OA D := by
  rw [map_natCast]; exact natCast_mem _ _

theorem eq_zero_of_hA {V : HSp D} {x : Fin V.rank → EAf D} (h : ∀ y, hA V x y = 0) : x = 0 := by
  have h1 : V.gram.map (inc D) *ᵥ x = 0 := funext fun i => by
    rw [← Formalism.UG.P.sf_single (cjA D)]; exact h _
  exact Matrix.mulVec_injective_of_isUnit (isUnit_gram V) (h1.trans (mulVec_zero _).symm)

theorem flat_inj (h : IsLine Y X ι z u) {x x' : Fin X.rank → EAf D} {a a' : EAf D}
    (e : mA Y X ι *ᵥ x + a • vA Y z = mA Y X ι *ᵥ x' + a' • vA Y z) : x = x' ∧ a = a' := by
  constructor
  · rw [← sub_eq_zero]
    refine eq_zero_of_hA fun y => ?_
    have h1 := hA_flat h x y a 0
    rw [e, hA_flat h] at h1
    rw [hA_sub_left]
    simp only [RingHom.map_zero, mul_zero, zero_mul, sub_zero] at h1
    rw [h1, sub_self]
  · have h1 := hA_flat h x 0 a (inc D (Tu D u)⁻¹)
    rw [e, hA_flat h, hA_zero_right, hA_zero_right, cjA_inc_inv, mul_assoc, mul_assoc, inc_inv_mul] at h1
    linear_combination h1

theorem mem_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E, y = ι x + (a : D.host.E) • ((Tu D u)⁻¹ • z + ι x₀) := by
  rw [glueLat, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, hx, a, by rw [← algebraMap_smul D.host.E a]; rfl⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨a, rfl⟩, by rw [← algebraMap_smul D.host.E a]; rfl⟩

set_option maxHeartbeats 1600000 in

theorem mem_hat_glueLat {L₀ : Lat X} {x₀ : X.V} (y : Fin Y.rank → EAf D) :
    y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔ ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z := by
  constructor
  · intro hy
    refine hat_induction (p := fun y => ∃ x ∈ hat L₀, ∃ a ∈ OA D,
      y = mA Y X ι *ᵥ (x + a • vA X x₀) + (a * inc D (Tu D u)⁻¹) • vA Y z) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, a, rfl⟩ := (mem_glueLat y).1 hy
      refine ⟨vA X x, inc_mem_hat hx, inc D a, (inc_mem_iff _).2 ⟨a, rfl⟩, ?_⟩
      change vA Y _ = _
      rw [vA_add, vA_smul, vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, mA_mulVec_vA, smul_add, smul_smul]
      abel
    · exact ⟨0, zero_mem_hat, 0, zero_mem _, by rw [zero_smul, add_zero, mulVec_zero, zero_mul, zero_smul, add_zero]⟩
    · rintro _ _ ⟨x, hx, a, ha, rfl⟩ ⟨x', hx', a', ha', rfl⟩
      refine ⟨x + x', add_mem_hat hx hx', a + a', add_mem ha ha', ?_⟩
      rw [add_smul, add_mul, add_smul, add_add_add_comm x, mulVec_add _ (x + _)]
      abel
    · rintro c hc _ ⟨x, hx, a, ha, rfl⟩
      refine ⟨c • x, smul_mem_hat hc hx, c * a, mul_mem hc ha, ?_⟩
      rw [smul_add, ← mulVec_smul, smul_add, smul_smul, smul_smul, mul_assoc]
  · rintro ⟨x, hx, a, ha, rfl⟩
    have h1 : mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) := by
      refine hat_induction (p := fun x => mA Y X ι *ᵥ x ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)))
        ?_ ?_ ?_ ?_ hx
      · intro x hx
        obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective x
        change mA Y X ι *ᵥ vA X x ∈ _
        rw [mA_mulVec_vA]
        exact vA_mem_hat Y ((mem_glueLat _).2 ⟨x, hx, 0, by simp⟩)
      · rw [mulVec_zero]; exact zero_mem_hat
      · intro a b ha hb; rw [mulVec_add]; exact add_mem_hat ha hb
      · intro c hc a ha; rw [mulVec_smul]; exact smul_mem_hat hc ha
    have h2 := smul_mem_hat ha (vA_mem_hat Y ((mem_glueLat (ι := ι) (z := z) (u := u) (L₀ := L₀) (x₀ := x₀)
      ((Tu D u)⁻¹ • z + ι x₀)).2 ⟨0, by simp, 1, by simp⟩))
    convert add_mem_hat h1 h2 using 1
    rw [vA_add, vA_smul, mulVec_add, mulVec_smul, mA_mulVec_vA, smul_add, smul_smul]
    abel

theorem IsGlueVec.congr {L₀ : Lat X} {f f' : Fin X.rank → EAf D} (h : IsGlueVec X u L₀ f) (hf : f - f' ∈ hat L₀) :
    IsGlueVec X u L₀ f' := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f - d := ⟨f - f', (sub_sub_cancel _ _).symm⟩
  rw [sub_sub_cancel] at hf
  refine ⟨?_, h.int, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · rw [smul_sub]; exact sub_mem_hat h.mul_mem (smul_mem_hat (inc_Tu_mem u) hf)
  · rw [hA_sub_left]; exact sub_mem (h.pair y hy) (h.int d hf y hy)
  · have h1 : hA X d f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (h.pair d hf)
    have := sub_mem (sub_mem h.norm (h.pair d hf)) (sub_mem h1 (h.int d hf d hf))
    rw [hA_sub_left, hA_sub_right, hA_sub_right]
    convert this using 1
    ring
  · obtain ⟨a, ha, H⟩ := h.dual y hy
    refine ⟨a, ha, ?_⟩
    convert add_mem_hat H (smul_mem_hat ha hf) using 1
    rw [smul_sub]; abel

set_option maxHeartbeats 1600000 in

theorem mem_hat_glueLat_iff_dual (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ : X.V} (hg : IsGlueVec X u L₀ (vA X x₀))
    (x : Fin X.rank → EAf D) (a : EAf D) :
    mA Y X ι *ᵥ x + a • vA Y z ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) ↔
      ∀ y ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)), hA Y y (mA Y X ι *ᵥ x + a • vA Y z) ∈ OA D := by
  simp only [mem_hat_glueLat]
  generalize vA X x₀ = f at hg
  have t := inc_inv_mul u
  constructor
  · rintro ⟨x₁, hx₁, a₁, ha₁, e⟩ _ ⟨x₂, hx₂, a₂, ha₂, rfl⟩
    have h1 : hA X x₂ f ∈ OA D := by rw [← cjA_hA]; exact cjA_mem (hg.pair _ hx₂)
    have := add_mem (add_mem (hg.int _ hx₂ _ hx₁) (mul_mem (cjA_mem ha₁) h1))
      (add_mem (mul_mem ha₂ (hg.pair _ hx₁)) (mul_mem (mul_mem ha₂ (cjA_mem ha₁)) hg.norm))
    rw [e, hA_flat h, hA_add_left, hA_add_right, hA_add_right, hA_smul_left, hA_smul_left, hA_smul_right, hA_smul_right,
      RingHom.map_mul, cjA_inc_inv]
    convert this using 1
    linear_combination (-(a₂ * cjA D a₁ * inc D (Tu D u)⁻¹)) * t
  · intro H
    obtain ⟨b, hb, hx⟩ := hg.dual x fun x' hx' => by
      have := H _ ⟨x', hx', 0, zero_mem _, rfl⟩
      rwa [hA_flat h, zero_smul, add_zero, zero_mul, zero_mul, zero_mul, sub_zero] at this
    have h1 := H _ ⟨0, zero_mem_hat, 1, one_mem _, rfl⟩
    rw [hA_flat h, zero_add, one_smul, one_mul] at h1
    have h2 := hg.pair _ hx
    rw [hA_sub_right, hA_smul_right] at h2
    have h3 : cjA D (a - b * inc D (Tu D u)⁻¹) ∈ OA D := by
      have := sub_mem (add_mem h2 (mul_mem (cjA_mem hb) hg.norm)) h1
      rw [RingHom.map_sub, RingHom.map_mul, cjA_inc_inv]
      convert this using 1
      linear_combination (-(cjA D a)) * t
    rw [cjA_mem_iff] at h3
    refine ⟨x - b • f - (a - b * inc D (Tu D u)⁻¹) • inc D (Tu D u) • f, sub_mem_hat hx (smul_mem_hat h3 hg.mul_mem),
      a * inc D (Tu D u), ?_, ?_⟩
    · convert add_mem (mul_mem h3 (inc_Tu_mem u)) hb using 1
      linear_combination b * t
    · congr 2
      · rw [smul_smul, sub_mul, mul_assoc b, t, mul_one, sub_smul]
        abel
      · linear_combination (-a) * t

end Flat

end GlobalTheory.AdIsom

end
