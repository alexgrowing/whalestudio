import Formalism.LocalToGlobal.Columns.RecLevelLocK

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn resS)
open Formalism.UG Formalism.UG.P

section Fun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

theorem rll_baseLb_le_Ker : baseLb E n ST ≤ baseKer E n ST := by
  refine le_inf (Deco.base_ok (E := E) (n := n) (ST := ST) (SG := ∅)).L_le_Lsh ?_
  exact le_iInf fun P => le_iInf fun _ => le_locP _ _

theorem rll_fLoc_eq_zero (x : baseDualV hc n ST v) :
    fLoc hc n ST v x = 0 ↔ x.1 ∈ Formalism.L2.Herm.locL v (baseKer E n ST) :=
  Submodule.Quotient.mk_eq_zero _

theorem fLoc_L (x : baseDualV hc n ST v)
    (hx : x.1 ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST)) : fLoc hc n ST v x = 0 :=
  (rll_fLoc_eq_zero hc n v x).2 (rll_latS_mono n v (rll_baseLb_le_Ker n) hx)

variable (h : BasePi ST π)
include h

theorem fLoc_natCast_smul_eq_zero_of_dvd (T : ℕ) (hT : π ∣ (T : 𝓞 E)) (x : baseDualV hc n ST v) :
    fLoc hc n ST v ((T : Formalism.BasicNotions.intV E v) • x) = 0 := by
  rw [rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  obtain ⟨q, hq⟩ := hT
  have htv : (((T : Formalism.BasicNotions.intV E v)) : Rv) = ιv pE * ιv (algebraMap (𝓞 E) E q) := by
    rw [← map_mul, ← map_mul, ← hq, map_natCast, map_natCast]
    rfl
  refine ⟨fun i hi => mul_mem (T : Formalism.BasicNotions.intV E v).2 (hx.1 i hi), ?_⟩
  show ιv (star pE / pE) * ((((T : Formalism.BasicNotions.intV E v)) : Rv) * x.1 (lastIdx n)) ∈ 𝒪v
  rw [htv, mul_assoc, rll_cp_mul v h, mul_left_comm]
  exact mul_mem (rll_incl_int v q) hx.2

theorem rll_coprime_v : ∃ a b : 𝓞 E,
    ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) = 1 := by
  obtain ⟨a, b, hab⟩ := h.cop
  refine ⟨a, b, ?_⟩
  rw [← algebraMap_cO, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hab, map_one, map_one]

theorem rll_pv_not_unit {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (s : Rv) (hs : s ∈ 𝒪v) : ιv pE * s ≠ 1 := by
  intro e
  have e1 := rll_IE_incl_mul v pE s
  rw [e] at e1
  have e2 : Formalism.L2.DIV.lc_eps E v =
      Formalism.L2.DIV.oToS F E π * (⟨afsplitIE v s, afsplit_IE_int v _ hs⟩ : Formalism.L2.Herm.intAf F E) := Subtype.ext e1
  have e3 := congrArg (resS F P) e2
  rw [Formalism.L2.DIV.lc_res_eps P v hov, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (h.mem hP),
    zero_mul] at e3
  exact one_ne_zero e3

theorem fLoc_ne (hv : v ∈ plUnder F ST) : fLoc hc n ST v ≠ 0 := by
  intro h0
  obtain ⟨P, hP, hov⟩ := hv
  have hm : (Pi.single (lastIdx n) 1 : Fin n → Rv) ∈ baseDualV hc n ST v := by
    rw [rll_dualV_eq hc n v h]; exact rll_single_mem_Sh n v h _
  have h1 : fLoc hc n ST v ⟨_, hm⟩ = 0 := by rw [h0]; rfl
  rw [rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)] at h1
  have h2 : ιv (star pE / pE) * (Pi.single (lastIdx n) 1 : Fin n → Rv) (lastIdx n) ∈ 𝒪v := h1.2
  rw [Pi.single_eq_same, mul_one] at h2
  obtain ⟨a, b, hab⟩ := rll_coprime_v v h
  have e1 : ιv (star pE) = ιv pE * ιv (star pE / pE) := by
    rw [← map_mul, mul_div_cancel₀ _ h.coe_ne_zero]
  refine rll_pv_not_unit v h hP hov (ιv (algebraMap (𝓞 E) E a) + ιv (algebraMap (𝓞 E) E b) * ιv (star pE / pE))
    (add_mem (rll_incl_int v a) (mul_mem (rll_incl_int v b) h2)) ?_
  rw [← hab]
  conv_rhs => rw [e1]
  ring

end Fun

section Card

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

def rll_rho (P : Pl E) : 𝒪v →+ kP P where
  toFun s := resS F P ⟨afsplitIE v s.1, afsplit_IE_int v _ s.2⟩
  map_zero' := by
    have : (⟨afsplitIE v ((0 : 𝒪v) : Rv), afsplit_IE_int v _ (0 : 𝒪v).2⟩ : Formalism.L2.Herm.intAf F E) = 0 :=
      Subtype.ext (map_zero _)
    rw [this, map_zero]
  map_add' a b := by
    have : (⟨afsplitIE v ((a + b : 𝒪v) : Rv), afsplit_IE_int v _ (a + b).2⟩ : Formalism.L2.Herm.intAf F E) =
        ⟨afsplitIE v a.1, afsplit_IE_int v _ a.2⟩ + ⟨afsplitIE v b.1, afsplit_IE_int v _ b.2⟩ :=
      Subtype.ext (map_add _ _ _)
    rw [this, map_add]

theorem rll_rho_incl_mul (P : Pl E) (r : 𝓞 E) (s : 𝒪v) (hm : ιv (algebraMap (𝓞 E) E r) * s.1 ∈ 𝒪v) :
    rll_rho v P ⟨_, hm⟩ = Ideal.Quotient.mk P.asIdeal r * rll_rho v P s := by
  show resS F P ⟨afsplitIE v (ιv (algebraMap (𝓞 E) E r) * s.1), _⟩ = _
  have : (⟨afsplitIE v (ιv (algebraMap (𝓞 E) E r) * s.1), afsplit_IE_int v _ hm⟩ : Formalism.L2.Herm.intAf F E) =
      Formalism.L2.DIV.oToS F E r * ⟨afsplitIE v s.1, afsplit_IE_int v _ s.2⟩ := Subtype.ext (rll_IE_incl_mul v _ _)
  rw [this, map_mul, Formalism.L2.DIV.resS_oToS]
  rfl

theorem rll_rho_one {P : Pl E} (hov : IsOver v P) : rll_rho v P 1 = 1 :=
  Formalism.L2.DIV.lc_res_eps P v hov

variable (h : BasePi ST π)
include h

theorem rll_rho_eq_zero {P : Pl E} (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) (s : 𝒪v) (hs : rll_rho v P s = 0) :
    ∃ w ∈ 𝒪v, s.1 = ιv pE * w := by
  obtain ⟨u, hu⟩ := rll_idS_inf h (t := (⟨afsplitIE v s.1, afsplit_IE_int v _ s.2⟩ : Formalism.L2.Herm.intAf F E)) (by
    intro Q hQ
    by_cases hQv : IsOver v Q
    · rw [huniq Q hQ hQv]; exact hs
    · refine Formalism.L2.DIV.resS_eq_zero_of_prV Q (Formalism.L2.DIV.underPl F Q) rfl _ ?_
      refine afsplit_prV_IE_ne v _ ?_ _
      rintro rfl; exact hQv rfl)
  refine ⟨prV (E := E) v (u : E ⊗[F] Formalism.L2.Herm.Af F), afsplit_prV_int v _ u.2, ?_⟩
  have e1 := congrArg (fun t : Formalism.L2.Herm.intAf F E => prV (E := E) v (t : E ⊗[F] Formalism.L2.Herm.Af F)) hu
  simp only [MulMemClass.coe_mul, map_mul, afsplit_prV_IE] at e1
  exact e1

theorem rll_last_mem (x : baseDualV hc n ST v) : ιv (star pE) * x.1 (lastIdx n) ∈ 𝒪v := by
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  exact ((rll_mem_loc_dLat n v _ h.star_ne_zero _).1 hx).2

def rll_psi (P : Pl E) : baseDualV hc n ST v →+ kP P where
  toFun x := rll_rho v P ⟨_, rll_last_mem hc n v h x⟩
  map_zero' := by
    have : (⟨_, rll_last_mem hc n v h 0⟩ : 𝒪v) = 0 := Subtype.ext (mul_zero _)
    rw [this, map_zero]
  map_add' a b := by
    have : (⟨_, rll_last_mem hc n v h (a + b)⟩ : 𝒪v) = ⟨_, rll_last_mem hc n v h a⟩ + ⟨_, rll_last_mem hc n v h b⟩ :=
      Subtype.ext (mul_add _ _ _)
    rw [this, map_add]

theorem rll_psi_surj {P : Pl E} (hov : IsOver v P) : Function.Surjective (rll_psi hc n v h P) := by
  intro c
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  have e0 : ιv (star pE) * ιv ((star pE)⁻¹ * algebraMap (𝓞 E) E r) = ιv (algebraMap (𝓞 E) E r) * ((1 : 𝒪v) : Rv) := by
    rw [← map_mul, mul_inv_cancel_left₀ h.star_ne_zero]
    exact (mul_one _).symm
  have hm : (Pi.single (lastIdx n) (ιv ((star pE)⁻¹ * algebraMap (𝓞 E) E r)) : Fin n → Rv) ∈ baseDualV hc n ST v := by
    rw [rll_dualV_eq hc n v h, rll_mem_loc_dLat n v _ h.star_ne_zero]
    refine ⟨fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _, ?_⟩
    rw [Pi.single_eq_same, e0]
    exact mul_mem (rll_incl_int v r) (one_mem _)
  refine ⟨⟨_, hm⟩, ?_⟩
  have e1 : (⟨_, rll_last_mem hc n v h ⟨_, hm⟩⟩ : 𝒪v) =
      ⟨ιv (algebraMap (𝓞 E) E r) * ((1 : 𝒪v) : Rv), mul_mem (rll_incl_int v r) (one_mem _)⟩ := by
    apply Subtype.ext
    show ιv (star pE) * (Pi.single (lastIdx n) (ιv ((star pE)⁻¹ * algebraMap (𝓞 E) E r)) : Fin n → Rv) (lastIdx n) = _
    rw [Pi.single_eq_same, e0]
  show rll_rho v P _ = _
  rw [e1, rll_rho_incl_mul, rll_rho_one v hov, mul_one]

theorem rll_psi_ker {P : Pl E} (hP : P ∈ ST) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) (x : baseDualV hc n ST v) :
    rll_psi hc n v h P x = 0 ↔ x.1 ∈ Formalism.L2.Herm.locL v (baseKer E n ST) := by
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  rw [rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have e0 : ιv (star pE / pE) * x.1 (lastIdx n) = ιv pE⁻¹ * (ιv (star pE) * x.1 (lastIdx n)) := by
    rw [← mul_assoc, ← map_mul, div_eq_inv_mul]
  constructor
  · intro h0
    obtain ⟨w, hw, e⟩ := rll_rho_eq_zero v h huniq _ h0
    refine ⟨hx.1, ?_⟩
    have e' : ιv (star pE) * x.1 (lastIdx n) = ιv pE * w := e
    rw [e0, e', rll_pinv_mul v h]
    exact hw
  · rintro ⟨_, h2⟩
    have e1 : (⟨_, rll_last_mem hc n v h x⟩ : 𝒪v) =
        ⟨ιv pE * ((⟨_, h2⟩ : 𝒪v) : Rv), mul_mem (rll_incl_int v π) h2⟩ := by
      apply Subtype.ext
      show ιv (star pE) * x.1 (lastIdx n) = ιv pE * (ιv (star pE / pE) * x.1 (lastIdx n))
      rw [e0, rll_p_mul_pinv v h]
    show rll_rho v P _ = 0
    rw [e1, rll_rho_incl_mul, Ideal.Quotient.eq_zero_iff_mem.2 (h.mem hP), zero_mul]

theorem fMod_card {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) :
    Nat.card (fMod hc n ST v) = Nat.card (𝓞 E ⧸ P.asIdeal) := by
  set p := (Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
    (baseDualV hc n ST v).subtype with hp
  have e : p.toAddSubgroup = (rll_psi hc n v h P).ker := by
    ext x
    rw [AddMonoidHom.mem_ker, rll_psi_ker hc n v h hP huniq]
    rfl
  calc Nat.card (fMod hc n ST v) = Nat.card (baseDualV hc n ST v ⧸ p.toAddSubgroup) := rfl
    _ = Nat.card (baseDualV hc n ST v ⧸ (rll_psi hc n v h P).ker) := by rw [e]
    _ = _ := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (rll_psi_surj hc n v h hov)).toEquiv

end Card

end Formalism.L2.Col
