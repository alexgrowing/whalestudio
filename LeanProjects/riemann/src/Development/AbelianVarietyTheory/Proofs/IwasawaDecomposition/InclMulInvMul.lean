import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.LevPackFrLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Reside

section Grp

theorem kill_or {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {T : ℕ} (hT : T.Prime) (hM : Nat.card M = T)
    (p q : A) (hpq : p * q = (T : A)) : (∀ m : M, p • m = 0) ∨ ∀ m : M, q • m = 0 := by
  haveI : Fact (Nat.card M).Prime := ⟨hM ▸ hT⟩
  haveI : Finite M := Nat.finite_of_card_ne_zero (hM ▸ hT.ne_zero)
  let φ : M →+ M := DistribMulAction.toAddMonoidHom M p
  rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card φ.range with h | h
  · left
    intro m
    have h1 : φ m ∈ φ.range := ⟨m, rfl⟩
    rw [h] at h1
    exact h1
  · right
    intro m
    have h1 : m ∈ φ.range := by rw [h]; trivial
    obtain ⟨m', rfl⟩ := h1
    show q • p • m' = 0
    rw [smul_smul, mul_comm, hpq, Nat.cast_smul_eq_nsmul, ← hM]
    exact card_nsmul_eq_zero'

theorem ker_of_prime {A M N : Type} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] (f : A →+ M) (ψ : A →+ N)
    (hN : (Nat.card N).Prime) (hf : ∃ a, f a ≠ 0) (hle : ∀ x, ψ x = 0 → f x = 0) (x : A) (hx : f x = 0) : ψ x = 0 := by
  by_contra h0
  haveI : Fact (Nat.card N).Prime := ⟨hN⟩
  haveI : Finite N := Nat.finite_of_card_ne_zero hN.ne_zero
  obtain ⟨a, ha⟩ := hf
  have h1 : AddSubgroup.zmultiples (ψ x) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (ψ x)) with h | h
    · exact absurd (AddSubgroup.zmultiples_eq_bot.1 h) h0
    · exact h
  have h2 : ψ a ∈ AddSubgroup.zmultiples (ψ x) := by rw [h1]; trivial
  obtain ⟨k, hk⟩ := h2
  have hk' : k • ψ x = ψ a := hk
  have h3 : ψ (a - k • x) = 0 := by rw [map_sub, map_zsmul, hk', sub_self]
  have h4 := hle _ h3
  rw [map_sub, map_zsmul, hx, smul_zero, sub_zero] at h4
  exact ha h4

theorem stabFun_congr {m A R M M' : Type} [Fintype m] [DecidableEq m] [CommRing A] [CommRing R] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (Λ : Submodule R (m → A)) (f : Λ →ₗ[R] M) (f' : Λ →ₗ[R] M')
    (hk : ∀ x, f x = 0 → f' x = 0) {g : GL m A} (hg : g ∈ stabFun Λ f) : g ∈ stabFun Λ f' := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨h1, fun x => ?_⟩
  have h3 := hk (⟨(g : Matrix m m A) *ᵥ x.1, (h1 x.1).1 x.2⟩ - x) (by rw [map_sub, h2, sub_self])
  rwa [map_sub, sub_eq_zero] at h3

end Grp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

theorem sig_sig (x : Rv) : sigR hc.sig (v.adicCompletion F) (sigR hc.sig (v.adicCompletion F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    have e : ∀ a : E, (hc.sig a) = star a := fun a => by
      simp [Formalism.BasicNotions.CMData.sig, starRingEnd_apply]
    simp [sigR, e]

theorem incl_mul_inv_mul {a : E} (ha : a ≠ 0) (x : Rv) : ιv a * (ιv a⁻¹ * x) = x := by
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

variable (h : BasePi ST π)
include h

theorem mem_dual (z : Fin n → Rv) : z ∈ baseDualV hc n ST v ↔
    (∀ i, i ≠ lastIdx n → z i ∈ 𝒪v) ∧ ιv (star pE) * z (lastIdx n) ∈ 𝒪v := by
  rw [rll_dualV_eq hc n v h, rll_mem_loc_dLat n v _ h.star_ne_zero]

theorem mem_base (z : Fin n → Rv) : z ∈ latS (F := F) (v.adicCompletion F) 𝒪v (baseLb E n ST) ↔
    (∀ i, i ≠ lastIdx n → z i ∈ 𝒪v) ∧ ιv pE⁻¹ * z (lastIdx n) ∈ 𝒪v := by
  have e := rll_mem_loc_dLat n v pE⁻¹ (inv_ne_zero h.coe_ne_zero) z
  rw [← rll_baseLb_eq n h] at e
  exact e

variable {M : Type} [AddCommGroup M] [Module (Formalism.BasicNotions.intV E v) M] (fT : baseDualV hc n ST v →ₗ[Formalism.BasicNotions.intV E v] M)
  (hL : ∀ x : baseDualV hc n ST v, x.1 ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) → fT x = 0)

include hL

theorem fT_last (c : 𝒪v) (hcM : ∀ m : M, c • m = 0) (x : baseDualV hc n ST v) (s : Rv) (hs : ιv (star pE) * s ∈ 𝒪v)
    (e : x.1 (lastIdx n) = c.1 * s) : fT x = 0 := by
  have ht : (Pi.single (lastIdx n) s : Fin n → Rv) ∈ baseDualV hc n ST v := by
    rw [mem_dual hc n v h]
    exact ⟨fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _, by rw [Pi.single_eq_same]; exact hs⟩
  let t : baseDualV hc n ST v := ⟨_, ht⟩
  have hx := (mem_dual hc n v h x.1).1 x.2
  have hy : fT (x - c • t) = 0 := by
    refine hL _ ((mem_base n v h _).2 ⟨fun i hi => ?_, ?_⟩)
    · show x.1 i - c.1 * (Pi.single (lastIdx n) s : Fin n → Rv) i ∈ 𝒪v
      rw [Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact hx.1 i hi
    · show ιv pE⁻¹ * (x.1 (lastIdx n) - c.1 * (Pi.single (lastIdx n) s : Fin n → Rv) (lastIdx n)) ∈ 𝒪v
      rw [Pi.single_eq_same, e, sub_self, mul_zero]
      exact zero_mem _
  have e2 : fT x = fT (x - c • t) + c • fT t := by rw [← map_smul, ← map_add, sub_add_cancel]
  rw [e2, hy, hcM, add_zero]

omit hL in
theorem ex_ne (hne : fT ≠ 0) : ∃ a, fT a ≠ 0 := by
  by_contra H
  push Not at H
  exact hne (LinearMap.ext H)

theorem fT_of_fLoc (hp : ∀ m : M, (⟨ιv pE, rll_incl_int v π⟩ : 𝒪v) • m = 0) (x : baseDualV hc n ST v)
    (hx : fLoc hc n ST v x = 0) : fT x = 0 := by
  rw [rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)] at hx
  refine fT_last hc n v h fT hL ⟨ιv pE, rll_incl_int v π⟩ hp x (ιv (star pE)⁻¹ * (ιv (star pE / pE) * x.1 (lastIdx n))) ?_ ?_
  · rw [incl_mul_inv_mul v h.star_ne_zero]
    exact hx.2
  · show x.1 (lastIdx n) = ιv pE * (ιv (star pE)⁻¹ * (ιv (star pE / pE) * x.1 (lastIdx n)))
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    have e : pE * (star pE)⁻¹ * (star pE / pE) = 1 := by
      have h1 := h.coe_ne_zero
      have h2 := h.star_ne_zero
      field_simp
    rw [e, map_one, one_mul]

theorem fLoc_of_fT (hcard : (Nat.card (fMod hc n ST v)).Prime) (hne : fT ≠ 0)
    (hp : ∀ m : M, (⟨ιv pE, rll_incl_int v π⟩ : 𝒪v) • m = 0) (x : baseDualV hc n ST v)
    (hx : fT x = 0) : fLoc hc n ST v x = 0 :=
  ker_of_prime fT.toAddMonoidHom (fLoc hc n ST v).toAddMonoidHom hcard (ex_ne hc n v h fT hne)
    (fT_of_fLoc hc n v h fT hL hp) x hx

omit hL

def psiC (P : Pl E) : baseDualV hc n ST v →+ kP P :=
  (rll_rho v P).comp (AddMonoidHom.mk' (fun x : baseDualV hc n ST v =>
    (⟨sigR hc.sig (v.adicCompletion F) (ιv (star pE) * x.1 (lastIdx n)), rll_sigV_mem hc v (rll_last_mem hc n v h x)⟩ : 𝒪v))
    (fun a b => Subtype.ext (by
      show sigR hc.sig (v.adicCompletion F) (ιv (star pE) * (a.1 (lastIdx n) + b.1 (lastIdx n))) = _
      rw [mul_add, map_add]
      rfl)))

theorem last_of_psiC {P : Pl E} (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) (x : baseDualV hc n ST v)
    (h0 : psiC hc n v h P x = 0) : x.1 (lastIdx n) ∈ 𝒪v := by
  obtain ⟨w, hw, e⟩ := rll_rho_eq_zero v h huniq _ h0
  have e1 := congrArg (sigR hc.sig (v.adicCompletion F)) e
  have e2 : sigR hc.sig (v.adicCompletion F) (sigR hc.sig (v.adicCompletion F) (ιv (star pE) * x.1 (lastIdx n))) =
      sigR hc.sig (v.adicCompletion F) (ιv pE * w) := e1
  rw [sig_sig, map_mul, rll_sigV_incl] at e2
  have e3 : x.1 (lastIdx n) = sigR hc.sig (v.adicCompletion F) w := by
    have e4 := congrArg (fun y => ιv (star pE)⁻¹ * y) e2
    beta_reduce at e4
    rw [← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h.star_ne_zero, map_one, one_mul, one_mul] at e4
    exact e4
  rw [e3]
  exact rll_sigV_mem hc v hw

include hL

theorem fT_of_last (hq : ∀ m : M, (⟨ιv (star pE), rll_incl_int v (cO E π)⟩ : 𝒪v) • m = 0) (x : baseDualV hc n ST v)
    (hx : x.1 (lastIdx n) ∈ 𝒪v) : fT x = 0 := by
  refine fT_last hc n v h fT hL ⟨ιv (star pE), rll_incl_int v (cO E π)⟩ hq x (ιv (star pE)⁻¹ * x.1 (lastIdx n)) ?_ ?_
  · rw [incl_mul_inv_mul v h.star_ne_zero]
    exact hx
  · exact (incl_mul_inv_mul v h.star_ne_zero _).symm

theorem last_of_fT {P : Pl E} (hcardP : (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (hne : fT ≠ 0) (hq : ∀ m : M, (⟨ιv (star pE), rll_incl_int v (cO E π)⟩ : 𝒪v) • m = 0) (x : baseDualV hc n ST v)
    (hx : fT x = 0) : x.1 (lastIdx n) ∈ 𝒪v :=
  last_of_psiC hc n v h huniq x (ker_of_prime fT.toAddMonoidHom (psiC hc n v h P) hcardP (ex_ne hc n v h fT hne)
    (fun y hy => fT_of_last hc n v h fT hL hq y (last_of_psiC hc n v h huniq y hy)) x hx)

end Loc

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

variable (h : BasePi ST π)
include h

theorem int_of_maps {g : GL (Fin n) Rv}
    (H1 : ∀ z ∈ latS (F := F) (v.adicCompletion F) 𝒪v (baseLb E n ST), (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈
      latS (F := F) (v.adicCompletion F) 𝒪v (baseLb E n ST))
    (H2 : ∀ z ∈ baseDualV hc n ST v, (g : Matrix (Fin n) (Fin n) Rv) *ᵥ z ∈ baseDualV hc n ST v) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) Rv) i j ∈ 𝒪v := by
  by_cases hi : i = lastIdx n
  · subst hi
    have hz : (Pi.single j (ιv pE) : Fin n → Rv) ∈ latS (F := F) (v.adicCompletion F) 𝒪v (baseLb E n ST) := by
      rw [mem_base n v h]
      refine ⟨fun i _ => ?_, ?_⟩
      · by_cases hi : i = j
        · subst hi; rw [Pi.single_eq_same]; exact rll_incl_int v π
        · rw [Pi.single_eq_of_ne hi]; exact zero_mem _
      · by_cases hj : lastIdx n = j
        · subst hj
          rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ h.coe_ne_zero, map_one]; exact one_mem _
        · rw [Pi.single_eq_of_ne hj, mul_zero]; exact zero_mem _
    have h2 := ((mem_base n v h _).1 (H1 _ hz)).2
    rwa [rll_mulVec_single, mul_comm _ (ιv pE), rll_pinv_mul v h] at h2
  · have hz : (Pi.single j 1 : Fin n → Rv) ∈ baseDualV hc n ST v := by
      rw [rll_dualV_eq hc n v h]; exact rll_single_mem_Sh n v h j
    have h2 := ((mem_dual hc n v h _).1 (H2 _ hz)).1 i hi
    rwa [rll_mulVec_single, mul_one] at h2

theorem fLoc_killed (t t' : baseDualV hc n ST v) (e : t'.1 = ιv pE • t.1) : fLoc hc n ST v t' = 0 := by
  have e1 : t' = (⟨ιv pE, rll_incl_int v π⟩ : 𝒪v) • t := Subtype.ext e
  rw [e1, map_smul]
  exact th_fLoc_pi hc n v h _ rfl _

variable {M : Type} [AddCommGroup M] [Module (Formalism.BasicNotions.intV E v) M] (fT : baseDualV hc n ST v →ₗ[Formalism.BasicNotions.intV E v] M)
  (hL : ∀ x : baseDualV hc n ST v, x.1 ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) → fT x = 0)

include hL

theorem row_inv {P : Pl E} (hcardP : (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (hne : fT ≠ 0) (hq : ∀ m : M, (⟨ιv (star pE), rll_incl_int v (cO E π)⟩ : 𝒪v) • m = 0) {g : GL (Fin n) Rv}
    (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (hS : g ∈ stabGL (latS (F := F) (v.adicCompletion F) 𝒪v (baseLb E n ST)))
    (hF : g ∈ stabFun (baseDualV hc n ST v) fT) : rowLocalCondition n π v g⁻¹ := by
  have hFi := Subgroup.inv_mem _ hF
  have hSi := Subgroup.inv_mem _ hS
  refine ⟨int_of_maps hc n v h (fun z hz => (hSi z).1 hz) (fun z hz => (hFi.1 z).1 hz), fun j => ?_⟩
  obtain ⟨hg, hf⟩ := hF
  have hw : (Pi.single (lastIdx n) (ιv (star pE)⁻¹) : Fin n → Rv) ∈ baseDualV hc n ST v := by
    rw [mem_dual hc n v h]
    refine ⟨fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _, ?_⟩
    rw [Pi.single_eq_same, ← map_mul, mul_inv_cancel₀ h.star_ne_zero, map_one]
    exact one_mem _
  let w : baseDualV hc n ST v := ⟨_, hw⟩
  let y : baseDualV hc n ST v := ⟨(g : Matrix (Fin n) (Fin n) Rv) *ᵥ w.1, (hg w.1).1 w.2⟩
  have hy0 : fT (y - w) = 0 := by rw [map_sub, hf w, sub_self]
  have hj : (y - w).1 j ∈ 𝒪v := by
    by_cases hjl : j = lastIdx n
    · subst hjl
      exact last_of_fT hc n v h fT hL hcardP huniq hne hq _ hy0
    · exact ((mem_dual hc n v h _).1 (y - w).2).1 j hjl
  have e0 : (y - w).1 j = ((g : Matrix (Fin n) (Fin n) Rv) j (lastIdx n) - (1 : Matrix (Fin n) (Fin n) Rv) j (lastIdx n)) * ιv (star pE)⁻¹ := by
    show ((g : Matrix (Fin n) (Fin n) Rv) *ᵥ (Pi.single (lastIdx n) (ιv (star pE)⁻¹) : Fin n → Rv)) j -
      (Pi.single (lastIdx n) (ιv (star pE)⁻¹) : Fin n → Rv) j = _
    rw [rll_mulVec_single, _root_.sub_mul]
    congr 1
    by_cases hjl : j = lastIdx n
    · subst hjl
      rw [Pi.single_eq_same, Matrix.one_apply_eq, one_mul]
    · rw [Pi.single_eq_of_ne hjl, Matrix.one_apply_ne hjl, zero_mul]
  set s := (y - w).1 j with hs
  have e1 : (g : Matrix (Fin n) (Fin n) Rv) j (lastIdx n) - (1 : Matrix (Fin n) (Fin n) Rv) j (lastIdx n) = ιv (star pE) * s := by
    rw [e0, mul_comm _ (ιv (star pE)⁻¹), incl_mul_inv_mul v h.star_ne_zero]
  refine ⟨sigR hc.sig (v.adicCompletion F) s, rll_sigV_mem hc v hj, ?_⟩
  have e2 : ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j =
      sigR hc.sig (v.adicCompletion F) ((g : Matrix (Fin n) (Fin n) Rv) j (lastIdx n)) := rll_inv_entry hc n v hU _ _
  have e3 : (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j =
      sigR hc.sig (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) Rv) j (lastIdx n)) := by
    by_cases hjl : j = lastIdx n
    · subst hjl
      rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hjl, Matrix.one_apply_ne (Ne.symm hjl), map_zero]
  rw [e2, e3, ← map_sub, e1, map_mul, rll_sigV_incl, star_star]

theorem fixes_of_row (hq : ∀ m : M, (⟨ιv (star pE), rll_incl_int v (cO E π)⟩ : 𝒪v) • m = 0) {g : GL (Fin n) Rv}
    (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (hg : g ∈ stabGL (baseDualV hc n ST v)) (h1 : rowLocalCondition n π v g) (h2 : rowLocalCondition n π v g⁻¹) :
    g ∈ stabFun (baseDualV hc n ST v) fT := by
  refine ⟨hg, fun x => ?_⟩
  have hx := (mem_dual hc n v h x.1).1 x.2
  have h0 : fT (⟨(g : Matrix (Fin n) (Fin n) Rv) *ᵥ x.1, (hg x.1).1 x.2⟩ - x) = 0 := by
    refine fT_of_last hc n v h fT hL hq _ ?_
    have e : ((g : Matrix (Fin n) (Fin n) Rv) *ᵥ x.1 - x.1) = ((g : Matrix (Fin n) (Fin n) Rv) - 1) *ᵥ x.1 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    show ((g : Matrix (Fin n) (Fin n) Rv) *ᵥ x.1 - x.1) (lastIdx n) ∈ 𝒪v
    rw [e]
    show ∑ j, ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) * x.1 j ∈ 𝒪v
    refine sum_mem fun j _ => ?_
    by_cases hj : j = lastIdx n
    · subst hj
      obtain ⟨s, hs, e1⟩ := h2.2 (lastIdx n)
      have e2 : ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n) =
          sigR hc.sig (v.adicCompletion F) ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n)) := rll_inv_entry hc n v hU _ _
      rw [e2, Matrix.one_apply_eq] at e1
      have e3 := congrArg (sigR hc.sig (v.adicCompletion F)) e1
      rw [map_sub, sig_sig, map_one, map_mul, rll_sigV_incl] at e3
      rw [Matrix.one_apply_eq, e3, mul_right_comm, mul_comm]
      exact mul_mem (rll_sigV_mem hc v hs) hx.2
    · exact mul_mem (sub_mem (h1.1 _ _) (by rw [Matrix.one_apply_ne (Ne.symm hj)]; exact zero_mem _)) (hx.1 j hj)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

omit hL in

theorem stab_eq (hL' : ∀ x : baseDualV hc n ST v, x.1 ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) → fT x = 0)
    {T : ℕ} (hT : T.Prime) (hTπ : π * cO E π = (T : 𝓞 E)) (hM : Nat.card M = T) (hne : fT ≠ 0)
    {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (hcardP : Nat.card (𝓞 E ⧸ P.asIdeal) = T) :
    levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) fT =
      levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  have huniq := h.over_unique hc hP hov
  have hpT : (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := hcardP ▸ hT
  have hfM : (Nat.card (fMod hc n ST v)).Prime := by rw [fMod_card hc n v h hP hov huniq]; exact hpT
  have hpq : (⟨ιv pE, rll_incl_int v π⟩ : 𝒪v) * ⟨ιv (star pE), rll_incl_int v (cO E π)⟩ = (T : 𝒪v) := by
    apply Subtype.ext
    show ιv pE * ιv (star pE) = ((T : 𝒪v) : Rv)
    have e : pE * star pE = (T : E) := by
      have e1 := congrArg (algebraMap (𝓞 E) E) hTπ
      rwa [map_mul, algebraMap_cO, map_natCast] at e1
    rw [← map_mul, e, map_natCast]
    rfl
  rcases kill_or hT hM _ _ hpq with hp | hq
  · ext g
    simp only [Subgroup.mem_inf]
    exact and_congr_right fun _ => ⟨stabFun_congr _ _ _ (fLoc_of_fT hc n v h fT hL' hfM hne hp),
      stabFun_congr _ _ _ (fT_of_fLoc hc n v h fT hL' hp)⟩
  · ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hG, hF⟩
      refine ⟨hG, ?_⟩
      have r2 := row_inv hc n v h fT hL' hpT huniq hne hq hG.1 hG.2 hF
      have r1 := row_inv hc n v h fT hL' hpT huniq hne hq (Subgroup.inv_mem _ hG.1) (Subgroup.inv_mem _ hG.2) (Subgroup.inv_mem _ hF)
      rw [inv_inv] at r1
      exact rll_mem_stabFun hc n v h hG.1 r1 r2
    · rintro ⟨hG, hF⟩
      refine ⟨hG, fixes_of_row hc n v h fT hL' hq hG.1 hF.1 (rll_Row_of_stabFun hc n v h hG.2 hF) ?_⟩
      exact rll_Row_of_stabFun hc n v h (Subgroup.inv_mem _ hG.2) (Subgroup.inv_mem _ hF)

end Stab

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

abbrev dualV (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v)
    (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) J S.Lb))

abbrev subK (S : StepLevel F E σ J T f bad) (Kr : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    Submodule (Formalism.BasicNotions.intV E v) (dualV S v) :=
  (latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) Kr).comap (dualV S v).subtype

structure SwapLaws (S : StepLevel F E σ J T f bad) (Kr : Submodule (𝓞 E) (Fin n → E)) : Prop where
  ne : ∀ v (_ : (T : 𝓞 F) ∈ v.asIdeal), (subK S Kr v).mkQ ≠ 0
  tor : ∀ v (_ : (T : 𝓞 F) ∈ v.asIdeal) x, (subK S Kr v).mkQ ((T : Formalism.BasicNotions.intV E v) • x) = 0
  card : ∀ v (_ : (T : 𝓞 F) ∈ v.asIdeal), Nat.card (dualV S v ⧸ subK S Kr v) = T
  lat : ∀ v (_ : (T : 𝓞 F) ∈ v.asIdeal) (x : dualV S v), x.1 ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) S.Lb →
    (subK S Kr v).mkQ x = 0
  stab : ∀ v (_ : (T : 𝓞 F) ∈ v.asIdeal), S.Uloc v = levelVL σ J v S.Lb ⊓ stabFun _ (subK S Kr v).mkQ

def swap (S : StepLevel F E σ J T f bad) (Kr : Submodule (𝓞 E) (Fin n → E)) (hl : SwapLaws S Kr) :
    StepLevel F E σ J T f bad :=
  { S with
    fM := fun v _ => dualV S v ⧸ subK S Kr v
    fM_acg := fun _ _ => inferInstance
    fM_mod := fun _ _ => inferInstance
    fT := fun v _ => (subK S Kr v).mkQ
    fT_ne := hl.ne
    fT_T := hl.tor
    fM_card := hl.card
    fT_L := hl.lat
    UlocAlt := hl.stab }

theorem swapLaws [StarRing E] (hc : Formalism.BasicNotions.CMData F E) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (hB : BasePi ST π)
    (hT : T.Prime) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (S : StepLevel F E hc.sig J T f bad) (hLb : S.Lb = baseLb E n ST) :
    ∃ hl : SwapLaws S (baseKer E n ST), FunKilled (swap S _ hl) π := by
  subst hJ
  rcases S with ⟨Lb, _, _, _, _, _, Uloc, _, _, _, fM, fT, ne, tor, card, lat, UT, _, _, _, _, _, _⟩
  obtain rfl : Lb = baseLb E n ST := hLb
  refine ⟨⟨fun v h => fLoc_ne hc n v hB ((mem_plUnder_iff_norm hc hST T hTπ v).2 h), fun v _ x => fLoc_natCast_smul_eq_zero_of_dvd hc n v hB T ⟨cO E π, hTπ.symm⟩ x,
    fun v h => ?_, fun v _ x hx => fLoc_L hc n v x hx, fun v h => ?_⟩, fun v h t t' e => ?_⟩
  · obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    exact (fMod_card hc n v hB hP hov (hB.over_unique hc hP hov)).trans (hcard P hP)
  · obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc hST T hTπ v).2 h
    exact (UT v h).trans (stab_eq hc n v hB (fT v h) (lat v h) hT hTπ (card v h) (ne v h) hP hov (hcard P hP))
  · exact fLoc_killed hc n v hB t t' e

end Swap

theorem mem_baseLb {B : Base} {X : PreX B.toPre} (hPr : (B.primes X).Ok) (u : B.Word) (n : ℕ) [NeZero n] (x : Fin n → B.host.E) :
    x ∈ baseLb B.fields.E n ((B.primes X).vT u) ↔ x ∈ baseL B n (X.piT u) := by
  have hB := basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u
  have hn := NeZero.ne n
  rw [rlc_mem_baseLb]
  constructor
  · rintro ⟨r, h1, h2⟩ j
    refine ⟨r j, (h1 j).symm, fun hj => ?_⟩
    have e : j = lastIdx n := Fin.ext (by simp only [lastIdx]; omega)
    rw [e]
    exact (hB.dvd _).1 h2
  · intro h
    choose r h1 h2 using h
    exact ⟨r, fun j => (h1 j).symm, (hB.dvd _).2 (h2 _ (by simp only [lastIdx]; omega))⟩

end GlobalTheory.Mem.Col2.Reside

end

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.charts_funKilled : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K → ∃ K' : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.ReadsK l Z u a i hi chOf K' ∧ ∀ β, FunKilled (K' β).lev (X.piT u) ∧ (K' β).lev.Lb = (K β).lev.Lb ∧ (K' β).lev.Uloc = (K β).lev.Uloc ∧ (K' β).lev.U = (K β).lev.U ∧ (∀ (κ' : (K' β).lev.U) (κ : (K β).lev.U), κ'.1 = κ.1 → (K' β).lev.chi κ' = (K β).lev.chi κ) ∧ (K' β).y = (K β).y ∧ (K' β).stabI = (K β).stabI := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K hK
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, -⟩ := hc i hi
  have hB := basePi_of_ok hX hPr u
  have hLb : ∀ β, (K β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := fun β => by
    obtain ⟨k, hk⟩ := hK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have hlaws := fun β => GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => hPr.vT_norm u P hP) hgr (K β).lev (hLb β)
  choose hl hk using hlaws
  refine ⟨fun β => { K β with lev := GlobalTheory.Mem.Col2.Reside.swap (K β).lev _ (hl β) }, hK, fun β => ⟨hk β, rfl, rfl, rfl, ?_, rfl, rfl⟩⟩
  intro κ' κ e
  exact congrArg _ (Subtype.ext e)
