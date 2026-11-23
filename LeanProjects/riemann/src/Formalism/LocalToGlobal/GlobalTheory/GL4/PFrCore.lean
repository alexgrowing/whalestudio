import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (F) in

def vi (x : n → E) : n → 𝒜 := fun i => ιA (x i)

theorem vi_mem_hat {Λ : Submodule (𝓞 E) (n → E)} {x : n → E} (hx : x ∈ Λ) : vi F x ∈ hat F Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem vi_add_smul (x w : n → E) (M : ℕ) : vi F (x + (M : E) • w) = vi F x + (M : 𝒜) • vi F w := by
  funext i
  simp [vi, map_add, map_mul, map_natCast]

theorem vi_smul_int (r : 𝓞 E) (x : n → E) : vi F (r • x) = ιA (algebraMap (𝓞 E) E r) • vi F x := by
  funext i
  simp [vi, Algebra.smul_def, map_mul]

theorem vi_sum {ι : Type} (s : Finset ι) (f : ι → n → E) : vi F (∑ j ∈ s, f j) = ∑ j ∈ s, vi F (f j) := by
  funext i
  simp [vi, map_sum, Finset.sum_apply]

theorem incl_int_mem (r : 𝓞 E) : ιA (algebraMap (𝓞 E) E r) ∈ 𝒮 := by
  have := levelaf_tmul_mem (F := F) (E := E) r (one_mem (intAd F))
  exact this

theorem gmv (G : Matrix n n E) (x : n → E) : (G.map ιA) *ᵥ vi F x = vi F (G *ᵥ x) := by
  funext i
  simp [vi, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem natCast_ne (M : ℕ) (hM : M ≠ 0) : ((M : ℕ) : 𝓞 F) ≠ 0 := by
  intro h
  apply hM
  have := congrArg (algebraMap (𝓞 F) F) h
  simpa using this

theorem levelafC_nat (M : ℕ) : levelafC (F := F) E ((M : ℕ) : 𝓞 F) = (M : 𝒜) := by
  induction M with
  | zero => simp [levelafC]
  | succ k ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    simp [levelafC, TensorProduct.tmul_add, Algebra.TensorProduct.one_def]

theorem approx_hat (M : ℕ) (hM : M ≠ 0) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜)
    (hu : u ∈ hat F Λ) : ∃ x ∈ Λ, ∃ z ∈ hat F Λ, u = vi F x + (M : 𝒜) • z := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, 0, zero_mem _, by rw [smul_zero, add_zero]; rfl⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp [vi]⟩
  | add u w _ _ hu hw =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨x', hx', z', hz', rfl⟩ := hw
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [vi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring
  | smul s u _ hu =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx (F := F) (E := E) csGlob_intAdApprox ((M : ℕ) : 𝓞 F)
      (natCast_ne M hM) (s : 𝒜) s.2
    refine ⟨b • x, Submodule.smul_mem _ b hx,
      (⟨t, ht⟩ : 𝒮) • vi F x + s • z, add_mem (Submodule.smul_mem _ _ (vi_mem_hat hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [levelafC_nat] at hs
    funext i
    have e1 : vi F (b • x) i = ιA (algebraMap (𝓞 E) E b) * ιA (x i) := by simp [vi, Algebra.smul_def, map_mul]
    rw [Pi.add_apply, e1]
    show (s : 𝒜) * (vi F x i + (M : 𝒜) * z i) = _ + (M : 𝒜) * (t * vi F x i + (s : 𝒜) * z i)
    rw [hs]
    simp only [vi]
    ring

theorem hat_fwd (G : Matrix n n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x ∈ Λ, G *ᵥ x ∈ Λ')
    (u : n → 𝒜) (hu : u ∈ hat F Λ) : (G.map ιA) *ᵥ u ∈ hat F Λ' := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    show G.map ιA *ᵥ vi F x ∈ _
    rw [gmv]
    exact vi_mem_hat (h x hx)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mulVec_add]; exact add_mem hu hw
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu

theorem hat_iff (G : GL n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ')
    (u : n → 𝒜) : u ∈ hat F Λ ↔ ((G : Matrix n n E).map ιA) *ᵥ u ∈ hat F Λ' := by
  constructor
  · exact hat_fwd _ (fun x hx => (h x).1 hx) u
  · intro hu
    have h1 : ∀ x ∈ Λ', ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ Λ := by
      intro x hx
      refine (h _).2 ?_
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hx
    have h2 := hat_fwd _ h1 _ hu
    rwa [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at h2

theorem dl_anti (σ : E →ₐ[F] E) (J : Matrix n n E) {A B : Submodule (𝓞 E) (n → E)} (h : A ≤ B) :
    dl σ J B ≤ dl σ J A := fun y hy =>
  (mem_dl σ J A y).2 fun x hx => (mem_dl σ J B y).1 hy x (h hx)

theorem dl_map (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J)
    {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ') :
    ∀ x ∈ dl σ J Λ, (G : Matrix n n E) *ᵥ x ∈ dl σ J Λ' := by
  intro x hx
  rw [mem_dl] at hx ⊢
  intro x' hx'
  have hG' : cT (σ : E →+* E) (G : Matrix n n E) * J * (G : Matrix n n E) = J := hG
  have h1 : ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x' ∈ Λ := by
    refine (h _).2 ?_
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact hx'
  have h2 := hx _ h1
  have h3 : x' = (G : Matrix n n E) *ᵥ (((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x') := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [h3, hform_mulVec, hG']
  exact h2

theorem bc_mem_UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (G : GL n E) (hG : G ∈ UJ (σ : E →+* E) J) :
    bc ιA G ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  have hc : (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (σ : E →+* E) =
      (sigR σ (FiniteAdeleRing (𝓞 F) F)).comp (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
    RingHom.ext fun a => (csDual_sig_incl σ a).symm
  exact base_change_mem_holds _ _ n _ _ ιA hc J G hG

theorem frames_core (σ : E →ₐ[F] E) (J : Matrix n n E) (Lb : Submodule (𝓞 E) (n → E))
    (hLbd : IsLat (dl σ J Lb)) {cls : Type} (Λ : cls → Submodule (𝓞 E) (n → E))
    (hΔ : ∀ c, IsLat (dl σ J (Λ c))) (y : cls → GL n 𝒜)
    (hy : ∀ c, y c ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ c (u : n → 𝒜), u ∈ hat F (Λ c) ↔ (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb)
    (M : ℕ) (hM : M ≠ 0) {m : Type} [Fintype m] (b : m → n → E) (hb : ∀ a, b a ∈ dl σ J Lb)
    (hgen : ∀ x ∈ dl σ J Lb, ∃ r : m → 𝓞 E, ∃ z ∈ dl σ J Lb, x = ∑ a, r a • b a + (M : E) • z) :
    ∃ e : cls → m → n → E, (∀ c a, e c a ∈ dl σ J (Λ c)) ∧
      ∀ c c' (G : GL n E), G ∈ UJ (σ : E →+* E) J →
        (∀ x, x ∈ Λ c ↔ (G : Matrix n n E) *ᵥ x ∈ Λ c') →
        (∀ a, ∃ w ∈ dl σ J (Λ c'), (G : Matrix n n E) *ᵥ e c a - e c' a = (M : E) • w) →
        ∃ k : GL n 𝒜, k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
          (∀ u : n → 𝒜, u ∈ hat F Lb ↔ (k : Matrix n n 𝒜) *ᵥ u ∈ hat F Lb) ∧
          (∀ u ∈ hat F (dl σ J Lb), ∃ z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u - u = (M : 𝒜) • z) ∧
          y c' = bc ιA G * y c * k⁻¹ := by

  have hya : ∀ c (w : n → 𝒜), w ∈ hat F (dl σ J Lb) → ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (dl σ J (Λ c)) := by
    intro c w hw
    have h1 : Λ c ≤ globLat (y c) Lb := fun x hx => (hyl c _).1 (vi_mem_hat hx)
    have h2 : globLat (y c) (dl σ J Lb) ≤ dl σ J (Λ c) :=
      (glob_dl_le σ J Lb (y c) (hy c)).trans (dl_anti σ J h1)
    have h3 : ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ w ∈ hat F (globLat (y c) (dl σ J Lb)) := by
      rw [mem_hat_glob hLbd]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact hw
    exact hat_mono h2 h3

  have hyb : ∀ c (u : n → 𝒜), u ∈ hat F (dl σ J (Λ c)) →
      (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro c u hu
    have h1 : Lb ≤ globLat (y c)⁻¹ (Λ c) := by
      intro x hx
      show ((((y c)⁻¹)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F x ∈ hat F (Λ c)
      rw [inv_inv, hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      exact vi_mem_hat hx
    have h2 : globLat (y c)⁻¹ (dl σ J (Λ c)) ≤ dl σ J Lb :=
      (glob_dl_le σ J (Λ c) _ (inv_mem (hy c))).trans (dl_anti σ J h1)
    have h3 : (((y c)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (globLat (y c)⁻¹ (dl σ J (Λ c))) := by
      rw [mem_hat_glob (hΔ c), inv_inv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hu
    exact hat_mono h2 h3

  have hfr : ∀ c a, ∃ x ∈ dl σ J (Λ c), ∃ z ∈ hat F (dl σ J (Λ c)),
      ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) = vi F x + (M : 𝒜) • z :=
    fun c a => approx_hat M hM _ _ (hya c _ (vi_mem_hat (hb a)))
  choose e he z hz hez using hfr
  refine ⟨e, he, ?_⟩
  intro c c' G hG hGΛ hGe
  set k : GL n 𝒜 := (y c')⁻¹ * bc ιA G * y c with hk
  have hkm : (k : Matrix n n 𝒜) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * (G : Matrix n n E).map ιA *
      ((y c : GL n 𝒜) : Matrix n n 𝒜) := by
    rw [hk, Units.val_mul, Units.val_mul]; rfl
  have hGd := dl_map σ J G hG hGΛ

  have hkd : ∀ u ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ u ∈ hat F (dl σ J Lb) := by
    intro u hu
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hyb c' _ (hat_fwd _ hGd _ (hya c _ hu))

  have hkb : ∀ a, ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (b a) - vi F (b a) = (M : 𝒜) • Z := by
    intro a
    obtain ⟨w, hw, hwe⟩ := hGe a
    have hGe' : (G : Matrix n n E) *ᵥ e c a = e c' a + (M : E) • w := sub_eq_iff_eq_add'.1 hwe
    have key : (G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) -
        ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a) =
        (M : 𝒜) • (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a) := by
      rw [hez c a, hez c' a, mulVec_add, mulVec_smul, gmv, hGe', vi_add_smul]
      simp only [smul_add, smul_sub]
      abel
    refine ⟨(((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (vi F w + (G : Matrix n n E).map ιA *ᵥ z c a - z c' a),
      hyb c' _ (sub_mem (add_mem (vi_mem_hat hw) (hat_fwd _ hGd _ (hz c a))) (hz c' a)), ?_⟩
    have h1 : vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        (((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have h2 : (k : Matrix n n 𝒜) *ᵥ vi F (b a) = (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) := by
      rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have h3 : (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ
        ((G : Matrix n n E).map ιA *ᵥ (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a))) - vi F (b a) =
        (((y c')⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ ((G : Matrix n n E).map ιA *ᵥ
          (((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) - ((y c' : GL n 𝒜) : Matrix n n 𝒜) *ᵥ vi F (b a)) := by
      rw [mulVec_sub, ← h1]
    rw [h2, h3, key, mulVec_smul]
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem (hy c')) (bc_mem_UPts σ J G hG)) (hy c)
  · intro u
    rw [hkm, ← mulVec_mulVec, ← mulVec_mulVec]
    have e1 : u ∈ hat F Lb ↔ ((y c : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F (Λ c) := by
      rw [hyl, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [e1, hat_iff G hGΛ, hyl]
  · intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      show ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z

      have hadd : ∀ x x' : n → E, (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x' - vi F x' = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (x + x') - vi F (x + x') = (M : 𝒜) • Z := by
        rintro x x' ⟨Z, hZ, hZe⟩ ⟨Z', hZ', hZe'⟩
        refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
        have : vi F (x + x') = vi F x + vi F x' := by funext i; simp [vi]
        rw [this, mulVec_add, smul_add, ← hZe, ← hZe']
        abel
      have hzero : ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (0 : n → E) - vi F 0 = (M : 𝒜) • Z :=
        ⟨0, zero_mem _, by
          have : vi F (0 : n → E) = 0 := by funext i; simp [vi]
          rw [this, mulVec_zero, sub_zero, smul_zero]⟩
      have hsmul : ∀ (r : 𝓞 E) (x : n → E),
          (∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F x - vi F x = (M : 𝒜) • Z) →
          ∃ Z ∈ hat F (dl σ J Lb), (k : Matrix n n 𝒜) *ᵥ vi F (r • x) - vi F (r • x) = (M : 𝒜) • Z := by
        rintro r x ⟨Z, hZ, hZe⟩
        refine ⟨(⟨_, incl_int_mem r⟩ : 𝒮) • Z, Submodule.smul_mem _ _ hZ, ?_⟩
        rw [vi_smul_int, mulVec_smul, ← smul_sub, hZe, Subring.smul_def, smul_comm]
      classical
      obtain ⟨r, z0, hz0, rfl⟩ := hgen x hx
      refine hadd _ _ ?_ ?_
      · have : ∀ s : Finset m, ∃ Z ∈ hat F (dl σ J Lb),
            (k : Matrix n n 𝒜) *ᵥ vi F (∑ a ∈ s, r a • b a) - vi F (∑ a ∈ s, r a • b a) = (M : 𝒜) • Z := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hzero
          | insert a s ha ih =>
            rw [Finset.sum_insert ha]
            exact hadd _ _ (hsmul _ _ (hkb a)) ih
        exact this Finset.univ
      · refine ⟨(k : Matrix n n 𝒜) *ᵥ vi F z0 - vi F z0, sub_mem (hkd _ (vi_mem_hat hz0)) (vi_mem_hat hz0), ?_⟩
        have : vi F ((M : E) • z0) = (M : 𝒜) • vi F z0 := by
          have := vi_add_smul (F := F) (0 : n → E) z0 M
          rwa [zero_add, show vi F (0 : n → E) = 0 from by funext i; simp [vi], zero_add] at this
        rw [this, mulVec_smul, smul_sub]
    | zero => exact ⟨0, zero_mem _, by rw [mulVec_zero, sub_zero, smul_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      obtain ⟨Z', hZ', hZe'⟩ := hw
      refine ⟨Z + Z', add_mem hZ hZ', ?_⟩
      rw [mulVec_add, smul_add, ← hZe, ← hZe']
      abel
    | smul s u _ hu =>
      obtain ⟨Z, hZ, hZe⟩ := hu
      refine ⟨s • Z, Submodule.smul_mem _ s hZ, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul, ← smul_sub, hZe, smul_comm]
  · rw [hk]
    group

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
