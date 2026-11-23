import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def FilA (a : ℤ) : AddSubgroup P.R.BdR := ((P.PD (botExt l)).Fil a).toAddSubgroup

theorem mem_Fil_iff (K : FinExt l) {a : ℤ} {x : P.R.BdR} : x ∈ Fil P a ↔ x ∈ (P.PD K).Fil a := by
  have := P.PD_Fil (botExt l) K a
  change x ∈ ((P.PD (botExt l)).Fil a : Set P.R.BdR) ↔ x ∈ ((P.PD K).Fil a : Set P.R.BdR)
  rw [this]

variable {P}

theorem Fil_zero_mem (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := (FilA P a).zero_mem
theorem Fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a := (FilA P a).add_mem hx hy
theorem Fil_neg {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : -x ∈ Fil P a := (FilA P a).neg_mem hx
theorem Fil_sum {a : ℤ} {ι : Type*} {s : Finset ι} {f : ι → P.R.BdR} (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a := (FilA P a).sum_mem h
theorem Fil_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy
theorem Fil_mul_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P 0) (hy : y ∈ Fil P a) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem Fil_mul_right {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P 0) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem one_mem_Fil : (1 : P.R.BdR) ∈ Fil P 0 := (P.PD (botExt l)).one_mem
theorem Fil_act (g : GQ l) {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at this

variable (P)

def S0 : Subring P.R.BdR where
  carrier := Fil P 0
  zero_mem' := Fil_zero_mem 0
  one_mem' := one_mem_Fil
  add_mem' := Fil_add
  neg_mem' := Fil_neg
  mul_mem' := Fil_mul_left

theorem mem_S0_of_sum_eq {x : P.R.BdR} : x ∈ S0 P ↔ x ∈ Fil P 0 := Iff.rfl

theorem om_mem_Fil (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  rw [mem_Fil_iff P (adjExt x)]
  have h := ((P.PD (adjExt x)).Fil 0).smul_mem ⟨x, mem_adjExt x⟩ (P.PD (adjExt x)).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact h

theorem kd_mem_Fil (c : ↥(MaximalUnramifiedExtension l)) : kd P c ∈ Fil P 0 := om_mem_Fil P _

theorem q_mem_Fil (q : ℚ_[l]) : algebraMap ℚ_[l] P.R.BdR q ∈ Fil P 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
  exact om_mem_Fil P _

theorem iota_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem iota_act (g : GQ l) (b : P.R.B) : P.ιB (P.actQ g b) = P.actQdR g (P.ιB b) := by
  have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_ι, P.PD_ι, P.PD_actdR] at this

theorem iota_kur (c : ↥(MaximalUnramifiedExtension l)) : P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P c := by
  have := (P.PD (adjExt (c : Om l))).ι.commutes ⟨c, mem_adjExt _, c.2⟩
  rw [P.PD_ι] at this
  exact this

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := rfl
theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  simp [fr, pow_add, AlgHom.mul_apply]
theorem fr_one (c : ↥(MaximalUnramifiedExtension l)) : fr l 1 c = frobUr l c := by simp [fr]
theorem fr_q (m : ℕ) (q : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q :=
  (frobUr l ^ m).commutes q
theorem fr_comm {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l r (fr l m c) = fr l m c := by
  rw [← fr_add, add_comm, fr_add, h]
theorem fr_mul {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (k : ℕ) : fr l (r * k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, fr_add, h, ih]
theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l (m % r) c = fr l m c := by
  conv_rhs => rw [← Nat.mod_add_div m r, fr_add, fr_mul h]

theorem phi_iter_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, phiB_algebraMap, add_comm, fr_add, fr_one]

def evHom (m : ℕ) : P.R.B →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp ((P.φB ^ m : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)

theorem evHom_apply (m : ℕ) (b : P.R.B) : evHom P m b = ev P m b := by
  simp [evHom, ev, AlgHom.coe_pow]

theorem ev_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P (fr l m c) := by
  rw [ev, phi_iter_kur, iota_kur]

theorem ev_act (m : ℕ) (g : GQ l) (b : P.R.B) : ev P m (P.actQ g b) = P.actQdR g (ev P m b) := by
  rw [ev, ev, ← iota_act]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

theorem act_kd {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQdR (g : GQ l) (kd P c) = kd P c := by
  change P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
  rw [P.actQdR_Om, mem_GK.1 g.2 _ hc]

theorem act_kur {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c :=
  P.actQ_Kur _ c c (mem_GK.1 g.2 _ hc)

theorem act_ks {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    actSt P (g : GQ l) (ks P c) = ks P c := by
  change actSt P (g : GQ l) (Polynomial.C _) = Polynomial.C _
  rw [actSt_C, act_kur P g hc]

theorem tz_add (a b : ℤ) : tz P (a + b) = tz P a * tz P b := by simp [tz, zpow_add]
theorem tz_zero : tz P 0 = 1 := by simp [tz]
theorem tz_one : tz P 1 = P.ιB P.tB := by simp [tz]

theorem fund {b : P.R.B} (h : P.φB b = b) (h0 : P.ιB b ∈ Fil P 0) : ∃ c : ℚ_[l], algebraMap ℚ_[l] P.R.B c = b :=
  (P.PD (botExt l)).fund b (by rw [P.PD_φ, h]) (by rw [P.PD_ι]; exact h0)

def resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) :
    ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) := ρ.comp (Subgroup.inclusion (GK_le hK))

theorem IsRat.resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1) {r : ℕ}
    {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) : IsRat r (resK hK ρ) where
  pos := h.pos
  le := fun c hc => hK (h.le c hc)
  rat := fun g => h.rat _
  cont := fun i j => (h.cont i j).comp (continuous_induced_rng.2 continuous_subtype_val)

theorem AdmDR.resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : AdmDR P ρ) : AdmDR P (resK hK ρ) := fun m =>
  (h m).imp fun _ hQ g => hQ ⟨g, GK_le hK g.2⟩

end GlobalTheory.PMon

end
