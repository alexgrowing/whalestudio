import Formalism.PeriodIntegrals.OrbRestr

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet

theorem orbMap_inj (D : D7) (p : ℕ) (z : Pl D) : Function.Injective (orbMap D p z) := by
  intro s t h
  exact ZMod.val_injective _ (posPl_inj D p z s.val t.val (ZMod.val_lt s) (ZMod.val_lt t) h)

def orbEmb (D : D7) (p : ℕ) (z : Pl D) (β : Type) : ZMod (nP D p) × β ↪ Pl D × β :=
  ⟨fun v => (orbMap D p z v.1, v.2), fun v w h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (orbMap_inj D p z h.1) h.2⟩

theorem orbEmb_apply (D : D7) (p : ℕ) (z : Pl D) (β : Type) (v : ZMod (nP D p) × β) :
    orbEmb D p z β v = (orbMap D p z v.1, v.2) := rfl

theorem restr_eq_killCompl (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    restr D p z Th = killCompl (orbEmb D p z (Fin N0 × Fin N1)) Th := by
  funext m
  show _ = killComplFun (orbEmb D p z (Fin N0 × Fin N1)) Th m
  unfold restr killComplFun
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

theorem natCast_val_add_mul (n : ℕ) [NeZero n] (s : ZMod n) (e : ℕ) :
    ((s.val + e * (n - 1) : ℕ) : ZMod n) = s - e := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn, ZMod.natCast_self, Nat.cast_one,
    ZMod.natCast_zmod_val]
  ring

theorem posPl_eq_orbMap (D : D7) (p : ℕ) (z : Pl D) (k : ℕ) :
    posPl D p z k = orbMap D p z (k : ZMod (nP D p)) := by
  show posPl D p z k = posPl D p z ((k : ZMod (nP D p)).val)
  rw [ZMod.val_natCast, posPl_mod]

theorem backPl_orbMap (D : D7) (p : ℕ) (z : Pl D) (s : ZMod (nP D p)) (e : ℕ) :
    backPl D p (orbMap D p z s) e = orbMap D p z (s - e) := by
  have h := posPl_eq_orbMap D p z (s.val + e * (nP D p - 1))
  rw [natCast_val_add_mul] at h
  show posPl D p (posPl D p z s.val) (e * (nP D p - 1)) = orbMap D p z (s - e)
  rw [posPl_add]
  exact h

theorem orbit_of_backPl (D : D7) (p : ℕ) (z y : Pl D) (s : ZMod (nP D p)) (e : ℕ)
    (h : backPl D p y e = orbMap D p z s) : ∃ s', orbMap D p z s' = y := by
  refine ⟨s + e, ?_⟩
  have h3 : e * (nP D p - 1) + e = e * nP D p := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne (nP D p))
    rw [hk, Nat.succ_sub_one, Nat.mul_succ]
  have h1 : posPl D p (backPl D p y e) e = y := by
    unfold backPl
    rw [posPl_add, h3, ← posPl_mod, Nat.mul_mod_left, posPl_zero]
  have h2 : posPl D p (orbMap D p z s) e = orbMap D p z (s + e) := by
    show posPl D p (posPl D p z s.val) e = _
    rw [posPl_add, posPl_eq_orbMap]
    congr 1
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  calc orbMap D p z (s + e) = posPl D p (orbMap D p z s) e := h2.symm
    _ = posPl D p (backPl D p y e) e := by rw [h]
    _ = y := h1

theorem JetTdeg_embDomain {σ τ : Type*} (f : σ ↪ τ) (m : σ →₀ ℕ) : JetTdeg (embDomain f m) = JetTdeg m := by
  unfold JetTdeg
  rw [Finsupp.sum_embDomain]

theorem killCompl_logPl_emb (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (z : Pl D) (w : ZMod (nP D p) × β) :
    killCompl (orbEmb D p z β) (logPl D p (orbEmb D p z β w)) = jetLogG p (nP D p) w := by
  have key : ∀ e : ℕ, ((backPl D p (orbEmb D p z β w).1 (2 * e), (orbEmb D p z β w).2) : Pl D × β)
      = orbEmb D p z β (w.1 - 2 * (e : ZMod (nP D p)), w.2) := by
    intro e
    rw [orbEmb_apply, orbEmb_apply]
    simp only [backPl_orbMap, Nat.cast_mul, Nat.cast_ofNat]
  funext m
  show killComplFun (orbEmb D p z β) (logPl D p (orbEmb D p z β w)) m = jetLogG p (nP D p) w m
  unfold killComplFun
  show logPl D p (orbEmb D p z β w) (embDomain (orbEmb D p z β) m) = jetLogG p (nP D p) w m
  simp only [logPl, jetLogG, JetTdeg_embDomain]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hm : m = Finsupp.single (w.1 - 2 * (e : ZMod (nP D p)), w.2) ((p ^ 2) ^ e)
  · rw [if_pos hm, if_pos]
    rw [key e, hm, Finsupp.embDomain_single]
  · rw [if_neg hm, if_neg]
    intro h'
    apply hm
    rw [key e, ← Finsupp.embDomain_single] at h'
    exact Finsupp.embDomain_injective _ h'

theorem killCompl_logPl_off (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (z : Pl D) (v : Pl D × β)
    (hv : ¬ ∃ w, orbEmb D p z β w = v) : killCompl (orbEmb D p z β) (logPl D p v) = 0 := by
  funext m
  show killComplFun (orbEmb D p z β) (logPl D p v) m = 0
  unfold killComplFun
  show logPl D p v (embDomain (orbEmb D p z β) m) = 0
  simp only [logPl]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [if_neg]
  intro h'
  apply hv
  have hk : (p ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hmem : (backPl D p v.1 (2 * e), v.2) ∈ (embDomain (orbEmb D p z β) m).support := by
    rw [h', Finsupp.support_single_ne_zero _ hk]
    exact Finset.mem_singleton_self _
  rw [Finsupp.support_embDomain] at hmem
  obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hmem
  rw [orbEmb_apply] at ha
  obtain ⟨s', hs'⟩ := orbit_of_backPl D p z v.1 a.1 (2 * e) (Prod.ext_iff.mp ha).1.symm
  exact ⟨(s', v.2), by rw [orbEmb_apply]; exact Prod.ext hs' rfl⟩

end PI.OrbJet.OrbW
