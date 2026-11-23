import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP)

namespace GlobalTheory.AdIsom.BaseVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem local_dual {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (O : Subring A) (σ : A →+* A)
    (hσσ : ∀ a, σ (σ a) = a) (hσ : ∀ a ∈ O, σ a ∈ O) (h : M → M → A)
    (hsl : ∀ a x y, h (a • x) y = a * h x y) (hsr : ∀ a x y, h x (a • y) = σ a * h x y)
    (hsub : ∀ x y y', h x (y - y') = h x y - h x y') (hc : ∀ x y, σ (h x y) = h y x) (N : Set M)
    (hbi : ∀ x, (∀ y, (∀ x' ∈ N, h x' y ∈ O) → h y x ∈ O) → x ∈ N)
    {e T Ti : A} (he : e ∈ O) (hee : e * e = e) (hT : T ∈ O) (hσT : σ T = T) (hTi : T * Ti = 1)
    (hu : ∀ a ∈ O, e * (Ti * a) ∉ O → ∃ b ∈ O, b * a = e) {f : M} (hf : e • f = f) (hTf : T • f ∈ N) (hfN : f ∉ N)
    (hN : ∀ y, σ e • y = y → (∀ x ∈ N, h x y ∈ O) → h f y ∈ O → y ∈ N) :
    ∃ g, σ e • g = g ∧ T • g ∈ N ∧ (∀ x ∈ N, h x g ∈ O) ∧ h f g = e * Ti ∧
      (∀ y, (∀ x ∈ N, h x y ∈ O) → ∃ a ∈ O, e • y - a • f ∈ N) ∧
      ∀ y, (∀ x ∈ N, h x y ∈ O) → ∃ a ∈ O, σ e • y - a • g ∈ N := by
  obtain ⟨y0, hy0d, hy0f⟩ : ∃ y, (∀ x' ∈ N, h x' y ∈ O) ∧ h y f ∉ O := by
    by_contra hne
    push Not at hne
    exact hfN (hbi f hne)
  have ha0O : h f y0 ∉ O := fun h' => hy0f (by rw [← hc]; exact hσ _ h')
  have hea0 : e * h f y0 = h f y0 := by rw [← hsl, hf]
  have hTa0 : T * h f y0 ∈ O := by rw [← hsl]; exact hy0d _ hTf
  have hTTi : Ti * T = 1 := by rw [mul_comm]; exact hTi
  obtain ⟨b, hb, hba⟩ := hu (T * h f y0) hTa0 (by rw [← mul_assoc Ti, hTTi, one_mul, hea0]; exact ha0O)
  have hσee : σ e * σ e = σ e := by rw [← map_mul, hee]
  have hxg : ∀ x, h x (σ (b * e) • y0) = b * e * h x y0 := fun x => by rw [hsr, hσσ]
  have hσeg : σ e • σ (b * e) • y0 = σ (b * e) • y0 := by
    rw [smul_smul, ← map_mul, show e * (b * e) = b * e by rw [mul_left_comm, hee]]
  have hgd : ∀ x ∈ N, h x (σ (b * e) • y0) ∈ O := fun x hx => by
    rw [hxg]; exact O.mul_mem (O.mul_mem hb he) (hy0d x hx)
  have hfg : h f (σ (b * e) • y0) = e * Ti := by
    rw [hxg]; linear_combination Ti * hba - b * h f y0 * hTi + b * hea0
  have hTg : T • σ (b * e) • y0 ∈ N := by
    apply hN
    · rw [smul_comm (σ e) T, hσeg]
    · intro x hx; rw [hsr, hσT]; exact O.mul_mem hT (hgd x hx)
    · rw [hsr, hσT, hfg, show T * (e * Ti) = e by linear_combination e * hTi]; exact he
  have hsix : ∀ y, (∀ x ∈ N, h x y ∈ O) →
      σ e • y - σ (T * h f y) • σ (b * e) • y0 ∈ N := by
    intro y hy
    have hTfy : T * h f y ∈ O := by rw [← hsl]; exact hy _ hTf
    apply hN
    · rw [smul_sub, smul_smul, hσee, smul_comm (σ e) _ (σ (b * e) • y0), hσeg]
    · intro x hx
      rw [hsub, hsr, hsr, hσσ, hσσ]
      exact O.sub_mem (O.mul_mem he (hy x hx)) (O.mul_mem hTfy (hgd x hx))
    · rw [hsub, hsr, hsr, hσσ, hσσ, hfg]
      rw [show e * h f y - T * h f y * (e * Ti) = 0 by linear_combination (-(e * h f y)) * hTi]
      exact O.zero_mem
  refine ⟨σ (b * e) • y0, hσeg, hTg, hgd, hfg, ?_, ?_⟩
  · intro y hy
    have hTgy : T * h (σ (b * e) • y0) y ∈ O := by rw [← hsl]; exact hy _ hTg
    refine ⟨σ (T * h (σ (b * e) • y0) y), hσ _ hTgy, hbi _ ?_⟩
    intro y' hy'
    have e1 : h y' (e • y - σ (T * h (σ (b * e) • y0) y) • f) =
        σ e * h y' y - T * h (σ (b * e) • y0) y * h y' f := by
      simp only [hsub, hsr, hσσ]
    have e2 : h (σ e • y' - σ (T * h f y') • σ (b * e) • y0) y =
        σ e * h y' y - T * h y' f * h (σ (b * e) • y0) y := by
      rw [← hc y (σ e • y' - σ (T * h f y') • σ (b * e) • y0)]
      simp only [hsub, hsr, hsl, hσσ, map_sub, map_mul, hσT, hc]
      try ring
    rw [e1, show σ e * h y' y - T * h (σ (b * e) • y0) y * h y' f =
        σ e * h y' y - T * h y' f * h (σ (b * e) • y0) y by ring, ← e2]
    exact hy _ (hsix y' hy')
  · intro y hy
    refine ⟨σ (T * h f y), hσ _ ?_, hsix y hy⟩
    rw [← hsl]; exact hy _ hTf

variable {D : D7}

theorem finite_over (u : D.what₂.Word) :
    {Q : Pl D.host.E | (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal}.Finite := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) = 0
  · convert Set.finite_empty
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro _
    exact T_notMem_sq u Q (by rw [hT]; exact Ideal.zero_mem _)
  · refine (Ideal.finite_factors (I := Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}) ?_).subset ?_
    · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · intro Q hQ
      exact Ideal.dvd_span_singleton.mpr hQ

theorem idem_mul_hA (X : HSp D) (Q : Pl D.host.E) (x y : Fin X.rank → EAf D) :
    idem Q * hA X x y = hA X x (idem (cP Q) • y) := by
  rw [hA_smul_right, ← cjA_idem, cjA_cjA]

theorem inCmp_idem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (Q : Pl D.host.E) {y : Fin n → EAf D}
    (hy : y ∈ hat Λ) : InCmp (idem Q) Λ (idem Q • y) := ⟨smul_mem_hat (idem_mem Q) hy, by rw [smul_smul, idem_mul_self]⟩

private theorem idem_smul_sum_eq_ite {D : D7} {M : Type*} [AddCommGroup M] [Module (EAf D) M] [DecidableEq (Pl D.host.E)]
    (s : Finset (Pl D.host.E)) (p q : Pl D.host.E → M) (hp : ∀ w ∈ s, idem w • p w = p w)
    (hq : ∀ w ∈ s, idem (cP w) • q w = q w) (v : Pl D.host.E) :
    idem v • ∑ w ∈ s, (p w + q w) = (if v ∈ s then p v else 0) + (if cP v ∈ s then q (cP v) else 0) := by
  rw [Finset.smul_sum]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun w => if w = v then p w else 0), Finset.sum_ite_eq']
    intro w hw
    split_ifs with h
    · subst h; exact hp w hw
    · rw [← hp w hw, smul_smul, idem_mul_ne (fun e => h e.symm), zero_smul]
  · rw [Finset.sum_congr rfl (g := fun w => if w = cP v then q w else 0), Finset.sum_ite_eq']
    intro w hw
    split_ifs with h
    · rw [show v = cP w by rw [h, cP_cP]]; exact hq w hw
    · rw [← hq w hw, smul_smul, idem_mul_ne (fun e => h (by rw [e, cP_cP])), zero_smul]

set_option maxHeartbeats 800000 in

theorem exists_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f₀ : Pl D.host.E → Fin X.rank → EAf D) (H : IsBasePair X u π L₀ f₀) :
    ∃ f, IsGlueVec X u L₀ f ∧ ∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f = f₀ w := by
  classical
  have hTO : inc D (Tu D u) ∈ OA D :=
    (inc_mem_iff _).mpr ⟨(((D.mem u).A.T : ℕ) : 𝓞 D.host.E), by simp [Tu]⟩
  have hσT : cjA D (inc D (Tu D u)) = inc D (Tu D u) := by rw [cjA_inc]; simp [Tu]
  have hσTi : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by rw [cjA_inc]; simp [Tu]
  have hTTi : inc D (Tu D u) * inc D (Tu D u)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (Tu_ne_zero u), map_one]
  have hA0' : ∀ x, hA X x 0 = 0 := fun x => by simpa using hA_smul_right X 0 x 0
  have HB := fun w (hw : π ∈ w.asIdeal) => H.2.2 w (idem w) (isPlIdem_idem w) hw
  have hloc : ∀ w : Pl D.host.E, π ∈ w.asIdeal → ∃ g, cjA D (idem w) • g = g ∧
      inc D (Tu D u) • g ∈ hat L₀ ∧ (∀ x ∈ hat L₀, hA X x g ∈ OA D) ∧
      hA X (f₀ w) g = idem w * inc D (Tu D u)⁻¹ ∧
      (∀ y, (∀ x ∈ hat L₀, hA X x y ∈ OA D) → ∃ a ∈ OA D, idem w • y - a • f₀ w ∈ hat L₀) ∧
      ∀ y, (∀ x ∈ hat L₀, hA X x y ∈ OA D) → ∃ a ∈ OA D, cjA D (idem w) • y - a • g ∈ hat L₀ := by
    intro w hw
    obtain ⟨hf, hTf, hfN, hiff⟩ := HB w hw
    exact local_dual (OA D) (cjA D) cjA_cjA (fun a ha => cjA_mem ha) (hA X) (hA_smul_left X)
      (hA_smul_right X) (hA_sub_right X) (cjA_hA X) (hat L₀) (fun x hx => mem_hat_of_bidual H.1 hx)
      (idem_mem w) (idem_mul_self w) hTO hσT hTTi (fun a ha h => exists_mul_eq_idem u w ha h) hf hTf hfN
      (fun y h1 h2 h3 => ((hiff y).mpr ⟨h1, fun x hx => h2 x hx.1, h3⟩).1)
  choose! g hg using hloc
  have hSf : {w : Pl D.host.E | π ∈ w.asIdeal}.Finite :=
    (finite_over u).subset (fun w hw => (T_mem_iff hπ w).mpr (Or.inl hw))
  have hmem : ∀ w, w ∈ hSf.toFinset ↔ π ∈ w.asIdeal := fun w => by
    rw [Set.Finite.mem_toFinset]; exact Iff.rfl
  have hgw : ∀ w, π ∈ w.asIdeal → idem (cP w) • g w = g w := fun w hw => by
    rw [← cjA_idem]; exact (hg w hw).1
  have hcomp := fun v => idem_smul_sum_eq_ite hSf.toFinset f₀ g (fun w hw => (HB w ((hmem w).mp hw)).1)
    (fun w hw => hgw w ((hmem w).mp hw)) v
  have hnot : ∀ v, π ∈ (cP v).asIdeal → π ∉ v.asIdeal := fun v h => by
    have := pi_notMem_cP hπ h
    rwa [cP_cP] at this
  have compS : ∀ v, π ∈ v.asIdeal → idem v • ∑ w ∈ hSf.toFinset, (f₀ w + g w) = f₀ v := fun v hv => by
    rw [hcomp, if_pos ((hmem v).mpr hv), if_neg (fun h => pi_notMem_cP hπ hv ((hmem _).mp h)), add_zero]
  have compC : ∀ v, π ∈ (cP v).asIdeal → idem v • ∑ w ∈ hSf.toFinset, (f₀ w + g w) = g (cP v) :=
    fun v hv => by
      rw [hcomp, if_neg (fun h => hnot v hv ((hmem v).mp h)), if_pos ((hmem _).mpr hv), zero_add]
  have comp0 : ∀ v, π ∉ v.asIdeal → π ∉ (cP v).asIdeal →
      idem v • ∑ w ∈ hSf.toFinset, (f₀ w + g w) = 0 := fun v h1 h2 => by
    rw [hcomp, if_neg (fun h => h1 ((hmem v).mp h)), if_neg (fun h => h2 ((hmem _).mp h)), add_zero]
  refine ⟨∑ w ∈ hSf.toFinset, (f₀ w + g w), ⟨?_, ?_, ?_, ?_, ?_⟩, compS⟩
  · rw [Finset.smul_sum]
    exact Finset.sum_induction _ (· ∈ hat L₀) (fun _ _ => add_mem_hat) zero_mem_hat
      (fun w hw => by
        rw [smul_add]
        exact add_mem_hat (HB w ((hmem w).mp hw)).2.1 (hg w ((hmem w).mp hw)).2.1)
  · intro x hx y hy
    rw [mem_OA_iff_idem]
    intro v
    rw [idem_mul_hA]
    by_cases h1 : π ∈ (cP v).asIdeal
    · obtain ⟨-, -, -, hiff⟩ := HB (cP v) h1
      have hx' : InCmp (cjA D (idem (cP v))) L₀ (cjA D (idem (cP v)) • x) := by
        rw [cjA_idem]; exact inCmp_idem _ hx
      have key := ((hiff _).mp hx').2.1 (idem (cP v) • y) (inCmp_idem _ hy)
      have e1 : hA X x (idem (cP v) • y) =
          cjA D (hA X (idem (cP v) • y) (cjA D (idem (cP v)) • x)) := by
        rw [cjA_hA, hA_smul_left, hA_smul_right, ← mul_assoc, ← map_mul, idem_mul_self]
      rw [e1]; exact cjA_mem key
    · by_cases h2 : π ∈ v.asIdeal
      · obtain ⟨-, -, -, hiff⟩ := HB v h2
        have hy' : InCmp (cjA D (idem v)) L₀ (cjA D (idem v) • y) := by
          rw [cjA_idem]; exact inCmp_idem _ hy
        have key := ((hiff _).mp hy').2.1 (idem v • x) (inCmp_idem _ hx)
        rw [← cjA_idem]
        have e1 : hA X x (cjA D (idem v) • y) = hA X (idem v • x) (cjA D (idem v) • y) := by
          rw [hA_smul_left, hA_smul_right, cjA_cjA, ← mul_assoc, idem_mul_self]
        rw [e1]; exact key
      · have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ (cP v).asIdeal := by
          rw [T_mem_iff hπ, cP_cP]; tauto
        have hloc := (H.2.1 (cP v) (idem (cP v)) (isPlIdem_idem _) hT (idem (cP v) • y)).mp
          (inCmp_idem _ hy)
        exact (mem_hat_dualL_iff H.1 _).mp hloc.1 x hx
  · intro y hy
    rw [mem_OA_iff_idem]
    intro v
    rw [← hA_smul_left]
    by_cases h1 : π ∈ v.asIdeal
    · rw [compS v h1]
      obtain ⟨hf, -, -, hiff⟩ := HB v h1
      have hy' : InCmp (cjA D (idem v)) L₀ (cjA D (idem v) • y) := by
        rw [cjA_idem]; exact inCmp_idem _ hy
      have key := ((hiff _).mp hy').2.2
      rwa [hA_smul_right, cjA_cjA, ← hA_smul_left, hf] at key
    · by_cases h2 : π ∈ (cP v).asIdeal
      · rw [compC v h2, ← cjA_hA]; exact cjA_mem ((hg (cP v) h2).2.2.1 y hy)
      · rw [comp0 v h1 h2, show hA X 0 y = 0 by simpa using hA_smul_left X 0 0 y]
        exact (OA D).zero_mem
  · rw [mem_OA_iff_idem]
    intro v
    rw [mul_sub, idem_mul_hA]
    by_cases h1 : π ∈ v.asIdeal
    · rw [compC (cP v) (by rwa [cP_cP]), cP_cP]
      rw [← (hg v h1).1, hA_smul_right, cjA_cjA, ← hA_smul_left, compS v h1, (hg v h1).2.2.2.1, sub_self]
      exact (OA D).zero_mem
    · by_cases h2 : π ∈ (cP v).asIdeal
      · rw [compS (cP v) h2]
        obtain ⟨hf, -⟩ := HB (cP v) h2
        rw [← hf, hA_smul_right, ← hA_smul_left, cjA_idem, cP_cP, compC v h2, ← cjA_hA,
          (hg (cP v) h2).2.2.2.1, map_mul, cjA_idem, cP_cP, hσTi, sub_self]
        exact (OA D).zero_mem
      · rw [comp0 (cP v) h2 (by rwa [cP_cP]), hA0', zero_sub]
        apply neg_mem
        exact (idem_mul_inv_mem_iff u v).mpr (by rw [T_mem_iff hπ]; tauto)
  · intro y hy
    have h5 : ∀ w, π ∈ w.asIdeal → ∃ a ∈ OA D, idem w • y - a • f₀ w ∈ hat L₀ :=
      fun w hw => (hg w hw).2.2.2.2.1 y hy
    have h6 : ∀ w, π ∈ w.asIdeal → ∃ a ∈ OA D, cjA D (idem w) • y - a • g w ∈ hat L₀ :=
      fun w hw => (hg w hw).2.2.2.2.2 y hy
    choose! a1 ha1 hy1 using h5
    choose! a2 ha2 hy2 using h6
    have hca := fun v => idem_smul_sum_eq_ite hSf.toFinset (fun w => idem w * a1 w) (fun w => idem (cP w) * a2 w)
      (fun w _ => by rw [smul_eq_mul, ← mul_assoc, idem_mul_self])
      (fun w _ => by rw [smul_eq_mul, ← mul_assoc, idem_mul_self]) v
    simp only [smul_eq_mul] at hca
    refine ⟨∑ w ∈ hSf.toFinset, (idem w * a1 w + idem (cP w) * a2 w), ?_, ?_⟩
    · exact Subring.sum_mem _ (fun w hw => add_mem (mul_mem (idem_mem w) (ha1 w ((hmem w).mp hw)))
        (mul_mem (idem_mem _) (ha2 w ((hmem w).mp hw))))
    · refine mem_hat_of_idem H.1.fg (fun v => ?_)
      rw [smul_sub, smul_comm (idem v)]
      by_cases h1 : π ∈ v.asIdeal
      · rw [compS v h1]
        obtain ⟨hf, -⟩ := HB v h1
        have e1 : (∑ w ∈ hSf.toFinset, (idem w * a1 w + idem (cP w) * a2 w)) • f₀ v = a1 v • f₀ v := by
          rw [← hf, smul_smul, smul_smul, mul_comm _ (idem v), hca, if_pos ((hmem v).mpr h1),
            if_neg (fun h => pi_notMem_cP hπ h1 ((hmem _).mp h)), add_zero, mul_comm (idem v)]
        rw [e1]; exact hy1 v h1
      · by_cases h2 : π ∈ (cP v).asIdeal
        · rw [compC v h2]
          have e1 : (∑ w ∈ hSf.toFinset, (idem w * a1 w + idem (cP w) * a2 w)) • g (cP v) =
              a2 (cP v) • g (cP v) := by
            rw [← hgw (cP v) h2, smul_smul, smul_smul, mul_comm _ (idem (cP (cP v))), cP_cP, hca,
              if_neg (fun h => hnot v h2 ((hmem v).mp h)), if_pos ((hmem _).mpr h2), zero_add,
              cP_cP, mul_comm (idem v)]
          have key := hy2 (cP v) h2
          rw [cjA_idem, cP_cP] at key
          rw [e1]; exact key
        · rw [comp0 v h1 h2, smul_zero, sub_zero]
          have hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
            rw [T_mem_iff hπ]; tauto
          have hyd : y ∈ hat (Formalism.L2.Herm.dualL D.sp.cm X L₀) := (mem_hat_dualL_iff H.1 y).mpr hy
          exact ((H.2.1 v (idem v) (isPlIdem_idem v) hT (idem v • y)).mpr (inCmp_idem _ hyd)).1

end GlobalTheory.AdIsom.BaseVec

end
