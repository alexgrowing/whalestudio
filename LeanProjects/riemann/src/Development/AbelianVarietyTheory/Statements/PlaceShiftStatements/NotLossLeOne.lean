import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem bigC_of_big {Q : ChP} (h : Big Q) : BigC fun _ ch _ _ => Q ch := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun CF hC => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x, h⟩ := h ε CF hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j _ => h D large₂ e hx Γ Pl0 T A Ks R F s ch i j⟩

theorem sig_eq {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : sig G = G.pl.sigma0 sc := rfl

theorem loss_single (w : PlL D) {a : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ lw w) :
    Loss (open Classical in Pi.single w a : PlL D → ℝ) (lw w * a) := by
  classical
  refine ⟨fun v => ?_, (Set.finite_singleton w).subset fun v hv => ?_, fun s => ?_⟩
  · by_cases h : v = w
    · subst h; simpa using ha
    · simp [h]
  · by_contra h
    exact hv (by simp [show v ≠ w from h])
  · by_cases h : w ∈ s
    · rw [Finset.sum_eq_single_of_mem w h fun v _ hv => by simp [hv]]; simp
    · rw [Finset.sum_eq_zero fun v hv => by simp [show v ≠ w from fun e => h (e ▸ hv)]]
      exact mul_nonneg hw ha

theorem loss_le {dl : PlL D → ℝ} {B : ℝ} (h : Loss dl B) : 0 ≤ B ∧ ∀ w, lw w * dl w ≤ B :=
  ⟨by simpa using h.2.2 ∅, fun w => by simpa using h.2.2 {w}⟩

theorem lossLe_iff (w : PlL D) {y : D.what₂.LL} (hy : y ≠ 0) (a : ℝ) : LossLe w (D.what₂.embLL y) a ↔ -a ≤ (vw w y : ℝ) :=
  ⟨fun ⟨_, e, h⟩ => by
    obtain rfl := D.what₂.embLL.injective e
    exact h.resolve_left hy, fun h => ⟨y, rfl, Or.inr h⟩⟩

theorem not_lossLe_one (w : PlL D) : ¬ LossLe w 1 (-1) := by
  rw [← map_one D.what₂.embLL, lossLe_iff w one_ne_zero, vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  norm_num

theorem inLat_of_mem {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {u : VV D.what₂.LL lam} (hu : u ∈ nabAtr (labLL D) lam Λ) : InLat lam w 0 Λ (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) :=
  ⟨u, 1, rfl, one_ne_zero, by rw [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]; simp, by rwa [one_smul]⟩

open Formalism.L2.Host in

theorem awayK : AwayK := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩
  have hr : ¬ (R.xiH (R.mu w)).UnrAt PP := (s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)
  by_cases hw : w ∈ R.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := s.mu_on w hw
    have e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    by_cases hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP
    · refine Or.inr fun l hl h1 h2 => hr fun x hx => ?_
      have hp : Formalism.EigenvalueLevelCeiling.plc w = l := by
        exact ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1
          ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))
      have a1 := hd x hx
      have a2 := hψ.atl PP (hp ▸ h1) x
      rw [e']
      change (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
      rw [a1, a2, mul_one]
    · refine Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
      have key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := fun p hp => by
        change algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal
        rwa [map_natCast]
      unfold CharFrame.delAt at hd
      split_ifs at hd
      · exact Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))
      · exact Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))
  · have e : R.mu w = A.μ0 := s.mu_off w hw
    refine absurd (fun x _ => ?_) hr
    rw [e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]
    rfl

theorem away_base {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (w : PlL D) :
    Away G μ₀ w := fun PP hP => by
  refine absurd (fun x _ => ?_) ((hL.Q_ram μ₀ PP).2 (Or.inl hP))
  rw [hL.xi_base]
  rfl

theorem not_absLe_two (σ : D.what₂.LL →+* ℂ) : ¬ AbsLe σ 2 0 := by
  rintro ⟨y, e, h⟩
  obtain rfl : y = 2 := D.what₂.embLL.injective (by rw [e, map_ofNat])
  rw [map_ofNat, Real.exp_zero] at h
  norm_num at h

theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') : LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, h⟩ := h
  obtain ⟨y', rfl, h'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl (by rw [hy, zero_mul])
  by_cases hy' : y' = 0
  · exact Or.inl (by rw [hy', mul_zero])
  refine Or.inr ?_
  have e : vw w (y * y') = vw w y + vw w y' := by
    rw [vw, vw, vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul] <;>
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff]
  have a1 := h.resolve_left hy
  have a2 := h'.resolve_left hy'
  rw [e]; push_cast; linarith

end GlobalTheory.SumSize.Model

end
