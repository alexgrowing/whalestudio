import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.RepRed

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem resV_C_mul {ι κ R : Type} [CommSemiring R] (f : κ → ι) (c : R) (Th : MvPowerSeries ι R) :
    resV f (MvPowerSeries.C c * Th) = MvPowerSeries.C c * resV f Th := by
  ext n
  show MvPowerSeries.coeff (Finsupp.mapDomain f n) (MvPowerSeries.C c * Th) =
    MvPowerSeries.coeff n (MvPowerSeries.C c * resV f Th)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  all_goals rfl

def LocalRepresentativeCondition (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (be : MvPowerSeries (Fin 2) (Formalism.MainNotions.FormalGroupSystem.K0 p)) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ (v : X.Pl), ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ExtensionLocalCondition p ℂ_[p] (OcC p) be
      (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j))) (thA ℂ_[p] φ (thFOf X pos F j L0 La')))

theorem adm_two_iff_local_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm2 D X (pendT X E hfin hst hLT pos F) ↔ LocalRepresentativeCondition X E hfin (beLT hLT) pos F := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La'),
      (pendT X E hfin hst hLT pos F).ThV v j La La' φ = MvPowerSeries.C (chiN X ℂ_[p] hfin j La) *
        resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] (frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ)
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')) := by
    intro v j La La' φ
    rw [← thA_SA X ℂ_[p] (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ, ← resV_C_mul]
    show resV _ ((pendT X E hfin hst hLT pos F).ThA j La La' φ) = _
    congr 1
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  have hu : ∀ j (La : X.Lt j), chiN X ℂ_[p] hfin j La ∈ OcC p ∧ (chiN X ℂ_[p] hfin j La)⁻¹ ∈ OcC p ∧
      chiN X ℂ_[p] hfin j La ≠ 0 := fun j La =>
    ⟨show ‖_‖ ≤ 1 by rw [hn], show ‖_‖ ≤ 1 by rw [norm_inv, hn, inv_one],
      fun h0 => by have := hn j La; rw [h0, norm_zero] at this; exact zero_ne_one this⟩
  constructor
  · rintro H v j hj ⟨c, L1⟩ h0 La' hL' φ0
    have hL0 : (X.Pj j).IsLatTup L1 := repOf_lat X.Lv hfin j (c, L1) h0
    have hh : L1 = (X.Lv.lev j c).smul (delt X hfin j c L1) ((X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) :=
      (lsmul_lsmul_inv _ _ _).symm
    have A : ∀ φ' : Frm X j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La',
        ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] φ' (thFOf X pos F j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La'))) := by
      intro φ'
      have H1 := H v j hj (c, L1) La' hL0 hL' (frmBack X (La := (c, L1)) (delt X hfin j c L1) hh φ')
      change ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThV v j (c, L1) La' _) at H1
      rw [key, frmMove_frmBack] at H1
      obtain ⟨hc, hc', hc0⟩ := hu j (c, L1)
      exact (K1gen_C_mul_iff (ι := Eidx _ _ _) hc hc' hc0).1 H1
    obtain ⟨L2, h2, e2⟩ := delt_spec X hfin j c L1 hL0
    have h21 : L2 = L1 := (repOf_ex X.Lv hfin j c L1 hL0).unique ⟨h2, _, e2⟩ ⟨h0, 1, (lsmul_one _ L1).symm⟩
    have e3 : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L1 := by
      generalize delt X hfin j c L1 = d at e2 ⊢
      conv_lhs => rw [e2]
      rw [lsmul_inv_lsmul, h21]
    have B : ∀ L3 (_ : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L3) (φ' : Frm X j (c, L3) La'),
        ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) (resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j)))
          (thA ℂ_[p] φ' (thFOf X pos F j (c, L3) La'))) := by
      intro L3 e
      subst e
      exact A
    exact B L1 e3 φ0
  · intro H v j hj La La' hL hL' φ
    change ExtensionLocalCondition p ℂ_[p] (OcC p) (beLT hLT) ((pendT X E hfin hst hLT pos F).ThV v j La La' φ)
    rw [key]
    obtain ⟨hc, -, -⟩ := hu j La
    refine K1gen_C_mul (ι := Eidx _ _ _) hc ?_
    obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j La.1 La.2 hL
    have e2 : (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2 = L1 := by
      generalize delt X hfin j La.1 La.2 = d at e1 ⊢
      rw [e1, lsmul_inv_lsmul]
    generalize frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ = φ0
    revert φ0
    rw [e2]
    intro φ0
    exact H v j hj (La.1, L1) h1 La' hL' φ0

theorem hasSubst_coordZA' (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA Kc j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun e => ?_
  rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Formalism.MainNotions.FormalGroupSystem.Sys.coordZA]

theorem applyD_C_mul {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (c : Kc)
    (f : MvPowerSeries σ Kc) : applyD P (MvPowerSeries.C c * f) = c • applyD P f := by
  rw [applyD, applyD, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPowerSeries.coeff_C_mul, smul_smul]
  congr 1
  ring

def GeZ (x : ℂ_[p]) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ 0 * b → x ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p

theorem geZ_mul_iff {c x : ℂ_[p]} (hc : ‖c‖ = 1) : GeZ (c * x) ↔ GeZ x := by
  have key : ∀ (a : ℤ) (b : ℕ), (c * x) ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p ↔
      x ^ b * (p : ℂ_[p]) ^ (-a) ∈ OcC p := by
    intro a b
    have e : ‖(c * x) ^ b * (p : ℂ_[p]) ^ (-a)‖ = ‖x ^ b * (p : ℂ_[p]) ^ (-a)‖ := by
      rw [mul_pow, mul_assoc, norm_mul, norm_pow, hc, one_pow, one_mul]
    change ‖(c * x) ^ b * (p : ℂ_[p]) ^ (-a)‖ ≤ 1 ↔ ‖x ^ b * (p : ℂ_[p]) ^ (-a)‖ ≤ 1
    rw [e]
  unfold GeZ
  simp only [key]

def Adm3Rep (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  ∀ j < X.mm, ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      GeZ (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j (thA ℂ_[p] φ (thFOf X pos F j L0 La')))))

theorem adm_three_iff_representative (D : Formalism.BasicNotions.D7) (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type}
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) :
    adm3 D X (pendT X E hfin hst hLT pos F) ↔ Adm3Rep X E hfin pos F := by
  let _ := wittFractionAlgebraCp p
  let _ := algKfC E.toCEmb
  have key : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j ((pendT X E hfin hst hLT pos F).ThA j La La' φ))) =
        chiN X ℂ_[p] hfin j La • MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] (frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ)
            (thFOf X pos F j (La.1, (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2) La')))) := by
    intro j La La' φ I n
    rw [← thA_SA X ℂ_[p] (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ, ← MvPolynomial.coeff_smul,
      ← applyD_C_mul, Sys.ThZA, Sys.ThZA, ← subst_C_mul' (hasSubst_coordZA' X ℂ_[p] j)]
    congr 3
    exact subst_C_mul' (hasSubst_invF ℂ_[p] φ) _ _
  have hn : ∀ j (La : X.Lt j), ‖chiN X ℂ_[p] hfin j La‖ = 1 := fun j La => norm_chiN X E.toCEmb hfin j La
  constructor
  · rintro H j hj ⟨c, L1⟩ h0 La' hL' φ0 I n
    have hL0 : (X.Pj j).IsLatTup L1 := repOf_lat X.Lv hfin j (c, L1) h0
    have hh : L1 = (X.Lv.lev j c).smul (delt X hfin j c L1) ((X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) :=
      (lsmul_lsmul_inv _ _ _).symm
    have A : ∀ φ' : Frm X j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La',
        GeZ (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] φ' (thFOf X pos F j (c, (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1) La'))))) := by
      intro φ'
      have H1 := H j hj (c, L1) La' hL0 hL' (frmBack X (La := (c, L1)) (delt X hfin j c L1) hh φ') I n
      change GeZ _ at H1
      rw [key, frmMove_frmBack, smul_eq_mul, geZ_mul_iff (hn j (c, L1))] at H1
      exact H1
    obtain ⟨L2, h2, e2⟩ := delt_spec X hfin j c L1 hL0
    have h21 : L2 = L1 := (repOf_ex X.Lv hfin j c L1 hL0).unique ⟨h2, _, e2⟩ ⟨h0, 1, (lsmul_one _ L1).symm⟩
    have e3 : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L1 := by
      generalize delt X hfin j c L1 = d at e2 ⊢
      conv_lhs => rw [e2]
      rw [lsmul_inv_lsmul, h21]
    have B : ∀ L3 (_ : (X.Lv.lev j c).smul (delt X hfin j c L1)⁻¹ L1 = L3) (φ' : Frm X j (c, L3) La'),
        GeZ (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA ℂ_[p] j
          (thA ℂ_[p] φ' (thFOf X pos F j (c, L3) La'))))) := by
      intro L3 e
      subst e
      exact A
    exact B L1 e3 φ0
  · intro H j hj La La' hL hL' φ I n
    change GeZ _
    rw [key, smul_eq_mul, geZ_mul_iff (hn j La)]
    obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j La.1 La.2 hL
    have e2 : (X.Lv.lev j La.1).smul (delt X hfin j La.1 La.2)⁻¹ La.2 = L1 := by
      generalize delt X hfin j La.1 La.2 = d at e1 ⊢
      rw [e1, lsmul_inv_lsmul]
    generalize frmMove X (delt X hfin j La.1 La.2) (lsmul_lsmul_inv _ _ _).symm φ = φ0
    revert φ0
    rw [e2]
    intro φ0
    exact H j hj (La.1, L1) h1 La' hL' φ0 I n

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
