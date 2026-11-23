import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedFrameGauge
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BiadditiveBalancedSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion

section Exp

variable {k : Type} [CommRing k] [Algebra ℚ k] {d n : ℕ}

omit [Algebra ℚ k] in
theorem cc_ev {m : ℕ} {a : Fin m → Pt k n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
  have e : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  have h0 : constantCoeff (ev a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero hs (fun p => ha p.1 p.2) (by simp)
  have hadd : ∀ f g : PS k m d, ev a (f + g) = ev a f + ev a g := fun f g => subst_add hs f g
  conv_lhs => rw [e, hadd, map_add, h0]
  simp [ev]

theorem expS_sum {ι : Type} (s : Finset ι) (g : ι → PS k n d) (hg : ∀ i, constantCoeff (g i) = 0) :
    FB.expS k (∑ i ∈ s, g i) = ∏ i ∈ s, FB.expS k (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [BalancedFrameGauge.expS_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      WickVanishing.gt_expS_add _ _ (hg a) (by simp [map_sum, hg]), ih]

theorem expS_smul_sum {ι : Type} [Fintype ι] (g : ι → PS k n d) (hg : ∀ i, constantCoeff (g i) = 0)
    (N : ℕ) : FB.expS k ((N : k) • ∑ i, g i) = ∏ i, FB.expS k (g i) ^ N := by
  have h : (N : k) • ∑ i, g i = ∑ _j : Fin N, ∑ i, g i := by
    rw [Nat.cast_smul_eq_nsmul]; simp
  rw [h, expS_sum _ _ (fun _ => by simp [map_sum, hg]), expS_sum _ _ hg, Finset.prod_pow]
  simp

end Exp

section Frames

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem gauge_iff (B : FB R d O) (h : PS k 2 d) :
    BalancedFrameGauge.IsBalancedGauge k B h ↔ BiadditiveBalancedSeries.IsBiaddBalanced B k h :=
  ⟨fun H => ⟨H.ax0, H.ax1, H.ph1, H.ph2, H.ad⟩, fun H => ⟨H.ax0, H.ax1, H.add1, H.add2, H.bal⟩⟩

omit [Algebra ℚ k] in
theorem cc_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) : constantCoeff h = 0 := by
  have := cc_ev (a := (![0, pt k d 0] : Fin 2 → Pt k 1 d))
    (fun j i => by fin_cases j <;> simp [pt]) h
  rw [← this, h0, map_zero]

omit [Algebra ℚ k] in
theorem cc_col (B : FB R d O) {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) (w0 : O) {n : ℕ}
    (b : Fin n) : constantCoeff (ev (n := n) ![pt k d b, comp1 (B.actK k w0) (pt k d b)] h) = 0 := by
  have hc : ∀ i, constantCoeff (comp1 (B.actK k w0) (pt k d b) i) = 0 := fun i => by
    have := cc_ev (a := (![pt k d b] : Fin 1 → Pt k n d))
      (fun j i => by fin_cases j; simp [pt]) (B.actK k w0 i)
    rw [comp1, this, FB.actK, constantCoeff_map, B.A.const, map_zero]
  have := cc_ev (a := (![pt k d b, comp1 (B.actK k w0) (pt k d b)] : Fin 2 → Pt k n d))
    (fun j i => by
      fin_cases j
      · simp [pt]
      · exact hc i) h
  rw [this, cc_of_ax k h0]

theorem val_eq (B : FB R d O) {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) (w0 : O)
    (N : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial (ι × Fin n) k) :
    BalancedFrameGauge.valCols k B h w0 N f u P = BiadditiveBalancedSeries.frameVal B k h w0 N f u P := by
  unfold BalancedFrameGauge.valCols BiadditiveBalancedSeries.frameVal BalancedFrameGauge.quotCols BiadditiveBalancedSeries.colSum
  rw [expS_smul_sum _ (cc_col k B h0 w0)]
  rfl

end Frames

section Letters

variable {E : Type} [Field E] [NumberField E] {k : Type} [Field k]

theorem conj_eq [IsCMField E] (τ : E →+* k) : BalancedFrameGauge.conjType E τ = BiadditiveBalancedSeries.conjEmb τ := rfl

theorem harmonic_iff [IsCMField E] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) :
    BalancedFrameGauge.IsHarmonic r P ↔ BiadditiveBalancedSeries.IsHarmonic r P := Iff.rfl

theorem eigen_eq [StarRing (𝓞 E)] {R : Type} [CommRing R] [Algebra R k] {d : ℕ} (B : FB R d (𝓞 E))
    (τ : E →+* k) : BalancedFrameGauge.lieEigen k B τ = BiadditiveBalancedSeries.lieEig B τ := rfl

theorem card_iff [CharZero k] :
    Fintype.card (E →+* k) = Module.finrank ℚ E ↔ Nat.card (E →+* k) = Module.finrank ℚ E := by
  rw [Nat.card_eq_fintype_card]

end Letters

section Bases

variable {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]

theorem indep_span_iff (W : Submodule k V) (v : ι → V) :
    (LinearIndependent k v ∧ Submodule.span k (Set.range v) = W) ↔
      ∃ b : Module.Basis ι k W, ∀ i, (b i : V) = v i := by
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨Module.Basis.span hv, fun i => by simp⟩
  · rintro ⟨b, hb⟩
    have e : v = W.subtype ∘ b := funext fun i => (hb i).symm
    subst e
    refine ⟨b.linearIndependent.map' _ (Submodule.ker_subtype W), ?_⟩
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Bases

theorem fixed_iff (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    (k : Type) [Field k] [CharZero k] (R : Type) [CommRing R] [Algebra R k] (d : ℕ) (B : FB R d (𝓞 E))
    (w0 : 𝓞 E) (r : (E →+* k) → ℕ) :
    (∀ (u : (Σ τ : E →+* k, Fin (r τ)) → Fin d → k),
      (∀ τ : E →+* k, LinearIndependent k (fun i : Fin (r τ) => u ⟨τ, i⟩) ∧
        Submodule.span k (Set.range fun i : Fin (r τ) => u ⟨τ, i⟩) = BalancedFrameGauge.lieEigen k B τ) →
      ∀ (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k), BalancedFrameGauge.IsHarmonic r P →
      ∀ (h h' : PS k 2 d), B.IsCanonGauge k h → BalancedFrameGauge.IsBalancedGauge k B h' →
      ∀ f : PS k n d, BalancedFrameGauge.valCols k B h w0 N f u P = BalancedFrameGauge.valCols k B h' w0 N f u P) ↔
    (∀ (u : ∀ τ : E →+* k, Module.Basis (Fin (r τ)) k (BiadditiveBalancedSeries.lieEig B τ))
      (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k),
      BiadditiveBalancedSeries.IsHarmonic r P →
      ∀ (f : PS k n d) (hc g : PS k 2 d), B.IsCanonGauge k hc → BiadditiveBalancedSeries.IsBiaddBalanced B k g →
        BiadditiveBalancedSeries.frameVal B k g w0 N f (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P =
          BiadditiveBalancedSeries.frameVal B k hc w0 N f
            (fun l : Σ τ : E →+* k, Fin (r τ) => (u l.1 l.2 : Fin d → k)) P) := by
  constructor
  · intro H u n N P hP f hc g hhc hg
    rw [← val_eq k B hg.ax0, ← val_eq k B hhc.ax0]
    refine (H _ (fun τ => ?_) n N P ((harmonic_iff r P).2 hP) hc g hhc ((gauge_iff k B g).2 hg) f).symm
    rw [eigen_eq]
    exact (indep_span_iff _ _).2 ⟨u τ, fun _ => rfl⟩
  · intro H u hu n N P hP h h' hh hh' f
    choose b hb using fun τ : E →+* k =>
      (indep_span_iff (BiadditiveBalancedSeries.lieEig B τ) (fun i : Fin (r τ) => u ⟨τ, i⟩)).1 (hu τ)
    have e : u = fun l : Σ τ : E →+* k, Fin (r τ) => (b l.1 l.2 : Fin d → k) :=
      funext fun l => (hb l.1 l.2).symm
    rw [val_eq k B hh.ax0, val_eq k B hh'.ax0, e]
    exact (H b n N P ((harmonic_iff r P).1 hP) f h h' hh ((gauge_iff k B h').1 hh')).symm

theorem balancedFrameValue_iff : BalancedFrameGauge.BalancedFrameValue ↔ BiadditiveBalancedSeries.BiaddBalancedValue := by
  constructor
  · intro H E _ _ _ _ hs k _ _ hk R _ _ d B w0 hw r
    exact (fixed_iff E k R d B w0 r).1 (H E hs k (card_iff.2 hk) R d B w0 hw r)
  · intro H E _ _ _ _ hs k _ _ hk R _ _ d B w0 hw r
    exact (fixed_iff E k R d B w0 r).2 (H E hs k (card_iff.1 hk) R d B w0 hw r)

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion
