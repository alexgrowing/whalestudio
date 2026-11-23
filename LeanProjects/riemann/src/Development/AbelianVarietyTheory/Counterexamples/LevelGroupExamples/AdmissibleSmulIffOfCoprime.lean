import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverDatum

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj GlobalTheory.LevelPairing
open CategoryTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.pd_pos (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) : 0 < d.pd := by
  obtain ⟨-, hM, -⟩ := h
  have h3 := d.l₂.three_le
  rw [hM] at h3
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, mul_zero] at h3
  omega

theorem Mb_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  intro h
  have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have := this (Ideal.subset_span rfl)
  rw [h, Ideal.mem_bot] at this
  exact hM (by exact_mod_cast this)

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.half_mul_conj (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) :
    d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} := by
  obtain ⟨-, hM, -, hMb, -⟩ := h
  have h2 := d.l₂.prod
  rw [hMb, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, l.prod] at h2
  have hne : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := l.three_le
    omega
  exact mul_left_cancel₀ hne h2

theorem half_unique (d d' : DeltaDat Xo c n) (h : d.IsLev) (h' : d'.IsLev) (e : d.l₂ = d'.l₂) :
    d.I = d'.I ∧ d.pd = d'.pd := by
  have hM : 0 < l.M := by have := l.three_le; omega
  refine ⟨mul_left_cancel₀ (Mb_ne_bot l) ?_, Nat.eq_of_mul_eq_mul_left hM ?_⟩
  · rw [← h.2.2.2.1, ← h'.2.2.2.1, e]
  · rw [← h.2.1, ← h'.2.1, e]

theorem isLev_change (d : DeltaDat Xo c n) (h : d.IsLev) (φ : (Fin n → LevQ Dw d.l₂) → c.F)
    (nab : NabV d.Xo₂ d.c₂) : DeltaDat.IsLev { d with φδ := φ, nab₂ := nab } := h

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
set_option synthInstance.maxHeartbeats 200000 in

theorem _root_.GlobalTheory.LevelCoverDatum.isLev_smul (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) (a : d.c₂.F) (ha : a ≠ 0) :
    _root_.Formalism.L2.Pj.DeltaDat.IsLev { d with cδ := a • d.cδ } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, Submodule.smul_mem _ a h8, ?_⟩
  intro k _ _ _ y₂
  have hy := h9 k y₂
  simp only [_root_.Formalism.L2.Pj.evR] at hy ⊢
  rw [_root_.Formalism.L2.Pj.evalAt_smul]
  exact mul_ne_zero ((map_ne_zero _).mpr ha) hy

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.zetaM_cover (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.l₂.M = l.M * d.pd) :
    _root_.Formalism.L2.Pj.zetaM d.c₂ ^ d.pd = d.eF (_root_.Formalism.L2.Pj.zetaM c) := by
  have h3 := d.l₂.three_le
  rw [h] at h3
  have hM : l.M ≠ 0 := fun h0 => by rw [h0, zero_mul] at h3; omega
  have hp : d.pd ≠ 0 := fun h0 => by rw [h0, mul_zero] at h3; omega
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]
  change ((_root_.Formalism.L2.Pj.zetaM d.c₂ : ℂ)) ^ d.pd = (_root_.Formalism.L2.Pj.zetaM c : ℂ)
  rw [_root_.GlobalTheory.LevelPairing.zetaM_coe, _root_.GlobalTheory.LevelPairing.zetaM_coe, h]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_w (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (x0 : Fin n → Dw.La) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).w x0 = _root_.Formalism.L2.Pj.x0Dat c x0 := by
  funext q
  apply Subtype.ext
  simp only [_root_.Formalism.L2.Pj.DeltaDat.w, _root_.Formalism.L2.Pj.noDelta, mul_one]
  unfold _root_.Formalism.L2.Pj.x0Dat
  rfl

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_etaOK (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).EtaOK ↔ (∀ a, (Xo.univ.eta a).left ≫ m.φ = (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA a).left ≫ m.φ = (Xo.univ.etaA a).left := by
  simp only [_root_.Formalism.L2.Pj.DeltaDat.EtaOK, _root_.Formalism.L2.Pj.noDelta, Nat.div_self l.A_pos, Category.id_comp]
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_) <;>
  · apply Iff.of_eq
    congr 3
    open scoped MonObj in exact pow_one _

end GlobalTheory.LevelCoverDatum
