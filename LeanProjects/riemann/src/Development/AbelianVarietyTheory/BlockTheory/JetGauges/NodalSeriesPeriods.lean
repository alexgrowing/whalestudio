import Mathlib

open PowerSeries

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods

abbrev Qbar : Type := ↥(algebraicClosure ℚ ℂ)

abbrev Place (p : ℕ) [Fact p.Prime] : Type := Qbar →+* ℂ_[p]

def IsLattice (Λ : AddSubgroup ℂ) : Prop :=
  ∃ L : PeriodPair, L.lattice.toAddSubgroup = Λ

def eisSum (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' ω : {ω : ℂ // ω ∈ Λ ∧ ω ≠ 0}, ((ω : ℂ) ^ k)⁻¹

def g₂ (Λ : AddSubgroup ℂ) : ℂ := 60 * eisSum Λ 4

def g₃ (Λ : AddSubgroup ℂ) : ℂ := 140 * eisSum Λ 6

def disc (Λ : AddSubgroup ℂ) : ℂ := g₂ Λ ^ 3 - 27 * g₃ Λ ^ 2

def shortCurve {K : Type} [Field K] (a b : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, -(a / 4), -(b / 4)⟩

theorem shortCurve_Δ {K : Type} [Field K] [CharZero K] (a b : K) :
    (shortCurve a b).Δ = a ^ 3 - 27 * b ^ 2 := by
  simp only [shortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

def curveAt {p : ℕ} [Fact p.Prime] (Λ : AddSubgroup ℂ) (h₂ : g₂ Λ ∈ algebraicClosure ℚ ℂ)
    (h₃ : g₃ Λ ∈ algebraicClosure ℚ ℂ) (lam : Place p) : WeierstrassCurve ℂ_[p] :=
  shortCurve (lam ⟨g₂ Λ, h₂⟩) (lam ⟨g₃ Λ, h₃⟩)

theorem curveAt_Δ {p : ℕ} [Fact p.Prime] (Λ : AddSubgroup ℂ) (h₂ : g₂ Λ ∈ algebraicClosure ℚ ℂ)
    (h₃ : g₃ Λ ∈ algebraicClosure ℚ ℂ) (lam : Place p) (h : disc Λ = 1) :
    (curveAt Λ h₂ h₃ lam).Δ = 1 := by
  have : (⟨g₂ Λ, h₂⟩ : Qbar) ^ 3 - 27 * (⟨g₃ Λ, h₃⟩ : Qbar) ^ 2 = 1 := Subtype.ext h
  rw [curveAt, shortCurve_Δ, ← map_one lam, ← this]
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat]

abbrev incl (p : ℕ) [Fact p.Prime] : 𝓞_ℂ_[p] →+* ℂ_[p] := algebraMap 𝓞_ℂ_[p] ℂ_[p]

def IsModel {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve ℂ_[p]) (W : WeierstrassCurve 𝓞_ℂ_[p])
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  C • E = W.map (incl p) ∧ IsUnit W.Δ

def HasLocalCoefficients {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve 𝓞_ℂ_[p]) : Prop :=
  ∃ k : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] k ∧
    incl p W.a₁ ∈ k ∧ incl p W.a₂ ∈ k ∧ incl p W.a₃ ∈ k ∧ incl p W.a₄ ∈ k ∧ incl p W.a₆ ∈ k

def diffFactor {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) : ℂ_[p]ˣ := C.u

section Expansion

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

def step (v : A⟦X⟧) : A⟦X⟧ :=
  1 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X ^ 3 * v ^ 2 + C W.a₄ * X ^ 4 * v ^ 2
    + C W.a₆ * X ^ 6 * v ^ 3

def vSer : A⟦X⟧ := mk fun n => coeff n ((step W)^[n + 1] 0)

def wSer : A⟦X⟧ := X ^ 3 * vSer W

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma nodal_map_sub_eq_X_mul_sub_mul (u v : A⟦X⟧) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v =
      X * (u - v) * (C W.a₁ + C W.a₂ * X + C W.a₃ * X ^ 2 * (u + v) + C W.a₄ * X ^ 3 * (u + v)
        + C W.a₆ * X ^ 5 * (u ^ 2 + u * v + v ^ 2)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step
  ring

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_succ_dvd_sub_of_X_pow_dvd {k : ℕ} {u v : A⟦X⟧} (h : X ^ k ∣ u - v) :
    X ^ (k + 1) ∣
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v := by
  rw [nodal_map_sub_eq_X_mul_sub_mul, pow_succ']
  exact Dvd.dvd.mul_right (mul_dvd_mul_left X h) _

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_dvd_iterate_sub_iterate (n m : ℕ) :
    X ^ n ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    have e1 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1 + m] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0) := by
      rw [show n + 1 + m = n + m + 1 by omega]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact X_pow_succ_dvd_sub_of_X_pow_dvd W ih

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma vSer_isFixedPt :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W) := by
  ext k
  have h : X ^ k ∣ _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0 := by
    rw [X_pow_dvd_iff]
    intro m hm
    have h2 := X_pow_dvd_iterate_sub_iterate W (m + 1) (k - (m + 1))
    rw [show m + 1 + (k - (m + 1)) = k by omega, X_pow_dvd_iff] at h2
    have h3 := h2 m (Nat.lt_succ_self m)
    rw [map_sub, sub_eq_zero] at h3
    rw [map_sub, sub_eq_zero, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]
    exact h3.symm
  have h2 := X_pow_succ_dvd_sub_of_X_pow_dvd W h
  have e : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k + 1] 0 =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
        ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0) :=
    Function.iterate_succ_apply' _ _ _
  rw [← e, X_pow_dvd_iff] at h2
  have h3 := h2 k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer_eq :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W = X ^ 3 + C W.a₁ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₂ * X ^ 2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₃ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₄ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₆ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 3 := by
  have hv := vSer_isFixedPt W
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer]
  conv_lhs => rw [hv, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step]
  ring

def epSer : A⟦X⟧ := invOfUnit (vSer W) 1

def numSer : A⟦X⟧ := X * d⁄dX A (epSer W) - 2 * epSer W

def denSer : A⟦X⟧ := -2 * epSer W + C W.a₁ * X * epSer W + C W.a₃ * X ^ 3

def jacSer : A⟦X⟧ :=
  1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * C W.a₃ * wSer W - 2 * C W.a₄ * X * wSer W
    - 3 * C W.a₆ * wSer W ^ 2

def omegaSer : A⟦X⟧ := invOfUnit (jacSer W) 1

end Expansion

def primitive {K : Type} [Field K] [CharZero K] (f : K⟦X⟧) : K⟦X⟧ :=
  mk fun
    | 0 => 0
    | n + 1 => coeff n f / (n + 1)

def logSer {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve 𝓞_ℂ_[p]) : ℂ_[p]⟦X⟧ :=
  primitive (PowerSeries.map (incl p) (omegaSer W))

def coordSer {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve 𝓞_ℂ_[p]) (ε₀ : ℂ_[p]ˣ) : ℂ_[p]⟦X⟧ :=
  C ((ε₀⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * logSer W

def IsParameter {A : Type} [CommRing A] (t : A⟦X⟧) : Prop :=
  constantCoeff t = 0 ∧ IsUnit (coeff 1 t)

def IsSeriesPeriod {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve 𝓞_ℂ_[p]) (ε₀ Ω : ℂ_[p]ˣ) : Prop :=
  ∃ t : 𝓞_ℂ_[p]⟦X⟧, IsParameter t ∧
    coordSer W ε₀ = C (Ω : ℂ_[p]) * (PowerSeries.log ℂ_[p]).subst (PowerSeries.map (incl p) t)

def IsPeriod {p : ℕ} [Fact p.Prime] (Λ : AddSubgroup ℂ) (lam : Place p) (Ω : ℂ_[p]ˣ) : Prop :=
  IsLattice Λ ∧ disc Λ = 1 ∧
    ∃ (h₂ : g₂ Λ ∈ algebraicClosure ℚ ℂ) (h₃ : g₃ Λ ∈ algebraicClosure ℚ ℂ)
      (W : WeierstrassCurve 𝓞_ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]),
      IsModel (curveAt Λ h₂ h₃ lam) W C ∧ IsSeriesPeriod W (diffFactor C) Ω

theorem eisSum_eq_G (L : PeriodPair) {k : ℕ} (hk : k ≠ 0) :
    eisSum L.lattice.toAddSubgroup k = L.G k := by
  let i : {ω : ℂ // ω ∈ L.lattice.toAddSubgroup ∧ ω ≠ 0} → L.lattice := fun ω => ⟨ω.1, ω.2.1⟩
  have hi : Function.Injective i := fun a b h => Subtype.ext (congrArg (fun x : L.lattice => (x : ℂ)) h)
  refine hi.tsum_eq (f := fun l : L.lattice => ((l : ℂ) ^ k)⁻¹) ?_
  intro l hl
  refine ⟨⟨l, l.2, fun h0 => hl ?_⟩, rfl⟩
  simp [h0, hk]

theorem g₂_eq (L : PeriodPair) : g₂ L.lattice.toAddSubgroup = L.g₂ := by
  rw [g₂, eisSum_eq_G L (by norm_num), PeriodPair.g₂]

theorem g₃_eq (L : PeriodPair) : g₃ L.lattice.toAddSubgroup = L.g₃ := by
  rw [g₃, eisSum_eq_G L (by norm_num), PeriodPair.g₃]

example {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve 𝓞_ℂ_[p]) (h : IsUnit W.Δ) :
    IsModel (W.map (incl p)) W 1 := ⟨one_smul _ _, h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods
