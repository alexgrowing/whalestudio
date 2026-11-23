import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesPropertiesStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) where
  mem v hv := hT'.mem _ (hT.mem v hv)
  add v hv w hw := by
    rw [hT.add v hv w hw, hT'.add _ (hT.mem v hv) _ (hT.mem w hw)]
  smul a v hv := by
    rw [hT.smul a v hv, hT'.smul a _ (hT.mem v hv)]
  cont W hW := cw_comp (Bm := fun v => dsigW (k := k) (r := r) R''.σ W (T' v)) hT (hT'.cont W hW)

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm := by
  induction W with
  | nil => exact hv
  | cons X W ih =>
    exact ((GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X (hW X List.mem_cons_self)).1 _
      (ih (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)))).1

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w := by
  have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1
  have h1 := ((h v hv).2.const_smul a).add (h w hw).2
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  funext t
  simp

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show dsig R.σ X (dsigW R.σ W (a • v + w)) = _
    rw [ih hW']
    exact dsig_lin hK hR (hW X List.mem_cons_self) a (dsigW_mem hK hR W hW' hv) (dsigW_mem hK hR W hW' hw)

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := by
  obtain ⟨hu, hi, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
      = gᴴ * Xᴴ * ((g⁻¹)ᴴ * Hpk k r) + (Hpk k r * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem norm_sigma (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ := by
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hR.2
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hm := hds.2.2.1.2.1 (P₀ * g * P₀⁻¹) hx' v
  have e2 : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e2] at hm
  exact hm

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hW'' : ∀ Y ∈ W.map (fun X => g⁻¹ * X * g), InLieHpk k r Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW' Z hZ)
    have hdet : IsUnit g.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR _ (inLie_conj hg (hW X List.mem_cons_self))).2.1 _
      (dsigW_mem hK hR _ hW'' hv) g hg
    rw [e] at h
    show dsig R.σ X (dsigW R.σ W (R.σ g v)) = R.σ g (dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', h]

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) where
  mem v hv := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv g hg
  add v _ w _ := map_add _ _ _
  smul a v _ := map_smul _ _ _
  cont W hW := by
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hK hR hg W hW hv, norm_sigma hR hg]

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDG ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) where
  mem v hv := Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a (hT.mem v hv)) (hT'.mem v hv)
  add v hv w hw := by
    rw [hT.add v hv w hw, hT'.add v hv w hw, smul_add]
    abel
  smul b v hv := by
    rw [hT.smul b v hv, hT'.smul b v hv, smul_add, smul_comm]
  cont W hW := by
    refine cw_of_semiBd R₀ (((semiBd_of_cw R₀ (hT.cont W hW)).mul (norm_nonneg a)).add
      (semiBd_of_cw R₀ (hT'.cont W hW))) (fun v hv => ?_)
    rw [dsigW_lin hK hR W hW a (hT.mem v hv) (hT'.mem v hv)]
    exact (norm_add_le _ _).trans (by rw [norm_smul])

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' _
  exact ⟨fun g hg => smMap_sigma hK hR hg, fun T T' hT hT' => smMap_comp hT hT',
    fun T T' a hT hT' => smMap_lin hK hR' a hT hT', fun Wp _ T Bm hT hB => cw_comp hT hB⟩

end GlobalTheory.SmMapAct
