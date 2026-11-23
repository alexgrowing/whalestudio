import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CuspDecayShortRow

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem pInf_posIdele (r : ℝ) (hr : 0 < r) :
    pInf E ((posIdele (K := E) r hr : GroundTheory.Global.IdeleGroup E) : Ad E) = fun _ => (r : ℂ) := by
  have h : ∀ x, pInf E (GlobalTheory.CuspRep.sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  rw [GlobalTheory.CuspBoundSiegel.posIdele_congr hr (Real.exp_pos _) (Real.exp_log hr).symm,
    GlobalTheory.CuspBoundSiegel.posIdele_exp]
  change pInf E (1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E _) = _
  simp only [map_add, map_sub, map_one, h, sub_self, zero_add]
  funext w
  simp [expU]
  rw [← Complex.ofReal_exp, Real.exp_log hr]

theorem pFin_posIdele (r : ℝ) (hr : 0 < r) :
    pFin E ((posIdele (K := E) r hr : GroundTheory.Global.IdeleGroup E) : Ad E) = 1 := by
  change ((posIdele r hr : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E)
  exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

theorem norm_pInf_posIdele (r : ℝ) (hr : 0 < r) :
    ‖pInf E ((posIdele (K := E) r hr : GroundTheory.Global.IdeleGroup E) : Ad E)‖ ≤ r := by
  rw [pInf_posIdele]
  exact (pi_norm_le_iff_of_nonneg hr.le).2 fun _ => by simp [abs_of_pos hr]

theorem norm_pInf_posIdele_inv (r : ℝ) (hr : 0 < r) :
    ‖pInf E (((posIdele (K := E) r hr)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E)‖ ≤ r⁻¹ := by
  rw [map_units_inv (pInf E), pInf_posIdele]
  exact (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hr.le)).2 fun _ => by simp [abs_of_pos hr]

variable {a : ℕ}

theorem diag_eq_infGL (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a) =
      infGL E a (GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a)) := by
  refine ga_ext (by rw [pInf_infGL]) ?_
  rw [pFin_infGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E (((diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j) =
    (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; exact pFin_posIdele _ _
  · exact map_zero _

theorem norm_diag_le (u : Fin a → GroundTheory.Global.IdeleGroup E) (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ i, ‖pInf E (u i : Ad E)‖ ≤ R) :
    ‖(Matrix.of.symm (GeneralLinearGroup.map (pInf E) (diagUnits a u : GA E a)).val : LieI (InfinitePlace E) a)‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
  change ‖pInf E (((diagUnits a u : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j)‖ ≤ R
  rw [coe_diagUnits, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hu i
  · rw [map_zero, norm_zero]; exact hR

theorem continuous_invT : Continuous (invT : GA E a → GA E a) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_diag (u : Fin a → GroundTheory.Global.IdeleGroup E) :
    invT (diagUnits a u : GA E a) = (diagUnits a u : GA E a)⁻¹ := by
  refine Units.ext ?_
  show ((((diagUnits a u : GA E a)⁻¹ : GA E a)) : Matrix (Fin a) (Fin a) (Ad E))ᵀ = _
  rw [← map_inv, coe_diagUnits, Matrix.diagonal_transpose]

theorem invT_ratGL (γ : GL (Fin a) E) : ∃ γ' : GL (Fin a) E, invT (ratGL E a γ) = ratGL E a γ' := by
  refine ⟨⟨(γ⁻¹.val)ᵀ, (γ.val)ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩, Units.ext ?_⟩
  show ((((ratGL E a γ)⁻¹ : GA E a)) : Matrix (Fin a) (Fin a) (Ad E))ᵀ = _
  rw [← map_inv]
  rfl

theorem vecMul_ne_zero (γ : GL (Fin a) E) {ξ : Fin a → E} (hξ : ξ ≠ 0) : ξ ᵥ* γ.val ≠ 0 := by
  intro h
  apply hξ
  have := congrArg (fun v => v ᵥ* γ⁻¹.val) h
  simpa [Matrix.vecMul_vecMul] using this

end CuspDecayShortRow

end PositivityTheory.AdelicQuotientData

namespace PositivityTheory.AdelicQuotientData

namespace CuspDecayShortRow

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem low (hH : H0) {C1 C2 : Set (GA E a)} (h1 : IsCompact C1) (h2 : IsCompact C2) :
    ∃ B : ℝ, ∃ N : ℕ, 0 ≤ B ∧ ∀ p ∈ C1, ∀ q ∈ C2, ∀ (y : GL (Fin a) (Cinf E)) (g : GA E a) ξ, ξ ≠ 0 →
      ht (g * p * infGL E a y * q) ξ ≤ B * (1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ +
        ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖) ^ N * ht g ξ := by
  obtain ⟨hpos, -, -, hcpt, -, ⟨B0, N, hB0, h6⟩, -⟩ := hH E a
  obtain ⟨B1, hB1⟩ := hcpt C1 h1
  obtain ⟨B2, hB2⟩ := hcpt C2 h2
  refine ⟨max B2 0 * B0 * max B1 0, N, by positivity, fun p hp q hq y g ξ hξ => ?_⟩
  have e1 : ht (g * p * infGL E a y * q) ξ ≤ max B2 0 * ht (g * p * infGL E a y) ξ :=
    (hB2 q hq _ ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _ ξ hξ).le)
  have e2 := h6 y⁻¹ (g * p * infGL E a y) ξ hξ
  rw [inv_inv, mul_assoc (g * p), ← map_mul, mul_inv_cancel, map_one, mul_one] at e2
  have e3 : ht (g * p) ξ ≤ max B1 0 * ht g ξ :=
    (hB1 p hp _ ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _ ξ hξ).le)
  have hS : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖ + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ =
      1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖ := by ring
  rw [hS] at e2
  have hP : 0 ≤ (1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ +
        ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖) ^ N := by positivity
  calc ht (g * p * infGL E a y * q) ξ ≤ max B2 0 * ht (g * p * infGL E a y) ξ := e1
    _ ≤ max B2 0 * (B0 * (1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ +
        ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖) ^ N * ht (g * p) ξ) :=
        mul_le_mul_of_nonneg_left e2 (le_max_right _ _)
    _ ≤ max B2 0 * (B0 * (1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ +
        ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖) ^ N * (max B1 0 * ht g ξ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 (mul_nonneg hB0 hP)) (le_max_right _ _)
    _ = _ := by ring

theorem chain {t : ℝ} (ht : 0 < t) (ha : 0 < a) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hs : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) (hp : ∏ i, r i = 1) :
    (∀ i, r i ≤ (max 1 t⁻¹) ^ a * r ⟨0, ha⟩) ∧ (∀ i, r ⟨a - 1, by omega⟩ ≤ (max 1 t⁻¹) ^ a * r i) ∧
      1 ≤ (max 1 t⁻¹) ^ a * r ⟨0, ha⟩ ∧ r ⟨a - 1, by omega⟩ ≤ (max 1 t⁻¹) ^ a := by
  set T := max 1 t⁻¹ with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTa : 1 ≤ T ^ a := one_le_pow₀ hT1
  have h1 : ∀ i, r i ≤ T ^ a * r ⟨0, ha⟩ := fun i => by
    have := CuspidalSpectrum.le_pow_mul_of_siegel ht hr hs (i : ℕ) ⟨0, ha⟩ i (by simp)
    exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 i.2.le) (hr _).le)
  have h2 : ∀ i, r ⟨a - 1, by omega⟩ ≤ T ^ a * r i := fun i => by
    have := CuspidalSpectrum.le_pow_mul_of_siegel ht hr hs (a - 1 - i) i ⟨a - 1, by omega⟩ (by simp; omega)
    exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 (by omega)) (hr _).le)
  refine ⟨h1, h2, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hlt : ∏ i, r i < 1 := by
      calc ∏ i, r i ≤ ∏ _i : Fin a, T ^ a * r ⟨0, ha⟩ :=
            Finset.prod_le_prod (fun i _ => (hr i).le) fun i _ => h1 i
        _ = (T ^ a * r ⟨0, ha⟩) ^ a := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ < 1 := pow_lt_one₀ (by have := hr ⟨0, ha⟩; positivity) hc (by omega)
    rw [hp] at hlt
    exact lt_irrefl _ hlt
  · by_contra hc
    push_neg at hc
    have hT0 : 0 < T ^ a := by positivity
    have hlt : 1 < ∏ i, r i := by
      have h3 : ∀ i, r ⟨a - 1, by omega⟩ / T ^ a ≤ r i := fun i => by
        rw [div_le_iff₀ hT0, mul_comm]; exact h2 i
      calc (1 : ℝ) < (r ⟨a - 1, by omega⟩ / T ^ a) ^ a :=
            one_lt_pow₀ ((one_lt_div hT0).2 hc) (by omega)
        _ = ∏ _i : Fin a, r ⟨a - 1, by omega⟩ / T ^ a := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i, r i := Finset.prod_le_prod (fun i _ => by have := hr ⟨a - 1, by omega⟩; positivity)
            fun i _ => h3 i
    rw [hp] at hlt
    exact lt_irrefl _ hlt

theorem combine {C B K P Q H v : ℝ} {N M : ℕ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hP : 0 < P) (hQ : 0 < Q)
    (hH : 0 ≤ H) (hPQ : P * Q ≤ K) (hlow : 1 ≤ B * P ^ N * H) (hv : v ≤ C * Q ^ (N * M)) :
    v ≤ C * (K ^ N * B) ^ M * H ^ M := by
  have hK : 0 ≤ K := le_trans (by positivity) hPQ
  have h1 : Q ^ N ≤ K ^ N * B * H := by
    calc Q ^ N ≤ Q ^ N * (B * P ^ N * H) := le_mul_of_one_le_right (by positivity) hlow
      _ = (P * Q) ^ N * B * H := by ring
      _ ≤ K ^ N * B * H := by gcongr
  calc v ≤ C * Q ^ (N * M) := hv
    _ = C * (Q ^ N) ^ M := by rw [pow_mul]
    _ ≤ C * (K ^ N * B * H) ^ M := by gcongr
    _ = C * (K ^ N * B) ^ M * H ^ M := by rw [mul_pow]; ring

end CuspDecayShortRow

end PositivityTheory.AdelicQuotientData

namespace PositivityTheory.AdelicQuotientData

namespace CuspDecayShortRow

set_option linter.unusedSectionVars false

open GroundTheory.Global in
theorem siegel {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ha : 0 < a)
    (hsc : ∀ s t, splitCentre E a (s + t) = splitCentre E a s * splitCentre E a t)
    (hcomm : ∀ t (g : GA E a), splitCentre E a t * g = g * splitCentre E a t) :
    ∃ ω : Set (GA E a), IsCompact ω ∧
      ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) ∧
      (∀ b ∈ ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) ∧ ∃ t : ℝ, 0 < t ∧
      ∀ g : GA E a, ∃ (γ : GL (Fin a) E) (c : ℝ) (b : GA E a) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (kk : GA E a),
        b ∈ ω ∧ (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ ∏ i, r i = 1 ∧
        kk ∈ (maxCompact (K := E) (n := a)) ∧
        ratGL E a γ * g = splitCentre E a c * (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk) := by
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : a * d ≠ 0 := (Nat.mul_pos ha hd0).ne'
  set m : AdelicGLn.AdelicGL E a → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (a * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a :=
    fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  have hsc' : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits a).comp
    (continuous_pi fun _ => GlobalTheory.CuspBoundSiegel.continuous_posIdele_pos.comp hsc')).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [GlobalTheory.CuspBoundSiegel.ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  refine ⟨f '' ω, hω'c, hω'B, hω'1, t, ht, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← GlobalTheory.CuspBoundSiegel.posIdele_mul]
    exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E a γ * g = _
    rw [e, hD, GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a hρpos, hsc]
    simp only [hf, GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a (hspos b)]
    symm
    calc splitCentre E a (Real.log (s b)) * splitCentre E a (Real.log ρ) *
          (b * (splitCentre E a (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E a (Real.log (s b)) * (splitCentre E a (Real.log ρ) *
            (b * (splitCentre E a (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E a (Real.log (s b)) * ((b * (splitCentre E a (Real.log (s b)))⁻¹) *
            splitCentre E a (Real.log ρ)) * D' * k := by rw [hcomm (Real.log ρ)]
      _ = (splitCentre E a (Real.log (s b)) * b) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E a (Real.log (s b))) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by rw [hcomm (Real.log (s b)) b]
      _ = b * (splitCentre E a (Real.log ρ) * D') * k := by group
  refine ⟨γ, Real.log (s b) + Real.log ρ, f b, r', hr'pos, k, ⟨b, hb, rfl⟩, fun i j hij => ?_, ?_, hk, key⟩
  · simp only [hr']
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le
  · simp only [hr']
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
      div_self hprod.ne']

end CuspDecayShortRow

end PositivityTheory.AdelicQuotientData

namespace PositivityTheory.AdelicQuotientData

namespace CuspDecayShortRow

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem lam_prod (ha : 0 < a) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (L : ℕ) :
    ∏ i, r i ^ ((Pi.single (⟨a - 1, by omega⟩ : Fin a) (L : ℝ) + Pi.single (⟨0, ha⟩ : Fin a) (-(L : ℝ)) : Fin a → ℝ) i) =
      (r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩) ^ L := by
  simp only [Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => Real.rpow_add (hr i) _ _), Finset.prod_mul_distrib]
  rw [Finset.prod_eq_single (⟨a - 1, by omega⟩ : Fin a)
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Real.rpow_zero]) (by simp),
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Real.rpow_zero]) (by simp)]
  rw [Pi.single_eq_same, Pi.single_eq_same, Real.rpow_neg (hr _).le, Real.rpow_natCast, Real.rpow_natCast,
    div_pow, div_eq_mul_inv]

theorem invT_split (hadd : ∀ s t, splitCentre E a (s + t) = splitCentre E a s * splitCentre E a t) (c : ℝ) :
    invT (splitCentre E a c) = splitCentre E a (-c) := by
  have h0 : splitCentre E a 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have e : splitCentre E a c = diagUnits a (fun _ : Fin a => posIdele (K := E) (Real.exp c) (Real.exp_pos c)) := by
    rw [GlobalTheory.CuspBoundSiegel.diagUnits_posIdele a (Real.exp_pos c), Real.log_exp]
  rw [e, invT_diag, ← e]
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← hadd, add_neg_cancel, h0]

theorem core_gen (hH : H0) (ha : 0 < a) (φ : Sm E a) (hφ : IsCuspForm φ)
    (hone : ∀ η : Fin a → E, η ≠ 0 → 1 ≤ ht (1 : GA E a) η)
    {ω : Set (GA E a)} (hω : IsCompact ω)
    (hωB : ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)))
    (hω1 : ∀ b ∈ ω, (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1)
    {t : ℝ} (ht0 : 0 < t) {C1 C2 : Set (GA E a)} (h1 : IsCompact C1) (h2 : IsCompact C2) (F : GA E a → ℂ)
    (hdec : ∀ g (ξ : Fin a → E), ξ ≠ 0 → ∃ (b : GA E a) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (kk xh : GA E a)
      (η : Fin a → E) (p q : GA E a) (y : GL (Fin a) (Cinf E)),
      b ∈ ω ∧ (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ ∏ i, r i = 1 ∧
      kk ∈ (maxCompact (K := E) (n := a)) ∧
      F g = φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk) ∧ η ≠ 0 ∧ ht g ξ = ht xh η ∧
      p ∈ C1 ∧ q ∈ C2 ∧ xh * p * infGL E a y * q = 1 ∧
      (y = GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a) ∨
       y = (GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a))⁻¹)) :
    Dec F := by
  intro M
  obtain ⟨B, N, hB, hlow⟩ := low hH h1 h2
  have hpos := (hH E a).1
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspRapidDecaySiegelGL E a φ hφ ω hω hωB hω1 t ht0
    (Pi.single (⟨a - 1, by omega⟩ : Fin a) ((N * M : ℕ) : ℝ) + Pi.single (⟨0, ha⟩ : Fin a) (-((N * M : ℕ) : ℝ)))
  set T := (max 1 t⁻¹) ^ a with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (le_max_left _ _)
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  refine ⟨max C 0 * ((T + 2 * T ^ 2) ^ N * B) ^ M, fun g ξ hξ => ?_⟩
  obtain ⟨b, r, hr, kk, xh, η, p, q, y, hb, hs, hprod, hk, hF, hη, hht, hp, hq, hone', hy⟩ := hdec g ξ hξ
  obtain ⟨c1, c2, c3, c4⟩ := chain ht0 ha r hr hs hprod
  rw [← hT] at c1 c2 c3 c4
  have hr0 : 0 < r ⟨0, ha⟩ := hr _
  have hrl : 0 < r ⟨a - 1, by omega⟩ := hr _
  have n1 : ‖(Matrix.of.symm (GeneralLinearGroup.map (pInf E)
      (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a)).val : LieI (InfinitePlace E) a)‖ ≤
      T * r ⟨0, ha⟩ :=
    norm_diag_le _ _ (by positivity) fun i => (norm_pInf_posIdele _ _).trans (c1 i)
  have n2 : ‖(Matrix.of.symm (GeneralLinearGroup.map (pInf E)
      (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a))⁻¹.val : LieI (InfinitePlace E) a)‖ ≤
      T / r ⟨a - 1, by omega⟩ := by
    have e : (GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a))⁻¹ =
        GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => (posIdele (K := E) (r i) (hr i))⁻¹) : GA E a) := by
      rw [← map_inv, ← map_inv]; rfl
    rw [e]
    refine norm_diag_le _ _ (by positivity) fun i => (norm_pInf_posIdele_inv _ _).trans ?_
    rw [le_div_iff₀ hrl, inv_mul_le_iff₀ (hr i), mul_comm]
    exact c2 i
  have hyP : 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) a)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) a)‖ ≤
      1 + T * r ⟨0, ha⟩ + T / r ⟨a - 1, by omega⟩ := by
    rcases hy with rfl | rfl
    · linarith
    · rw [inv_inv]; linarith
  have hP0 : 0 < 1 + T * r ⟨0, ha⟩ + T / r ⟨a - 1, by omega⟩ := by positivity
  have hH0 : 0 ≤ ht g ξ := (hpos g ξ hξ).le
  have hlowb : 1 ≤ B * (1 + T * r ⟨0, ha⟩ + T / r ⟨a - 1, by omega⟩) ^ N * ht g ξ := by
    have h := hlow p hp q hq y xh η hη
    rw [hone', ← hht] at h
    calc (1 : ℝ) ≤ ht 1 η := hone η hη
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hyP N) hB) hH0
  have hPQ : (1 + T * r ⟨0, ha⟩ + T / r ⟨a - 1, by omega⟩) * (r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩) ≤
      T + 2 * T ^ 2 := by
    have d1 : r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩ ≤ T := by rw [div_le_iff₀ hr0]; exact c1 _
    have d2 : T * r ⟨a - 1, by omega⟩ ≤ T * T := mul_le_mul_of_nonneg_left c4 hT0
    have d3 : T / r ⟨0, ha⟩ ≤ T * T := by rw [div_le_iff₀ hr0]; nlinarith
    have e : (1 + T * r ⟨0, ha⟩ + T / r ⟨a - 1, by omega⟩) * (r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩) =
        r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩ + T * r ⟨a - 1, by omega⟩ + T / r ⟨0, ha⟩ := by
      field_simp
    rw [e]; nlinarith
  have hv : ‖F g‖ ≤ max C 0 * (r ⟨a - 1, by omega⟩ / r ⟨0, ha⟩) ^ (N * M) := by
    rw [hF]
    have := hC b hb r hr hs hprod kk hk
    rw [lam_prod ha r hr] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  exact combine (le_max_right _ _) hB hP0 (div_pos hrl hr0) hH0 hPQ hlowb hv

theorem core (hD : D0) (hH : H0) (ha : 0 < a) (φ : Sm E a) (hφ : IsCuspForm φ)
    (hA : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) :
    Dec φ.1 ∧ Dec fun g => φ.1 (invT g) := by
  obtain ⟨-, -, -, hrat, -, -, -, hcomm, hadd, -, -⟩ := hD E a
  obtain ⟨-, hhrat, hhcen, -, -, -, hinvT⟩ := hH E a
  obtain ⟨ω, hω, hωB, hω1, t, ht0, hsieg⟩ := siegel a ha hadd hcomm
  have hmc : IsCompact (maxCompact (K := E) (n := a) : Set (GA E a)) := isCompact_maxCompact
  have hDt1 : Dt (1 : GA E a) = 1 := by have := hrat 1; rwa [map_one] at this
  have hone : ∀ η : Fin a → E, η ≠ 0 → 1 ≤ ht (1 : GA E a) η := fun η hη => by
    unfold ht; rw [hDt1, Real.one_rpow, div_one]; exact one_le_height_one hη
  constructor
  · refine core_gen hH ha φ hφ hone hω hωB hω1 ht0 (hmc.image continuous_inv) (hω.image continuous_inv) _
      fun g ξ hξ => ?_
    obtain ⟨γ, c, b, r, hr, kk, hb, hs, hp, hk, he⟩ := hsieg g
    have hη := vecMul_ne_zero γ⁻¹ hξ
    refine ⟨b, r, hr, kk, b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk, ξ ᵥ* (γ⁻¹).val, kk⁻¹, b⁻¹,
      (GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a))⁻¹,
      hb, hs, hp, hk, ?_, hη, ?_, ⟨kk, hk, rfl⟩, ⟨b, hb, rfl⟩, ?_, Or.inr rfl⟩
    · rw [← hA c (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk), ← he, hφ.1.left]
    · have e1 : g = ratGL E a γ⁻¹ * (splitCentre E a c * (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk)) := by
        rw [← he, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      conv_lhs => rw [e1]
      rw [hhrat, hhcen _ _ _ hη]
    · rw [map_inv, ← diag_eq_infGL]; group
  · refine core_gen hH ha φ hφ hone hω hωB hω1 ht0 (hmc.image continuous_invT.inv) (hω.image continuous_invT.inv) _
      fun g ξ hξ => ?_
    obtain ⟨γ, c, b, r, hr, kk, hb, hs, hp, hk, he⟩ := hsieg (invT g)
    obtain ⟨γ', hγ'⟩ := invT_ratGL γ⁻¹
    have hη := vecMul_ne_zero γ' hξ
    refine ⟨b, r, hr, kk, invT (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk), ξ ᵥ* γ'.val,
      (invT kk)⁻¹, (invT b)⁻¹,
      GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) : GA E a),
      hb, hs, hp, hk, ?_, hη, ?_, ⟨kk, hk, rfl⟩, ⟨b, hb, rfl⟩, ?_, Or.inl rfl⟩
    · show φ.1 (invT g) = _
      rw [← hA c (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk), ← he, hφ.1.left]
    · have e1 : invT g = ratGL E a γ⁻¹ * (splitCentre E a c *
          (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk)) := by
        rw [← he, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      have e2 : g = ratGL E a γ' * (splitCentre E a (-c) *
          invT (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * kk)) := by
        have e3 := congrArg invT e1
        rw [(hinvT g g).2, (hinvT _ _).1, (hinvT (splitCentre E a c) _).1, hγ', invT_split hadd] at e3
        exact e3
      conv_lhs => rw [e2]
      rw [hhrat, hhcen _ _ _ hη]
    · rw [(hinvT _ _).1, (hinvT _ _).1, invT_diag, ← diag_eq_infGL]; group

theorem dec_mul (hH : H0) {F : GA E a → ℂ} (hF : Dec F) (h : GA E a) : Dec fun g => F (g * h) := by
  obtain ⟨hpos, -, -, hcpt, -⟩ := hH E a
  obtain ⟨B, hB⟩ := hcpt {h} isCompact_singleton
  intro M
  obtain ⟨C, hC⟩ := hF M
  refine ⟨max C 0 * (max B 0) ^ M, fun g ξ hξ => ?_⟩
  have h1 : ht (g * h) ξ ≤ max B 0 * ht g ξ :=
    (hB h rfl g ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos g ξ hξ).le)
  calc ‖F (g * h)‖ ≤ C * ht (g * h) ξ ^ M := hC _ ξ hξ
    _ ≤ max C 0 * ht (g * h) ξ ^ M :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hpos _ ξ hξ).le _)
    _ ≤ max C 0 * (max B 0 * ht g ξ) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _ ξ hξ).le h1 M) (le_max_right _ _)
    _ = max C 0 * (max B 0) ^ M * ht g ξ ^ M := by ring

end CuspDecayShortRow

theorem cusp_decay_short_row_of : D0 → H0 → CuspDecayShortRowColumn := by
  intro hD hH E _ _ _ k hk π hπ φ hφ h
  obtain ⟨-, -, -, -, -, -, hinvT⟩ := hH E k
  obtain ⟨h1, h2⟩ := CuspDecayShortRow.core hD hH hk φ (π.cusp φ hφ) (hπ φ hφ)
  refine ⟨CuspDecayShortRow.dec_mul hH h1 h, ?_⟩
  have e : (fun g => φ.1 (invT g * h)) = fun g => (fun g => φ.1 (invT g)) (g * invT h) := by
    funext g
    simp only [(hinvT g (invT h)).1, (hinvT h h).2]
  rw [e]
  exact CuspDecayShortRow.dec_mul hH h2 (invT h)

end PositivityTheory.AdelicQuotientData

end
