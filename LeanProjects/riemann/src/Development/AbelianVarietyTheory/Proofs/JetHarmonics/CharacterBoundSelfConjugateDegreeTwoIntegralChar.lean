import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvExpLinearPartIntegralCharMemIntegralGerm

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CharSquare

open GlobalTheory.RowLawSquare

theorem tsum_alt (l : ℝ) (hl : 1 < l) (a b : ℝ) (m : ℕ → ℝ) (h0 : ∀ k, m (2 * k) = a) (h1 : ∀ k, m (2 * k + 1) = b) :
    ∑' i : ℕ, l ^ (-((i : ℝ) + 1)) * m i = (a * l + b) / (l ^ 2 - 1) := by
  have hp : 0 < l := by linarith
  have hq : (l ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hg := hasSum_geometric_of_lt_one (r := (l ^ 2)⁻¹) (by positivity) hq
  have e : ∀ i : ℕ, l ^ (-((i : ℝ) + 1)) = (l ^ (i + 1))⁻¹ := fun i => by
    rw [Real.rpow_neg hp.le, ← Real.rpow_natCast]; push_cast; rfl
  have hne : l ^ 2 - 1 ≠ 0 := by nlinarith
  have he : HasSum (fun k : ℕ => l ^ (-(((2 * k : ℕ) : ℝ) + 1)) * m (2 * k)) (l⁻¹ * a * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left (l⁻¹ * a))
    rw [e, h0, pow_succ, pow_mul, inv_pow]; field_simp
  have ho : HasSum (fun k : ℕ => l ^ (-(((2 * k + 1 : ℕ) : ℝ) + 1)) * m (2 * k + 1))
      ((l ^ 2)⁻¹ * b * (1 - (l ^ 2)⁻¹)⁻¹) := by
    refine Eq.mp (congrArg (HasSum · _) (funext fun k => Eq.symm ?_)) (hg.mul_left ((l ^ 2)⁻¹ * b))
    rw [e, h1, add_assoc, pow_add, pow_mul, inv_pow]; field_simp
  rw [(HasSum.even_add_odd (f := fun i : ℕ => l ^ (-((i : ℝ) + 1)) * m i) he ho).tsum_eq]
  field_simp

theorem alt_le (l : ℝ) (hl : 1 < l) (n j j' : ℝ) (hj : 0 ≤ j) (hj' : 0 ≤ j') :
    ((n + j) * l + j') / (l ^ 2 - 1) ≤ n * (l / (l ^ 2 - 1)) + (j + j') / (l - 1) := by
  have h1 : 0 < l - 1 := by linarith
  have h2 : 0 < l ^ 2 - 1 := by nlinarith
  have e : (j + j') / (l - 1) = (j + j') * (l + 1) / (l ^ 2 - 1) := by
    field_simp; ring
  rw [e, ← mul_div_assoc, ← add_div]
  refine div_le_div_of_nonneg_right ?_ h2.le
  nlinarith

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem exists_unit (a : ZMod d) (g : Fin 2) : ∃ col, V.v (p.gm a col g) = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ r, 0 < V.v (p.gm (a + p.hd) r (1 - g) * p.gm a r g) := fun r => by
    have h1 : (0 : WithTop ℝ) ≤ V.v (p.gm (a + p.hd) r (1 - g)) := gm_int Y p _ _ _
    have h2 : (0 : WithTop ℝ) ≤ V.v (p.gm a r g) := gm_int Y p _ _ _
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (lt_of_le_of_ne h2 (hc r).symm) (le_add_of_nonneg_left h1)
  have hg : 1 - g ≠ g := by fin_cases g <;> decide
  have e := p.gm_hyp a (1 - g) g
  rw [if_neg hg, Fin.sum_univ_two] at e
  have := V.v.map_lt_add (hpos 0) (hpos 1)
  rw [e, V.v.map_one] at this
  exact lt_irrefl _ this

omit [CharZero C] in
theorem inCol_eq (col : Fin 2) (f : PS C 1 dd) : inCol col (un1 f) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) f :=
  subst_singlePointUncurry (fun _ => MvPowerSeries.constantCoeff_X _) f

omit [CharZero C] in
theorem intS_inCol (col : Fin 2) {f : PS C 1 dd} (hf : IntS V f) : IntS V (inCol col (un1 f)) := by
  rw [inCol_eq]
  exact intS_subst V (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X V _) hf

omit [CharZero C] in

theorem coeff_inCol (col : Fin 2) (f : PS C 1 dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (inCol col (un1 f)) = MvPowerSeries.coeff μ
      (MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X (col, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := by
  have hS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd =>
      (MvPowerSeries.X (col, q.2) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  rw [inCol_eq, coeff_rename_low (fun q : Fin 1 × Fin dd => (col, q.2)) (N := 1)
    (g := MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i, Pdiv.ChartF.dl f i • (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)) ?_ μ hμ]
  · rw [← MvPowerSeries.coe_substAlgHom (R := C) hS, map_add, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hS, MvPowerSeries.subst_X hS]
    congr 2
    rw [← MvPowerSeries.coe_substAlgHom (R := C) hS]
    exact (MvPowerSeries.substAlgHom (R := C) hS).commutes _
  · intro e he
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simp
    · obtain ⟨⟨s, i⟩, rfl⟩ : ∃ q, e = Finsupp.single q 1 := finsupp_deg_one e h
      obtain rfl : s = 0 := Subsingleton.elim _ _
      simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, Pdiv.ChartF.dl]

omit [CharZero C] in
theorem cc_inCol (col : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.constantCoeff (inCol col (un1 f)) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_inCol col f 0 (by simp)]
  simp

omit [CharZero C] in
theorem lin_inCol (col : Fin 2) (f : PS C 1 dd) (x : Fin 2 × Fin dd) :
    MvPowerSeries.coeff (Finsupp.single x 1) (inCol col (un1 f)) = if x.1 = col then Pdiv.ChartF.dl f x.2 else 0 := by
  rw [coeff_inCol col f _ (by simp)]
  obtain ⟨r, i⟩ := x
  by_cases h : r = col <;>
    simp [MvPowerSeries.coeff_C, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, h]

theorem lin_u (col g : Fin 2) (f : PS C 1 dd) (x : I0) :
    ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 f)) * (Y.rawSelf p).u g x i =
      p.gm (p.ty0 x) col g * ∑ i, Pdiv.ChartF.dl f i * p.e x i := by
  simp only [lin_inCol, Fintype.sum_prod_type, ite_mul, zero_mul, FBChart.rawSelf]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem char_inCol (col : Fin 2) {f : PS C 1 dd} (hf : Pdiv.ChartF.IsCh Y.B.G.F f) :
    MvPowerSeries.subst (addP (Y.rawSelf p) (gp C _ (0 : Fin 2)) (gp C _ 1)) (inCol col (un1 f)) =
      MvPowerSeries.subst (gp C _ (0 : Fin 2)) (inCol col (un1 f)) *
        MvPowerSeries.subst (gp C _ (1 : Fin 2)) (inCol col (un1 f)) := by
  have z := fun (j : Fin 2) => zc_col (zc_gp (C := C) (κ := Fin 2 × Fin dd) j) col
  have h2 := zc2 (z 0) (z 1)
  have e := congrArg (sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col]) hf.2
  have hm : ∀ f g : PS C 2 dd, sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] (f * g) =
      sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] f *
        sb ![RowLawSquare.colOf (gp C _ (0 : Fin 2)) col, RowLawSquare.colOf (gp C _ 1) col] g :=
    fun f g => MvPowerSeries.subst_mul (hasSubst_sb h2) f g
  rw [substPointsPowerSeries_eval_one h2 (zc_addOf Y 0 1), sb_addOf Y h2, hm, substPointsPowerSeries_eval_one h2 (zc_pt 0), substPointsPowerSeries_eval_one h2 (zc_pt 1), sb_pt' h2,
    sb_pt' h2] at e
  rw [subst_inCol (zc_addP Y p (zc_gp _) (zc_gp _)), subst_inCol (zc_gp _), subst_inCol (zc_gp _)]
  have e2 := col_addP Y p (zc_gp (C := C) (0 : Fin 2)) (zc_gp 1) col
  unfold RowLawSquare.colOf at e2
  rw [e2]
  exact e

end Chart

theorem isSat_fst {C : Type} [Field C] {V : VF C} {m : ZMod 2 → ℕ} {n : ℕ} {w : Fin n → (Σ s : ZMod 2, Fin (m s)) → C}
    (hw : IsSat V w) (h1 : ∀ q i, w q ⟨1, i⟩ = 0) : IsSat V fun q i => w q ⟨0, i⟩ := by
  obtain ⟨hi, u, hu, e⟩ := hw
  refine ⟨fun _ _ => hi _ _, fun i q => u ⟨0, i⟩ q, fun _ _ => hu _ _, fun q q' => ?_⟩
  rw [← e q q', Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
    Finset.sum_pair (by decide)]
  simp [h1]

theorem chSt_rawSelf : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → lab.RankOK Dw → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (p o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hst T io y C3 C _ _ V ι hι k Y hY hy Orb _ lab hA hR p hp o Hc g a hbig w hw hw0
  have ha : a = ((g.val : ℕ) : ZMod 2) := (hp.big o g a).1 hbig
  have h1 : ∀ q i, w q ⟨1, i⟩ = 0 := fun q i => hw0 q _ (by
    simp only [FBChart.rawSelf, hp.ty0, hp.hd, ha]
    fin_cases g <;> decide)
  obtain ⟨χ, hχ, hdet⟩ := GlobalTheory.T.exists_characters_bounded_minor_eigenspace hup E H Dw lv Xo c hst T io y C3 C V ι hι k Y hY hy hA.unr 2 (lab.tau o)
    (fun s s' h => (Prod.ext_iff.1 (hA.inj (a₁ := (o, s)) (a₂ := (o, s')) h)).2) (hA.frob o) 0 _ _ (isSat_fst hw h1)
  obtain ⟨col, hcol⟩ := exists_unit Y (p o) 0 g
  refine ⟨fun ρ x => ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (inCol col (un1 (χ ρ))) *
    (Y.rawSelf (p o)).u g x i, fun ρ x => ?_, fun S t ht ρ => ?_, fun _ => ?_, fun hall => ?_⟩
  · exact VF.Ge.sum fun i _ => (intS_inCol col (hχ ρ).1 _).mul_int
      ((rlaw_rawSelf C V _ _ Y 2 _ (p o)).uint g x i)
  · exact GlobalTheory.RowLaw.upG_mvExp_char_mem_intGerm C V 2 _ _ _ (rlaw_rawSelf C V _ _ Y 2 _ (p o)) Hc _
      (intS_inCol col (hχ ρ).1) (by rw [cc_inCol, (hχ ρ).2.1]) (char_inCol Y (p o) col (hχ ρ).2) g S t ht
  · have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hm : ∀ i : ℕ, ComplexEmbedding.conjugate (lab.tau o (0 + ((i + 1 : ℕ) : ZMod 2))) = lab.tau o i := fun i => by
      rw [← hA.conj]
      congr 1
      push_cast
      generalize (i : ZMod 2) = z
      revert z
      decide
    simp only [hm] at hdet
    rw [tsum_alt V.l hl ((lab.n : ℝ) + lab.j) lab.j' (fun i : ℕ => (Dw.mult (lab.tau o i) : ℝ))
      (fun k => by
        have : ((2 * k : ℕ) : ZMod 2) = 0 := by push_cast; exact mul_eq_zero_of_left rfl _
        simp only [this, (hR o).1, Nat.cast_add])
      (fun k => by
        have : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
          push_cast; rw [mul_eq_zero_of_left (show (2 : ZMod 2) = 0 from rfl), zero_add]
        simp only [this, (hR o).2])] at hdet
    have hM : (Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, MvPowerSeries.coeff (Finsupp.single i 1)
        (inCol col (un1 (χ ρ))) * (Y.rawSelf (p o)).u g x i) * w q x) =
        (p o).gm 0 col g • Matrix.of fun ρ q : Fin (Y.rawSelf (p o)).n => ∑ x, (∑ i, Pdiv.ChartF.dl (χ ρ) i *
          ι (chartUnitVectors C3 ⟨lab.tau o 0, x⟩ i)) * w q ⟨0, x⟩ := by
      ext ρ q
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, lin_u, hp.ty0, hp.e]
      rw [Fintype.sum_sigma, show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
      simp only [h1, mul_zero, Finset.sum_const_zero, add_zero]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [hM, Matrix.det_smul, V.v.map_mul, V.v.map_pow, hcol, smul_zero, zero_add]
    refine hdet.trans (WithTop.coe_le_coe.2 ?_)
    simp only [FBChart.rawSelf, hp.n, hp.j, hp.j', Formalism.IncomingBounds.gam]
    exact alt_le _ hl _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact absurd (((hp.big o g 0).1 (hall 0)).trans ((hp.big o g 1).1 (hall 1)).symm) (by decide)

end GlobalTheory.CharSquare
