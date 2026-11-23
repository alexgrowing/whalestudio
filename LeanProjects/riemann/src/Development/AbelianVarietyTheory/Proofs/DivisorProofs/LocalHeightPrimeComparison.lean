import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointResultOfFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdExpoSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevelStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf

set_option autoImplicit false

noncomputable section

open Formalism.MainNotions.DIV.Cons (intO)
open Formalism.L2.Pj GlobalTheory.HalfGeo GlobalTheory.LineNorm MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.EqHalf.EigNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

theorem isLeast_ball {K : Type} [NormedField K] [IsUltrametricDist K] {n g : ℕ} (M : Matrix (Fin n) (Fin g) K)
    (hM : Function.Injective M.mulVec) (S : Finset (Fin g)) (i : Fin g) (hi : i ∉ S) :
    IsLeast {r : ℝ | ∃ cf : Fin g → K, cf i ≠ 0 ∧ (∀ l, l ∉ S → l ≠ i → cf l = 0) ∧ (∀ m, ‖M.mulVec cf m‖ ≤ 1) ∧
      r = ‖cf i‖⁻¹} (colMinor (NormedField.toAbsoluteValue K) M (insert i S) /
        colMinor (NormedField.toAbsoluteValue K) M S) := by
  set w := NormedField.toAbsoluteValue K with hw
  have hwa : ∀ x, w x = ‖x‖ := fun _ => rfl
  have hna : IsNonarchimedean w := fun a b => IsUltrametricDist.norm_add_le_max a b
  obtain ⟨hpos, hq⟩ := (GlobalTheory.ConstLat.MinorQuot.colMinor_pos_and_quotient w hna M).2 hM
  obtain ⟨hle, u, hu1, hu, he⟩ := hq S i hi
  constructor
  · have hne : M.mulVec u ≠ 0 := by
      intro h0
      have : u = 0 := hM (by rw [h0, Matrix.mulVec_zero])
      rw [this] at hu1
      exact zero_ne_one hu1
    obtain ⟨r, hr⟩ := Function.ne_iff.1 hne
    haveI : Nonempty (Fin n) := ⟨r⟩
    obtain ⟨m₀, hm₀⟩ := exists_eq_ciSup_of_finite (f := fun m => w (M.mulVec u m))
    have hs : supN w (M.mulVec u) = ‖M.mulVec u m₀‖ := hm₀.symm
    have h0 : 0 < ‖M.mulVec u m₀‖ := hs ▸ (w.pos hr).trans_le (le_supN w _ r)
    have h0' : M.mulVec u m₀ ≠ 0 := norm_pos_iff.1 h0
    refine ⟨(M.mulVec u m₀)⁻¹ • u, by simp [hu1, h0'], fun l h1 h2 => by simp [hu l h1 h2], fun m => ?_, ?_⟩
    · rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ h0, _root_.mul_one, ← hs]
      exact le_supN w _ m
    · rw [he, hs, mul_div_cancel_left₀ _ (hpos S).ne']
      simp [hu1]
  · rintro r ⟨cf, h1, h2, h3, rfl⟩
    rw [div_le_iff₀ (hpos S), mul_comm]
    refine (hle ((cf i)⁻¹ • cf) (by simp [h1]) fun l a b => by simp [h2 l a b]).trans
      (mul_le_mul_of_nonneg_left (supN_le w (inv_nonneg.2 (norm_nonneg _)) fun m => ?_) (hpos S).le)
    rw [hwa, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg _)) (h3 m)

theorem log_colMinor {K L : Type} [Field K] [NormedField L] (w : AbsoluteValue K ℝ) (io : K →+* L) {c : ℝ} (hc : 0 < c)
    (hw : ∀ z, w z = ‖io z‖ ^ c) {n g : ℕ} (M : Matrix (Fin n) (Fin g) K) (S : Finset (Fin g))
    (h : 0 < colMinor (NormedField.toAbsoluteValue L) (M.map io) S) :
    Real.log (colMinor w M S) = c * Real.log (colMinor (NormedField.toAbsoluteValue L) (M.map io) S) := by
  have hd : ∀ σ : S → Fin n, io (M.submatrix σ Subtype.val).det = ((M.map io).submatrix σ Subtype.val).det := fun σ => by
    rw [RingHom.map_det]
    rfl
  rw [← Real.log_rpow h]
  congr 1
  unfold colMinor at h ⊢
  rcases isEmpty_or_nonempty (S → Fin n) with h0 | h0
  · rw [Real.iSup_of_isEmpty] at h
    exact absurd h (lt_irrefl _)
  obtain ⟨σ, hσ⟩ := exists_eq_ciSup_of_finite
    (f := fun σ : S → Fin n => NormedField.toAbsoluteValue L ((M.map io).submatrix σ Subtype.val).det)
  refine le_antisymm (ciSup_le fun τ => ?_) ?_
  · rw [hw, hd]
    exact Real.rpow_le_rpow (norm_nonneg _) (le_ciSup
      (f := fun σ : S → Fin n => NormedField.toAbsoluteValue L ((M.map io).submatrix σ Subtype.val).det)
      (Set.finite_range _).bddAbove τ) hc.le
  · rw [← hσ]
    refine le_of_eq_of_le ?_ (le_ciSup (f := fun σ : S → Fin n => w (M.submatrix σ Subtype.val).det)
      (Set.finite_range _).bddAbove σ)
    rw [hw, hd]
    rfl

end Linear

section Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem exists_basis {p : ℕ} [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) :
    ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e := by
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  obtain ⟨⟨V, hV⟩, g, e, hz, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t X (𝟙 X) (x (IsLocalRing.closedPoint _))
  obtain ⟨φ, hφ⟩ := GlobalTheory.ShFam.Pad.Pull.exists_fromSpec hV x (Scheme.preimage_eq_top_of_closedPoint_mem x hz).ge
  have h := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t φ he
  rw [Category.comp_id, hφ] at h
  exact ⟨g, _, h⟩

theorem ball [IsLocallyNoetherian X] (hX : X.IsSeparated) {p : ℕ} [hp : Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X)
    {n N g : ℕ} (hn : 2 ≤ n) (χ : Fin N → TorsChar t x (p ^ n)) (hχ : Gens χ)
    (u : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (hu : ∀ l, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (u l))
    (hind : IsIndep t (spMap (intO ℂ_[p]).subtype ≫ x) u)
    (hspan : ∀ w, IsTanAtG t (spMap (intO ℂ_[p]).subtype ≫ x) w → ∃ cf, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w)
    (Mc : Matrix (Fin N) (Fin g) ℂ_[p]) (hM : DlogVals t x χ u Mc) :
    (∀ cf w, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w →
      (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ m, ‖Mc.mulVec cf m‖ ≤ 1)) ∧ Function.Injective Mc.mulVec := by
  obtain ⟨g', e, he⟩ := exists_basis (t := t) x
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  choose b hb using fun i => hspan _ (heC.1 i)
  choose h hh hh' using fun i m => hM (e i) (b i) (he.1 i) (hb i) m
  have hval : ∀ (a : Fin g' → ℂ_[p]) m, Mc.mulVec (∑ i, a i • b i) m = ∑ i, (h i m : ℂ_[p]) * a i := fun a m => by
    rw [Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hh, mul_comm]
    rfl
  have hD : ∀ m, DlogIs t p n (χ m) e fun i => h i m := fun m a v hav w hw => by
    obtain ⟨r, hr, hr'⟩ := hM v _ (GlobalTheory.LineNorm.Chart.comb_tan he.1 hav)
      (GlobalTheory.LineNorm.Chart.comb_comb hu hb (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hav)) m
    rw [hr' w hw]
    congr 1
    apply Subtype.ext
    rw [hr]
    refine (hval _ m).trans ?_
    push_cast
    rfl
  let χ₂ : Fin N → TorsChar t x (p ^ 2) := fun m => GlobalTheory.HTLevel.res (pow_dvd_pow p hn) (χ m)
  have hχ₂ : Gens χ₂ := fun c' => by
    obtain ⟨c'', hc''⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ 2) (p ^ n) (pow_ne_zero _ hp.out.ne_zero) (pow_dvd_pow p hn) c'
    obtain ⟨k, hk⟩ := hχ c''
    refine ⟨k, fun B _ _ _ w hw => ?_⟩
    obtain ⟨s, hs⟩ := pow_dvd_pow p hn
    rw [← hc'' B w hw]
    exact hk B w (by rw [hs, pow_mul, hw, one_pow])
  have hD₂ : ∀ m, DlogIs t p 2 (χ₂ m) e fun i => h i m := fun m =>
    GlobalTheory.HTLevel.dlog_down hn (χ m) (χ₂ m) (fun _ _ _ _ _ _ => rfl) he.1 (hD m)
  obtain ⟨N', c', nn, kk, hall, hkk, hF⟩ := GlobalTheory.HalfGeo.fullSt E H X t p x N χ₂ hχ₂
  have hlat := GlobalTheory.HTLevelSq.mem_latHT_iff_sq E H X t hX p x g' e he N' c' _ hall (hF g' e _ he.1 hD₂)
  have hco : ∀ cf w, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w → ∃ a,
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w ∧
        cf = ∑ i, a i • b i := fun cf w hw => by
    obtain ⟨a, ha, -⟩ := he.2 _ (intO ℂ_[p]).subtype w (GlobalTheory.LineNorm.Chart.comb_tan hu hw)
    exact ⟨a, ha, hind _ _ w hw (GlobalTheory.LineNorm.Chart.comb_comb hu hb ha)⟩
  have main : ∀ cf w, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) u cf w →
      (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ m, ‖Mc.mulVec cf m‖ ≤ 1) := fun cf w hw => by
    obtain ⟨a, ha, rfl⟩ := hco cf w hw
    rw [(hlat a w ha).1]
    simp only [GlobalTheory.HalfGeo.PointClauses.val_comb, hval]
    refine ⟨fun H m => ?_, fun H j => ?_⟩
    · simpa [hkk, Pi.single_apply] using H (kk m)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ _) (norm_nonneg _) (H m)
  refine ⟨main, fun cf cf' hcf => ?_⟩
  rw [← sub_eq_zero]
  have h0 : Mc.mulVec (cf - cf') = 0 := by rw [Matrix.mulVec_sub, hcf, sub_self]
  obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t hu (cf - cf')
  obtain ⟨a, ha, hab⟩ := hco _ w hw
  rw [hab]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_contra hne
  have hai : a i ≠ 0 := fun h => hne (by rw [h, zero_smul])
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm ℂ_[p]
  have h1 := Guard.comb_smul hu hw (y / ((p : ℂ_[p]) * a i))
  have h2 := Guard.comb_smul heC.1 ha (y / ((p : ℂ_[p]) * a i))
  have h3 := (main _ _ h1).2 fun m => by
    have : Mc.mulVec (fun k => y / ((p : ℂ_[p]) * a i) * (cf - cf') k) = (y / ((p : ℂ_[p]) * a i)) • Mc.mulVec (cf - cf') :=
      Matrix.mulVec_smul Mc (y / ((p : ℂ_[p]) * a i)) (cf - cf')
    rw [this, h0]
    simp
  have h4 := (hlat _ _ h2).2 h3 i
  have : (p : ℂ_[p]) * (y / ((p : ℂ_[p]) * a i) * a i) = y := by field_simp
  rw [this] at h4
  linarith

end Ball

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {X : Scheme.{0}} {t : SAB H X}

theorem comb_concat {k : Type} [CommRing k] {x : Sp k ⟶ X} {u : GlobalTheory.LocM.Vecs Dw t k} (hu : ∀ τ i, IsTanAtG t x (u τ i))
    (a : Letter Dw → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      (fun i => a ((letters Dw).get i)) w ↔ w = (tv (∑ y : Letter Dw, a y • GlobalTheory.LieMet.tanOf (hu y.1 y.2))).left := by
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw))]
  exact GlobalTheory.LineNorm.Chart.comb_iff (fun i => hu _ _) _ w

theorem span_concat {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X} {u : GlobalTheory.LocM.Vecs Dw t k}
    (hu : GlobalTheory.LocM.IsFrame t f x u) (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cf, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w := by
  let _ : Algebra c.F k := f.toAlgebra
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨P, hP, hPs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := k) t.act
  let m : TanM x t.G := GlobalTheory.LieMet.tanOf hw
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End k (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj P hP hPs τ m)
  choose a ha using fun τ => (hu.2 τ _ (GlobalTheory.LieMet.isTan_tv (proj ρ (embK c) α τ m))
    fun s => congrArg (fun z => (tv z).left) (hE τ s)).exists
  refine ⟨_, (comb_concat (fun τ i => (hu.1 τ i).1) (fun y => a y.1 y.2) w).2 ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_congr rfl fun τ _ =>
    (GlobalTheory.LieMet.tan_ext ((GlobalTheory.LineNorm.Chart.comb_iff (fun i => (hu.1 τ i).1) _ _).1 (ha τ))).symm, hsum]
  rfl

theorem comb_block {k : Type} [CommRing k] {x : Sp k ⟶ X} {u : GlobalTheory.LocM.Vecs Dw t k} (hu : ∀ τ i, IsTanAtG t x (u τ i))
    (τ : E →+* ℂ) (a : Letter Dw → k) (ha : ∀ y, y.1 ≠ τ → a y = 0) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (u τ) (fun j => a ⟨τ, j⟩) w ↔
      IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
        (fun i => a ((letters Dw).get i)) w := by
  rw [comb_concat hu, GlobalTheory.LineNorm.Chart.comb_iff (hu τ), Fintype.sum_sigma, Finset.sum_eq_single τ
    (fun σ _ hσ => Finset.sum_eq_zero fun i _ => by rw [ha ⟨σ, i⟩ hσ, zero_smul]) (fun h => absurd (Finset.mem_univ _) h)]

theorem lt_iff {i j : Fin (letters Dw).length} (h : ((letters Dw).get i).1 = ((letters Dw).get j).1) :
    i < j ↔ (((letters Dw).get i).2 : ℕ) < ((letters Dw).get j).2 := by
  have hp := List.pairwise_iff_get.1 (GlobalTheory.Proof.frame_combination_coeff_unique.pairwise_letters Dw)
  refine ⟨fun hij => hp i j hij h, fun hij => ?_⟩
  rcases lt_trichotomy i j with h1 | rfl | h1
  · exact h1
  · exact absurd hij (lt_irrefl _)
  · exact absurd (hp j i h1 h.symm) (not_lt.2 hij.le)

theorem grNorm_block {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X}
    {u : GlobalTheory.LocM.Vecs Dw t C} (hu : ∀ τ i, IsTanAtG t x (u τ i)) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {N : ℕ}
    (Mc : Matrix (Fin N) (Fin (letters Dw).length) C) (hM : Function.Injective Mc.mulVec)
    (hΛ : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w →
      (w ∈ Λ ↔ ∀ m, ‖Mc.mulVec cf m‖ ≤ 1)) {J : Type} (β : Fin (letters Dw).length → J)
    (hβ : ∀ i j, β i = β j ↔ ((letters Dw).get i).1 = ((letters Dw).get j).1) (i : Fin (letters Dw).length) :
    GlobalTheory.ShFam.Pad.grNorm t x Λ (u ((letters Dw).get i).1) ((letters Dw).get i).2 =
      colMinor (NormedField.toAbsoluteValue C) Mc (blkLe β i) / colMinor (NormedField.toAbsoluteValue C) Mc (blkLt β i) := by
  have hi : i ∉ blkLt β i := by simp [blkLt]
  have hins : blkLe β i = insert i (blkLt β i) := by
    ext j
    simp only [blkLe, blkLt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      exact h1.eq_or_lt.imp id fun h => ⟨h, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_rfl, rfl⟩
      · exact ⟨h1.le, h2⟩
  rw [hins, ← (isLeast_ball Mc hM _ i hi).csInf_eq]
  unfold GlobalTheory.ShFam.Pad.grNorm
  congr 1
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have he : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
  have hS : ∀ j, (j ∉ blkLt β i ∧ j ≠ i) ↔ (((letters Dw).get j).1 = ((letters Dw).get i).1 →
      (((letters Dw).get i).2 : ℕ) < ((letters Dw).get j).2) := fun j => by
    simp only [blkLt, Finset.mem_filter, Finset.mem_univ, true_and, hβ]
    constructor
    · rintro ⟨h1, h2⟩ h3
      exact (lt_iff h3.symm).1 (lt_of_le_of_ne (not_lt.1 fun h => h1 ⟨h, h3⟩) h2.symm)
    · intro h
      refine ⟨fun h1 => absurd ((lt_iff h1.2.symm).2 (h h1.2)) (not_lt.2 h1.1.le), ?_⟩
      rintro rfl
      exact lt_irrefl _ (h rfl)
  ext r
  constructor
  · rintro ⟨cf, h1, h2, ⟨w, hw, hc⟩, rfl⟩
    let a : Letter Dw → C := fun y => if h : y.1 = ((letters Dw).get i).1 then cf (h ▸ y.2) else 0
    have ha : (fun j => a ⟨((letters Dw).get i).1, j⟩) = cf := funext fun j => dif_pos rfl
    have hai : a ((letters Dw).get i) = cf ((letters Dw).get i).2 := dif_pos rfl
    refine ⟨fun j => a ((letters Dw).get j), fun h => h1 (hai.symm.trans h), fun j hj hj' => ?_, (hΛ _ w ?_).1 hw, congrArg (fun z => ‖z‖⁻¹) hai.symm⟩
    · have h3 := (hS j).1 ⟨hj, hj'⟩
      show a ((letters Dw).get j) = 0
      revert h3
      generalize (letters Dw).get j = y
      obtain ⟨τ, s⟩ := y
      intro h3
      by_cases hy : τ = ((letters Dw).get i).1
      · subst hy
        exact (dif_pos rfl).trans (h2 _ (h3 rfl))
      · exact dif_neg hy
    · exact (comb_block hu _ a (fun y hy => dif_neg hy) w).1 (ha.symm ▸ hc)
  · rintro ⟨cg, h1, h2, h3, rfl⟩
    let a : Letter Dw → C := fun y => cg (e.symm y)
    have ha : (fun j => a ((letters Dw).get j)) = cg := funext fun j => congrArg cg (e.symm_apply_apply j)
    have hai : a ((letters Dw).get i) = cg i := congrFun ha i
    have h0 : ∀ y : Letter Dw, (y.1 = ((letters Dw).get i).1 → (((letters Dw).get i).2 : ℕ) < y.2) → a y = 0 := fun y hy => by
      have h4 := (hS (e.symm y)).2 (by rw [he]; exact hy)
      exact h2 _ h4.1 h4.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t (hu ((letters Dw).get i).1) fun j => a ⟨_, j⟩
    refine ⟨fun j => a ⟨_, j⟩, fun h => h1 (hai.symm.trans h), fun k hk => h0 _ fun _ => hk, ⟨w, (hΛ cg w ?_).2 h3, hw⟩, congrArg (fun z => ‖z‖⁻¹) hai.symm⟩
    exact ha ▸ (comb_block hu _ a (fun y hy => h0 y fun h => absurd h hy) w).1 hw

end Frame

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {X : Scheme.{0}} {t : SAB H X}

theorem log_grNorm [IsLocallyNoetherian X] (hX : X.IsSeparated) {p : ℕ} [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X)
    {xC : Sp ℂ_[p] ⟶ X} (hx : spMap (intO ℂ_[p]).subtype ≫ x = xC) {n N g : ℕ} (hn : 2 ≤ n)
    (χ : Fin N → TorsChar t x (p ^ n)) (hχ : Gens χ) {f : c.F →+* ℂ_[p]} {u : GlobalTheory.LocM.Vecs Dw t ℂ_[p]}
    (hu : GlobalTheory.LocM.IsFrame t f xC u) (hg : (letters Dw).length = g) (Mc : Matrix (Fin N) (Fin g) ℂ_[p])
    (hM : DlogVals t x χ (fun i => u ((letters Dw).get (Fin.cast hg.symm i)).1 ((letters Dw).get (Fin.cast hg.symm i)).2) Mc)
    {J : Type} (β : Fin g → J)
    (hβ : ∀ i j, β i = β j ↔ ((letters Dw).get (Fin.cast hg.symm i)).1 = ((letters Dw).get (Fin.cast hg.symm j)).1)
    (i : Fin g) : (∀ S, 0 < colMinor (NormedField.toAbsoluteValue ℂ_[p]) Mc S) ∧
    Real.log (GlobalTheory.ShFam.Pad.grNorm t xC (latHT t p xC) (u ((letters Dw).get (Fin.cast hg.symm i)).1)
      ((letters Dw).get (Fin.cast hg.symm i)).2) =
      Real.log (colMinor (NormedField.toAbsoluteValue ℂ_[p]) Mc (blkLe β i)) -
        Real.log (colMinor (NormedField.toAbsoluteValue ℂ_[p]) Mc (blkLt β i)) := by
  subst hg hx
  obtain ⟨h1, h2⟩ := ball hX x hn χ hχ _ (fun i => (hu.1 _ _).1)
    (GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame E H Dw l c X t _ f _ u hu).1 (span_concat hu) Mc hM
  have hpos := GlobalTheory.ConstLat.MinorQuot.colMinor_pos (NormedField.toAbsoluteValue ℂ_[p]) Mc h2
  refine ⟨hpos, ?_⟩
  rw [← Real.log_div (hpos _).ne' (hpos _).ne']
  exact congrArg Real.log (grNorm_block (fun τ i => (hu.1 τ i).1) _ Mc h2 h1 β hβ i)

theorem lnStep_inl {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X) (u : GlobalTheory.LocM.Vecs Dw t C)
    (p : ℕ) {b : Bool} (hb : b = true) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    lnStep t x u p b (.inl (τ, (k : ℕ))) = Real.log (GlobalTheory.ShFam.Pad.grNorm t x (latHT t p x) (u τ) k) -
      (if τ (H.rt : E) = H.rt0 then vDiff E p else 0) * Real.log p := by
  subst hb
  refine (dif_pos k.2).trans ?_
  simp only [true_and, ite_mul, zero_mul]
  rfl

end Point

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₀} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F} (Y : FlagCpt Z ε)

theorem lgOf_eig [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) {v : HeightOneSpectrum (𝓞 F)} [hp : Fact (resP v).Prime]
    (e : Ext v) (y : AlgPt Y.Y) (x : Sp ↥(intO ℂ_[resP v]) ⟶ Z.X) {n N g : ℕ} (hn : 2 ≤ n)
    (χ : Fin N → TorsChar Z.t x (resP v ^ n)) (hχ : Gens χ) (hg : (letters Dw).length = g)
    (M : Matrix (Fin N) (Fin g) (AlgebraicClosure F)) (ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v])
    (hψ : ψ = (ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom)
    (hx : spMap (intO ℂ_[resP v]).subtype ≫ x = spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ GlobalTheory.Toroidal.genι Z)
    (L : Fin g → Letter Dw) (hL : ∀ i, L i = (letters Dw).get (Fin.cast hg.symm i))
    (hM : DlogVals Z.t x χ (fun i => spMap (dualMap ψ) ≫ (Y.gr_spec (below y.1)).choose_spec.choose.v (L i).1 (L i).2)
      (M.map (ioOf (resP v) e)))
    {J : Type} (β : Fin g → J) (hβ : ∀ i j, β i = β j ↔ (L i).1 = (L j).1) (a : ℕ → Bool) (ha : a (resP v) = true)
    (R : Option ℝ) (i : Fin g) :
    lgOf Y (eigSym Dw a R (Sum.inl i : Fin g ⊕ Fin g)) v e y =
      Real.log (e.w (valAt y.1 (genAt (divOf Y (expo Dw (eigSym Dw a R (Sum.inl i : Fin g ⊕ Fin g)))) (below y.1) *
        (((Y.gr_spec (below y.1)).choose_spec.choose_spec.choose (L i).1 (L i).2 : Y.Y.Fnˣ) : Y.Y.Fn)))) +
        Real.log (colMinor e.w M (blkLe β i)) - Real.log (colMinor e.w M (blkLt β i)) +
          (if (L i).1 (H.rt : E) = H.rt0 then vDiff E (resP v) else 0) *
            Real.log (e.w ((resP v : ℕ) : AlgebraicClosure F)) := by
  obtain rfl : L = fun i => (letters Dw).get (Fin.cast hg.symm i) := funext hL
  obtain ⟨hpos, hgr⟩ := log_grNorm hX x hx hn χ hχ (isFrame_fr Y (below y.1) ψ) hg _ hM β hβ i
  have hw0 : 0 < e.w ((resP v : ℕ) : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hw1 : e.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have e1 : ((resP v : ℕ) : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [e1, e.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hlp : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hc := div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp
  have hcv := fun S => log_colMinor e.w (ioOf (resP v) e) hc
    (GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow (resP v) v (residueCharacteristic_mem v) e) M S (hpos S)
  have hsym : eigSym Dw a R (Sum.inl i : Fin g ⊕ Fin g) = Finsupp.single (a, R,
      .inl (((letters Dw).get (Fin.cast hg.symm i)).1, (((letters Dw).get (Fin.cast hg.symm i)).2 : ℕ))) 1 :=
    eigAt_of_lt Dw _ _ 1 (Fin.cast hg.symm i).2
  have hlg := (GlobalTheory.CovHt.RootFirst.lgOf_single_inl Y _ _ _ _ _ hsym v e y).2
  rw [← hψ] at hlg
  have hst := (lnStep_inl _ (GlobalTheory.LocM.Vecs.bc ψ (fr Y (below y.1)).v) (resP v) ha _ _).trans (congrArg (· - _) hgr)
  refine hlg.trans ((congrArg₂ (· + ·) (congrArg (fun z => Real.log (e.w (valAt y.1 z)))
    ((Units.val_mul _ _).trans (mul_comm _ _))) (congrArg (_ * ·) hst)).trans ?_)
  rw [hcv, hcv]
  field_simp
  ring

end Flag

section Setup

variable {D : D7} (O : Setup D)

theorem coe_letterEmb (i : Fin (D.R.f * O.N)) (z : D.host.E) :
    ((O.κ.e (letterEmb O i z) : O.κ.c.F) : ℂ) = (letterAt O i).1 z := by
  have h : (letters O.S.Dw)[(i : ℕ)]? = some (letterAt O i) :=
    List.getElem?_eq_getElem (Fin.cast (length_letters O).symm i).2
  unfold letterEmb
  rw [h]
  simp

theorem letterEmb_eq_iff (i j : Fin (D.R.f * O.N)) : letterEmb O i = letterEmb O j ↔ (letterAt O i).1 = (letterAt O j).1 := by
  refine ⟨fun h => RingHom.ext fun z => ?_, fun h => RingHom.ext fun z => O.κ.e.injective (Subtype.ext ?_)⟩
  · rw [← coe_letterEmb, h, coe_letterEmb]
  · rw [coe_letterEmb, h, coe_letterEmb]

theorem letterEmb_mem_iff (i : Fin (D.R.f * O.N)) :
    letterEmb O i ∈ cmSet O ↔ (letterAt O i).1 (O.A.H.rt : D.host.E) = O.A.H.rt0 := by
  rw [← coe_letterEmb]
  rfl

end Setup

theorem lg_eigA : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hp : (resP v).Prime) (e : Ext v) (y : AlgPt (O.Φ.C c).Y) (Ch : Type)
    (inC : Ch → Prop) (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL)),
    resP v = p → PtData O c b n hp e y inC M → ∀ a, inC a → ∀ i, (eigA O c T R i).lg v e y =
      Real.log (e.w (valAt y.1 (genAt (eigA O c T R i).D (below y.1) * (dgOf O c (below y.1) i : (O.Φ.C c).Y.Fn)))) +
        Real.log (colMinor e.w (M a) (blkLe (fun l : Fin (D.R.f * O.N) => letterEmb O l) i)) -
          Real.log (colMinor e.w (M a) (blkLt (fun l : Fin (D.R.f * O.N) => letterEmb O l) i)) +
            (if letterEmb O i ∈ cmSet O then vDiff D.host.E p else 0) * Real.log (e.w (p : AlgebraicClosure D.what₂.LL)) := by
  intro _ _ _ _ _ D O _ T R _ p _ hpT c b n hn v hp e y Ch inC M hv hD a ha i
  haveI : Fact (resP v).Prime := ⟨hp⟩
  subst hv
  obtain ⟨xO, χ, hx, hχ, -, -, hM⟩ := hD
  obtain ⟨hX, hN, -⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hMa := hM a ha
  rw [funext fun l => uAt.eq_1 O c e y l, frAt.eq_1] at hMa
  rw [ptAt.eq_1] at hx
  rw [dgOf.eq_1, if_congr (letterEmb_mem_iff O i) rfl rfl]
  exact lgOf_eig (O.Φ.C c) hX e y xO (le_trans (by norm_num) hn) χ hχ (length_letters O) (M a) _ (psiAt.eq_1 O c e y) hx
    (letterAt O) (letterAt.eq_1 O) hMa _ (letterEmb_eq_iff O) _ (decide_eq_true hpT) _ i

end GlobalTheory.EqHalf.EigNorm
