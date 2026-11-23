import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartLineBaseRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartMinorRegularityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartSectionDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameDetIsUnitOfIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CramerTriBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroAtOfWLtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameLeftInvMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameGram
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof

theorem cramerCol_apply_eq {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K)
    (Tm : Matrix (Fin g) (Fin g) K) (hT : Tm.BlockTriangular id) (hd : ∀ i, Tm i i ≠ 0)
    (σ : ∀ k : ℕ, Fin k → Fin (g + g)) (r : Fin (g + g)) (k : Fin g) :
    cramerCol H σ r k = minorAt (H * Tm⁻¹) ((k : ℕ) + 1) k.2 (Fin.snoc (σ k) r) /
      minorAt (H * Tm⁻¹) ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1)) := by
  simp only [cramerCol, Matrix.of_apply]
  rw [minor_eq_mul_inv H Tm hT hd _ k.2 (Fin.snoc (σ k) r), minor_eq_mul_inv H Tm hT hd _ k.2 (σ ((k : ℕ) + 1))]
  exact mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun i _ => hd _)

theorem rowSel_mul_apply {R : Type} [CommRing R] {g : ℕ} {n : Type} [Fintype n] (τ : Fin g → Fin (g + g))
    (M : Matrix (Fin (g + g)) n R) (l : Fin g) (k : n) : (rowSel (R := R) τ * M : Matrix (Fin g) n R) l k = M (τ l) k := by
  simp [rowSel, Matrix.mul_apply]

theorem chartM_regAt_unitAt : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (q : Idx ι L), ∀ x ∈ chartOpen V U H L m r q, ¬ IsUnit (p : V.X.presheaf.stalk x) → (∀ i k, RegAt x (chartM V H J q i k)) ∧ UnitAt x (chartM V H J q).det := by
  intro F _ _ Y C g A p V W ι U H J d T L m r hH q x hx hpx
  obtain ⟨hp, hg0, hJ, hW, hm, -, -, hT, -, -, -, hreg, -⟩ := id hH
  have hx' : x ∈ chartSet V U H L m r q := hx

  have hmin : ∀ (k : ℕ) (hk : k ≤ g), minorAt (H q.1) k hk (q.2.1 k) ≠ 0 := by
    intro k hk h0
    apply (hx'.2.2 k hk).ne_zero
    simp [nmin, h0, zero_pow hm.ne']
  obtain ⟨B, -, -, -, hdet⟩ := cramerCol_tri_det (H q.1) q.2.1 hmin
  have hU1 : (rowSel (q.2.1 g) * chartU V H q).det = 1 := by
    have e : rowSel (q.2.1 g) * chartU V H q =
        (toG V).symm.toRingHom.mapMatrix (rowSel (q.2.1 g) * cramerCol (H q.1) q.2.1) := by
      ext l k
      exact (rowSel_mul_apply _ _ l k).trans
        (congrArg (toG V).symm.toRingHom (rowSel_mul_apply (q.2.1 g) (cramerCol (H q.1) q.2.1) l k).symm)
    exact (congrArg Matrix.det e).trans ((RingHom.map_det _ _).symm.trans ((congrArg _ hdet).trans (map_one _)))
  have hU1u : IsUnit (rowSel (q.2.1 g) * chartU V H q).det := by rw [hU1]; exact isUnit_one
  have hTz : ∀ y, ((T y).map V.φ).BlockTriangular id := fun y => blockTriangular_map V (hT y).1
  have hdz : ∀ y i, ((T y).map V.φ) i i ≠ 0 := fun y i => by
    rw [Matrix.map_apply, (hT y).2 i, map_ne_zero]; exact Units.ne_zero _

  have hU : ∀ r' k, RegAt x (chartU V H q r' k) := by
    intro r' k
    refine GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V p hp W hW (chartOpen V U H L m r q) _ ?_ ?_ x hx hpx
    · intro z hz
      have hz' : V.j z ∈ chartSet V U H L m r q := hz
      simp only [chartU, Matrix.map_apply]
      rw [regAt_symm, cramerCol_apply_eq (H q.1) _ (hTz (V.π z)) (hdz (V.π z)), div_eq_mul_inv]
      exact (regAt_minor _ (hreg q.1 z hz'.1) _ _ _).mul
        (GlobalTheory.T.hodge_chart_line_base_regular A p V W U H J d T L m r hH q z hz _ k.2).inv.regAt
    · intro v hv e y hy z yt hzy hc ht
      have ht' : ⊤ ≤ (spMap e.O.subtype ≫ yt) ⁻¹ᵁ chartOpen V U H L m r q :=
        fun q' _ => ht (x := spMap e.O.subtype q') trivial
      have hb : V.j (below z) ∈ chartOpen V U H L m r q := by
        have h0 : below (spMap e.O.subtype ≫ yt) ∈ chartOpen V U H L m r q := ht' trivial
        rw [hc] at h0; exact h0
      have hb' : V.j (below z) ∈ chartSet V U H L m r q := hb
      have hby : below y.1 = V.π (below z) := by rw [← hzy]; rfl
      simp only [chartU, Matrix.map_apply]
      rw [valAt_symm, cramerCol_apply_eq (H q.1) _ (hTz (V.π (below z))) (hdz _), div_eq_mul_inv]
      have hHz := hreg q.1 (below z) hb'.1
      have hD := GlobalTheory.T.hodge_chart_line_base_regular A p V W U H J d T L m r hH q (below z) hb _ k.2
      have hN := minor_valAt z _ hHz _ k.2 (Fin.snoc (q.2.1 k) r')
      have hD' := minor_valAt z _ hHz _ k.2 (q.2.1 ((k : ℕ) + 1))
      rw [Res.valAt_mul hN.1 hD.inv.regAt, valAt_inv z hD, hN.2, hD'.2, map_mul, map_inv₀, ← div_eq_mul_inv]
      obtain ⟨hpos, hmx⟩ := GlobalTheory.T.hodge_chart_minor_regularity A p V W U H J d T L m r hH v hv e y hy z yt hzy hc q ht _ k.2
      rw [hby] at hpos hmx
      exact (div_le_one hpos).2 (hmx _)

  obtain ⟨S, hS⟩ := exists_lift (chartU V H q) hU
  have hJ' : IsUnit (J.map (Int.castRingHom (V.X.presheaf.stalk x))).det := by
    have h := hJ.map (Int.castRingHom (V.X.presheaf.stalk x))
    rw [RingHom.map_det] at h; exact h
  have hJF : IsUnit (J.map (Int.castRingHom V.X.functionField)).det := by
    have h := hJ.map (Int.castRingHom V.X.functionField)
    rw [RingHom.map_det] at h; exact h
  have hJmap : (J.map (Int.castRingHom (V.X.presheaf.stalk x))).map (algebraMap _ V.X.functionField) =
      J.map (Int.castRingHom V.X.functionField) := by
    ext a b; simp
  have hSdet : (rowSel (q.2.1 g) * S).det = 1 := by
    apply IsFractionRing.injective (V.X.presheaf.stalk x) V.X.functionField
    refine (RingHom.map_det _ _).trans ?_
    have e : (algebraMap (V.X.presheaf.stalk x) V.X.functionField).mapMatrix (rowSel (q.2.1 g) * S) =
        rowSel (q.2.1 g) * chartU V H q := by
      ext l k
      exact (congrArg _ (rowSel_mul_apply _ _ l k)).trans
        ((congrArg (fun M => M (q.2.1 g l) k) hS).trans (rowSel_mul_apply _ _ l k).symm)
    exact (congrArg Matrix.det e).trans (hU1.trans (map_one _).symm)
  have hSu : IsUnit (rowSel (q.2.1 g) * S).det := by rw [hSdet]; exact isUnit_one
  have hM : chartM V H J q = (fullFrame S (J.map (Int.castRingHom (V.X.presheaf.stalk x)))
      (leftInv S (q.2.1 g))).map (algebraMap (V.X.presheaf.stalk x) V.X.functionField) := by
    rw [fullFrame_leftInv_map _ S _ _ hJ' hSu, hS, hJmap]; rfl

  have hmax : ∀ i k, (S.transpose * J.map (Int.castRingHom (V.X.presheaf.stalk x)) * S) i k ∈
      IsLocalRing.maximalIdeal (V.X.presheaf.stalk x) := by
    intro i k
    have hf : algebraMap (V.X.presheaf.stalk x) V.X.functionField
        ((S.transpose * J.map (Int.castRingHom (V.X.presheaf.stalk x)) * S) i k) =
        ((chartU V H q).transpose * J.map (Int.castRingHom V.X.functionField) * chartU V H q) i k := by
      rw [← hS, ← hJmap, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]; rfl
    have hval : ∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W →
        ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
        ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r q →
        e.w (valAt (z ≫ V.j) (((chartU V H q).transpose * J.map (Int.castRingHom V.X.functionField) * chartU V H q) i k)) < 1 := by
      intro v hv e y hy z yt hzy hc ht
      have h2 := (GlobalTheory.T.hodge_chart_section_divisor A p V W U H J d T L m r hH v hv e y hy z yt hzy hc q ht).2 i (Fin.castAdd g k)
      have hif : ¬ ((i : ℕ) + ((Fin.castAdd g k : Fin (g + g)) : ℕ) = 2 * g - 1) := by
        have := i.2; have := k.2; simp only [Fin.coe_castAdd]; omega
      simp only [chartM] at h2
      rw [if_neg hif, sub_zero, (fullFrame_gram (chartU V H q) (J.map (Int.castRingHom _)) (q.2.1 g) hJF hU1u i k).1] at h2
      exact h2
    obtain ⟨a, ha, hae⟩ := GlobalTheory.Cover.ZeroAtFibre.zeroAt_of_w_lt_one F Y V p hp W hW (chartOpen V U H L m r q) _ hval
      x hx hpx ⟨_, hf⟩
    obtain rfl := IsFractionRing.injective (V.X.presheaf.stalk x) V.X.functionField (hae.trans hf.symm)
    exact ha
  refine ⟨fun i k => ?_, ?_⟩
  · rw [hM]; exact ⟨_, rfl⟩
  · refine ⟨_, GlobalTheory.T.full_frame_det_isUnit_of_isotropic S _ (q.2.1 g) hJ' hSu hmax, ?_⟩
    rw [hM, RingHom.map_det]; rfl

end GlobalTheory.WholeFlag.GlueProof
