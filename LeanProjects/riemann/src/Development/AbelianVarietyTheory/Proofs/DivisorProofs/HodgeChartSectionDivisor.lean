import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CramerTriBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
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

namespace GlobalTheory.WholeFlag.GlueProof.TestPt

theorem det_rowSel_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g : ℕ} (τ : Fin g → Fin (g + g))
    (M : Matrix (Fin (g + g)) (Fin g) R) :
    (rowSel τ * M.map f : Matrix (Fin g) (Fin g) S).det = f (rowSel τ * M : Matrix (Fin g) (Fin g) R).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  change ∑ r, (rowSel τ : Matrix (Fin g) (Fin (g + g)) S) a r * f (M r b) =
    f (∑ r, (rowSel τ : Matrix (Fin g) (Fin (g + g)) R) a r * M r b)
  simp [rowSel]

theorem gram_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n g : ℕ} (J : Matrix (Fin n) (Fin n) ℤ)
    (M : Matrix (Fin n) (Fin g) R) (i k : Fin g) :
    ((M.map f).transpose * J.map (Int.castRingHom S) * M.map f) i k =
      f ((M.transpose * J.map (Int.castRingHom R) * M) i k) := by
  simp [Matrix.mul_apply, map_sum]

theorem gram_eq_dot {K : Type} [CommRing K] {n g : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (H : Matrix (Fin n) (Fin g) K) (B : Matrix (Fin g) (Fin g) K) (i k : Fin g) :
    ((H * B).transpose * J * (H * B)) i k =
      dotProduct (H *ᵥ fun l => B l i) (J *ᵥ (H *ᵥ fun l => B l k)) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl

theorem gramA : ∀ {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {Z : Scheme.{0}} [IsIntegral Z] (z : Sp (AlgebraicClosure F) ⟶ Z) {g : ℕ} (Hz : Matrix (Fin (g + g)) (Fin g) Z.functionField) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (ν : ℕ → ℝ), (∀ r l, RegAt (below z) (Hz r l)) → (∀ (k : ℕ) (hk : k ≤ g), UnitAt (below z) (minorAt Hz k hk (σ k))) → (∀ k, k ≤ g → 0 < ν k) → (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (Hz.map (valAt z)) k hk τ) ≤ ν k) → (∀ (k : ℕ) (hk : k ≤ g), e.w (minorAt (Hz.map (valAt z)) k hk (σ k)) = ν k) → (∀ u u' : Fin g → AlgebraicClosure F, (∀ r, e.w ((Hz.map (valAt z) *ᵥ u) r) ≤ 1) → (∀ r, e.w ((Hz.map (valAt z) *ᵥ u') r) ≤ 1) → e.w (dotProduct (Hz.map (valAt z) *ᵥ u) (J.map (Int.castRingHom (AlgebraicClosure F)) *ᵥ (Hz.map (valAt z) *ᵥ u'))) < 1) → ∀ i k : Fin g, e.w (valAt z (((cramerCol Hz σ).transpose * J.map (Int.castRingHom Z.functionField) * cramerCol Hz σ) i k)) < 1 := by
  intro F _ _ v e Z _ z g Hz σ J ν hreg hunit hν hle heq hiso i k
  have hval : ∀ (r : Fin (g + g)) (c : Fin g), RegAt (below z) (cramerCol Hz σ r c) ∧
      valAt z (cramerCol Hz σ r c) = cramerCol (Hz.map (valAt z)) σ r c := by
    intro r c
    have h1 := minor_valAt z Hz hreg ((c : ℕ) + 1) c.2 (Fin.snoc (σ c) r)
    have h2 := minor_valAt z Hz hreg ((c : ℕ) + 1) c.2 (σ ((c : ℕ) + 1))
    have h3 := hunit ((c : ℕ) + 1) c.2
    simp only [cramerCol, Matrix.of_apply, div_eq_mul_inv]
    refine ⟨h1.1.mul h3.inv.regAt, ?_⟩
    rw [Res.valAt_mul h1.1 h3.inv.regAt, valAt_inv z h3, h1.2, h2.2]
  have hne : ∀ (k : ℕ) (hk : k ≤ g), minorAt (Hz.map (valAt z)) k hk (σ k) ≠ 0 := by
    intro k hk h0
    have h1 := heq k hk
    rw [h0, map_zero] at h1
    exact (hν k hk).ne h1
  obtain ⟨B, -, -, hB, -⟩ := cramerCol_tri_det (Hz.map (valAt z)) σ hne
  have hint : ∀ (c : Fin g) (r : Fin (g + g)), e.w ((Hz.map (valAt z) *ᵥ fun l => B l c) r) ≤ 1 := by
    intro c r
    have h1 : (Hz.map (valAt z) *ᵥ fun l => B l c) r = cramerCol (Hz.map (valAt z)) σ r c := by
      rw [hB]; rfl
    rw [h1]
    simp only [cramerCol, Matrix.of_apply]
    rw [map_div₀, heq _ c.2, div_le_one (hν _ c.2)]
    exact hle _ c.2 _
  obtain ⟨S, hS⟩ := exists_lift (cramerCol Hz σ) fun r c => (hval r c).1
  have hSv : S.map (Scheme.stalkClosedPointTo z).hom = Hz.map (valAt z) * B := by
    rw [← map_valAt_lift, hS, ← hB]
    ext r c
    exact (hval r c).2
  have h := hiso _ _ (hint i) (hint k)
  rw [← gram_eq_dot, ← hSv] at h
  rw [← hS, gram_map, Res.valAt_algebraMap, ← gram_map]
  exact h

end GlobalTheory.WholeFlag.GlueProof.TestPt

namespace GlobalTheory.WholeFlag.GlueProof

theorem glue_test : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ q : Idx ι L, ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r q → (∀ i, (A i).lg v e y = Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (chartC V H q i : V.G.functionField))))) ∧ ∀ (i : Fin g) (k : Fin (g + g)), e.w (valAt (z ≫ V.j) (((chartM V H J q).transpose * J.map (Int.castRingHom V.X.functionField) * chartM V H J q) (Fin.castAdd g i) k) - (if (i : ℕ) + k = 2 * g - 1 then 1 else 0)) < 1 := by
  intro F _ _ Y C g A p V W ι U H J d T L m r h v hv e y hyW z yt hzy hyt q hq
  obtain ⟨hp, hg, hJ, hgW, hm, -, -, hTri, hGd, hrl, hnorm, hreg, hν⟩ := h

  have hmem : ∀ pt, yt pt ∈ chartSet V U H L m r q := fun pt => hq (show pt ∈ (⊤ : (Sp e.O).Opens) from trivial)
  have hbz : V.j (below z) ∈ chartSet V U H L m r q := by
    have e1 : below (z ≫ V.j) = V.j (below z) := rfl
    rw [← e1, ← hyt]
    exact hmem _
  have hby : below y.1 = V.π (below z) := by rw [← hzy]; rfl
  obtain ⟨ν, hνpos, hνlg, hνU⟩ := hν v hv e y hyW z yt hzy hyt
  obtain ⟨hle, hatt, hiso, -⟩ := hνU q.1 fun pt _ => (hmem pt).1

  set Tz : Matrix (Fin g) (Fin g) Y.Fn := T (below y.1) with hTz
  set Hz : Matrix (Fin (g + g)) (Fin g) V.G.functionField := H q.1 * (Tz.map V.φ)⁻¹ with hHz
  have hTzTri : Tz.BlockTriangular id := (hTri (below y.1)).1
  have hTzd : ∀ i, Tz i i = (d (below y.1) i : Y.Fn) := (hTri (below y.1)).2
  have hHzreg : ∀ r l, RegAt (below z) (Hz r l) := by
    have h1 := hreg q.1 (below z) hbz.1
    rw [← hby] at h1
    exact h1
  have hGdz : ∀ i, UnitAt (V.π (below z)) (genAt (A i).D (below y.1) * d (below y.1) i) := by
    intro i; rw [← hby]; exact hGd i (below y.1)
  have hrlz : ∀ i, UnitAt (below z) (V.φ (genAt (A i).D (below y.1) ^ m) * frames r q.2.2 i) := by
    intro i
    have hx : below z ∈ ((L i).pull V.j).U (fun _ => q.2.2 i) := by
      exact (GlobalTheory.LB.pull_U (L := L i) V.j (fun _ => q.2.2 i)).symm ▸ hbz.2.1 i
    have h1 := hrl i (fun _ => q.2.2 i) (below z) hx
    rw [← hby] at h1
    exact h1
  have hν0 : ν 0 = 1 := by
    obtain ⟨σ0, h0⟩ := hatt 0 (Nat.zero_le g)
    rw [← h0, minorAt_zero, map_one]

  have hn1 : ∀ (k : ℕ) (hk : k ≤ g), e.w (valAt z (nmin V (H q.1) (frames r q.2.2) m k hk (q.2.1 k))) = 1 := by
    intro k hk
    rw [← valAt_symm V z, ← hyt]
    exact NormExt.w_valAt_eq_one e yt ((hmem _).2.2 k hk)
  have hunit : ∀ (k : ℕ) (hk : k ≤ g), UnitAt (below z) (minorAt Hz k hk (q.2.1 k)) := by
    intro k hk
    have hu : UnitAt (below z) (nmin V (H q.1) (frames r q.2.2) m k hk (q.2.1 k)) :=
      (unitAt_symm V).1 (hbz.2.2 k hk)
    exact (unitAt_minor_of_nmin V (H q.1) (frames r q.2.2) m hm k hk (q.2.1 k) Tz (d (below y.1))
      (fun i => genAt (A i).D (below y.1)) hTzTri hTzd hHzreg (fun i => V.unitAt_φ (hGdz i)) hrlz).2 hu
  have hmin : ∀ (k : ℕ) (hk : k ≤ g), e.w (minorAt (Hz.map (valAt z)) k hk (q.2.1 k)) = ν k := by
    intro k hk
    have hw := w_nmin V e z (H q.1) (frames r q.2.2) m k hk (q.2.1 k) Tz (d (below y.1))
      (fun i => genAt (A i).D (below y.1)) hTzTri hTzd hHzreg hGdz hrlz ν hνpos hν0 (fun i => (A i).lg v e y)
      (fun i => by
        have h1 := hnorm i v hv e y z yt (fun _ => q.2.2 i) hzy hyt (fun pt _ => (hmem pt).2.1 i)
        exact h1)
      (fun i => by rw [hνlg i, hzy])
    rw [hn1 k hk] at hw
    have hνk := hνpos k hk
    have hmpos : (0 : ℝ) < ν k ^ m := pow_pos hνk m
    have h2 : e.w (minorAt (Hz.map (valAt z)) k hk (q.2.1 k)) ^ m = ν k ^ m := by
      field_simp at hw; linarith
    exact (pow_left_inj₀ (e.w.nonneg _) hνk.le hm.ne').1 h2

  have hTd0 : ∀ i, (Tz.map V.φ) i i ≠ 0 := fun i => by
    rw [Matrix.map_apply, hTzd, map_ne_zero]; exact Units.ne_zero _
  have hTri' : (Tz.map V.φ).BlockTriangular id := blockTriangular_map V hTzTri
  obtain ⟨-, hcr, hfr⟩ := GlobalTheory.ConstLat.CramerFrame.triChange (H q.1) (Tz.map V.φ) hTri' hTd0 (q.2.1)
  have hne : ∀ (k : ℕ) (hk : k ≤ g), minorAt Hz k hk (q.2.1 k) ≠ 0 := fun k hk => (hunit k hk).ne_zero
  refine ⟨fun i => ?_, fun i k => ?_⟩
  ·
    have hc : (chartC V H q i : V.G.functionField) = V.φ (d (below y.1) i) *
        minorAt Hz ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) * (minorAt Hz i i.2.le (q.2.1 i))⁻¹ := by
      show (GlobalTheory.ConstLat.CramerFrame.frameC (H q.1) q.2.1 i : V.G.functionField) = _
      rw [hfr hne i, Matrix.map_apply, hTzd, div_eq_mul_inv]
    have hGdu : UnitAt (below z) (V.φ (genAt (A i).D (below y.1) * d (below y.1) i)) := V.unitAt_φ (hGdz i)
    have hM1 := minor_valAt z Hz hHzreg ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1))
    have hM0 := hunit (i : ℕ) i.2.le
    have e2 : V.φ (genAt (A i).D (below y.1)) * (chartC V H q i : V.G.functionField) =
        V.φ (genAt (A i).D (below y.1) * d (below y.1) i) * minorAt Hz ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) *
          (minorAt Hz i i.2.le (q.2.1 i))⁻¹ := by
      rw [hc, map_mul]; ring
    rw [e2, Res.valAt_mul (hGdu.regAt.mul hM1.1) hM0.inv.regAt, Res.valAt_mul hGdu.regAt hM1.1, valAt_inv z hM0,
      hM1.2, (minor_valAt z Hz hHzreg (i : ℕ) i.2.le (q.2.1 i)).2, V.valAt_φ z (hGdz i).regAt, map_mul, map_mul,
      map_inv₀, hmin _ i.2, hmin _ i.2.le, hνlg i, hzy]
    have h1 : 0 < e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i)) := by
      have h1' := e.w.pos (Res.valAt_ne_zero hGdu)
      rw [V.valAt_φ z (hGdz i).regAt, hzy] at h1'
      exact h1'
    have h2 := hνpos _ (Nat.succ_le_of_lt i.2)
    have h3 := hνpos _ i.2.le
    rw [Real.log_mul (mul_pos h1 h2).ne' (inv_pos.2 h3).ne', Real.log_mul h1.ne' h2.ne', Real.log_inv]
    ring
  ·
    have hJX : IsUnit (J.map (Int.castRingHom V.X.functionField)).det := by
      rw [show (J.map (Int.castRingHom V.X.functionField)).det = Int.castRingHom V.X.functionField J.det from
        (RingHom.map_det _ J).symm]; exact hJ.map _
    obtain ⟨B, -, -, -, hB1⟩ := cramerCol_tri_det Hz q.2.1 hne
    have hU : chartU V H q = (cramerCol Hz q.2.1).map (toG V).symm.toRingHom := by
      rw [chartU, hcr]; rfl
    have hRU : IsUnit (rowSel (q.2.1 g) * chartU V H q : Matrix (Fin g) (Fin g) V.X.functionField).det := by
      rw [hU]
      have e3 := (TestPt.det_rowSel_map (toG V).symm.toRingHom (q.2.1 g) (cramerCol Hz q.2.1)).trans
        ((congrArg (toG V).symm.toRingHom hB1).trans (map_one _))
      exact e3 ▸ isUnit_one
    have hG := fullFrame_gram (chartU V H q) (J.map (Int.castRingHom V.X.functionField)) (q.2.1 g) hJX hRU i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · have hk : ¬ ((i : ℕ) + (Fin.castAdd g k : ℕ) = 2 * g - 1) := by simp only [Fin.val_castAdd]; omega
      rw [chartM, (hG k).1, if_neg hk, sub_zero, hU, TestPt.gram_map]
      change e.w (valAt (z ≫ V.j) ((toG V).symm _)) < 1
      rw [valAt_symm]
      exact TestPt.gramA e z Hz q.2.1 J ν hHzreg hunit hνpos hle hmin hiso i k
    · have hk : ((i : ℕ) + (Fin.natAdd g k : ℕ) = 2 * g - 1) ↔ ((i : ℕ) + k = g - 1) := by
        simp only [Fin.val_natAdd]; omega
      rw [chartM, (hG k).2]
      simp only [antiDiag, Matrix.of_apply]
      by_cases hik : (i : ℕ) + k = g - 1
      · rw [if_pos hik, if_pos (hk.2 hik), Res.valAt_one, sub_self, map_zero]; exact one_pos
      · rw [if_neg hik, if_neg (fun h => hik (hk.1 h)), Res.valAt_zero, sub_self, map_zero]; exact one_pos

end GlobalTheory.WholeFlag.GlueProof

end
