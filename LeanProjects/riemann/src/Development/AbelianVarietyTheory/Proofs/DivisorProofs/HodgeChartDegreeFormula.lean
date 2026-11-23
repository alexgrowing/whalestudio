import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CramerTriBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompareFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WValAtLeOneAndUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartHeightBoundStatement
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

namespace GlobalTheory.WholeFlag.GlueProof.Compare

open GlobalTheory.TrueGeo.SmallSec

theorem cramerCol_mul_inv {K : Type} [Field K] {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) K) (T : Matrix (Fin g) (Fin g) K)
    (hT : T.BlockTriangular id) (hd : ∀ i, T i i ≠ 0) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) :
    cramerCol H σ = cramerCol (H * T⁻¹) σ := by
  ext r k
  simp only [cramerCol, Matrix.of_apply]
  rw [minor_eq_mul_inv H T hT hd, minor_eq_mul_inv H T hT hd _ _ (σ _),
    mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun j _ => hd _)]

section Val

variable {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (y : Sp K ⟶ Z)

theorem valAt_div {f h : Z.functionField} (hf : RegAt (below y) f) (hh : UnitAt (below y) h) :
    valAt y (f / h) = valAt y f / valAt y h := by
  rw [div_eq_mul_inv, Res.valAt_mul hf hh.inv.regAt, valAt_inv y hh, div_eq_mul_inv]

theorem valAt_cramerCol {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) Z.functionField) (σ : ∀ k : ℕ, Fin k → Fin (g + g))
    (hH : ∀ r l, RegAt (below y) (H r l)) (hu : ∀ (k : ℕ) (hk : k ≤ g), UnitAt (below y) (minorAt H k hk (σ k)))
    (r : Fin (g + g)) (k : Fin g) : valAt y (cramerCol H σ r k) = cramerCol (H.map (valAt y)) σ r k := by
  simp only [cramerCol, Matrix.of_apply]
  rw [valAt_div y (minor_valAt y H hH _ _ _).1 (hu _ _), (minor_valAt y H hH _ _ _).2, (minor_valAt y H hH _ _ _).2]

theorem valAt_inv_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) Z.functionField) (hM : ∀ i j, RegAt (below y) (M i j))
    (hN : ∀ i j, RegAt (below y) (N i j)) (hd : UnitAt (below y) M.det) :
    valAt y M.det = (M.map (valAt y)).det ∧
      ∀ i j, valAt y ((M⁻¹ * N) i j) = ((M.map (valAt y))⁻¹ * N.map (valAt y)) i j := by
  obtain ⟨S, rfl⟩ := exists_lift M hM
  obtain ⟨R, rfl⟩ := exists_lift N hN
  have e : (S.map (algebraMap _ Z.functionField)).det = algebraMap _ Z.functionField S.det :=
    (RingHom.map_det _ S).symm
  have hS : IsUnit S.det := by
    obtain ⟨a, ha, h⟩ := hd
    rw [e] at h
    rwa [← IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h]
  have hinv : ∀ {A : Type} [CommRing A] (f : Z.presheaf.stalk (below y) →+* A), (S.map f)⁻¹ = S⁻¹.map f := by
    intro A _ f
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul S hS, Matrix.map_one _ (map_zero f) (map_one f)]
  refine ⟨?_, fun i j => ?_⟩
  · rw [e, Res.valAt_algebraMap, map_valAt_lift]
    exact RingHom.map_det _ S
  · rw [map_valAt_lift, map_valAt_lift, hinv, hinv, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply,
      Matrix.map_apply]
    exact Res.valAt_algebraMap y _

end Val

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem chart_facts {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type}
    (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ)
    (h : Hyp A p V W U H J d T L m r) (q : Idx ι L) (z : V.G) (hz : V.j z ∈ chartOpen V U H L m r q) :
    (∀ r l, RegAt z ((H q.1 * ((T (V.π z)).map V.φ)⁻¹) r l)) ∧
    (∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H q.1 * ((T (V.π z)).map V.φ)⁻¹) k hk (q.2.1 k))) ∧
    cramerCol (H q.1) q.2.1 = cramerCol (H q.1 * ((T (V.π z)).map V.φ)⁻¹) q.2.1 ∧
    ∀ i : Fin g, (chartC V H q i : V.G.functionField) =
      minorAt (H q.1 * ((T (V.π z)).map V.φ)⁻¹) ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) /
        minorAt (H q.1 * ((T (V.π z)).map V.φ)⁻¹) (i : ℕ) i.2.le (q.2.1 (i : ℕ)) * V.φ (d (V.π z) i) := by
  obtain ⟨_, _, _, _, hm, _, _, hTT, hGd0, hrl0, _, hHz0, _⟩ := h
  obtain ⟨hzU, hzL, hzmin⟩ := hz
  set Tz := T (V.π z) with hTz
  have hT : Tz.BlockTriangular id := (hTT (V.π z)).1
  have hTd : ∀ j, Tz j j = (d (V.π z) j : Y.Fn) := (hTT (V.π z)).2
  have hHz : ∀ r l, RegAt z ((H q.1 * (Tz.map V.φ)⁻¹) r l) := hHz0 q.1 z hzU
  have hGd : ∀ j, UnitAt z (V.φ (genAt (A j).D (V.π z) * d (V.π z) j)) := fun j => V.unitAt_φ (hGd0 j (V.π z))
  have hrl : ∀ j, UnitAt z (V.φ (genAt (A j).D (V.π z) ^ m) * (frames r q.2.2 j : V.G.functionField)) := by
    intro j
    apply hrl0 j (fun _ => q.2.2 j) z
    simp only [LB.pull, LB.LinComb, LB.wchart]
    simpa using hzL j
  have hmin : ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H q.1 * (Tz.map V.φ)⁻¹) k hk (q.2.1 k)) := by
    intro k hk
    exact (unitAt_minor_of_nmin V (H q.1) (frames r q.2.2) m hm k hk (q.2.1 k) Tz (d (V.π z))
      (fun j => genAt (A j).D (V.π z)) hT hTd hHz hGd hrl).2 (unitAt_symm V |>.1 (hzmin k hk))
  have hd : ∀ j, (Tz.map V.φ) j j ≠ 0 := fun j => by
    rw [Matrix.map_apply, hTd, map_ne_zero]; exact Units.ne_zero _
  have hTm := blockTriangular_map V hT
  refine ⟨hHz, hmin, cramerCol_mul_inv _ _ hTm hd _, fun i => ?_⟩
  set a := minorAt (H q.1 * (Tz.map V.φ)⁻¹) ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) with ha
  set b := minorAt (H q.1 * (Tz.map V.φ)⁻¹) (i : ℕ) i.2.le (q.2.1 (i : ℕ)) with hb
  have hua : UnitAt z a := hmin _ _
  have hub : UnitAt z b := hmin _ _
  set P := ∏ j : Fin (i : ℕ), (Tz.map V.φ) (Fin.castLE i.2.le j) (Fin.castLE i.2.le j) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hd _
  have e1 : minorAt (H q.1) ((i : ℕ) + 1) i.2 (q.2.1 ((i : ℕ) + 1)) = a * (P * V.φ (d (V.π z) i)) := by
    rw [minor_eq_mul_inv (H q.1) _ hTm hd _ i.2, Fin.prod_univ_castSucc]
    congr 2
    have : Fin.castLE i.2 (Fin.last (i : ℕ)) = i := Fin.ext rfl
    rw [this, Matrix.map_apply, hTd]
  have e2 : minorAt (H q.1) (i : ℕ) i.2.le (q.2.1 (i : ℕ)) = b * P := minor_eq_mul_inv (H q.1) _ hTm hd _ i.2.le _
  have hdi : V.φ (d (V.π z) i) ≠ 0 := by rw [map_ne_zero]; exact Units.ne_zero _
  unfold chartC
  rw [dif_pos, Units.val_mk0, e1, e2]
  · field_simp [hub.ne_zero, hP0]
  · rw [e1, e2]
    exact div_ne_zero (mul_ne_zero hua.ne_zero (mul_ne_zero hP0 hdi)) (mul_ne_zero hub.ne_zero hP0)

theorem compare_charts : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ q b : Idx ι L, ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r q → ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r b → ∀ (k : Fin g) (i : Fin (g + g)), ((k : ℕ) < i → e.w (valAt (z ≫ V.j) (((chartM V H J q)⁻¹ * chartM V H J b) i (Fin.castAdd g k))) < 1) ∧ e.w (valAt (z ≫ V.j) (((chartM V H J q)⁻¹ * chartM V H J b) (Fin.castAdd g k) (Fin.castAdd g k)) - valAt z ((chartC V H q k / chartC V H b k : V.G.functionFieldˣ) : V.G.functionField)) < 1 := by
  intro F _ _ Y C g A p V W ι U H J d T L m r h v hv e y hyW z yt hz hyt q b hq hb k i
  have hby : below y.1 = V.π (below z) := by rw [← hz]; rfl
  have hzs : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := by
    rw [← Category.assoc, hz]; exact y.2
  have hcv := GlobalTheory.NormExt.asIdeal_closedPt V e z yt hzs hyt
  have hp : ¬ IsUnit (p : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
    rw [GlobalTheory.Mean4O.Cover.RegOverP.isUnit_natCast_stalk_iff, hcv, not_not, ← hv, ← Ideal.Quotient.eq_zero_iff_mem,
      map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hsp : below (z ≫ V.j) ⤳ yt (IsLocalRing.closedPoint e.O) := by
    rw [← hyt]; exact GlobalTheory.NormExt.below_specializes e yt
  have key : ∀ c : Idx ι L, ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r c →
      ⊤ ≤ yt ⁻¹ᵁ U c.1 ∧ (∀ s l, RegAt (below (z ≫ V.j)) (chartM V H J c s l)) ∧
      UnitAt (below (z ≫ V.j)) (chartM V H J c).det ∧
      (∀ s l, e.w (valAt (z ≫ V.j) (chartM V H J c s l)) ≤ 1) ∧
      e.w (valAt (z ≫ V.j) (chartM V H J c).det) = 1 ∧
      ∃ (β : Matrix (Fin g) (Fin g) (AlgebraicClosure F)) (u : V.G.functionField), β.BlockTriangular id ∧
        (∀ l, β l l ≠ 0) ∧
        (∀ s l, valAt (z ≫ V.j) (chartM V H J c s (Fin.castAdd g l)) = (valMat V (H c.1) (T (below y.1)) z * β) s l) ∧
        (rowSel (c.2.1 g) * (valMat V (H c.1) (T (below y.1)) z * β)).det = 1 ∧
        UnitAt (below z) u ∧ (chartC V H c k : V.G.functionField) = u * V.φ (d (below y.1) k) ∧
        valAt z u = (β k k)⁻¹ := by
    intro c hc
    have hcc : yt (IsLocalRing.closedPoint e.O) ∈ chartOpen V U H L m r c := hc trivial
    obtain ⟨hreg, hdet⟩ := GlobalTheory.T.hodge_chart_height_bound A p V W U H J d T L m r h c _ hcc hp
    have hzc : V.j (below z) ∈ chartOpen V U H L m r c := hsp.mem_open (chartOpen V U H L m r c).isOpen hcc
    obtain ⟨f1, f2, f3, f4⟩ := chart_facts A p V W U H J d T L m r h c (below z) hzc
    rw [← hby] at f1 f2 f3 f4
    have hmv : ∀ (n : ℕ) (hn : n ≤ g) (σ : Fin n → Fin (g + g)),
        valAt z (minorAt (H c.1 * ((T (below y.1)).map V.φ)⁻¹) n hn σ) =
          minorAt (valMat V (H c.1) (T (below y.1)) z) n hn σ := fun n hn σ => (minor_valAt z _ f1 n hn σ).2
    have hne : ∀ (n : ℕ) (hn : n ≤ g), minorAt (valMat V (H c.1) (T (below y.1)) z) n hn (c.2.1 n) ≠ 0 :=
      fun n hn => by rw [← hmv]; exact Res.valAt_ne_zero (f2 n hn)
    obtain ⟨β, b1, b2, b3, b4⟩ := cramerCol_tri_det (valMat V (H c.1) (T (below y.1)) z) c.2.1 hne
    refine ⟨fun x _ => (hc (x := x) trivial).1, fun s l => GlobalTheory.NormExt.regAt_of_specializes hsp (hreg s l),
      GlobalTheory.NormExt.unitAt_of_specializes hsp hdet, fun s l => ?_, ?_, β, _, b1, fun l => ?_, fun s l => ?_, ?_, ?_,
      f4 k, ?_⟩
    · rw [← hyt]; exact (GlobalTheory.NormExt.w_valAt_le_one_and_unitAt e yt (hreg s l)).1
    · rw [← hyt]; exact GlobalTheory.NormExt.w_valAt_eq_one e yt hdet
    · rw [b2]; exact div_ne_zero (hne _ _) (hne _ _)
    · rw [← b3, chartM, fullFrame_left, chartU, Matrix.map_apply, valAt_symm, f3]
      exact valAt_cramerCol z _ _ f1 f2 s l
    · rw [← b3]; exact b4
    · rw [div_eq_mul_inv]; exact (f2 _ _).mul (f2 _ _).inv
    · rw [valAt_div z (f2 _ _).regAt (f2 _ _), hmv, hmv, b2, inv_div]
  obtain ⟨q1, q2, q3, q4, q5, βq, uq, q6, q7, q8, q9, q10, q11, q12⟩ := key q hq
  obtain ⟨b1, b2, -, b4, -, βb, ub, b6, b7, b8, b9, b10, b11, b12⟩ := key b hb
  obtain ⟨ν, -, -, hν⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2 v hv e y hyW z yt hz hyt
  obtain ⟨v1, v2⟩ := valAt_inv_mul (z ≫ V.j) _ _ q2 b2 q3
  have main := GlobalTheory.WholeFlag.Glue.Lattice.compare_frames e.w e.O e.mem_O (valMat V (H q.1) (T (below y.1)) z)
    (valMat V (H b.1) (T (below y.1)) z) βq βb (q.2.1 g) (b.2.1 g) ((chartM V H J q).map (valAt (z ≫ V.j)))
    q6 b6 q7 b7 (fun s l => by rw [← q8]; exact q4 _ _) (fun s l => by rw [← b8]; exact b4 _ _)
    (by rw [q9, map_one]) (by rw [b9, map_one]) ((hν q.1 q1).2.2.2 b.1 b1) ((hν b.1 b1).2.2.2 q.1 q1)
    q4 (by rw [← v1]; exact q5) q8 k i
  have hcol : ∀ j, valAt (z ≫ V.j) (((chartM V H J q)⁻¹ * chartM V H J b) j (Fin.castAdd g k)) =
      (((chartM V H J q).map (valAt (z ≫ V.j)))⁻¹ * (valMat V (H b.1) (T (below y.1)) z * βb)) j k := by
    intro j
    rw [v2, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun s _ => by rw [← b8]; rfl
  have hrat : valAt z ((chartC V H q k / chartC V H b k : V.G.functionFieldˣ) : V.G.functionField) =
      βb k k / βq k k := by
    have hdk : V.φ (d (below y.1) k) ≠ 0 := by rw [map_ne_zero]; exact Units.ne_zero _
    rw [Units.val_div_eq_div_val, q11, b11, mul_div_mul_right _ _ hdk, valAt_div z q10.regAt b10, q12, b12,
      inv_div_inv]
  rw [hcol, hcol, hrat]
  exact main

end GlobalTheory.WholeFlag.GlueProof.Compare
