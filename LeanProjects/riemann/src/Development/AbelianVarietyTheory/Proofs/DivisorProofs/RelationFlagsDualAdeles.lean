import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRegularTriangularBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationPowerBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantEmbeddingCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLatticeRegularAtPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLeftInverseRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartMinorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLatticeTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverChartLatticeTransformInverseStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelGlue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem frameOn_mono {C : CxSt F} {g : ℕ} {V : Cover Y} {W : Y.X.Opens} {U U' : V.X.Opens}
    {H : Matrix (Fin (g + g)) (Fin g) V.G.functionField} {d : Y.X → Fin g → Y.Fnˣ} {T : Y.X → Matrix (Fin g) (Fin g) Y.Fn}
    {A : Fin g → Adl C Y} {p : ℕ} {Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField}
    {Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField} {c : Fin g → V.G.functionFieldˣ}
    (h : FrameOn V W U H d T A p Um Lf c) (hU : U' ≤ U) : FrameOn V W U' H d T A p Um Lf c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, fun x hx => h2 x (hU hx), fun i z hz => h3 i z (hU hz),
    fun v hv e y hy z yt hz hyt hU' => h4 v hv e y hy z yt hz hyt fun w hw => hU (hU' hw)⟩

theorem regAt_compl {X : Scheme.{0}} [IsIntegral X] (x : X) {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) X.functionField)
    (L : Matrix (Fin g) (Fin (g + g)) X.functionField) (Ji : Matrix (Fin (g + g)) (Fin (g + g)) X.functionField)
    (hU : ∀ i j, RegAt x (U i j)) (hL : ∀ i j, RegAt x (L i j)) (hJ : ∀ i j, RegAt x (Ji i j)) :
    ∀ i j, RegAt x (ConstLat.compl U L Ji i j) := by
  intro i j
  induction j using Fin.addCases with
  | left l => simpa [ConstLat.compl] using hU i l
  | right l =>
    simp only [ConstLat.compl, Matrix.of_apply, Fin.addCases_right, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_induction _ (RegAt x) (fun a b ha hb => ha.add hb) (regAt_zero x) fun m _ => ?_
    exact (hJ i m).mul (hL _ m)

theorem unitAt_dual {V : Cover Y} {z : V.G} {b a : Y.Fnˣ} {c : V.G.functionFieldˣ}
    (hba : UnitAt (V.π z) ((b : Y.Fn) * a)) (hac : UnitAt z (V.φ a * c)) :
    UnitAt z (V.φ b * ((c⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) := by
  have h0 : V.φ (a : Y.Fn) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
  have h0' : ((c : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
  have e : V.φ (b : Y.Fn) * ((c⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ ((b : Y.Fn) * a) * (V.φ a * c)⁻¹ := by
    rw [map_mul, Units.val_inv_eq_inv_val]; field_simp
  rw [e]; exact (V.unitAt_φ hba).mul hac.inv

theorem lg_dual {C : CxSt F} {g : ℕ} {A B : Fin g → Adl C Y} {p : ℕ} (hAB : DualAt A B p) (V : Cover Y)
    {v : HeightOneSpectrum (𝓞 F)} (hv : resP v = p) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (hz : z ≫ V.π = y.1) (l : Fin g) (c : V.G.functionFieldˣ)
    (hu : UnitAt (below z) (V.φ (genAt (A l.rev).D (below y.1)) * c))
    (hlg : (A l.rev).lg v e y = Real.log (e.w (valAt z (V.φ (genAt (A l.rev).D (below y.1)) * (c : V.G.functionField))))) :
    (B l).lg v e y =
      Real.log (e.w (valAt z (V.φ (genAt (B l).D (below y.1)) * ((c⁻¹ : V.G.functionFieldˣ) : V.G.functionField)))) := by
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hu' : UnitAt (V.π (below z)) (genAt (B l).D (below y.1) * genAt (A l.rev).D (below y.1)) := by
    rw [hπ]; exact hAB.1 l _
  have n1 : e.w (valAt y.1 (genAt (B l).D (below y.1) * genAt (A l.rev).D (below y.1))) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hAB.1 l _))
  have n2 : e.w (valAt z (V.φ (genAt (A l.rev).D (below y.1)) * (c : V.G.functionField))) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hu)
  have key : V.φ (genAt (B l).D (below y.1)) * ((c⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ (genAt (B l).D (below y.1) * genAt (A l.rev).D (below y.1)) *
        (V.φ (genAt (A l.rev).D (below y.1)) * c)⁻¹ := by
    have h0 : V.φ (genAt (A l.rev).D (below y.1) : Y.Fn) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have h0' : ((c : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
    rw [map_mul, Units.val_inv_eq_inv_val]; field_simp
  rw [key, SmallSec.valAt_mul (V.unitAt_φ hu').regAt hu.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hu,
    V.valAt_φ z hu'.regAt, hz, map_mul, map_inv₀, Real.log_mul n1 (inv_ne_zero n2), Real.log_inv, ← hlg, hAB.2 l v hv]
  ring

theorem relFlag_glue : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A A' B B' : Fin g → Adl C Y) (p n : ℕ),
    p.Prime → n ≠ 0 → DualAt A B p → DualAt A' B' p → (∀ k, RelData A A' p n k) →
    ∀ k, RelFlag (fun i : Fin (g + g) => Sum.elim A B (finSumFinEquiv.symm i))
      (fun i : Fin (g + g) => Sum.elim A' B' (finSumFinEquiv.symm i)) p n k := by
  intro F _ _ Y C g A A' B B' p n hp hn hAB hAB' hR k
  obtain ⟨k', hk'⟩ := GlobalTheory.T.valuation_power_bounds (F := F) p n k hp hn
  obtain ⟨V, W, ι, U0, H0, d, T, J, P, Q, hJ, hPQ, hW, hcov, hT, hLA, hLA', hch, hiso⟩ := hR k'
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_constant_embedding_cover V
  have hfr : ∀ x : {x : V.X // ¬ IsUnit (p : V.X.presheaf.stalk x)}, ∃ (a : ι) (U : V.X.Opens)
      (Um Um' : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf Lf' : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
      (c c' : Fin g → V.G.functionFieldˣ), U ≤ U0 a ∧ x.1 ∈ U ∧ FrameOn V W U (H0 a) d T A p Um Lf c ∧
        FrameOn V W U (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) d T A' p Um' Lf' c' := by
    intro x
    obtain ⟨a, ha⟩ := hcov x.1 x.2
    obtain ⟨U1, Um, Lf, c, h1, hx1, hf1⟩ :=
      GlobalTheory.T.chart_regular_triangular_base A p hp V W hW (U0 a) (H0 a) d T hT hLA (hch a).1 (hch a).2.1 x.1 ha x.2
    obtain ⟨U2, Um', Lf', c', h2, hx2, hf2⟩ :=
      GlobalTheory.T.chart_regular_triangular_base A' p hp V W hW (U0 a) _ d T hT hLA' (hch a).2.2.1 (hch a).2.2.2 x.1 ha x.2
    exact ⟨a, U1 ⊓ U2, Um, Um', Lf, Lf', c, c', inf_le_left.trans h1, ⟨hx1, hx2⟩, frameOn_mono hf1 inf_le_left,
      frameOn_mono hf2 inf_le_right⟩
  choose a U Um Um' Lf Lf' c c' hU hxU hf hf' using hfr
  have hPQX : P.map κ * Q.map κ = 1 := by
    have h := congrArg κ.mapMatrix hPQ.1
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hdetJ : IsUnit (J.map (Int.castRingHom V.X.functionField)).det := by
    have h := RingHom.map_det (Int.castRingHom V.X.functionField) J
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; exact hJ.map _
  have hJJ : J.map (Int.castRingHom V.X.functionField) * (J.map (Int.castRingHom V.X.functionField))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetJ
  have hJJ' : ((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) *
      (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose) = 1 := by
    have hQP : Q.map κ * P.map κ = 1 := mul_eq_one_comm.1 hPQX
    calc _ = (Q.map κ).transpose * (J.map (Int.castRingHom V.X.functionField) * ((Q.map κ * P.map κ) *
          ((J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose))) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hQP, Matrix.one_mul, ← Matrix.mul_assoc (J.map (Int.castRingHom V.X.functionField)), hJJ, Matrix.one_mul,
          ← Matrix.transpose_mul, hPQX, Matrix.transpose_one]
  have hreg := fun x hx => GlobalTheory.T.second_lattice_regular_at_p V κ J p n P Q hp hJ hPQ x hx
  have hdet : ∀ x, ∀ x' ∈ U x, ¬ IsUnit (p : V.X.presheaf.stalk x') →
      UnitAt x' (compl (Um x) (Lf x) (J.map (Int.castRingHom V.X.functionField))⁻¹).det :=
    fun x => GlobalTheory.T.cover_chart_left_inverse_regular A p hp V W hW (U x) (H0 (a x)) d T (Um x) (Lf x) (c x) _ _ (hf x) hJJ
      (fun x' _ hx' i j => ⟨(hreg x' hx' i j).2.2.2.2, (hreg x' hx' i j).2.2.1⟩)
      (fun v hv e y hy z yt hz hyt hU' i j =>
        (GlobalTheory.T.cover_chart_minor_decomposition A p k' hp V W U0 H0 d T J (a x) (U x) (Um x) (Lf x) (c x) (hU x) (hf x) hiso v hv e y hy z yt hz hyt
          hU' i j).trans_lt (hk' v hv e).2.2)
  have hdet' : ∀ x, ∀ x' ∈ U x, ¬ IsUnit (p : V.X.presheaf.stalk x') →
      UnitAt x' (compl (Um' x) (Lf' x)
        (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose)).det :=
    fun x => GlobalTheory.T.cover_chart_left_inverse_regular A' p hp V W hW (U x) _ d T (Um' x) (Lf' x) (c' x) _ _ (hf' x) hJJ'
      (fun x' _ hx' i j => ⟨(hreg x' hx' i j).1, (hreg x' hx' i j).2.1⟩)
      (fun v hv e y hy z yt hz hyt hU' i j =>
        (GlobalTheory.T.cover_chart_lattice_transform A' p n k' hp hn V W U0 H0 d T J P Q κ hκ hPQ (a x) (U x) (Um' x) (Lf' x) (c' x) (hU x)
          (hch (a x)).1 (hf' x) hiso v hv e y hy z yt hz hyt hU' i j).trans_lt (hk' v hv e).2.1)
  refine ⟨hn, V, W, {x : V.X // ¬ IsUnit (p : V.X.presheaf.stalk x)}, U,
    fun x => compl (Um x) (Lf x) (J.map (Int.castRingHom V.X.functionField))⁻¹,
    fun x => compl (Um' x) (Lf' x) (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose),
    fun x i => Sum.elim (c x) (fun l => (c x l.rev)⁻¹) (finSumFinEquiv.symm i),
    fun x i => Sum.elim (c' x) (fun l => (c' x l.rev)⁻¹) (finSumFinEquiv.symm i), P.map κ, Q.map κ, hW, hPQX,
    fun i j => ?_, fun x hx => ⟨⟨x, hx⟩, hxU _⟩, fun x x' hx' hpx' => ?_, fun x i z hz => ?_, ?_⟩
  · have h1 := (hPQ.2.1 i j).1.map κ.toIntAlgHom
    have h2 := (hPQ.2.1 i j).2.map κ.toIntAlgHom
    change IsIntegral ℤ (κ ((n : F) * P i j)) at h1
    change IsIntegral ℤ (κ ((n : F) * Q i j)) at h2
    rw [map_mul, map_natCast] at h1 h2
    exact ⟨h1, h2⟩
  · refine ⟨fun i j => ⟨regAt_compl x' _ _ _ (fun i j => ((hf x).2.1 x' hx' hpx' i j).1)
      (fun i j => ((hf x).2.1 x' hx' hpx' j i).2) (fun i j => (hreg x' hpx' i j).2.2.1) i j,
      regAt_compl x' _ _ _ (fun i j => ((hf' x).2.1 x' hx' hpx' i j).1)
      (fun i j => ((hf' x).2.1 x' hx' hpx' j i).2) (fun i j => (hreg x' hpx' i j).2.1) i j,
      (hreg x' hpx' i j).2.2.2.1⟩, hdet x x' hx' hpx', hdet' x x' hx' hpx'⟩
  · induction i using Fin.addCases with
    | left i =>
      simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
      exact ⟨(hf x).2.2.1 i z hz, (hf' x).2.2.1 i z hz⟩
    | right l =>
      simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      exact ⟨unitAt_dual (hAB.1 l _) ((hf x).2.2.1 l.rev z hz), unitAt_dual (hAB'.1 l _) ((hf' x).2.2.1 l.rev z hz)⟩
  · intro v hv e y hy z yt hz hyt x hx
    have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
    have hPin : V.j (below z) ∈ U x := by
      have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
        change (z ≫ V.j) _ = _
        rw [← hyt]; rfl
      rw [e2]; exact hx trivial
    have h1 := ((hf x).2.2.2 v hv e y hy z yt hz hyt hx).1
    have h2 := ((hf' x).2.2.2 v hv e y hy z yt hz hyt hx).1
    refine ⟨fun i => ?_, fun b hb i => GlobalTheory.T.cover_chart_lattice_transform_inverse A A' p n k k' hp hn V W U0 H0 d T J P Q κ hκ hJ hPQ hiso hLA hLA' (a x) (a b)
      (U x) (U b) (Um' x) (Um b) (Lf' x) (Lf b) (c' x) (c b) (hU x) (hU b) (hch (a x)).1 (hf' x) (hf b) (hdet' x)
      v hv e y hy z yt hz hyt hx hb (hk' v hv e).1 i⟩
    induction i using Fin.addCases with
    | left i =>
      simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
      exact ⟨h1 i, h2 i⟩
    | right l =>
      simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      have hu := (hf x).2.2.1 l.rev (below z) hPin
      have hu' := (hf' x).2.2.1 l.rev (below z) hPin
      rw [hπ] at hu hu'
      exact ⟨lg_dual hAB V hv e y z hz l _ hu (h1 l.rev), lg_dual hAB' V hv e y z hz l _ hu' (h2 l.rev)⟩

end GlobalTheory.RelGlue
