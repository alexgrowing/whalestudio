import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem C1_mul (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c1 (W := W) hn (mm A U) = mm A (c1 (W := W) hn U) := by
  ext i j; rfl

theorem mul_sub_one_mulVec_mem_spL (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c2 (W := W) hn (mm A U) = mm A (c2 (W := W) hn U) := by
  ext i j; rfl

theorem isOneCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c1 (W := W) hn (U + V) = c1 (W := W) hn U + c1 (W := W) hn V := by
  ext i j; rfl

theorem isTwoCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c2 (W := W) hn (U + V) = c2 (W := W) hn U + c2 (W := W) hn V := by
  ext i j; rfl

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c1 (W := W) hn (jn hn x v) = x := by
  ext i j
  simp [c1, jn]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c2 (W := W) hn (jn hn x v) = v := by
  ext i j
  simp [c2, jn]

theorem ww_mul_inv (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h b : GA D W) :
    ww W x₀ (h * b⁻¹) = mm (mt W b) (ww W x₀ h) := by
  simp only [ww, mm, mul_inv_rev, inv_inv, mt_mul, Matrix.mul_assoc]

theorem ac_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {g : GA D B} {α : Mx D t t} {c : Mx D t W.rank} {b : GA D W}
    (h1 : mm (mt B g) d.jX = mm d.jX α) (h2 : mm (mt B g) d.j0 = mm d.jX c + mm d.j0 (mt W b)) (p : Par D n t W) :
    ac B g (zp d hn x₀ p) =
      zp d hn x₀ (p.1 * b⁻¹, mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0, p.2.2) := by
  have key : mm (mt B g) (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) =
      mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹)) := by
    rw [isOneCochain_add, C1_mul, first_columns_join_eq, ww_mul_inv]
    simp only [mm] at h1 h2 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.add_mul, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : mm (mt B g) (mm d.jX (c2 (W := W) hn p.2.1)) =
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) := by
    rw [isTwoCochain_add, mul_sub_one_mulVec_mem_spL, second_columns_join_eq]
    simp only [mm] at h1 ⊢
    rw [← Matrix.mul_assoc, h1, add_zero, Matrix.mul_assoc]
  unfold ac zp
  refine Prod.ext key ?_
  change mm (mt B g) (mm (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 (W := W) hn p.2.1)) =
    mm (mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹))) p.2.2 +
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0))
  rw [← key, ← key2]
  simp only [mm]
  rw [Matrix.mul_add, Matrix.mul_assoc]

theorem map_aff {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure]
    (φ : G ≃ₜ+ G) (s : G) : ν.map (fun U => φ U + s) = (addEquivAddHaarChar φ)⁻¹ • ν := by
  have h := addEquivAddHaarChar_smul_map ν φ
  have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
  have hm : ν.map φ = (addEquivAddHaarChar φ)⁻¹ • ν := by
    conv_rhs => rw [← h]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  have e : (fun U : G => φ U + s) = (fun U => U + s) ∘ φ := rfl
  have hφ : Measurable (φ : G → G) := φ.continuous.measurable
  rw [e, ← Measure.map_map (measurable_add_const s) hφ, hm, Measure.map_smul, map_add_right_eq_self]

theorem map_skew {H A Y : Type} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace Y] {m : Measure H} {ν : Measure A}
    {μ : Measure Y} [SFinite m] [SFinite ν] [SFinite μ] {g : H → H} (hg : MeasurePreserving g m m) {f : H → A → A}
    (hf : Measurable (Function.uncurry f)) {c : ℝ≥0} (hc : ∀ h, ν.map (f h) = c • ν) :
    (m.prod (ν.prod μ)).map (fun p : H × A × Y => (g p.1, f p.1 p.2.1, p.2.2)) = c • m.prod (ν.prod μ) := by
  have hfm : ∀ h, Measurable (f h) := fun h => hf.of_uncurry_left
  have hs : Measurable (Function.uncurry fun (h : H) (z : A × Y) => ((f h z.1, z.2) : A × Y)) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)
  have h1 : ∀ h, (ν.prod μ).map (fun z : A × Y => ((f h z.1, z.2) : A × Y)) = c • (ν.prod μ) := fun h => by
    have e := Measure.map_prod_map ν μ (hfm h) measurable_id
    rw [Measure.map_id, hc h] at e
    have e2 : (c • ν).prod μ = c • ν.prod μ := by
      have := Measure.prod_smul_left (μ := ν) (ν := μ) (c : ℝ≥0∞)
      exact this
    rw [e2] at e
    exact e.symm
  have h2 := (hg.skew_product hs (.of_forall h1)).map_eq
  rw [h2]
  exact Measure.prod_smul_right (μ := m) (ν := ν.prod μ) (c : ℝ≥0∞)

theorem map_left_add (a : GL (Fin t) (AE D)) (ν : Measure (Mx D t n)) (hν : ν.IsAddHaarMeasure) (s : Mx D t n) :
    ν.map (fun U => mm a.1 U + s) = ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) = absA D (Matrix.GeneralLinearGroup.det a) ^ n := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n
      a (1 : GL (Fin n) (AE D))
    simpa using this
  have h := map_aff ν (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) s
  rw [hc, ← inv_pow] at h
  rw [← h]
  congr 1
  funext U
  simp only [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.mul_one, mm]

theorem map_tau {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure)
    (a : GL (Fin t) (AE D)) (b : GA D W) {S : GA D W → Mx D t n} (hS : Continuous S) :
    (Q0 I μ).map (fun p : Par D n t W => (p.1 * b, mm a.1 p.2.1 + S p.1, p.2.2)) =
      ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • Q0 I μ := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨g1, g2, g3, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hH := hf.1
  have hhaar := I.haar
  haveI := GlobalTheory.RegSch.Ibp.isMulRightInvariant I.m
  have hr : MeasurePreserving (fun h : GA D W => h * b) I.m I.m := measurePreserving_mul_right I.m b
  have hsm : Measurable (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) := by
    have : Continuous (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) :=
      (continuous_const.matrix_mul continuous_snd).add (hS.comp continuous_fst)
    exact this.measurable
  exact map_skew hr hsm fun h => map_left_add a I.μ₁ hH (S h)

theorem continuous_S (hn : W.rank + t = n) (c : Mx D t W.rank) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun h : GA D W => jn hn (mm c (ww W x₀ h)) (0 : Mx D t t) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun h : GA D W => mm c (ww W x₀ h) := continuous_const.matrix_mul (continuous_ww x₀)
  refine continuous_matrix fun i j => ?_
  unfold jn
  simp only [Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact hc.matrix_elem i k
  | inr k => exact continuous_const

theorem law : Law := by
  intro D n t B W d hn I μ hμ x₀ q
  subst hn
  obtain ⟨c, g, hcg⟩ := GlobalTheory.RegSch.IkStab.exists_valuation_adapted_index d q.2
  have h1 := GlobalTheory.RegSW.mul_jX d q
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨p1, p2⟩ := top_par (D := D) (W.rank + t) t W
  obtain ⟨-, -, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t (W.rank + t)
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have o0 : OpensMeasurableSpace (Par D (W.rank + t) t W) := p1.opensMeasurable
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have hS := continuous_S (W := W) (t := t) rfl c x₀
  have hac : Measurable (ac B (q : GA D B) (a := W.rank) (b := t)) :=
    ((continuous_ac B).comp (continuous_const.prodMk continuous_id)).measurable
  have hτ : Measurable fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    Continuous.measurable ((continuous_fst.mul continuous_const).prodMk
      (((continuous_const.matrix_mul (continuous_fst.comp continuous_snd)).add (hS.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd)))
  have e : (ac B (q : GA D B)) ∘ zp d rfl x₀ = zp d rfl x₀ ∘ fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    funext fun p => ac_zp d rfl x₀ h1 hcg p
  unfold rho
  rw [Measure.map_map hac (measurable_zp d rfl x₀), e, ← Measure.map_map (measurable_zp d rfl x₀) hτ,
    map_tau I μ hμ (GlobalTheory.RegSW.onX d q) g⁻¹ hS, Measure.map_smul]
  rfl

end GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

end
