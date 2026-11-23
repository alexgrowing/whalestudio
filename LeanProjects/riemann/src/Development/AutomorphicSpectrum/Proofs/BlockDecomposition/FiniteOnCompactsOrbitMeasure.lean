import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem isCompact_mt_preimage (V : HSp D) {T : Set (Mx D V.rank V.rank)} (hT : IsCompact T) :
    IsCompact {g : GA D V | mt V g ∈ T} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, i4, -⟩ := top_mx (D := D) V.rank V.rank
  have i1 : T1Space (Mx D V.rank V.rank) := @T2Space.t1Space _ _ i4
  have he : Topology.IsClosedEmbedding (fun g : GA D V =>
      Units.embedProduct (Mx D V.rank V.rank) (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g)) :=
    Units.isClosedEmbedding_embedProduct.comp (isClosedEmbedding_matHom_GAd D.sp.cm.sig V.gram)
  have hc : Continuous fun X : Mx D V.rank V.rank => giA V * (adj X * gA V) :=
    continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)
  have hK := he.isCompact_preimage (hT.prod ((hT.image hc).image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (hT.isClosed.preimage (continuous_mt V)) fun g hg => ?_
  refine ⟨hg, _, ⟨mt V g, hg, rfl⟩, ?_⟩
  simp only [Units.embedProduct_apply]
  rw [← GlobalTheory.MixModel.mt_inv]; rfl

theorem det_ne_zero {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} {b : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hb : b.det ≠ 0) (h : gramQ W x₀ = b) : x₀.det ≠ 0 := by
  intro h0
  apply hb
  rw [← h, gramQ]
  simp [Matrix.det_mul, h0]

theorem rat_inv_mul {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀⁻¹) (rat x₀) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_mul_inv {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀) (rat x₀⁻¹) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem join_first_second_columns_eq (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with s | s <;> simp [jn, c1, c2]

theorem continuous_jn (hn : W.rank + t = n) {a : ℕ} :
    Continuous fun p : Mx D a W.rank × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
  · exact (continuous_fst.matrix_elem i s)
  · exact (continuous_snd.matrix_elem i s)

theorem box_rec (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    mm d.p0 (mm d.jX u + mm d.j0 w) = w ∧ mm d.pX (mm d.jX u + mm d.j0 w) = u := by
  constructor
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.p0_j0,
      Matrix.zero_mul, Matrix.one_mul, zero_add]
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, d.pX_j0,
      Matrix.zero_mul, Matrix.one_mul, add_zero]

theorem zp_rec (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (p : Par D n t W) :
    mm d.p0 (zp d hn x₀ p).1 = ww W x₀ p.1 ∧ mm d.pX (zp d hn x₀ p).1 = c1 hn p.2.1 ∧
      mm d.p0 (zp d hn x₀ p).2 = mm (ww W x₀ p.1) p.2.2 ∧
      mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2) = c2 hn p.2.1 := by
  obtain ⟨h1, h2⟩ := box_rec (a := W.rank) d (c1 hn p.2.1) (ww W x₀ p.1)
  refine ⟨h1, h2, ?_, ?_⟩
  · change mm d.p0 (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1)) = _
    simp only [mm] at h1 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc d.p0 _ p.2.2, h1, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  · change mm d.pX (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1) -
      mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2) = _
    rw [add_sub_cancel_left, mm, mm, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

theorem ac_ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V g (ac V g⁻¹ z) = z := by
  have e : ∀ {c : ℕ} (x : Mx D V.rank c), mm (mt V g) (mm (mt V g⁻¹) x) = x := fun x => by
    rw [mm, mm, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul]
  exact Prod.ext (e z.1) (e z.2)

theorem exists_box (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (hx : x₀.det ≠ 0)
    {C : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hC : IsCompact C) :
    ∃ (Ah : Set (GA D W)) (AU : Set (Mx D t n)) (Ay : Set (Mx D W.rank t)),
      IsCompact Ah ∧ IsCompact AU ∧ IsCompact Ay ∧ ∀ (k : I.l.K) (p : Par D n t W),
        ac B ((k : GA D B)⁻¹) (zp d hn x₀ p) ∈ C → p.1 ∈ Ah ∧ p.2.1 ∈ AU ∧ p.2.2 ∈ Ay := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨t1, -, -, -, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨t2, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨t3, -, -, -, -⟩ := top_mx (D := D) t W.rank
  obtain ⟨t4, -, -, -, -⟩ := top_mx (D := D) t t
  set C' : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    (fun u : GA D B × (Mx D B.rank W.rank × Mx D B.rank t) => ac B u.1 u.2) '' ((I.l.K : Set (GA D B)) ×ˢ C) with hC'
  have cC' : IsCompact C' := (I.good.isCompact_K.prod hC).image (continuous_ac B)
  set Aw : Set (Mx D W.rank W.rank) := (fun z : Mx D B.rank W.rank × Mx D B.rank t => mm d.p0 z.1) '' C' with hAw
  have cAw : IsCompact Aw := cC'.image (continuous_const.matrix_mul continuous_fst)
  set T : Set (Mx D W.rank W.rank) := (fun X : Mx D W.rank W.rank => mm X (rat x₀⁻¹)) '' Aw with hT
  have cT : IsCompact T := cAw.image (continuous_id.matrix_mul continuous_const)
  set Ah : Set (GA D W) := (fun g : GA D W => g⁻¹) '' {g : GA D W | mt W g ∈ T} with hAh
  have cAh : IsCompact Ah := (isCompact_mt_preimage W cT).image continuous_inv
  set Ay : Set (Mx D W.rank t) :=
    (fun u : GA D W × (Mx D B.rank W.rank × Mx D B.rank t) => mm (rat x₀⁻¹) (mm (mt W u.1) (mm d.p0 u.2.2))) ''
      (Ah ×ˢ C') with hAy
  have cAy : IsCompact Ay := (cAh.prod cC').image (continuous_const.matrix_mul
    (((continuous_mt W).comp continuous_fst).matrix_mul
      (continuous_const.matrix_mul (continuous_snd.comp continuous_snd))))
  set AU : Set (Mx D t n) :=
    (fun u : (Mx D B.rank W.rank × Mx D B.rank t) × Mx D W.rank t =>
      jn hn (mm d.pX u.1.1) (mm d.pX (u.1.2 - mm u.1.1 u.2))) '' (C' ×ˢ Ay) with hAU
  have s2 : ContinuousSub (Mx D B.rank t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ t2
  have cAU : IsCompact AU := (cC'.prod cAy).image ((continuous_jn (W := W) hn).comp
    ((continuous_const.matrix_mul (continuous_fst.comp continuous_fst)).prodMk
      (continuous_const.matrix_mul ((continuous_snd.comp continuous_fst).sub
        ((continuous_fst.comp continuous_fst).matrix_mul continuous_snd)))))
  refine ⟨Ah, AU, Ay, cAh, cAU, cAy, fun k p hp => ?_⟩
  have e1 := rat_mul_inv hx
  have e2 := rat_inv_mul hx
  simp only [mm] at e1 e2
  have hz : zp d hn x₀ p ∈ C' := ⟨((k : GA D B), ac B ((k : GA D B)⁻¹) (zp d hn x₀ p)), ⟨k.2, hp⟩, ac_ac B _ _⟩
  obtain ⟨r1, r2, r3, r4⟩ := zp_rec d hn x₀ p
  have hw : ww W x₀ p.1 ∈ Aw := ⟨_, hz, r1⟩
  have hg : mt W p.1⁻¹ ∈ T := ⟨_, hw, by
    change mm (mm (mt W p.1⁻¹) (rat x₀)) (rat x₀⁻¹) = _
    simp only [mm]
    rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  have hh : p.1 ∈ Ah := ⟨p.1⁻¹, hg, inv_inv _⟩
  have hy : p.2.2 ∈ Ay := ⟨(p.1, zp d hn x₀ p), ⟨hh, hz⟩, by
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm d.p0 (zp d hn x₀ p).2)) = _
    rw [r3]
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm (mm (mt W p.1⁻¹) (rat x₀)) p.2.2)) = _
    simp only [mm]
    rw [← Matrix.mul_assoc (mt W p.1), ← Matrix.mul_assoc (mt W p.1),
      GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, ← Matrix.mul_assoc, e2, Matrix.one_mul]⟩
  have hU : p.2.1 ∈ AU := ⟨(zp d hn x₀ p, p.2.2), ⟨hz, hy⟩, by
    change jn hn (mm d.pX (zp d hn x₀ p).1) (mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2)) = _
    rw [r2, r4, join_first_second_columns_eq]⟩
  exact ⟨hh, hU, hy⟩

end GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem isFiniteMeasureOnCompacts_nuT : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  intro D n t B W d hn I μ hμ b₀ hb x₀ hx
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, -, k4, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, -, l4, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := 𝓕
  have := I.haar
  have := I.probK
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have := sigmaFinite_parameter_product_measure I μ hμ
  refine ⟨fun C hC => ?_⟩
  obtain ⟨Ah, AU, Ay, cAh, cAU, cAy, h⟩ := Cpt.exists_box d hn I (Cpt.det_ne_zero hb hx) hC
  rw [nuT, Measure.map_apply (measurable_pi hn I x₀) hC.measurableSet]
  have hsub : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹' C ⊆
      Set.univ ×ˢ (Ah ×ˢ (AU ×ˢ Ay)) := fun p hp => by
    obtain ⟨a, b, c⟩ := h p.1 p.2 hp
    exact ⟨trivial, a, b, c⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Q0, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.mul_lt_top cAh.measure_lt_top
    (ENNReal.mul_lt_top cAU.measure_lt_top cAy.measure_lt_top))

end GlobalTheory.CompanionTheory.ColumnSplitting
end
