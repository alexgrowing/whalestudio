import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellFew

theorem det_split {R : Type} [CommRing R] {n : ℕ} (e : R) (he : e * e = e)
    (M N : Matrix (Fin n) (Fin n) R) :
    Matrix.det ((1 - e) • N + e • M) = (1 - e) * Matrix.det N + e * Matrix.det M := by
  have hprod : ∀ (s : Finset (Fin n)) (a b : Fin n → R),
      ∏ i ∈ s, ((1 - e) * a i + e * b i) = (1 - e) * ∏ i ∈ s, a i + e * ∏ i ∈ s, b i := by
    intro s a b
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih]
      have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
      have h2 : (1 - e) * e = 0 := by linear_combination -he
      linear_combination (a i * ∏ i ∈ s, a i) * h1 + (b i * ∏ i ∈ s, b i) * he +
        (a i * ∏ i ∈ s, b i + b i * ∏ i ∈ s, a i) * h2
  simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hprod]
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

theorem few_roots {m p M : ℕ} {Ω : Fin m → Type} [∀ i, Field (Ω i)] [∀ i, CharZero (Ω i)]
    (A B : ∀ i, Matrix (Fin p) (Fin p) (Ω i)) (h1 : ∀ i, Matrix.det (A i - B i) ≠ 0)
    (t : Fin M → ℚ) (ht : Function.Injective t) :
    Set.ncard {j | ¬ ∀ i, Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) ≠ 0} ≤ m * p := by
  classical
  have hone : ∀ i, (Finset.univ.filter fun j => Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) = 0).card ≤ p := by
    intro i
    set P : Polynomial (Ω i) := Matrix.det ((Polynomial.X : Polynomial (Ω i)) • (-B i).map Polynomial.C + (A i).map Polynomial.C) with hP
    have hev : ∀ r : Ω i, P.eval r = Matrix.det (A i - r • B i) := by
      intro r
      have := RingHom.map_det (Polynomial.evalRingHom r) ((Polynomial.X : Polynomial (Ω i)) • (-B i).map Polynomial.C + (A i).map Polynomial.C)
      simp only [Polynomial.coe_evalRingHom] at this
      rw [hP, this]
      congr 1
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
        Matrix.sub_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hP0 : P ≠ 0 := by
      intro h0
      apply h1 i
      have := hev 1
      rw [h0] at this
      simpa using this.symm
    have hdeg : P.natDegree ≤ p := by
      have := Polynomial.natDegree_det_X_add_C_le (-B i) (A i)
      simpa using this
    calc _ ≤ P.roots.toFinset.card := by
          refine Finset.card_le_card_of_injOn (fun j => ((t j : ℚ) : Ω i)) ?_ ?_
          · intro j hj
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
            simp only [Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset]
            rw [Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hev]
            exact hj
          · intro a _ b _ hab
            exact ht (Rat.cast_injective hab)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ ≤ p := hdeg
  have hsub : {j | ¬ ∀ i, Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) ≠ 0} ⊆
      ((Finset.univ.biUnion fun i => Finset.univ.filter fun j => Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) = 0 : Finset (Fin M)) : Set (Fin M)) := by
    intro j hj
    simp only [Set.mem_setOf_eq, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, by simp, by simpa using hi⟩
  calc _ ≤ Set.ncard ((Finset.univ.biUnion fun i => Finset.univ.filter fun j => Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) = 0 : Finset (Fin M)) : Set (Fin M)) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.biUnion fun i => Finset.univ.filter fun j => Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) = 0 : Finset (Fin M)).card := Set.ncard_coe_finset _
    _ ≤ ∑ i : Fin m, (Finset.univ.filter fun j => Matrix.det (A i - ((t j : ℚ) : Ω i) • B i) = 0).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin m, p := Finset.sum_le_sum fun i _ => hone i
    _ = m * p := by simp

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' = blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable {D : D7} {p : ℕ}

theorem cA_incA_sig (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem cA_incA_rat (q : ℚ) : cA D (incA D (q : D.host.E)) = incA D (q : D.host.E) := by
  rw [cA_incA_sig]
  congr 1
  exact map_ratCast (D.sp.cm.sig : D.host.E →+* D.host.E) q

theorem adj_rat (y : HermE D p) : adj (rat y.1 : Mx D p p) = rat y.1 := by
  ext i j
  have h := congrFun (congrFun y.2 i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at h
  simp only [adj, rat, Matrix.transpose_apply, Matrix.map_apply]
  rw [cA_incA_sig]
  exact congrArg _ h

theorem mat_mul (g h : G D p) : mat (g * h) = mat g * mat h := by
  simp [mat, map_mul]

theorem mat_one' : mat (1 : G D p) = 1 := by
  simp [mat]

theorem matrix_eq_block_decomposition (g : G D p) :
    mat g = blk4 ((mat g).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      ((mat g).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ (cB g) (dB g) := by
  unfold blk4 cB dB
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem mat_conj (w n : G D p) (b : Mx D p p) (hw : IsW w) (hn : mat n = blk4 1 b 0 1) :
    mat (w * n * w⁻¹) = blk4 1 0 (-b) 1 := by
  have hK : (blk4 0 (-1) 1 0 : Mx D (p + p) (p + p)) * mat w = 1 := by
    rw [hw, submatrix_fromBlocks_mul]
    simpa using block_matrix_one
  have hinv : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    have h1 : mat w * mat w⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one']
    calc mat w⁻¹ = (blk4 0 (-1) 1 0 * mat w) * mat w⁻¹ := by rw [hK, one_mul]
      _ = blk4 0 (-1) 1 0 := by rw [mul_assoc, h1, mul_one]
  rw [mat_mul, mat_mul, hinv, hn, hw, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

theorem cB_of (g : G D p) {a b c d : Mx D p p} (h : mat g = blk4 a b c d) : cB g = c := by
  unfold cB
  rw [h]
  unfold blk4
  simp

theorem cB_mul_conj (x γ : G D p) (b : Mx D p p) (h : mat γ = blk4 1 0 (-b) 1) :
    cB (x * γ) = cB x - dB x * b := by
  have h1 := mat_mul x γ
  rw [h, matrix_eq_block_decomposition x, submatrix_fromBlocks_mul] at h1
  rw [cB_of _ h1]
  simp [sub_eq_add_neg]

def lineS (e : AE D) (he2 : e * e = e) (hce : cA D e = e) (Y : Mx D p p) (hY : adj Y = Y) (s : AE D) (hs : cA D s = s) :
    hermS D p e :=
  ⟨⟨(s * e) • Y, by
    show adj ((s * e) • Y) = (s * e) • Y
    ext i j
    have h := congrFun (congrFun hY i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply] at h
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs, hce, h]⟩, by
    show e • ((s * e) • Y) = (s * e) • Y
    rw [smul_smul]
    congr 1
    linear_combination s * he2⟩

theorem cell_iff {m : ℕ} {Ω : Fin m → Type} [∀ i, Field (Ω i)] (φ : ∀ i, AE D →+* Ω i) (e : AE D) (he2 : e * e = e)
    (hcrit : ∀ z : AE D, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0) (M : Mx D p p) :
    IsUnit (Matrix.det ((1 - e) • (1 : Mx D p p) + e • M)) ↔ ∀ i, Matrix.det ((φ i).mapMatrix M) ≠ 0 := by
  rw [det_split e he2 M 1, Matrix.det_one, mul_one, hcrit]
  exact forall_congr' fun i => by rw [RingHom.map_det]

theorem mem_iff (nb : hermA D p → G D p) (hnb : IsNMap nb) (w : G D p) (hw : IsW w) (e : AE D) (he2 : e * e = e)
    (hce : cA D e = e) {m : ℕ} {Ω : Fin m → Type} [∀ i, Field (Ω i)] (φ : ∀ i, AE D →+* Ω i) (hφe : ∀ i, φ i e = 1)
    (hcrit : ∀ z : AE D, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0) (Y : Mx D p p) (hY : adj Y = Y)
    (x : G D p) (s : AE D) (hs : cA D s = s) :
    x * (w * nb (lineS e he2 hce Y hY s hs).1 * w⁻¹) ∈ cell e ↔
      ∀ i, Matrix.det ((φ i).mapMatrix (cB x) - φ i s • (φ i).mapMatrix (dB x * Y)) ≠ 0 := by
  have hmat : mat (w * nb (lineS e he2 hce Y hY s hs).1 * w⁻¹) = blk4 1 0 (-((s * e) • Y)) 1 :=
    mat_conj w _ _ hw (hnb _)
  show IsUnit _ ↔ _
  rw [cB_mul_conj x _ _ hmat, cell_iff φ e he2 hcrit]
  refine forall_congr' fun i => ?_
  have : (φ i).mapMatrix (cB x - dB x * (s * e) • Y) =
      (φ i).mapMatrix (cB x) - φ i s • (φ i).mapMatrix (dB x * Y) := by
    rw [map_sub, Matrix.mul_smul]
    generalize dB x * Y = Z
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hφe, mul_one]
  rw [this]

theorem small_line (nb : hermA D p → G D p) (w : G D p) (e : AE D) (he2 : e * e = e) (hce : cA D e = e)
    (hcont0 : Continuous (fun y : hermS D p e => nb y.1)) (hnb0 : nb (0 : hermS D p e).1 = 1)
    (hsm : ∀ V ∈ 𝓝 (0 : AE D), ∀ M : ℕ, ∃ t : Fin M → ℚ, Function.Injective t ∧ ∀ j, incA D (t j : D.host.E) * e ∈ V)
    (Y : Mx D p p) (hY : adj Y = Y) (V : Set (G D p)) (hV : V ∈ 𝓝 (1 : G D p)) (M : ℕ) :
    ∃ t : Fin M → ℚ, Function.Injective t ∧
      ∀ j, w * nb (lineS e he2 hce Y hY (incA D (t j : D.host.E)) (cA_incA_rat _)).1 * w⁻¹ ∈ V := by
  have hcont : Continuous (fun z : hermS D p e => w * nb z.1 * w⁻¹) :=
    (continuous_const.mul hcont0).mul continuous_const
  have hV0 : (fun z : hermS D p e => w * nb z.1 * w⁻¹) ⁻¹' V ∈ 𝓝 (0 : hermS D p e) := by
    apply hcont.continuousAt.preimage_mem_nhds
    show V ∈ 𝓝 (w * nb (0 : hermS D p e).1 * w⁻¹)
    rw [hnb0, mul_one, mul_inv_cancel]
    exact hV
  have hind : Topology.IsInducing (fun z : hermS D p e => (z.1.1 : Mx D p p)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hind.nhds_eq_comap, Filter.mem_comap] at hV0
  obtain ⟨W', hW', hsub⟩ := hV0
  have hV' : (fun a : AE D => a • Y) ⁻¹' W' ∈ 𝓝 (0 : AE D) := by
    have hc : Continuous (fun a : AE D => a • Y) := continuous_id.smul continuous_const
    apply hc.continuousAt.preimage_mem_nhds
    show W' ∈ 𝓝 ((0 : AE D) • Y)
    rw [zero_smul]
    exact hW'
  obtain ⟨t, ht, htV⟩ := hsm _ hV' M
  exact ⟨t, ht, fun j => hsub (a := lineS e he2 hce Y hY _ (cA_incA_rat _)) (htV j)⟩

theorem few_core (mu : (G D p → ℂ) → ℂ) (h : G D p → ℝ) (nb : hermA D p → G D p) (hnb : IsNMap nb) (w : G D p) (hw : IsW w)
    (hInv : ∀ y, Inv (P D p) h mu (w * nb y * w⁻¹)) (e : AE D) (he2 : e * e = e) (hce : cA D e = e)
    (τ : G D p → hermS D p e) (hcell : IsCell (P D p) (cell e) τ w (fun y : hermS D p e => nb y.1))
    {m : ℕ} {Ω : Fin m → Type} [∀ i, Field (Ω i)] (φ : ∀ i, AE D →+* Ω i) (hφe : ∀ i, φ i e = 1)
    (hcrit : ∀ z : AE D, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0)
    (hsm : ∀ V ∈ 𝓝 (0 : AE D), ∀ M : ℕ, ∃ t : Fin M → ℚ, Function.Injective t ∧ ∀ j, incA D (t j : D.host.E) * e ∈ V)
    (g : G D p) (Y : Mx D p p) (hY : adj Y = Y)
    (hy : IsUnit (Matrix.det ((1 - e) • (1 : Mx D p p) + e • (cB g - dB g * Y)))) :
    ∃ (U : Set (G D p)) (d : ℕ), IsOpen U ∧ g ∈ U ∧ (∀ q ∈ P D p, ∀ x ∈ U, q * x ∈ U) ∧ ∀ V ∈ 𝓝 (1 : G D p), ∀ M : ℕ,
      ∃ γ : Fin M → G D p, (∀ j, γ j ∈ V ∧ Inv (P D p) h mu (γ j)) ∧ ∀ x ∈ U, Set.ncard {j | x * γ j ∉ cell e} ≤ d := by
  have hcz : ∀ i, CharZero (Ω i) := fun i =>
    (RingHom.charZero_iff ((φ i).comp (incA D)).injective).1 inferInstance
  have memI := mem_iff nb hnb w hw e he2 hce φ hφe hcrit Y hY
  have hnb0 : nb (0 : hermS D p e).1 = 1 := by
    have := hcell.nbAdd 0 0
    simpa using this
  refine ⟨{x | x * (w * nb (lineS e he2 hce Y hY 1 (map_one _)).1 * w⁻¹) ∈ cell e}, m * p, ?_, ?_, ?_, ?_⟩
  · exact hcell.isOpen.preimage (continuous_id.mul continuous_const)
  · show _ ∈ cell e
    rw [memI]
    intro i
    have h2 := (cell_iff φ e he2 hcrit _).1 hy i
    rw [map_sub] at h2
    simpa using h2
  · intro q hq x hx
    show _ ∈ cell e
    rw [mul_assoc]
    exact (hcell.left q hq _ hx).1
  · intro V hV M
    obtain ⟨t, ht, htV⟩ := small_line nb w e he2 hce hcell.nbCont hnb0 hsm Y hY V hV M
    refine ⟨fun j => _, fun j => ⟨htV j, hInv _⟩, ?_⟩
    intro x hx
    have h1 : ∀ i, Matrix.det ((φ i).mapMatrix (cB x) - (φ i).mapMatrix (dB x * Y)) ≠ 0 := by
      have := (memI x 1 (map_one _)).1 hx
      simpa using this
    have hset : {j | x * (w * nb (lineS e he2 hce Y hY (incA D (t j : D.host.E)) (cA_incA_rat _)).1 * w⁻¹) ∉ cell e} =
        {j | ¬ ∀ i, Matrix.det ((φ i).mapMatrix (cB x) - ((t j : ℚ) : Ω i) • (φ i).mapMatrix (dB x * Y)) ≠ 0} := by
      ext j
      simp only [Set.mem_setOf_eq]
      rw [memI]
      refine not_congr (forall_congr' fun i => ?_)
      have : φ i (incA D (t j : D.host.E)) = ((t j : ℚ) : Ω i) :=
        map_ratCast ((φ i).comp (incA D)) (t j)
      rw [this]
    rw [hset]
    exact few_roots (fun i => (φ i).mapMatrix (cB x)) (fun i => (φ i).mapMatrix (dB x * Y)) h1 t ht

theorem fewC : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.UnitCrit → PositivityTheory.Rg.Rsw.Cell.Move → PositivityTheory.Rg.Rsw.Cell.SmallRat →
    PositivityTheory.Rg.Rsw.Cell.CellAlg → PositivityTheory.Rg.Rsw.Cell.FewC := by
  intro hI hU hM hS hC D p mu h nb hnb w hw hInv S e he g
  obtain ⟨he2, hce⟩ := (hI D S).2 e he
  obtain ⟨τ, hcell, -, -⟩ := hC D p nb hnb w hw S e he
  obtain ⟨m, Ω, inst, φ, hφe, hcrit⟩ := hU D S e he
  obtain ⟨y, hy⟩ := hM D p S e he g
  exact @few_core D p mu h nb hnb w hw hInv e he2 hce τ hcell m Ω inst φ hφe hcrit (hS D S e he) g (rat y.1) (adj_rat y) hy

end GlobalTheory.CompanionTheory.CellFew

end
