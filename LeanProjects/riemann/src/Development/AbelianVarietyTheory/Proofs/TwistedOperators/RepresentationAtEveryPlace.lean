import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowRep
open GlobalTheory.RootEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem diag_conj_symR {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {x y : GL (n ⊕ Fin c) k}
    {f : n ⊕ Fin c → k} (hy : y.val = diagonal f) (hx : x ∈ symR k n c) : y⁻¹ * x * y ∈ symR k n c := by
  have hf : ∀ r, f r ≠ 0 := fun r h => by
    have := congrFun (congrFun y.mul_inv r) r
    rw [hy, diagonal_mul, h, zero_mul, one_apply_eq] at this
    exact zero_ne_one this
  obtain rfl : y = GlobalTheory.SplitFlip.diagGL fun r => Units.mk0 (f r) (hf r) := Units.ext hy
  have ent : ∀ {m : Type} [Fintype m] [DecidableEq m] (g : m → kˣ) (z : GL m k) r s,
      ((GlobalTheory.SplitFlip.diagGL g)⁻¹ * z * GlobalTheory.SplitFlip.diagGL g).val r s = ((g r)⁻¹ : kˣ) * z.val r s * g s := by
    intro m _ _ g z r s
    change ((diagonal fun i => (((g i)⁻¹ : kˣ) : k)) * z.val * diagonal fun i => (g i : k)) r s = _
    rw [mul_diagonal, diagonal_mul]
  generalize (fun r => Units.mk0 (f r) (hf r)) = g
  have hN : ∀ p, N k n c p ≤ (N k n c p).comap (MulAut.conj (GlobalTheory.SplitFlip.diagGL g)⁻¹).toMonoidHom := fun p =>
    (Subgroup.closure_le _).2 fun z hz => Subgroup.subset_closure fun r s hrs => by
      change ((GlobalTheory.SplitFlip.diagGL g)⁻¹ * z * GlobalTheory.SplitFlip.diagGL g).val r s = _
      rw [ent, hz r s hrs]
      by_cases h : r = s
      · subst h; simp
      · simp [one_apply_ne h]
  have h : symR k n c ≤ (symR k n c).comap (MulAut.conj (GlobalTheory.SplitFlip.diagGL g)⁻¹).toMonoidHom := by
    refine sup_le ?_ (sup_le (fun z hz => Subgroup.mem_sup_right (Subgroup.mem_sup_left (hN _ hz)))
      fun z hz => Subgroup.mem_sup_right (Subgroup.mem_sup_right (hN _ hz)))
    rintro _ ⟨z, rfl⟩
    refine Subgroup.mem_sup_left ⟨(GlobalTheory.SplitFlip.diagGL (g ∘ Sum.inl))⁻¹ * z * GlobalTheory.SplitFlip.diagGL (g ∘ Sum.inl), Units.ext ?_⟩
    ext r s
    change fromBlocks _ 0 0 1 r s = ((GlobalTheory.SplitFlip.diagGL g)⁻¹ * embX c z * GlobalTheory.SplitFlip.diagGL g).val r s
    rw [ent]
    change _ = _ * fromBlocks z.val 0 0 1 r s * _
    rcases r with r | r <;> rcases s with s | s
    · exact ent _ _ _ _
    · simp
    · simp
    · by_cases h : r = s
      · subst h; simp
      · simp [one_apply_ne h]
  exact h hx

def piAt {D : D7} (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

def sumCols {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) {K : Type} [Field K] (π : AE D →+* K)
    (b : Matrix (Fin A.rank) (Fin A.rank) K) (u : Fin c → K) : Matrix (Fin B.rank) (Fin A.rank ⊕ Fin c) K :=
  fromCols ((frameMat B A d.ι).map (π.comp (incA D)) * b) (d.a.map (π.comp (incA D)) * diagonal u)

theorem frame_val {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (w : Pl D.host.E)
    {β : GL (Fin A.rank) (Lev.EAf D)} {β' : GL (Fin B.rank) (Lev.EAf D)} {u : Fin c → Kw w} (hF : IsSumFrame d w β β' u) :
    ∃ Γ : Matrix (Fin A.rank ⊕ Fin c) (Fin B.rank) (Kw w), Γ * sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u = 1 ∧
      sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u * Γ = 1 ∧ ∀ g : GA D B,
      (frameGL d.rank (inBasis rfl β' w (Lev.finE B g))).val =
        Γ * ((mt B g).map (piAt w) * sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u) := by
  have hπ : ∀ {p q : ℕ} (X : Matrix (Fin p) (Fin q) D.host.E), X.map ((piAt w).comp (incA D)) = X.map (algebraMap D.host.E (Kw w)) :=
    fun X => Matrix.ext fun i j => GlobalTheory.FunObj.Comparison₂.cpt_tmul w _
  have e : sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u = (GlobalTheory.StdFrames.loc w β').val.submatrix id (frame d.rank) := by
    rw [sumCols, hπ, hπ]; exact hF.symm
  rw [e]
  refine ⟨((GlobalTheory.StdFrames.loc w β')⁻¹).val.submatrix (frame d.rank) id, ?_, ?_, fun g => ?_⟩
  · exact (congrArg (fun X => X.submatrix (frame d.rank) (frame d.rank)) (GlobalTheory.StdFrames.loc w β').inv_mul).trans
      (submatrix_one_equiv _)
  · exact (submatrix_mul_equiv _ _ _ (frame d.rank) _).trans
      ((congrArg (fun X => X.submatrix id id) (GlobalTheory.StdFrames.loc w β').mul_inv).trans rfl)
  · refine Matrix.ext fun r s => ?_
    change (GlobalTheory.StdFrames.loc w (β'⁻¹ * Lev.finE B g * β'⁻¹⁻¹)).val (frame d.rank r) (frame d.rank s) =
      ((GlobalTheory.StdFrames.loc w β')⁻¹ * (GlobalTheory.StdFrames.loc w (Lev.finE B g) * GlobalTheory.StdFrames.loc w β')).val (frame d.rank r) (frame d.rank s)
    rw [inv_inv, map_mul, map_mul, map_inv, mul_assoc]

theorem mul_sumCols_diag {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) {K : Type} [Field K] (π : AE D →+* K)
    (b : Matrix (Fin A.rank) (Fin A.rank) K) (u : Fin c → K) {g : GA D B} {l : Fin c → D.host.E}
    (h0 : HMul.hMul (mt B g) (rat (frameMat B A d.ι)) = rat (frameMat B A d.ι))
    (h1 : HMul.hMul (mt B g) (rat d.a) = rat (d.a * diagonal l)) :
    ∃ f, (mt B g).map π * sumCols d π b u = sumCols d π b u * diagonal f := by
  refine ⟨Sum.elim (fun _ => 1) fun p => π (incA D (l p)), ?_⟩
  have a0 : (mt B g).map π * (frameMat B A d.ι).map (π.comp (incA D)) = (frameMat B A d.ι).map (π.comp (incA D)) :=
    Matrix.map_mul.symm.trans (congrArg (·.map π) h0)
  have a1 : (mt B g).map π * d.a.map (π.comp (incA D)) = (d.a * diagonal l).map (π.comp (incA D)) :=
    Matrix.map_mul.symm.trans (congrArg (·.map π) h1)
  rw [Matrix.map_mul, diagonal_map (map_zero _)] at a1
  rw [sumCols, mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a0, a1]
  refine Matrix.ext fun r s => ?_
  refine Eq.trans ?_ (mul_diagonal _ _ _ _).symm
  rcases s with s | s
  · exact (mul_one _).symm
  · simp only [fromCols_apply_inr, mul_diagonal, Sum.elim_inr, RingHom.comp_apply]
    ring

theorem frame_diag {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (w : Pl D.host.E)
    {β : GL (Fin A.rank) (Lev.EAf D)} {β' : GL (Fin B.rank) (Lev.EAf D)} {u : Fin c → Kw w} (hF : IsSumFrame d w β β' u)
    {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank) (hab : a + c = b) {g : GA D B} {l : Fin c → D.host.E}
    (h0 : HMul.hMul (mt B g) (rat (frameMat B A d.ι)) = rat (frameMat B A d.ι))
    (h1 : HMul.hMul (mt B g) (rat d.a) = rat (d.a * diagonal l)) :
    ∃ f, (frameGL hab (inBasis hb β' w (Lev.finE B g))).val = diagonal f := by
  subst ha hb
  obtain ⟨Γ, h, -, e⟩ := frame_val d w hF
  obtain ⟨f, hf⟩ := mul_sumCols_diag d (piAt w) (GlobalTheory.StdFrames.loc w β).val u h0 h1
  exact ⟨f, (e g).trans ((congrArg (Γ * ·) hf).trans ((Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * diagonal f) h).trans (Matrix.one_mul _))))⟩

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem glue_alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {X X' Y Y' G H : Matrix n n R} {e e' : R}
    (h0 : e * e' = 0) (h1 : e * e = e) (h2 : e' * e' = e') (hX : e • X = X) (hY : e • Y = Y) (hX' : e' • X' = X')
    (hY' : e' • Y' = Y') (hYX : Y * X = e • 1) (hXY : X' * Y' = e' • 1) (hHG : H * G = 1) (hGH : G * H = 1) :
    (X' + G * (Y * H) + (1 - e - e') • 1) * (G * (X + H * (Y' * G) + (1 - e - e') • 1)) = G := by
  have f1 : (1 - e - e') * e = 0 := by linear_combination -h1 - h0
  have f2 : (1 - e - e') * e' = 0 := by linear_combination -h2 - h0
  have f3 : (1 - e - e') * (1 - e - e') = 1 - e - e' := by linear_combination -f1 - f2
  have c1 : ∀ Z : Matrix n n R, H * (G * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have c2 : ∀ Z : Matrix n n R, G * (H * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hGH, Matrix.one_mul]
  have t1 : X' * (G * X) = 0 := by
    rw [← hX, ← hX', Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h0, zero_smul]
  have t2 : X' * (Y' * G) = e' • G := by rw [← Matrix.mul_assoc, hXY, Matrix.smul_mul, Matrix.one_mul]
  have t3 : (1 - e - e') • X' = 0 := by rw [← hX', smul_smul, f2, zero_smul]
  have t4 : Y * (H * (Y' * G)) = 0 := by
    rw [← hY, ← hY', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, h0, zero_smul]
  have t5 : (1 - e - e') • Y = 0 := by rw [← hY, smul_smul, f1, zero_smul]
  have t6 : (1 - e - e') • X = 0 := by rw [← hX, smul_smul, f1, zero_smul]
  have t7 : (1 - e - e') • Y' = 0 := by rw [← hY', smul_smul, f2, zero_smul]
  have u3 : (1 - e - e') • (X' * G) = 0 := by rw [← Matrix.smul_mul, t3, Matrix.zero_mul]
  have u5 : (1 - e - e') • (G * Y) = 0 := by rw [← Matrix.mul_smul, t5, Matrix.mul_zero]
  have u6 : (1 - e - e') • (G * X) = 0 := by rw [← Matrix.mul_smul, t6, Matrix.mul_zero]
  have u7 : (1 - e - e') • (Y' * G) = 0 := by rw [← Matrix.smul_mul, t7, Matrix.zero_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c1, c2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, hHG, t1, t2, t4, hYX, smul_add, u3, u5, u6, u7, smul_smul, f3, Matrix.mul_zero, add_zero, zero_add]
  rw [← add_smul, ← add_smul]
  convert one_smul R G using 2
  ring

variable {D : D7}

theorem exists_lift {n : ℕ} (P : Finset (Pl D.host.E)) (M : ∀ w : P, Matrix (Fin n) (Fin n) (Kw w.1)) :
    ∃ X : Matrix (Fin n) (Fin n) (AE D), X.map (infPart D) = 0 ∧ (∀ w : P, X.map (piAt w.1) = M w) ∧
      ∀ w ∉ P, X.map (piAt w) = 0 := by
  classical
  refine ⟨Matrix.of fun i j => ∑ w : P, atPl w.1 (M w i j), Matrix.ext fun i j => ?_, fun w => Matrix.ext fun i j => ?_,
    fun w hw => Matrix.ext fun i j => ?_⟩
  · exact (map_sum (infPart D) _ _).trans (Finset.sum_eq_zero fun v _ => (atPl_spec v.1 _).1)
  · refine (map_sum (piAt w.1) _ _).trans ((Finset.sum_eq_single w (fun v _ hv => ?_) fun h => absurd (Finset.mem_univ _) h).trans ?_)
    · exact ((atPl_spec v.1 _).2 w.1).trans (Pi.single_eq_of_ne (fun h => hv (Subtype.ext h.symm)) _)
    · exact ((atPl_spec w.1 _).2 w.1).trans (Pi.single_eq_same _ _)
  · refine (map_sum (piAt w) _ _).trans (Finset.sum_eq_zero fun v _ => ?_)
    exact ((atPl_spec v.1 _).2 w).trans (Pi.single_eq_of_ne (fun h : w = v.1 => hw (by rw [h]; exact v.2)) _)

theorem mx_ext {n : ℕ} {X Y : Matrix (Fin n) (Fin n) (AE D)} (h : X.map (infPart D) = Y.map (infPart D))
    (h' : ∀ w : Pl D.host.E, X.map (piAt w) = Y.map (piAt w)) : X = Y :=
  Matrix.ext fun i j => ae_ext (congrFun (congrFun h i) j) fun w => congrFun (congrFun (h' w) i) j

theorem map_smul_mx {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : Type} (e : R) (X : Matrix n n R) :
    (e • X).map f = f e • X.map f := Matrix.ext fun _ _ => f.map_mul _ _

theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : Type} {e : R} {X : Matrix n n R}
    (h : X.map f = 0 ∨ f e = 1) : (e • X).map f = X.map f := by
  rw [map_smul_mx]
  rcases h with h | h
  · rw [h, smul_zero]
  · rw [h, one_smul]

theorem map_mul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n] {e : R}
    {X Y : Matrix n n R} (h : (X.map f = 0 ∧ f e = 0) ∨ (f e = 1 ∧ Y.map f * X.map f = 1)) :
    (Y * X).map f = (e • (1 : Matrix n n R)).map f := by
  rw [map_smul_mx, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h, h', zero_smul, Matrix.mul_zero]
  · rw [h, h', one_smul]

theorem map_glue {R S : Type} [CommRing R] [Field S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n] {e e' : R}
    {Y' : Matrix n n R} (h0 : e * e' = 0) (h : f e = 1) (hY : e' • Y' = Y') (X G H : Matrix n n R) :
    (X + H * (Y' * G) + (1 - e - e') • (1 : Matrix n n R)).map f = X.map f := by
  have hp : f e' = 0 := by
    have := congrArg f h0
    rwa [map_mul, h, one_mul, map_zero] at this
  have h3 : Y'.map f = 0 := by rw [← hY, map_smul_mx, hp, zero_smul]
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, h3, map_smul_mx, map_sub,
    map_sub, map_one, hp, h]
  simp

theorem supp_glue {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e e' : R} {X Y' : Matrix n n R}
    (h0 : e * e' = 0) (h1 : e * e = e) (h2 : e' * e' = e') (hX : e • X = X) (hY : e' • Y' = Y') (G H : Matrix n n R) (i j : n) :
    (e + e') * (X + H * (Y' * G) + (1 - e - e') • (1 : Matrix n n R) - 1) i j =
      (X + H * (Y' * G) + (1 - e - e') • (1 : Matrix n n R) - 1) i j := by
  have h3 : e' • (H * (Y' * G)) = H * (Y' * G) := by rw [← Matrix.mul_smul, ← Matrix.smul_mul, hY]
  have k1 : e * X i j = X i j := congrFun (congrFun hX i) j
  have k2 : e' * (H * (Y' * G)) i j = (H * (Y' * G)) i j := congrFun (congrFun h3 i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  generalize (H * (Y' * G)) i j = z at k2 ⊢
  generalize (1 : Matrix n n R) i j = o
  linear_combination (1 - e') * k1 + (1 - e) * k2 + (X i j + z - 2 * o) * h0 - o * h1 - o * h2

set_option maxHeartbeats 1600000 in

theorem exists_glue (V : HSp D) {e : AE D} (h0 : e * cA D e = 0) (hee : e * e = e) {X Y : Mx D V.rank V.rank} (hX : e • X = X)
    (hY : e • Y = Y) (hYX : HMul.hMul Y X = e • (1 : Mx D V.rank V.rank)) :
    ∃ r : GA D V, SuppAt e V r ∧ ∀ w : Pl D.host.E, piAt w e = 1 → (mt V r).map (piAt w) = X.map (piAt w) := by
  have hc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hX' : cA D e • adj X = adj X := by rw [← adj_smul, hX]
  have hY' : cA D e • adj Y = adj Y := by rw [← adj_smul, hY]
  have hXY : HMul.hMul (adj X) (adj Y) = cA D e • (1 : Mx D V.rank V.rank) := by
    rw [← adj_mul, hYX, adj_smul, adj_one]
  have key := glue_alg h0 hee hc hX hY hX' hY' hYX hXY (giA_mul_gA V) (gA_mul_giA V)
  have hf : cA D (1 - e - cA D e) = 1 - e - cA D e := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, cA_cA, sub_right_comm]
  have hadj : adj (X + HMul.hMul (giA V) (HMul.hMul (adj Y) (gA V)) + (1 - e - cA D e) • (1 : Mx D V.rank V.rank)) =
      adj X + HMul.hMul (gA V) (HMul.hMul Y (giA V)) + (1 - e - cA D e) • (1 : Mx D V.rank V.rank) := by
    rw [adj_add, adj_add, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, adj_smul, adj_one, Matrix.mul_assoc, hf]
  obtain ⟨r, hr⟩ : ∃ r : GA D V, mt V r = X + HMul.hMul (giA V) (HMul.hMul (adj Y) (gA V)) + (1 - e - cA D e) • (1 : Mx D V.rank V.rank) :=
    ⟨ofMat V _ ((congrArg (HMul.hMul · _) hadj).trans key), rfl⟩
  refine ⟨r, fun i j => ?_, fun w hw => ?_⟩
  · rw [hr]
    have := supp_glue h0 hee hc hX hY' (gA V) (giA V) i j
    exact this
  · rw [hr]
    have := map_glue (piAt w) h0 hw hY' X (gA V) (giA V)
    exact this

set_option maxHeartbeats 800000 in

theorem exists_suppAt_loc_eq : ∀ {D : D7} (V : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (g : ∀ w : P, GL (Fin V.rank) (Kw w.1)), ∃ r : GA D V, SuppAt e V r ∧ ∀ w : P, GlobalTheory.StdFrames.loc w.1 (Lev.finE V r) = g w := by
  intro D V P e he g
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e1 : ∀ w ∈ P, piAt w e = 1 := e1
  replace e2 : ∀ w ∉ P, piAt w e = 0 := e2
  have hee : e * e = e := ae_ext (((infPart D).map_mul e e).trans ((congrArg (HMul.hMul (infPart D e)) e0).trans ((mul_zero _).trans e0.symm))) fun w => by
    change piAt w (e * e) = piAt w e
    rw [RingHom.map_mul]
    by_cases h : w ∈ P
    · rw [e1 w h, mul_one]
    · rw [e2 w h, mul_zero]
  have sm : ∀ X : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map (infPart D) = 0 → (∀ w ∉ P, X.map (piAt w) = 0) → e • X = X :=
    fun X a c => mx_ext (map_smul_eq _ (.inl a)) fun w => map_smul_eq _ ((em (w ∈ P)).elim (fun h => .inr (e1 w h)) fun h => .inl (c w h))
  obtain ⟨X, a, b, c⟩ := exists_lift P fun w => (g w).val
  obtain ⟨Y, a', b', c'⟩ := exists_lift P fun w => (g w)⁻¹.val
  obtain ⟨r, hr, h⟩ := exists_glue V he.2 hee (sm X a c) (sm Y a' c') (mx_ext (map_mul_eq _ (.inl ⟨a, e0⟩)) fun w =>
    map_mul_eq _ ((em (w ∈ P)).elim (fun h => .inr ⟨e1 w h, by rw [b ⟨w, h⟩, b' ⟨w, h⟩, Units.inv_mul]⟩) fun h => .inl ⟨c w h, e2 w h⟩))
  exact ⟨r, hr, fun w => Units.ext ((h w.1 (e1 _ w.2)).trans (b w))⟩

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.LocGrpIff
variable {D : D7} {K : Type} [Field K] (π : AE D →+* K)

section Witt
variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y₀ : Type} [Fintype Y₀] [DecidableEq Y₀]
  (b : Matrix (Fin S₀.rank) Y₀ K) (b' : Matrix Y₀ (Fin S₀.rank) K)

def wCols : Matrix (Fin S.rank) (Y₀ ⊕ (Fin ρ ⊕ Fin ρ)) K := fromCols (d.j0.map π * b) (fromCols (d.jX.map π) (d.jY.map π))

def wRows : Matrix (Y₀ ⊕ (Fin ρ ⊕ Fin ρ)) (Fin S.rank) K := fromRows (b' * d.p0.map π) (fromRows (d.pX.map π) (d.pY.map π))

theorem wRows_wCols (hb : b' * b = 1) : wRows π d b' * wCols π d b = 1 := by
  have h0 : ∀ {a b : ℕ}, (0 : Mx D a b).map π = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : ∀ {a : ℕ}, (1 : Mx D a a).map π = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [wRows, wCols, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc _ (d.j0.map π), ← Matrix.map_mul, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX, d.pY_j0, d.pY_jY,
    d.p0_jX, d.p0_j0, d.p0_jY, h0, h1, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, hb, fromBlocks_one,
    fromRows_zero, fromCols_zero]

theorem tri_flag {g : GA D S} (hg : g ∈ flagN d) (z z' : Y₀ ⊕ (Fin ρ ⊕ Fin ρ)) (hz : wlev Y₀ ρ z' ≤ wlev Y₀ ρ z) :
    (wRows π d b' * ((mt S g).map π - 1 : Matrix (Fin S.rank) (Fin S.rank) K) * wCols π d b) z z' = 0 := by
  obtain ⟨T, B, hT, hX, h0⟩ := flag_cols d hg
  have z0 : ∀ {a b : ℕ}, (0 : Mx D a b).map π = 0 := Matrix.map_zero _ (map_zero _)
  have m1 : (mt S g).map π - 1 = (mt S g - 1).map π := by
    rw [Matrix.map_sub _ (map_sub π), Matrix.map_one _ (map_zero _) (map_one _)]
  have cX : (mt S g - 1).map π * d.jX.map π = d.jX.map π * T.map π := by
    rw [← Matrix.map_mul, hX, Matrix.map_mul]
  have c0 : (mt S g - 1).map π * (d.j0.map π * b) = d.jX.map π * (B.map π * b) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, h0, Matrix.map_mul, Matrix.mul_assoc]
  have r0 : ∀ {Z : Type} (C : Matrix (Fin ρ) Z K), b' * d.p0.map π * (d.jX.map π * C) = 0 := fun C => by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.p0_jX, z0, Matrix.zero_mul, Matrix.mul_zero]
  have rY : ∀ {Z : Type} (C : Matrix (Fin ρ) Z K), d.pY.map π * (d.jX.map π * C) = 0 := fun C => by
    rw [← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.pY_jX, z0, Matrix.zero_mul]
  have rX : ∀ {Z : Type} (C : Matrix (Fin ρ) Z K), d.pX.map π * (d.jX.map π * C) = C := fun C => by
    rw [← Matrix.mul_assoc _ _ C, ← Matrix.map_mul, d.pX_jX, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rw [m1, Matrix.mul_assoc]
  rcases z with a | i | i <;> rcases z' with c | j | j <;> simp only [wlev, Sum.elim_inr, Sum.elim_inl] at hz
  · change (b' * d.p0.map π * ((mt S g - 1).map π * (d.j0.map π * b))) a c = 0
    rw [c0, r0]; rfl
  · change (b' * d.p0.map π * ((mt S g - 1).map π * d.jX.map π)) a j = 0
    rw [cX, r0]; rfl
  · omega
  · omega
  · change (d.pX.map π * ((mt S g - 1).map π * d.jX.map π)) i j = 0
    rw [cX, rX, Matrix.map_apply, hT i j (by rw [Fin.le_def]; omega), RingHom.map_zero]
  · omega
  · change (d.pY.map π * ((mt S g - 1).map π * (d.j0.map π * b))) i c = 0
    rw [c0, rY]; rfl
  · change (d.pY.map π * ((mt S g - 1).map π * d.jX.map π)) i j = 0
    rw [cX, rY]; rfl
  · change (d.pY.map π * ((mt S g - 1).map π * d.jY.map π)) i j = 0
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, flag_YY d hg (by rw [Fin.le_def]; omega), RingHom.map_zero]

theorem uni_flag (hb : b' * b = 1) {Y : Type} [Fintype Y] [DecidableEq Y] {F : Matrix (Fin S.rank) Y K} {Γ : Matrix Y (Fin S.rank) K}
    (h1 : Γ * F = 1) (h2 : F * Γ = 1) (τ : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → Y) (hτ : Function.Surjective τ) (t : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → K)
    (ht : ∀ r z, F r (τ z) = t z * wCols π d b r z) (l : Y → ℕ) (hl : ∀ z z', l (τ z') ≤ l (τ z) → wlev Y₀ ρ z' ≤ wlev Y₀ ρ z)
    {g : GA D S} (hg : g ∈ flagN d) (r s : Y) (hrs : l s ≤ l r) : (Γ * ((mt S g).map π * F)) r s = (1 : Matrix Y Y K) r s := by
  obtain ⟨z, rfl⟩ := hτ r
  obtain ⟨z', rfl⟩ := hτ s
  have h := tri_flag π d b b' hg z z' (hl _ _ hrs)
  have e : (mt S g).map π - 1 = F * (Γ * ((mt S g).map π * F) - 1) * Γ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2, ← Matrix.mul_assoc F, h2, Matrix.one_mul, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  rw [e] at h
  have := transfer_back h1 (wRows_wCols π d b b' hb) τ hτ t ht _ z z' h
  rwa [Matrix.sub_apply, sub_eq_zero] at this

end Witt

theorem emb_par {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1)
    {u : Fin c → K} {Γ : Matrix (Fin A.rank ⊕ Fin c) (Fin B.rank) K} (h : Γ * sumCols d π b u = 1)
    {M : Matrix (Fin B.rank) (Fin B.rank) K} {C : Matrix (Fin A.rank) (Fin A.rank) K}
    (h0 : M * (frameMat B A d.ι).map (π.comp (incA D)) = (frameMat B A d.ι).map (π.comp (incA D)) * C)
    (h1 : ∀ p, M *ᵥ (fun r => π (incA D (d.a r p))) = fun r => π (incA D (d.a r p))) (r s : Fin A.rank ⊕ Fin c)
    (hrs : r.isRight ∨ s.isRight) : (Γ * (M * sumCols d π b u)) r s = (1 : Matrix (Fin A.rank ⊕ Fin c) (Fin A.rank ⊕ Fin c) K) r s := by
  have a1 : M * d.a.map (π.comp (incA D)) = d.a.map (π.comp (incA D)) := Matrix.ext fun r p => congrFun (h1 p) r
  have e : M * sumCols d π b u = sumCols d π b u * fromBlocks (b' * C * b) 0 0 1 := by
    refine Eq.trans ?_ (fromCols_mul_fromBlocks _ _ _ _ _ _).symm
    rw [sumCols, mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, a1]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b, hb, Matrix.one_mul]
  have e2 : Γ * (M * sumCols d π b u) = fromBlocks (b' * C * b) 0 0 1 := (congrArg (Γ * ·) e).trans ((Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) h).trans (Matrix.one_mul _)))
  rw [e2]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.LocGrpIff
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem jac_par {D : D7} {K : Type} [Field K] (π : AE D →+* K) {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1) {u : Fin (2 * σ) → K}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ)) (Fin B.rank) K} (h1 : Γ * sumCols d π b u = 1) (h2 : sumCols d π b u * Γ = 1)
    (Φ : GA D B →* GL (Fin A.rank ⊕ Fin (2 * σ)) K) (hΦ : ∀ g, (Φ g).val = Γ * ((mt B g).map π * sumCols d π b u)) :
    jacGrp (jacDec d rfl) ≤ (ParabolicEntries.parGroup K (Fin A.rank) (2 * σ + 1) fun i : Fin (2 * σ) => 2 * (i.val + 1)).comap Φ := by
  have hσ : σ ≤ 2 * σ := by omega
  refine sup_le (fun g hg r s _ hrs => ?_) ?_
  · rw [hΦ]
    refine uni_flag π (jacDec d rfl) b b' (mul_eq_one_comm.1 hb) h1 h2
      (Sum.map id (Sum.elim (fun i : Fin σ => Fin.castLE hσ i) fun i : Fin σ => (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (fun _ => 1) (Sum.elim (fun i => u (Fin.castLE hσ i)) fun i => u (Fin.castLE hσ i).rev)) ?_ _ ?_ hg r s hrs
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases h : j.val < σ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Sum.elim_inr, Fin.val_rev, Fin.val_castLE]; omega))⟩
    · rintro r (a | i | i)
      · exact (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
      · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
    · rintro (a | i | i) (a' | j | j) <;>
        simp only [wlev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega
  · rintro _ ⟨x, rfl⟩ r s hrs _
    rw [hΦ]
    have eX := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclX x))
    have eY := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclY x))
    refine emb_par π d hb h1 (C := (mt A x).map π)
      ((Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) ((jacDec d rfl).wittDecomp_anisotropicEmbedding_inclAnisotropic x)).trans Matrix.map_mul)) (fun p => ?_) r s hrs
    by_cases h : p.val < σ
    · exact fix_col eX 1 ⟨p.val, h⟩ fun r => (one_mul _).symm
    · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hσ q).rev :=
        ⟨⟨2 * σ - 1 - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      exact fix_col eY 1 q fun r => (one_mul _).symm

theorem jacGrp_mem_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b), ∀ g ∈ jacGrp (jacDec d h), frameGL hab (GlobalTheory.FunObj.inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c := by
  intro D A B c σ ε d h hσ w β β' u hF _ a b ha hb hab g hg
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  have := jac_par (piAt w) d (GlobalTheory.StdFrames.loc w β).mul_inv h1 h2
    ((frameGL d.rank).toMonoidHom.comp ((inBasis rfl β' w).comp (Lev.finE B))) e hg
  have h3 := ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff (Kw w) (Fin A.rank) (2 * σ) σ).2 hσ (by omega) _).2 this
  have hle : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ (Kw w) (Fin A.rank) (2 * σ) σ ≤ symR (Kw w) (Fin A.rank) (2 * σ) := by
    rw [symR, symN_even]
    exact sup_le (sup_le_sup_left le_sup_left _) (sup_le_sup_left le_sup_right _)
  exact hle h3

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
open GlobalTheory.RootEx GlobalTheory.LocGrp GlobalTheory.LocGrpIff
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem bes_par {D : D7} {K : Type} [Field K] (π : AE D →+* K) {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1))
    (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1) {u : Fin (2 * σ + 1) → K}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin B.rank) K} (h1 : Γ * sumCols d π b u = 1) (h2 : sumCols d π b u * Γ = 1)
    (Φ : GA D B →* GL (Fin A.rank ⊕ Fin (2 * σ + 1)) K) (hΦ : ∀ g, (Φ g).val = Γ * ((mt B g).map π * sumCols d π b u)) :
    besGrp (diagDec (besDec d rfl) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) ≤
      (ParabolicEntries.parGroup K (Fin A.rank) (σ + 1) fun i : Fin (2 * σ + 1) => i.val + 1).comap Φ := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* K := π.comp (incA D)
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * ((diagDec (besDec d rfl) l hl).jX.map π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) = φ (star (l i)) * ((diagDec (besDec d rfl) l hl).jY.map π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z K), (diagDec (besDec d rfl) l hl).j0.map π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : (diagDec (besDec d rfl) l hl).j0.map π =
        (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  refine sup_le (fun g hg r s _ hrs => ?_) ?_
  · rw [hΦ]
    refine uni_flag π (diagDec (besDec d rfl) l hl) (Y₀ := Fin A.rank ⊕ Fin 1)
      ((fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix E.symm id) ((fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix id E.symm) ?_ h1 h2
      (Sum.elim (Sum.map id fun _ => ⟨σ, by omega⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, by omega⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i)))) ?_ _ ?_ hg r s hrs
    · refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
      rw [fromBlocks_multiply]
      simp [mul_eq_one_comm.1 hb]
    · rintro (a | j)
      · exact ⟨Sum.inl (Sum.inl a), rfl⟩
      · rcases lt_trichotomy j.val σ with h | h | h
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
    · have e := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K))
      rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at e
      rintro r ((a | a) | i | i)
      · exact (congrFun (congrFun e r) (Sum.inl a)).symm.trans (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun e r) (Sum.inr a)).symm))
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
    · rintro ((a | a) | i | i) ((a' | a') | j | j) <;>
        simp only [wlev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega
  · rintro _ ⟨x, rfl⟩ r s hrs _
    rw [hΦ, embA_apply]
    set h := diagDec (besDec d rfl) l hl
    set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)
    have eX := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclX (o.emb (x, 1))))
    have eY := (Matrix.map_mul (f := π)).symm.trans (congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclY (o.emb (x, 1))))
    have e0 := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (h.wittDecomp_anisotropicEmbedding_inclAnisotropic (o.emb (x, 1)))).trans Matrix.map_mul)
    have eA := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (o.emb_jA x 1)).trans Matrix.map_mul)
    have eB := (Matrix.map_mul (f := π)).symm.trans ((congrArg (·.map π) (o.emb_jB x 1)).trans Matrix.map_mul)
    rw [GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at eB
    have jA : h.j0.map π * o.jA.map π = (frameMat B A d.ι).map φ := by
      have e : o.jA.map π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) K) (0 : Matrix (Fin 1) (Fin A.rank) K)).submatrix E.symm id := by
        rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
      rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    have jB : h.j0.map π * o.jB.map π = (midCol d rfl).map φ := by
      have e : o.jB.map π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) K) (1 : Matrix (Fin 1) (Fin 1) K)).submatrix E.symm id := by
        rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
      refine (congrArg (h.j0.map π * ·) e).trans ((core _).trans ?_)
      rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
    refine emb_par π d hb h1 (C := (mt A x).map π) ?_ (fun p => ?_) r s hrs
    · change _ * (frameMat B A d.ι).map φ = (frameMat B A d.ι).map φ * _
      rw [← jA, ← Matrix.mul_assoc, e0, Matrix.mul_assoc, eA, Matrix.mul_assoc]
    rcases lt_trichotomy p.val σ with hp | hp | hp
    · exact fix_col eX _ ⟨p.val, hp⟩ fun r => vX r ⟨p.val, hp⟩
    · obtain rfl : p = ⟨σ, hσ'⟩ := Fin.ext hp
      have eZ : (mt B (h.emb0 (o.emb (x, 1)))).map π * (h.j0.map π * o.jB.map π) = h.j0.map π * o.jB.map π := by
        rw [← Matrix.mul_assoc, e0, Matrix.mul_assoc, eB]
      exact fix_col eZ 1 (0 : Fin 1) fun r => ((one_mul _).trans (congrFun (congrFun jB r) (0 : Fin 1))).symm
    · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hσ q).rev :=
        ⟨⟨2 * σ - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      exact fix_col eY _ q fun r => vY r q

theorem besGrp_mem_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) (w : Formalism.L2.DIV.Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b), ∀ g ∈ besGrp (diagDec (besDec d h) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _), frameGL hab (GlobalTheory.FunObj.inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c := by
  intro D A B c σ d h l hl w β β' u hF _ a b ha hb hab g hg
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  have := bes_par (piAt w) d l hl (GlobalTheory.StdFrames.loc w β).mul_inv h1 h2
    ((frameGL d.rank).toMonoidHom.comp ((inBasis rfl β' w).comp (Lev.finE B))) e hg
  have h3 := ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff (Kw w) (Fin A.rank) (2 * σ + 1) (σ + 1)).1 _).2 this
  rw [symR, symN_odd]
  exact h3

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_isTilt (G : GridData L sc) (j : ℕ) : ∃ δ, GlobalTheory.RowVal.IsTilt G j δ := by
  obtain ⟨n, hn⟩ := D.R.m_even
  by_cases hj : j < D.R.m ∧ ¬ Even j
  · obtain ⟨h₁, ho⟩ := hj
    obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := by
      obtain ⟨i, hi⟩ := Nat.not_even_iff_odd.1 ho
      exact ⟨(D.R.m - 1 - j) / 2, by omega⟩
    have hx : ∀ a : ℕ, D.host.xi0 ^ a ≠ 0 := fun a => pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
    let x : GL (Fin σ) (AE D) := ⟨rat (diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹), rat (diagonal fun a : Fin σ => D.host.xi0 ^ a.1),
      by rw [← rat_mul, diagonal_mul_diagonal]; simp only [inv_mul_cancel₀ (hx _), diagonal_one, rat_one],
      by rw [← rat_mul, diagonal_mul_diagonal]; simp only [mul_inv_cancel₀ (hx _), diagonal_one, rat_one]⟩
    refine ⟨(rowJac G j h₁ σ hσ).levi x, HypDec.levi_mem_GQ _ (rat_mem _) (rat_mem _), fun h => absurd h ho, fun σ' h₁' h₂ => ?_⟩
    obtain rfl : σ = σ' := by omega
    refine ⟨HypDec.wittDecomp_levi_inclAnisotropic _ x, (HypDec.levi_jX _ x).trans (rat_mul _ _).symm, (HypDec.levi_jY _ x).trans ?_⟩
    refine Eq.trans ?_ (rat_mul _ _).symm
    congr 1
    refine (rat_conjTranspose _).symm.trans (congrArg rat ?_)
    rw [diagonal_conjTranspose]; rfl
  · refine ⟨1, one_mem _, fun _ => rfl, fun σ h₁ h₂ => ?_⟩
    obtain ⟨i, hi⟩ : Even j := by by_contra h; exact hj ⟨h₁, h⟩
    omega

theorem locAt_lat (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m)
    {k : GA D (G.V (.grid D.R.m j))} (hk : k ∈ GlobalTheory.RowVal.latGrp G j) : locAt B t w j hj k ∈ givenLevel G t w (D.R.m, j) := by
  have hm : 1 ≤ D.R.m := by omega
  have hl : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 → givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _ := by
    rintro ⟨_ | a, _ | b⟩ h h'
    · omega
    · simp at h
    · simp at h'
    · rfl
  have hf : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (B.β i j) (G.Λ (.grid i j)) := by
    rintro (_ | i) h h'
    · omega
    · exact B.isFrame (i + 1) j h h' hj
  rw [hl _ hm h1]
  refine GlobalTheory.FunObj.LevRowSucc.KO_of_St (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ _ ?_
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ (hf hm le_rfl)
  have h2 : Lev.finE (G.V (.grid D.R.m j)) k ∈ G.levMax (.grid D.R.m j) := hk.2
  rw [GridData.levMax, congLev_top] at h2
  rw [hs]
  exact h2.2

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem exists_inBasis_eq {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (g : GL (Fin n') (Kw w)) :
    ∃ g' : GL (Fin n) (Kw w), ∀ x, GlobalTheory.StdFrames.loc w x = g' → inBasis h β w x = g := by
  subst h
  refine ⟨GlobalTheory.StdFrames.loc w β * g * (GlobalTheory.StdFrames.loc w β)⁻¹, fun x hx => ?_⟩
  have e : GlobalTheory.StdFrames.loc w (β⁻¹ * x * β⁻¹⁻¹) = g := by
    rw [inv_inv, map_mul, map_mul, hx, map_inv]
    group
  exact Units.ext (Matrix.ext fun i j => congrArg (fun z : GL (Fin n') (Kw w) => z.val i j) e)

theorem exists_hasLoc {μ₀ : T} (hL : L.Is μ₀) (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m)
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)) : ∃ r, GlobalTheory.RowVal.HasLoc t B hj r g := by
  obtain ⟨e, he⟩ := exists_idemSum_locPl' hL G t
  choose g' hg' using fun w : locPl G t =>
    exists_inBasis_eq (rank_vertex G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w.1 (g w)
  obtain ⟨r, hr, h⟩ := exists_suppAt_loc_eq (G.V (.grid D.R.m j)) _ e he g'
  exact ⟨r, e, he, hr, fun w => hg' w _ (h w)⟩

theorem conj_rowR {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} {g : Fin (Γ.rank (Γ.m, j)) → kˣ} (hy : ∃ f, (toFrame hs hj y).val = diagonal f)
    (hx : x ∈ rowR hs hj) : (y * GlobalTheory.SplitFlip.diagGL g)⁻¹ * x * (y * GlobalTheory.SplitFlip.diagGL g) ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  have hf' : (toFrame hs hj (GlobalTheory.SplitFlip.diagGL g)).val = diagonal _ :=
    submatrix_diagonal_equiv (fun i => (g i : k)) (frame h)
  have := diag_conj_symR hf' (diag_conj_symR hf hx)
  change toFrame hs hj _ ∈ symR _ _ _
  rw [map_mul, map_mul, map_inv, map_mul]
  convert this using 1
  change _ = _ * (_ * toFrame hs hj x * _) * _
  group

theorem frameScal_ne (w : Pl D.host.E) (c n : ℕ) (p : Fin c) : frameSign (Kw w) c p * (unifAt w : Kw w) ^ n ≠ 0 := by
  refine mul_ne_zero ?_ (pow_ne_zero _ (unifAt w).ne_zero)
  unfold frameSign
  split_ifs
  · exact neg_ne_zero.2 one_ne_zero
  · exact one_ne_zero

theorem locAt_row (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) {j : ℕ}
    (hi : j ∈ GlobalTheory.RowVal.idx D) (hj : j ≤ D.R.m) (hj' : j < (locGrid G t w).m) {r : GA D (G.V (.grid D.R.m j))}
    (hr : r ∈ GlobalTheory.RowVal.rowGrp G j) : locAt S.B t w j hj r ∈ rowR one_le_sLen hj' := by
  have hm := idx_le hi
  obtain ⟨n, hn⟩ := D.R.m_even
  have hF := S.row t ht w hw j hj'
  unfold GlobalTheory.RowVal.rowGrp at hr
  split_ifs at hr with h h'
  · exact jacGrp_mem_symR (G.rowDec j hj') _ (by omega) w _ _ _ hF (fun p => frameScal_ne w _ _ p) (topRank_eq G t w hj) (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ r hr
  · exact besGrp_mem_symR (G.rowDec j hj') _ _ _ w _ _ _ hF (fun p => frameScal_ne w _ _ p) (topRank_eq G t w hj) (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ r hr
  · omega

theorem isTilt_unique {j : ℕ} (hj : j < D.R.m) {δ δ' : GA D (G.V (.grid D.R.m j))} (h : GlobalTheory.RowVal.IsTilt G j δ)
    (h' : GlobalTheory.RowVal.IsTilt G j δ') : δ = δ' := by
  rcases Nat.even_or_odd j with e | ⟨i, hi⟩
  · rw [h.2.1 e, h'.2.1 e]
  · obtain ⟨n, hn⟩ := D.R.m_even
    have hσ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨a, b, c⟩ := h.2.2 _ hj hσ
    obtain ⟨a', b', c'⟩ := h'.2.2 _ hj hσ
    exact (rowJac G j hj _ hσ).ga_ext (b.trans b'.symm) (a.trans a'.symm) (c.trans c'.symm)

theorem locAt_tilt (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) {j : ℕ}
    (hj : j ≤ D.R.m) (hj' : j < (locGrid G t w).m) {δ : GA D (G.V (.grid D.R.m j))} (h : GlobalTheory.RowVal.IsTilt G j δ) :
    ∃ f, (toFrame one_le_sLen hj' (locAt S.B t w j hj δ)).val = diagonal f := by
  rcases Nat.even_or_odd j with e | ⟨i, hi⟩
  · rw [h.2.1 e, map_one]
    exact ⟨fun _ => 1, (congrArg Units.val (map_one (toFrame (G := locGrid G t w) one_le_sLen hj'))).trans diagonal_one.symm⟩
  · obtain ⟨n, hn⟩ := D.R.m_even
    have hj₁ : j < D.R.m := hj'
    obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := ⟨(D.R.m - 1 - j) / 2, by omega⟩
    obtain ⟨a, b, c⟩ := h.2.2 σ hj₁ hσ
    refine frame_diag (G.rowDec j hj₁) w (S.row t ht w hw j hj₁) (topRank_eq G t w hj) (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _
      (l := fun p => if p.1 < σ then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (2 * σ - 1 - p.1))) a
      (Matrix.ext fun r p => ?_)
    have hp := p.2
    have hc : σ ≤ D.R.m - 1 - j := by clear hp; omega
    refine Eq.trans ?_ (congrArg (incA D) (mul_diagonal _ _ _ _).symm)
    by_cases hp' : p.1 < σ
    · rw [if_pos hp']
      exact (congrFun (congrFun b r) ⟨p.1, hp'⟩).trans (congrArg (incA D) (mul_diagonal _ _ _ _))
    · rw [if_neg hp']
      obtain ⟨q, rfl⟩ : ∃ q : Fin σ, p = (Fin.castLE hc q).rev :=
        ⟨⟨2 * σ - 1 - p.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
      rw [show 2 * σ - 1 - (Fin.castLE hc q).rev.1 = q.1 by
        have := q.2; simp only [Fin.val_rev, Fin.val_castLE]; omega]
      exact (congrFun (congrFun c r) q).trans (congrArg (incA D) (mul_diagonal _ _ _ _))

theorem tilt_conj (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) {j : ℕ}
    (hj : j ≤ D.R.m) (hj' : j < (locGrid G t w).m) (s : ℤˣ) {δ δ' : GA D (G.V (.grid D.R.m j))} (h : GlobalTheory.RowVal.IsTilt G j δ)
    (h' : GlobalTheory.RowVal.IsTilt G j δ') {x : GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w)} (hx : x ∈ rowR one_le_sLen hj') :
    (locAt S.B t w j hj δ' * GlobalTheory.RowVal.sgnAt G t s w j)⁻¹ * x * (locAt S.B t w j hj δ * GlobalTheory.RowVal.sgnAt G t s w j) ∈
      rowR one_le_sLen hj' := by
  obtain rfl := isTilt_unique hj' h h'
  exact conj_rowR (Γ := locGrid G t w) one_le_sLen hj' (locAt_tilt S ht hw hj hj' h) hx

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1600000 in

theorem rep_at : Big fun ch => ∀ s, RepAt ch s := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro s t
  refine ⟨fun β => ?_, fun β β' b b' hb hb' hc => ?_⟩
  · classical
    have key : ∀ j, ∃ bj : GA D (ch.G.V (.grid D.R.m j)), (j ∉ GlobalTheory.RowVal.idx D → bj = 1) ∧ (j ∈ GlobalTheory.RowVal.idx D → ∀ hj : j ≤ D.R.m, ∃ δ r,
        GlobalTheory.RowVal.IsTilt ch.G j δ ∧
        GlobalTheory.RowVal.HasLoc t ch.S.B hj r (fun w => GlobalTheory.RowVal.sgnAt ch.G t s w.1 j * (repsAt ch.G t w.1).elt (β w) (D.R.m, j)) ∧
        GlobalTheory.RowVal.IsFinOf (δ * r) bj) := by
      intro j
      by_cases hj : j ∈ GlobalTheory.RowVal.idx D
      · have hjm := idx_le hj
        obtain ⟨δ, hδ⟩ := exists_isTilt ch.G j
        obtain ⟨r, hr⟩ := exists_hasLoc hS.core.lev ch.S.B t (j := j) (by omega) (fun w => GlobalTheory.RowVal.sgnAt ch.G t s w.1 j * (repsAt ch.G t w.1).elt (β w) (D.R.m, j))
        obtain ⟨bj, hbj⟩ := exists_isFinOf _ (δ * r)
        exact ⟨bj, fun h => absurd hj h, fun _ _ => ⟨δ, r, hδ, hr, hbj⟩⟩
      · exact ⟨1, fun _ => rfl, fun h => absurd h hj⟩
    choose b hb1 hb2 using key
    exact ⟨b, hb1, hb2⟩
  · funext w i
    have hi : i.1 + 1 ∈ GlobalTheory.RowVal.idx D := by
      have := i.2
      simp only [GlobalTheory.RowVal.idx, List.mem_range'_1]
      change i.1 < D.R.m - 2 at this
      omega
    have hjm := idx_le hi
    have hj : i.1 + 1 ≤ D.R.m := by omega
    have hj' : i.1 + 1 < (locGrid ch.G t w.1).m := by change i.1 + 1 < D.R.m; omega
    obtain ⟨δ, r, hδ, ⟨e, -, -, hr⟩, -, a₁, ha₁, hf⟩ := hb.2 _ hi hj
    obtain ⟨δ', r', hδ', ⟨e', -, -, hr'⟩, -, a₁', ha₁', hf'⟩ := hb'.2 _ hi hj
    obtain ⟨x, hx, a, ha, y, hy, hxy⟩ := hc _ hi
    have h1 : ∀ z ∈ GinfC (ch.G.V (.grid D.R.m (i.1 + 1))), locAt ch.S.B t w.1 (i.1 + 1) hj z = 1 :=
      fun z hz => locAt_inf ch.S.B t w.1 _ hj hz
    obtain ⟨ρ, hρ⟩ : ∃ ρ : GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1), ρ = (repsAt ch.G t w.1).rep i (β w i) := ⟨_, rfl⟩
    obtain ⟨ρ', hρ'⟩ : ∃ ρ : GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1), ρ = (repsAt ch.G t w.1).rep i (β' w i) := ⟨_, rfl⟩
    have eb := congrArg (locAt ch.S.B t w.1 (i.1 + 1) hj) hf
    rw [map_mul, map_mul, h1 _ ha₁, one_mul, loc_rep ch.S.B t s β w i hj r ρ hρ (hr w)] at eb
    have eb' := congrArg (locAt ch.S.B t w.1 (i.1 + 1) hj) hf'
    rw [map_mul, map_mul, h1 _ ha₁', one_mul, loc_rep ch.S.B t s β' w i hj r' ρ' hρ' (hr' w)] at eb'
    have ex := congrArg (locAt ch.S.B t w.1 (i.1 + 1) hj) hxy
    rw [map_mul, map_mul, map_mul, h1 _ ha, mul_one, eb, eb'] at ex
    have hX := locAt_row ch.S.toGridChoice (Set.mem_univ t) w.2 hi hj hj' hx
    have hY := locAt_lat ch.S.B t w.1 hjm.1 hj hy
    have hN := tilt_conj ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' s hδ hδ' hX
    rw [← (repsAt ch.G t w).mk_rep i (β w i), ← (repsAt ch.G t w).mk_rep i (β' w i), ← hρ, ← hρ']
    exact mk_eq_of (Gp := GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (rowR one_le_sLen hj')
      (givenLevel ch.G t w.1 (D.R.m, i.1 + 1)) ex hN hY

end GlobalTheory.RowRep

end
