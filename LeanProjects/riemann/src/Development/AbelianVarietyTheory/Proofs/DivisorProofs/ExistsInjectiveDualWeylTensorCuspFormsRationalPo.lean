import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdemAtEqOneIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtMulTriangularIntVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTvalInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorValueOfTriangularLawStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement

noncomputable section

namespace GlobalTheory.DefPt.ReadsPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Frames GlobalTheory.FlatLine.Definite
open scoped Matrix Classical

theorem mem_SS_of_isSec {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (hp : X.p0 = 0)
    {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) : P ∈ X.SS la := by
  refine ⟨⟨hP, ?_⟩, fun ξ hξ => absurd hξ (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl hp) ξ)⟩
  obtain ⟨C, hC⟩ := (GlobalTheory.DefiniteFrames.isCompact_ortho X (Or.inl hp)).bddAbove_image
    ((continuousOn_pnorm X la hP.1.continuousOn).mono fun x hx => PIW.FdPA.orthonormal_domain r X x hx)
  refine ⟨C, fun x hx => ?_⟩
  rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ (FrameDegreeData.bOf_mem X hx)]
  exact hC ⟨_, FrameDegreeData.ortho_bOf X hx, rfl⟩

theorem tval_map {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {S S' : Type} [CommRing S]
    [CommRing S'] (φ : S →+* S') (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    φ (tval la x y) = tval la (fun I => φ (x I)) fun t => (y t).map φ := by
  simp only [tval, map_sum, map_mul, map_prod]
  refine Finset.sum_congr rfl fun I _ => congrArg _ (Finset.prod_congr rfl fun t _ => ?_)
  rw [← GlobalTheory.DualWeyl.evalAt_map, MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom S)) (Int.castRingHom S')]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def rdVal (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (Y : Mats Dw S) (s : S) : S := s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

variable {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Z : Comp Xo c} {y₀ : FrPt Xo c c.F}

theorem map_rdVal (x : TIdx (part Dw a) → c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (Y : Mats Dw S) (s : S) : φ (rdVal a n x Y s) = rdVal a n x (fun τ => (Y τ).map φ) (φ s) := by
  have h := tval_map (part Dw a) φ.toRingHom (fun I => algebraMap c.F S (x I)) Y
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] at h
  rw [rdVal, rdVal, map_mul, map_pow, h]

theorem reads_of_test {x : TIdx (part Dw a) → c.F} {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (hs : f ∈ suppOn Z)
    (h : ∀ (p : TRing c.F) (z y : FrPt Xo c p.R) (Y : Mats Dw p.R) (s : (p.R)ˣ), (∀ τ, IsUnit (Y τ).det) →
      FrMap (Algebra.ofId c.F p.R) y₀ z → FrChg (fun τ => (Y τ)ᵀ) (s : p.R) z y → f p y = rdVal a n x Y (s : p.R)) :
    Reads Z y₀ a n x f := by
  refine ⟨hs, fun S _ _ z y Y s hY hsu hz hy => ?_⟩
  obtain ⟨A, _, _, π, X, u, hft, hred, hF⟩ := GlobalTheory.exists_frameRing_reduced (K := c.F) (fun τ => Dw.mult τ) c.F
  obtain ⟨q, ⟨e⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 A hft hred
  obtain ⟨hX, hU⟩ := GlobalTheory.FrameRing_of_algEquiv _ π X u hF e.symm
  generalize (fun τ => (X τ).map e.symm) = X' at hX hU
  generalize Units.map (e.symm : A →* q.R) u = u' at hU
  obtain ⟨k, ⟨-, hk2, hk3⟩, -⟩ := hU S (Algebra.ofId c.F S) Y hsu.unit hY
  obtain ⟨w₀, hw₀⟩ := exists_bc (Algebra.ofId c.F q.R) y₀
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c q.R w₀ (fun τ => (X' τ)ᵀ) u' fun τ => by
    rw [Matrix.det_transpose]; exact hX τ
  have hm : FrMap k w y := by
    refine (ChgBC.frChg_baseChange E H Dw l Xo c q.R S k w₀ w z y _ _ hw
      (frMap_of_comp (Subsingleton.elim _ _) hw₀ hz)).2 ?_
    simp only [Matrix.transpose_map, hk2, hk3]
    exact hy
  rw [evR_of_frMap_test hf hm, h q w₀ w X' u' hX hw₀ hw, map_rdVal, funext hk2, hk3]
  rfl

theorem exists_chg
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ (w z : FrPt Xo c (S ⧸ Ideal.span {1 - idemAt Z y})) (Y : Mats Dw (S ⧸ Ideal.span {1 - idemAt Z y}))
      (s : (S ⧸ Ideal.span {1 - idemAt Z y})), (∀ τ, IsUnit (Y τ).det) ∧ IsUnit s ∧
      FrMap (Ideal.Quotient.mkₐ c.F _) y w ∧ FrMap (Algebra.ofId c.F _) y₀ z ∧ FrChg (fun τ => (Y τ)ᵀ) s z w := by
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨w, hw⟩ := exists_bc π y
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (S ⧸ Ideal.span {1 - idemAt Z y})) y₀
  have hwZ : LiesOn Z w := (idemAt_eq_one_iff Z w).1
    ((CompSplitPfB.cspB_idem_map _ _ π y.x_over w.x_over hw.1).symm.trans hπ)
  obtain ⟨g, s, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ z w).1 ((hy₀ _ w hwZ).trans hz.1.symm)
  exact ⟨w, z, fun τ => (g τ)ᵀ, s, fun τ => by rw [Matrix.det_transpose]; exact hg τ, s.isUnit, hw, hz, hc⟩

theorem eq_of_reads
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) {x : TIdx (part Dw a) → c.F} {f g : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n) (h : Reads Z y₀ a n x f) (h' : Reads Z y₀ a n x g) : f = g := by
  funext p y
  obtain ⟨w, z, Y, s, hY, hs, hw, hz, hc⟩ := exists_chg hy₀ y
  refine eq_of_mk_eq (e := idemAt Z y) (CompSplitPfB.cspB_idem_idem _ _ _ _)
    (congrFun (congrFun ((mem_suppOn_iff_idem_mul_of_natural hf.1 Z).1 h.1) p) y)
    (congrFun (congrFun ((mem_suppOn_iff_idem_mul_of_natural hg.1 Z).1 h'.1) p) y) ?_
  exact (evR_of_frMap_test hf.1 hw).symm.trans (((h.2 _ z w Y s hY hs hz hc).trans
    (h'.2 _ z w Y s hY hs hz hc).symm).trans (evR_of_frMap_test hg.1 hw))

def IsRd (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) {S : Type}
    [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (t : S) : Prop :=
  idemAt Z y * t = t ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (w z : FrPt Xo c T)
    (Y : Mats Dw T) (s : T), FrMap φ y w → FrMap (Algebra.ofId c.F T) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z w →
      φ t = rdVal a n x Y s

theorem existsUnique_isRd (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (x : TIdx (part Dw a) → c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : ∃ t, IsRd Z y₀ a n x y t ∧ ∀ t', IsRd Z y₀ a n x y t' → t' = t := by
  have he : IsIdempotentElem (idemAt Z y) := CompSplitPfB.cspB_idem_idem _ _ _ _
  obtain ⟨w, z, Y, s, -, -, hw, hz, hc⟩ := exists_chg hy₀ y
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨t, ht⟩ := Ideal.Quotient.mkₐ_surjective c.F _ (rdVal a n x Y s)
  have k : idemAt Z y * (idemAt Z y * t) = idemAt Z y * t := by rw [← mul_assoc, he.eq]
  have ht₁ : π (idemAt Z y * t) = rdVal a n x Y s := by rw [map_mul, hπ, one_mul]; exact ht
  refine ⟨idemAt Z y * t, ⟨k, fun T _ _ φ w' z' Y' s' hw' hz' hc' => ?_⟩,
    fun t' ht' => eq_of_mk_eq he ht'.1 k ((ht'.2 _ π w z Y s hw hz hc).trans ht₁.symm)⟩
  have h1 : φ (idemAt Z y) = 1 := (CompSplitPfB.cspB_idem_map _ _ φ y.x_over w'.x_over hw'.1).trans
    ((CompSplitPfB.cspB_idem_congr _ _ z'.x_over w'.x_over hc'.1).trans
      ((idemAt_eq_one_iff Z z').2 (liesOn_frMap hz' h₀)))
  let ψ := Ideal.Quotient.liftₐ (Ideal.span {1 - idemAt Z y}) φ fun b hb => by
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, map_sub, h1, map_one, sub_self, mul_zero]
  have hψ : ψ.comp π = φ := Ideal.Quotient.liftₐ_comp _ _ _
  have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ z w z' w' _ s hc
    (frMap_of_comp (Subsingleton.elim _ _) hz hz')).1 (frMap_of_comp hψ hw hw')
  obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c T z' w').2 _ _ _ _ hc' c₁
  have e₃ : Y' = fun τ => (Y τ).map ψ := funext fun τ => Matrix.transpose_injective (congrFun e₁ τ)
  rw [e₂, e₃, ← hψ, AlgHom.comp_apply, ht₁, map_rdVal]

theorem exists_reads (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (x : TIdx (part Dw a) → c.F) :
    ∃ f ∈ sec Xo c a n, Reads Z y₀ a n x f := by
  choose f hf hu using fun (p : TRing c.F) (y : FrPt Xo c p.R) => existsUnique_isRd (n := n) h₀ hy₀ x y
  have hm : f ∈ sec Xo c a n := by
    refine ⟨fun p q φ y z h => (hu q z _ ⟨?_, fun T _ _ ψ w z' Y s hw hz hc => ?_⟩).symm,
      fun p t y y' h => (hu p y' _ ⟨?_, fun T _ _ ψ w' z' Y s hw hz hc => ?_⟩).symm⟩
    · rw [idemAt, ← CompSplitPfB.cspB_idem_map _ _ φ y.x_over z.x_over h.1, ← map_mul]
      exact congrArg φ (hf p y).1
    · exact (hf p y).2 T (ψ.comp φ) w z' Y s (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ h hw) hz hc
    · rw [mul_left_comm, idemAt, CompSplitPfB.cspB_idem_congr _ _ y.x_over y'.x_over h.1]
      exact congrArg _ (hf p y).1
    · obtain ⟨k, k0, k1, hk⟩ := ((frBor_calculus E H Dw l Xo c _ y y' y').1 t).1 h
      obtain ⟨w, hw₀⟩ := exists_bc ψ y
      have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ y y' w w' k _ hk hw₀).1 hw
      obtain ⟨g, u, -, c₀⟩ := (frChg_exists_unique E H Dw l Xo c T z' w).1 (c₁.1.symm.trans hc.1)
      have c₂ := (frChg_refl_and_comp E H Dw l Xo c T z' w w').2 _ _ _ _ c₀ c₁
      obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c T z' w').2 _ _ _ _ hc c₂
      have e₃ : Y = fun τ => (g τ)ᵀ * ((k τ).map ψ)ᵀ := funext fun τ => by
        rw [← Matrix.transpose_mul, ← congrFun e₁ τ, Matrix.transpose_transpose]
      rw [map_mul, (hf p y).2 T ψ w z' (fun τ => (g τ)ᵀ) u hw₀ hz c₀, e₂, e₃, rdVal, rdVal,
        GlobalTheory.DefPt.tval_mul_triangular _ _ _ _ _ _ _ fun τ i j hij => by
          show ψ (k τ j i) = 0
          rw [k0 τ j i hij, map_zero]]
      simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, ex, map_mul, map_prod, map_pow, diagChar, part,
        Matrix.transpose_apply, Matrix.map_apply, k1, mul_pow]
      ring
  refine ⟨f, hm, reads_of_test hm.1 ((mem_suppOn_iff_idem_mul_of_natural hm.1 Z).2
    (funext fun p => funext fun y => (hf p y).1)) fun p z y Y s _ hz hc => ?_⟩
  exact (hf p y).2 _ (AlgHom.id c.F _) y z Y s (frMap_unique_refl_iff E H Dw l Xo c _ _ (AlgHom.id c.F _) y).2.1 hz hc

theorem exists_coord {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (hs : f ∈ suppOn Z) : ∃ x, Reads Z y₀ a n x f := by
  obtain ⟨G, hG, -⟩ := GlobalTheory.LamT.FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c c.F y₀ a n f hf
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_tensor_value_of_triangular_law _ Dw.mult (part Dw a) c.F G fun y b hy hb => by
    have h := GlobalTheory.LamT.evalFr_mul_tri hf hG inferInstance (AlgHom.id c.F c.F) y b (fun τ => (hy τ).isUnit)
      (fun τ => by
        rw [Matrix.det_of_upperTriangular (hb τ).1]
        exact (Finset.prod_ne_zero_iff.2 fun i _ => (hb τ).2 i).isUnit)
      (fun τ i j hij => (hb τ).1 hij) fun τ i => ((hb τ).2 i).isUnit
    have h2 : MvPolynomial.map (AlgHom.id c.F c.F).toRingHom G = G := MvPolynomial.map_id G
    rw [h2] at h
    exact h
  refine ⟨x, reads_of_test hf.1 hs fun p z y Y s hY hz hc => ?_⟩
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hg : ∀ τ, IsUnit ((Y τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hY τ
  obtain ⟨z₁, h₁, -⟩ := existsUnique_frChg E H Dw l Xo c _ z _ 1 hg
  obtain ⟨z₂, h₂, -⟩ := existsUnique_frChg E H Dw l Xo c _ z₁ (fun _ => 1) s (fun _ => by simp)
  have h₃ := (frChg_refl_and_comp E H Dw l Xo c _ z z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [Units.val_one, mul_one, one_mul] at h₁ h₃
  obtain rfl : z₂ = y := (existsUnique_frChg E H Dw l Xo c _ z _ s hg).unique h₃ hc
  let t : Ix Dw → (p.R)ˣ := fun i => match i with
    | none => s
    | some _ => 1
  have e := GlobalTheory.LamT.evR_frChg_tri hred hf t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
    (fun τ i => Matrix.one_apply_eq i) h₂
  rw [hG _ _ z z₁ Y hY hz h₁, hx, evR_of_frMap_test hf.1
    (frMap_unique_refl_iff E H Dw l Xo c _ _ (AlgHom.id c.F _) z₂).2.1] at e
  refine e.trans ?_
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, ex, t, Units.val_one, one_pow, Finset.prod_const_one,
    mul_one]
  rfl

theorem reads_add {x x' : TIdx (part Dw a) → c.F} {f g : Rul Xo c} (h : Reads Z y₀ a n x f) (h' : Reads Z y₀ a n x' g) :
    Reads Z y₀ a n (x + x') (f + g) := by
  refine ⟨add_mem h.1 h'.1, fun S _ _ z y Y s hY hs hz hc => ?_⟩
  refine (evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y).trans
    ((congrArg₂ (· + ·) (h.2 S z y Y s hY hs hz hc) (h'.2 S z y Y s hY hs hz hc)).trans ?_)
  simp only [tval, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]

theorem reads_smul (b : c.F) {x : TIdx (part Dw a) → c.F} {f : Rul Xo c} (h : Reads Z y₀ a n x f) :
    Reads Z y₀ a n (b • x) (b • f) := by
  refine ⟨Submodule.smul_mem _ b h.1, fun S _ _ z y Y s hY hs hz hc => ?_⟩
  refine (evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) b f y).trans
    ((congrArg (algebraMap c.F S b * ·) (h.2 S z y Y s hY hs hz hc)).trans ?_)
  simp only [tval, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem eq_zero_of_reads {x : TIdx (part Dw a) → c.F} (h : Reads Z y₀ a n x 0) : x = 0 := by
  refine GlobalTheory.CoordVanish.eq_zero_of_tval_invertible _ _ _ c.F x fun Y hY => ?_
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F c.F) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c c.F z (fun τ => (Y τ)ᵀ) 1 fun τ => by
    rw [Matrix.det_transpose]; exact (hY τ).isUnit
  have e := (h.2 c.F z y Y 1 (fun τ => (hY τ).isUnit) isUnit_one hz hy).symm.trans (evalAt_zero _ _ y)
  simpa using e

theorem mem_cusp_of_sec {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hq : Dw.q = 0)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hd : Dom a n) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    f ∈ cusp Xo c U a n :=
  (mem_cusp Xo c U a n f).2 ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun k =>
    mem_SS_of_isSec _ (((hU σ hσ).2.1 k).1.trans hq) ((hU σ hσ).2.2.2.2.1 a n hd f hf k)⟩

theorem exists_linearMap_reads : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), ∃ φ : (TIdx (part Dw a) → c.F) →ₗ[c.F] Rul Xo c, Function.Injective φ ∧ LinearMap.range φ = cuspOn U Z (wtZ a n) ∧ ∀ x, Reads Z P.y₀ a n x (φ x) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n hD hd Z P
  choose F hF hR using fun x : TIdx (part Dw a) → c.F => exists_reads (n := n) P.on P.only x
  let φ : (TIdx (part Dw a) → c.F) →ₗ[c.F] Rul Xo c :=
    { toFun := F
      map_add' := fun x x' => eq_of_reads P.only (hF _) (add_mem (hF x) (hF x')) (hR _) (reads_add (hR x) (hR x'))
      map_smul' := fun b x =>
        eq_of_reads P.only (hF _) (Submodule.smul_mem _ b (hF x)) (hR _) (reads_smul b (hR x)) }
  refine ⟨φ, (injective_iff_map_eq_zero φ).2 fun x hx => eq_zero_of_reads (n := n) ((show F x = 0 from hx) ▸ hR x), ?_, hR⟩
  ext f
  rw [cuspOn, cuspW_wtZ]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨mem_cusp_of_sec hD.q hD.unf hd (hF x), (hR x).1⟩
  · rintro ⟨h1, h2⟩
    have hf := cusp_le_sec Xo c U a n h1
    obtain ⟨x, hx⟩ := exists_coord (y₀ := P.y₀) hf h2
    exact ⟨x, eq_of_reads P.only (hF x) hf (hR x) hx⟩

end GlobalTheory.DefPt.ReadsPt
