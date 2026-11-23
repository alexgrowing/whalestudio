import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsCoordsAtOfCoordTie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatRestrictComapSpan
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

section Point

variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def InBlockChart (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) : Prop :=
  ∀ k, InChart ξ (fun i => x ⟨k, i⟩) (c k) q

def ptIdeal (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (x : (Σ k, J k) → Ω) (q : Cpt ξ) : Ideal (MRing J) :=
  Ideal.span {g | ∃ d : K → ℕ, IsMultiHomog g d ∧ ∀ c, InBlockChart ξ x c q →
    ¬ unitAt ξ q (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k)}

variable {ξ : Spec (CommRingCat.of Ω) ⟶ Z} {x : (Σ k, J k) → Ω} {R : Type} [Field R]
  {z : Spec (CommRingCat.of R) ⟶ Z} {w : (Σ k, J k) → R}

theorem unitAt_iff_of_valAt {a : Ω} {r : R} (h : ValAt ξ z a r) (hz : genPt ξ ⤳ centre z) :
    unitAt ξ ⟨centre z, hz⟩ a ↔ r ≠ 0 := by
  constructor
  · obtain ⟨_, s, rfl, rfl⟩ := h
    rintro ⟨h0, -, t, ht⟩ hr
    have hs : ¬ IsUnit s := fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero hr
    have hu : IsUnit (1 - s * t) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun hu => hs (isUnit_of_mul_isUnit_left hu)
    have := hu.map (genMap ξ ⟨centre z, hz⟩)
    rw [map_sub, map_one, map_mul, ht, mul_inv_cancel₀ h0, sub_self] at this
    exact not_isUnit_zero this
  · intro hr
    obtain ⟨h0, _, t, ht, -⟩ := CoordModel.valAt_inv (r := Units.mk0 r hr) h
    obtain ⟨_, s, hs, -⟩ := h
    exact ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩

omit [Fintype K] [∀ k, Fintype (J k)] in

theorem valAt_aeval {σ : Type} {a : σ → Ω} {r : σ → R} (hz : genPt ξ ⤳ centre z) (h : ∀ p, ValAt ξ z (a p) (r p))
    (s : MvPolynomial σ ℤ) : ValAt ξ z (MvPolynomial.aeval a s) (MvPolynomial.aeval r s) := by
  induction s using MvPolynomial.induction_on with
  | C n => exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩
  | add p q hp hq =>
    obtain ⟨_, x, hx, hx'⟩ := hp
    obtain ⟨_, y, hy, hy'⟩ := hq
    exact ⟨hz, x + y, by rw [map_add, map_add, hx, hy],
      (map_add (Scheme.stalkClosedPointTo z).hom x y).trans (by rw [map_add, ← hx', ← hy']; rfl)⟩
  | mul_X p i hp => simpa using CoordModel.valAt_mul hp (h i)

omit [Fintype K] [∀ k, Fintype (J k)] in

theorem inBlockChart_centre_iff (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) (c : ∀ k, J k) :
    InBlockChart ξ x c ⟨centre z, hz⟩ ↔ ∀ k, w ⟨k, c k⟩ ≠ 0 := by
  refine forall_congr' fun k => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, hd⟩ := hw.1 k
    obtain ⟨hd0, hv⟩ := hw.2 k d hd
    obtain ⟨r, hr, e⟩ := hv (c k)
    have hu : unitAt ξ ⟨centre z, hz⟩ (x ⟨k, c k⟩ / x ⟨k, d⟩) := by
      obtain ⟨_, s, hs, -⟩ := hr
      refine ⟨div_ne_zero h.1 hd0, ⟨s, hs⟩, ?_⟩
      rw [inv_div]
      exact h.2 d
    rw [e]
    exact mul_ne_zero ((unitAt_iff_of_valAt hr hz).1 hu) hd.ne_zero
  · obtain ⟨h0, hv⟩ := hw.2 k (c k) (IsUnit.mk0 _ h)
    refine ⟨h0, fun i => ?_⟩
    obtain ⟨r, ⟨_, s, hs, -⟩, -⟩ := hv i
    exact ⟨s, hs⟩

theorem valAt_form (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    ValAt ξ z (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k) (MvPolynomial.aeval w g / ∏ k, w ⟨k, c k⟩ ^ d k) := by
  have hy := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  choose r hr hr' using fun p : Σ k, J k => (hw.2 p.1 (c p.1) (IsUnit.mk0 _ (hc p.1))).2 p.2
  convert valAt_aeval hz hr g using 1
  · have e : x = fun p => x ⟨p.1, c p.1⟩ * (x ⟨p.1, p.2⟩ / x ⟨p.1, c p.1⟩) :=
      funext fun p => (mul_div_cancel₀ _ (hy p.1)).symm
    have e' := aeval_blockScale hg (fun k => x ⟨k, c k⟩) fun p => x ⟨p.1, p.2⟩ / x ⟨p.1, c p.1⟩
    rw [← e] at e'
    have h0 : (∏ k, x ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    rw [e']
    field_simp
  · have e : w = fun p => w ⟨p.1, c p.1⟩ * r p := funext fun p => (hr' p).trans (mul_comm _ _)
    have e' := aeval_blockScale hg (fun k => w ⟨k, c k⟩) r
    rw [← e] at e'
    have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    rw [e']
    field_simp

theorem form_mem_mCoordIdeal_iff (w : (Σ k, J k) → R) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal w ↔ MvPolynomial.aeval w g = 0 := by
  refine ⟨fun h => ?_, GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hg⟩
  have h' : mConeMap w g = 0 := h
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog w hg] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact MvPolynomial.C_eq_zero.1 h1
  · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero _))

theorem ptIdeal_centre (hw : CoordsAt ξ x z w) (hz : genPt ξ ⤳ centre z) :
    ptIdeal ξ x ⟨centre z, hz⟩ = mCoordIdeal w := by
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → ∀ c, InBlockChart ξ x c ⟨centre z, hz⟩ →
      (¬ unitAt ξ ⟨centre z, hz⟩ (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k) ↔ g ∈ mCoordIdeal w) := by
    intro g d hg c hc
    have hc' := (inBlockChart_centre_iff hw hz c).1 hc
    have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [unitAt_iff_of_valAt (valAt_form hw hz hc' hg) hz, form_mem_mCoordIdeal_iff w hg, not_not, div_eq_zero_iff,
      or_iff_left h0]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro g ⟨d, hg, h⟩
    choose c hc using hw.1
    have hc' := (inBlockChart_centre_iff hw hz c).2 fun k => (hc k).ne_zero
    exact (key g d hg c hc').1 (h c hc')
  · obtain ⟨T, hT, e⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    refine e.le.trans (Ideal.span_mono fun g hg => ?_)
    obtain ⟨d, hd⟩ := hT g hg
    exact ⟨d, hd, fun c hc => (key g d hd c hc).2 (e ▸ Ideal.subset_span hg)⟩

theorem mCoordIdeal_le_ptIdeal (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (x : (Σ k, J k) → Ω) (q : Cpt ξ) :
    mCoordIdeal x ≤ ptIdeal ξ x q := by
  obtain ⟨T, hT, e⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x
  refine e.le.trans (Ideal.span_mono fun g hg => ?_)
  obtain ⟨d, hd⟩ := hT g hg
  refine ⟨d, hd, fun c _ h => h.1 ?_⟩
  rw [(form_mem_mCoordIdeal_iff x hd).1 (e ▸ Ideal.subset_span hg), zero_div]

omit [∀ k, Fintype (J k)] in

theorem exists_inBlockChart (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    ∃ c, InBlockChart ξ x c q := by
  classical
  obtain ⟨c, h0, hc⟩ := h.cover q
  have h1 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 h0 k (Finset.mem_univ k)
  refine ⟨c, fun k => ⟨h1 k, fun i => ?_⟩⟩
  convert hc (Function.update c k i) using 1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem exists_ptIdeal_eq (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    ∃ (R : Type) (_ : Field R) (z : Spec (CommRingCat.of R) ⟶ Z) (w : (Σ k, J k) → R),
      centre z = q.1 ∧ CoordsAt ξ x z w ∧ ptIdeal ξ x q = mCoordIdeal w := by
  let z : Spec (CommRingCat.of (Z.residueField q.1)) ⟶ Z := Z.fromSpecResidueField q.1
  have e : centre z = q.1 := Scheme.fromSpecResidueField_apply _ _
  have hz : genPt ξ ⤳ centre z := by rw [e]; exact q.2
  have eq : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  obtain ⟨c, hc⟩ := exists_inBlockChart h ⟨centre z, hz⟩
  obtain ⟨w, hw⟩ := CoordModel.exists_coordsAt x hz (fun k => ⟨c k, hc k⟩) h.gen
  exact ⟨_, inferInstance, z, w, e, hw, (congrArg (ptIdeal ξ x) eq).trans (ptIdeal_centre hw hz)⟩

theorem ptIdeal_isPrime (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    (ptIdeal ξ x q).IsPrime := by
  obtain ⟨R, _, z, w, -, -, e⟩ := exists_ptIdeal_eq h q
  rw [e]
  exact RingHom.ker_isPrime _

theorem ptIdeal_isRelevant (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ) :
    IsRelevant (ptIdeal ξ x q) := by
  obtain ⟨R, _, z, w, -, hw, e⟩ := exists_ptIdeal_eq h q
  rw [e]
  choose c hc using hw.1
  exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant w c fun k => (hc k).ne_zero

theorem RegAt.mem_regAt (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) {q : Cpt ξ} {s : Ω}
    (hs : RegAt x (ptIdeal ξ x q) s) : s ∈ regAt ξ q := by
  obtain ⟨R, _, z, w, e, hw, -⟩ := exists_ptIdeal_eq h q
  have hz : genPt ξ ⤳ centre z := e ▸ q.2
  obtain rfl : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  obtain ⟨d, g, t, hg, ht, htQ, e'⟩ := hs
  rw [ptIdeal_centre hw hz, form_mem_mCoordIdeal_iff w ht] at htQ
  choose c hc using hw.1
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have h0 : (∏ k, w ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
  obtain ⟨h1, -, h2⟩ := (unitAt_iff_of_valAt (valAt_form hw hz hc' ht) hz).2 (div_ne_zero htQ h0)
  obtain ⟨_, u, hu, -⟩ := valAt_form hw hz hc' hg
  have h3 := (regAt ξ ⟨centre z, hz⟩).mul_mem ⟨u, hu⟩ h2
  rwa [e', mul_div_assoc, mul_assoc, mul_inv_cancel₀ h1, mul_one] at h3

theorem inBlockChart_iff_X_notMem (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) (q : Cpt ξ)
    (c : ∀ k, J k) : InBlockChart ξ x c q ↔ ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ ptIdeal ξ x q := by
  obtain ⟨R, _, z, w, e, hw, -⟩ := exists_ptIdeal_eq h q
  have hz : genPt ξ ⤳ centre z := e ▸ q.2
  obtain rfl : q = ⟨centre z, hz⟩ := Subtype.ext e.symm
  rw [ptIdeal_centre hw hz, inBlockChart_centre_iff hw hz]
  refine forall_congr' fun k => not_congr ?_
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, mul_eq_zero, MvPolynomial.C_eq_zero,
    or_iff_left (MvPolynomial.X_ne_zero _)]

end Point

section Blocks

def omEmb (p q : ℕ) (a : Fin q) : Fin (p + q) := ⟨a, by omega⟩

def wEmb (p q : ℕ) (a : Fin p) : Fin (p + q) := ⟨q + a, by omega⟩

def omBlock {R : Type} {p q : ℕ} (T : Matrix (Fin (p + q)) (Fin (p + q)) R) : Matrix (Fin q) (Fin q) R :=
  T.submatrix (omEmb p q) (omEmb p q)

def wBlock {R : Type} {p q : ℕ} (T : Matrix (Fin (p + q)) (Fin (p + q)) R) : Matrix (Fin p) (Fin p) R :=
  T.submatrix (wEmb p q) (wEmb p q)

theorem mem_omIdx_iff (p q : ℕ) (i : Fin (p + q)) : i ∈ omIdx (p + q) p ↔ ∃ a, omEmb p q a = i := by
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨⟨i, by omega⟩, rfl⟩, fun ⟨a, h⟩ => by subst h; show (a : ℕ) < _; omega⟩

theorem mem_wIdx_iff (p q : ℕ) (i : Fin (p + q)) : i ∈ wIdx (p + q) p ↔ ∃ a, wEmb p q a = i := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨⟨i - q, by omega⟩, Fin.ext (by show q + (i - q) = i; omega)⟩,
    fun ⟨a, h⟩ => by subst h; show _ ≤ q + (a : ℕ); omega⟩

theorem omEmb_strictMono (p q : ℕ) : StrictMono (omEmb p q) := fun _ _ h => h

theorem wEmb_strictMono (p q : ℕ) : StrictMono (wEmb p q) := fun _ _ h => Nat.add_lt_add_left h q

def blockEquiv (p q : ℕ) : Fin q ⊕ Fin p ≃ Fin (p + q) := finSumFinEquiv.trans (finCongr (Nat.add_comm q p))

theorem blockEquiv_inl (p q : ℕ) (a : Fin q) : blockEquiv p q (.inl a) = omEmb p q a := rfl

theorem blockEquiv_inr (p q : ℕ) (a : Fin p) : blockEquiv p q (.inr a) = wEmb p q a := rfl

variable {R : Type} [CommRing R] {p q : ℕ}

theorem IsBlockDiag.eq_fromBlocks {T : Matrix (Fin (p + q)) (Fin (p + q)) R} (h : IsBlockDiag p T) :
    T.submatrix (blockEquiv p q) (blockEquiv p q) = Matrix.fromBlocks (omBlock T) 0 0 (wBlock T) := by
  ext (a | a) (b | b)
  · rfl
  · exact h _ _ (by show ¬ ((a : ℕ) < _ ↔ q + (b : ℕ) < _); omega)
  · exact h _ _ (by show ¬ (q + (a : ℕ) < _ ↔ (b : ℕ) < _); omega)
  · rfl

theorem IsBlockDiag.ext_blocks {T T' : Matrix (Fin (p + q)) (Fin (p + q)) R} (h : IsBlockDiag p T)
    (h' : IsBlockDiag p T') (e₁ : omBlock T = omBlock T') (e₂ : wBlock T = wBlock T') : T = T' := by
  have e := h.eq_fromBlocks
  rw [e₁, e₂, ← h'.eq_fromBlocks] at e
  ext a b
  simpa using congrFun (congrFun e ((blockEquiv p q).symm a)) ((blockEquiv p q).symm b)

theorem IsBlockDiag.det_eq_blocks {T : Matrix (Fin (p + q)) (Fin (p + q)) R} (h : IsBlockDiag p T) :
    T.det = (omBlock T).det * (wBlock T).det := by
  rw [← Matrix.det_submatrix_equiv_self (blockEquiv p q), h.eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁]

theorem minorIJ_omIdx (T : Matrix (Fin (p + q)) (Fin (p + q)) R) :
    minorIJ T (omIdx (p + q) p) (omIdx (p + q) p) = (omBlock T).det := by
  rw [minorIJ, dif_pos rfl]
  let e : Fin q ≃ omIdx (p + q) p := Equiv.ofBijective (fun a => ⟨omEmb p q a, (mem_omIdx_iff p q _).2 ⟨a, rfl⟩⟩)
    ⟨fun a b h => (omEmb_strictMono p q).injective (congrArg Subtype.val h),
      fun i => let ⟨a, ha⟩ := (mem_omIdx_iff p q _).1 i.2; ⟨a, Subtype.ext ha⟩⟩
  rw [← Matrix.det_submatrix_equiv_self (e.trans ((omIdx (p + q) p).orderIsoOfFin rfl).symm.toEquiv)]
  congr 1
  ext a b
  simp [omBlock, ← Finset.coe_orderIsoOfFin_apply, e]
  rfl

theorem minorIJ_wIdx (T : Matrix (Fin (p + q)) (Fin (p + q)) R) :
    minorIJ T (wIdx (p + q) p) (wIdx (p + q) p) = (wBlock T).det := by
  rw [minorIJ, dif_pos rfl]
  let e : Fin p ≃ wIdx (p + q) p := Equiv.ofBijective (fun a => ⟨wEmb p q a, (mem_wIdx_iff p q _).2 ⟨a, rfl⟩⟩)
    ⟨fun a b h => (wEmb_strictMono p q).injective (congrArg Subtype.val h),
      fun i => let ⟨a, ha⟩ := (mem_wIdx_iff p q _).1 i.2; ⟨a, Subtype.ext ha⟩⟩
  rw [← Matrix.det_submatrix_equiv_self (e.trans ((wIdx (p + q) p).orderIsoOfFin rfl).symm.toEquiv)]
  congr 1
  ext a b
  simp [wBlock, ← Finset.coe_orderIsoOfFin_apply, e]
  rfl

def colFrame {V : Type} [AddCommGroup V] [Module R V] {r : ℕ} (e : Fin r → V) (T : Matrix (Fin r) (Fin r) R) :
    Fin r → V := fun b => ∑ a, T a b • e a

theorem colFrame_one {V : Type} [AddCommGroup V] [Module R V] {r : ℕ} (e : Fin r → V) :
    colFrame e (1 : Matrix (Fin r) (Fin r) R) = e := by
  funext b
  simp [colFrame, Matrix.one_apply]

theorem colFrame_mul {V : Type} [AddCommGroup V] [Module R V] {r : ℕ} (e : Fin r → V)
    (T U : Matrix (Fin r) (Fin r) R) : colFrame e (T * U) = colFrame (colFrame e T) U := by
  funext b
  simp only [colFrame, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

example : omBlock (p := 1) (q := 2) !![(1 : ℤ), 2, 0; 3, 4, 0; 0, 0, 5] = !![1, 2; 3, 4] ∧
    wBlock (p := 1) (q := 2) !![(1 : ℤ), 2, 0; 3, 4, 0; 0, 0, 5] = !![5] := by
  constructor <;> decide

example : colFrame (R := ℤ) (fun a : Fin 2 => (Pi.single a 1 : Fin 2 → ℤ)) !![1, 2; 0, 1] 1 = ![2, 1] := by
  decide

end Blocks

section DualMetric

variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over Z} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

def DualGramAt (M : LieModel G ξ Li) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ Z) (V : Submodule Ω Li) {r : ℕ}
    (φ : Fin r → Module.Dual Ω V) (Γ' : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ (v : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), (∀ a b, φ a (v b) = if a = b then 1 else 0) ∧
    M.GramAt L z (fun b => (v b : Li)) Γ ∧ Γ'ᵀ * Γ = 1

theorem gramAt_conjTranspose {M : LieModel G ξ Li} {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ Z} {r : ℕ}
    {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ} (h : M.GramAt L z b Γ) : M.GramAt L z b Γᴴ :=
  let ⟨v, hv, h'⟩ := h
  ⟨v, hv, fun p q => (h' q p).conj⟩

theorem dualGram_inner {r : ℕ} {Γ Γ' : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.IsHermitian) (h : Γ'ᵀ * Γ = 1)
    {y y' u u' : Fin r → ℂ} (hu : ∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) (hu' : ∀ x, star u' ⬝ᵥ Γ *ᵥ x = y' ⬝ᵥ x) :
    star y ⬝ᵥ Γ' *ᵥ y' = star u' ⬝ᵥ Γ *ᵥ u := by
  have rep : ∀ {y u : Fin r → ℂ}, (∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) → star u ᵥ* Γ = y := fun {y u} hu =>
    dotProduct_eq _ _ fun x => by rw [← Matrix.dotProduct_mulVec, hu]
  have h1 : Γ' *ᵥ y' = star u' := by
    rw [← rep hu', ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, mul_eq_one_comm.1 h, Matrix.vecMul_one]
  have h2 : star y = Γ *ᵥ u := by
    rw [← rep hu, Matrix.star_vecMul, star_star, hΓ.eq]
  rw [h1, h2, dotProduct_comm]

theorem dualGram_norm {r : ℕ} {Γ Γ' : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.IsHermitian) (h : Γ'ᵀ * Γ = 1)
    {y u : Fin r → ℂ} (hu : ∀ x, star u ⬝ᵥ Γ *ᵥ x = y ⬝ᵥ x) : star y ⬝ᵥ Γ' *ᵥ y = star u ⬝ᵥ Γ *ᵥ u :=
  dualGram_inner hΓ h hu hu

theorem dualGram_det {r : ℕ} {Γ Γ' : Matrix (Fin r) (Fin r) ℂ} (h : Γ'ᵀ * Γ = 1) : Γ'.det * Γ.det = 1 := by
  rw [← Matrix.det_transpose Γ', ← Matrix.det_mul, h, Matrix.det_one]

example : (!![2, Complex.I; -Complex.I, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * !![1, Complex.I; -Complex.I, 2] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end DualMetric

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}

def omBundle {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S x)
    (τ : CMType H) : Lat 𝔐.ξ (Module.Dual Ω (𝔐.Vgen (.inr τ))) :=
  ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype).dual

theorem omBundle_isVB {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) : (omBundle 𝔐 τ).IsVB D.q ⊤ :=
  (Lat.isVBOn_dual_and_bidual _ _ _ _ _ _ _ (Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (𝔐.vb (.inr τ))).1).1

theorem mem_V_iff_omBundle {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) (q : Cpt 𝔐.ξ) (e : 𝔐.Vgen (.inr τ)) :
    (e : 𝔐.Li) ∈ 𝔐.V (.inr τ) q ↔ ∀ φ ∈ omBundle 𝔐 τ q, φ e ∈ regAt 𝔐.ξ q :=
  (Lat.isVBOn_dual_and_bidual _ _ _ _ _ _ _ (Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (𝔐.vb (.inr τ))).1).2 q trivial e

theorem omBundle_dualFrame {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S x) (τ : CMType H) (q : Cpt 𝔐.ξ) {φ : Fin D.q → Module.Dual Ω (𝔐.Vgen (.inr τ))}
    (hφ : (omBundle 𝔐 τ).IsFrameAt φ q) :
    (∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, φ a (v b) = if a = b then 1 else 0) ∧
    ∀ v : Fin D.q → 𝔐.Vgen (.inr τ), (∀ a b, φ a (v b) = if a = b then 1 else 0) →
      (𝔐.V (.inr τ)).IsFrameAt (fun b => (v b : 𝔐.Li)) q := by
  obtain ⟨hres, hmap⟩ := Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (𝔐.vb (.inr τ))
  obtain ⟨U, hU, b, hb, hf⟩ := hres q trivial
  let B : Module.Basis (Fin D.q) Ω (𝔐.Vgen (.inr τ)) := Module.Basis.mk (hf q trivial hU).1 hb.ge
  haveI := Module.Finite.of_basis B
  have hrk : Module.finrank Ω (𝔐.Vgen (.inr τ)) = D.q := by simpa using Module.finrank_eq_card_basis B
  constructor
  · let C := basisOfLinearIndependentOfCardEqFinrank' φ hφ.1 (by simp [Subspace.dual_finrank_eq, hrk])
    have hC : ∀ a, C a = φ a := fun a => by simp [C]
    refine ⟨fun b => (Module.evalEquiv Ω _).symm (C.coord b), fun a b => ?_⟩
    rw [Module.apply_evalEquiv_symm_apply, ← hC, Module.Basis.coord_apply, C.repr_self, Finsupp.single_apply]
  · intro v hv
    have hli : LinearIndependent Ω v := LinearIndependent.of_pairwise_dual_eq_zero_one v φ
      (fun a b hab => (hv a b).trans (if_neg hab)) (fun a => by rw [hv, if_pos rfl])
    let C := basisOfLinearIndependentOfCardEqFinrank' v hli (by simp [hrk])
    have hC : ⇑C = v := by simp [C]
    have hr : ∀ e a, C.repr e a = φ a e := fun e a => by
      conv_rhs => rw [← C.sum_repr e]
      simp [hC, hv]
    refine ⟨hli.map' (𝔐.Vgen (.inr τ)).subtype (Submodule.ker_subtype _), ?_⟩
    have key : ∀ e : 𝔐.Vgen (.inr τ), (e : 𝔐.Li) ∈ 𝔐.V (.inr τ) q ↔
        e ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range v) := fun e => by
      rw [← hC, LatDual.mem_span_basis_iff, mem_V_iff_omBundle, hφ.2]
      refine ⟨fun h a => hr e a ▸ h _ (Submodule.subset_span ⟨a, rfl⟩), fun h ψ hψ => ?_⟩
      induction hψ using Submodule.span_induction with
      | mem ψ hψ => obtain ⟨a, rfl⟩ := hψ; exact hr e a ▸ h a
      | zero => simp
      | add ψ ψ' _ _ h1 h2 => simpa using add_mem h1 h2
      | smul t ψ _ h1 => exact mul_mem t.2 h1
    refine le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)
    · have he' : e ∈ _ := (hmap q trivial).ge he
      obtain ⟨e, -, rfl⟩ := Submodule.mem_map.1 he'
      have h2 := (key e).1 he
      rwa [← lat_restrict_comap_span] at h2
    · rintro _ ⟨b, rfl⟩
      exact (key _).2 (Submodule.subset_span ⟨b, rfl⟩)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

structure FlagTie (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) where

  eW : ∀ τ : CMType H, Module.Basis (Fin D.p) M.Ω (𝔐.Vgen (.inl τ))

  eO : ∀ τ : CMType H, Module.Basis (Fin D.q) M.Ω (Module.Dual M.Ω (𝔐.Vgen (.inr τ)))
  frameW : ∀ (q : Cpt 𝔐.ξ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F →
    M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → ∀ τ,
      (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (eW τ a : 𝔐.Li)) (wBlock (F.T τ))) q
  frameO : ∀ (q : Cpt 𝔐.ξ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F →
    M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → ∀ τ, (omBundle 𝔐 τ).IsFrameAt (colFrame (eO τ) (omBlock (F.T τ))) q

variable {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

def FlagTie.wFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.p → 𝔐.Li := colFrame (fun a => (tie.eW τ a : 𝔐.Li)) (wBlock (F.T τ))

def FlagTie.omFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → Module.Dual M.Ω (𝔐.Vgen (.inr τ)) := colFrame (tie.eO τ) (omBlock (F.T τ))

theorem exists_goodFrame (𝔐 : HodgeCpt Y S M.x) (q : Cpt 𝔐.ξ) :
    ∃ F, M.IsFrame F ∧ M.GoodAt F (ptIdeal 𝔐.ξ M.x q) :=
  M.frames _ (ptIdeal_isPrime 𝔐.tie q) (ptIdeal_isRelevant 𝔐.tie q) (mCoordIdeal_le_ptIdeal _ _ q)

theorem FlagTie.exists_frames (tie : FlagTie M 𝔐) (q : Cpt 𝔐.ξ) :
    ∃ F, M.IsFrame F ∧ M.GoodAt F (ptIdeal 𝔐.ξ M.x q) ∧ ∀ τ,
      (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) q ∧ (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) q :=
  let ⟨F, h, h'⟩ := exists_goodFrame 𝔐 q
  ⟨F, h, h', fun τ => ⟨tie.frameW q F h h' τ, tie.frameO q F h h' τ⟩⟩

theorem FlagTie.frames_centre (tie : FlagTie M 𝔐) {R : Type} [Field R] {z : Spec (CommRingCat.of R) ⟶ 𝔐.X}
    {w : (Σ k, baseIdx ι M.blk k) → R} (hw : CoordsAt 𝔐.ξ M.x z w)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (h : M.IsFrame F) (h' : M.GoodAt F (mCoordIdeal w))
    (τ : CMType H) : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre z, 𝔐.all _⟩ ∧
      (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre z, 𝔐.all _⟩ := by
  rw [← ptIdeal_centre hw (𝔐.all _)] at h'
  exact ⟨tie.frameW _ F h h' τ, tie.frameO _ F h h' τ⟩

structure BaseMetric.IsHodge {n : ℕ} (BM : BaseMetric M n) (tie : FlagTie M 𝔐) : Prop where
  interior : ∀ (x : BM.Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) →
    (x ∉ ReciprocityTheory.AnForm.P.bdry BM.s ↔ 𝔐.Interior z)
  gramW : ∀ i τ, ∀ x ∈ BM.O i \ ReciprocityTheory.AnForm.P.bdry BM.s, ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X,
    CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) → 𝔐.M.GramAt 𝔐.t.PP.L z (tie.wFrame (BM.F i) τ) (wBlock (BM.G i τ x))
  gramO : ∀ i τ, ∀ x ∈ BM.O i \ ReciprocityTheory.AnForm.P.bdry BM.s, ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X,
    CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) →
      DualGramAt 𝔐.M 𝔐.t.PP.L z (𝔐.Vgen (.inr τ)) (tie.omFrame (BM.F i) τ) (omBlock (BM.G i τ x))

theorem BaseMetric.frames_of_tie {n : ℕ} (BM : BaseMetric M n) (tie : FlagTie M 𝔐) {i : Fin BM.q} {x : BM.Rb.X}
    (hx : x ∈ BM.O i) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz : CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x))
    (τ : CMType H) : (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame (BM.F i) τ) ⟨centre z, 𝔐.all _⟩ ∧
      (omBundle 𝔐 τ).IsFrameAt (tie.omFrame (BM.F i) τ) ⟨centre z, 𝔐.all _⟩ :=
  tie.frames_centre hz (BM.isFrame i) (BM.good i x hx) τ

end Comparison₂

end GlobalTheory.CompanionTheory.Ar.PB
