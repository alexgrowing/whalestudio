import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]

abbrev siegel : Subgroup (GL (n ⊕ n) k) := stabGL (diagSub k (Equiv.refl (n ⊕ n)))

abbrev io : GL n k × GL n k →* GL (n ⊕ n) k := blkGL (Equiv.refl (n ⊕ n))

def absRatio : siegel k n →* ℝ≥0 :=
  (distribHaarChar k).comp ((GeneralLinearGroup.det.comp (leviGL (Equiv.refl (n ⊕ n)))) ^ 2 /
    GeneralLinearGroup.det.comp (siegel k n).subtype)

def sphSection (s : ℂ) (h : GL (n ⊕ n) k) : ℂ :=
  npow (iwAbs (absRatio k n) (KO k (n ⊕ n)) h) (s + (Fintype.card n : ℂ) / 2)

variable {k n}

theorem coe_absRatio (p : siegel k n) : (absRatio k n p : ℝ) =
    nabs k (GeneralLinearGroup.det (leviGL (Equiv.refl (n ⊕ n)) p)) ^ 2 /
      nabs k (GeneralLinearGroup.det (p : GL (n ⊕ n) k)) := by
  simp [absRatio, nabs]

theorem absRatio_eq (p : siegel k n) {a d : kˣ} (ha : (a : k) = (leviMat (Equiv.refl (n ⊕ n)) p.1.1).det)
    (hd : (d : k) = (quotMat (Equiv.refl (n ⊕ n)) p.1.1).det) : (absRatio k n p : ℝ) = nabs k a / nabs k d := by
  have h1 : GeneralLinearGroup.det (leviGL (Equiv.refl (n ⊕ n)) p) = a := Units.ext ha.symm
  have h2 : GeneralLinearGroup.det (p : GL (n ⊕ n) k) = a * d :=
    Units.ext (by rw [Units.val_mul, ha, hd]; exact (mem_stabGL_diagSub.1 p.2).det_eq)
  have := (nabs_pos' k a).ne'
  rw [coe_absRatio, h1, h2, nabs_mul']
  field_simp

theorem nabs_det_of_mem_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  apply nabs_eq_one
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] in
theorem fromBlocks_int {A B C D : Matrix n n k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k])
    (hC : ∀ i j, C i j ∈ 𝒪[k]) (hD : ∀ i j, D i j ∈ 𝒪[k]) (i j) : fromBlocks A B C D i j ∈ 𝒪[k] := by
  rcases i with i | i <;> rcases j with j | j <;> simp [*]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] in
theorem one_int (i j : n) : (1 : Matrix n n k) i j ∈ 𝒪[k] := by
  rw [one_apply]; split_ifs
  exacts [one_mem _, zero_mem _]

def shear (B C : Matrix n n k) (h : B * C = 0) (h' : C * B = 0) : GL (n ⊕ n) k :=
  ⟨fromBlocks 1 B C 1, fromBlocks 1 (-B) (-C) 1, by simp [fromBlocks_multiply, h, h'],
    by simp [fromBlocks_multiply, h, h']⟩

theorem shear_mem {B C : Matrix n n k} (h : B * C = 0) (h' : C * B = 0) (hB : ∀ i j, B i j ∈ 𝒪[k])
    (hC : ∀ i j, C i j ∈ 𝒪[k]) : shear B C h h' ∈ KO k (n ⊕ n) :=
  (SplitFlip.mem_KO_iff _).2 ⟨fromBlocks_int one_int hB hC one_int,
    fromBlocks_int one_int (fun i j => neg_mem (hB i j)) (fun i j => neg_mem (hC i j)) one_int⟩

theorem io_mem_KO {x y : GL n k} (hx : x ∈ KO k n) (hy : y ∈ KO k n) : io k n (x, y) ∈ KO k (n ⊕ n) := by
  rw [SplitFlip.mem_KO_iff] at hx hy ⊢
  rw [← map_inv]
  exact ⟨fromBlocks_int hx.1 (fun _ _ => zero_mem _) (fun _ _ => zero_mem _) hy.1,
    fromBlocks_int hx.2 (fun _ _ => zero_mem _) (fun _ _ => zero_mem _) hy.2⟩

theorem isIwasawa : IsIwasawa (absRatio k n) (KO k (n ⊕ n)) := by
  constructor
  · intro g
    let δ : GL (n ⊕ n) k := shear 0 1 (by simp) (by simp)
    have hδ : δ ∈ KO k (n ⊕ n) := shear_mem _ _ (fun _ _ => zero_mem _) one_int
    obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (n ⊕ n) (Sum.elim (fun _ => 0) fun _ => 1) (δ⁻¹ * g)
    have h21 : b.1.toBlocks₂₁ = 0 := by
      ext i j
      exact hb (by simp)
    refine ⟨⟨δ * b * δ⁻¹, mem_stabGL_diagSub.2 ?_⟩, δ * w, mul_mem hδ hw, ?_⟩
    · have : (δ * b * δ⁻¹).1 = fromBlocks 1 0 1 1 * b.1 * fromBlocks 1 (-0) (-1) 1 := rfl
      rw [this, ← fromBlocks_toBlocks b.1, h21]
      simp [KeepsDiag, leviMat, fromBlocks_multiply]
      abel
    · show g = δ * b * δ⁻¹ * (δ * w)
      rw [inv_mul_eq_iff_eq_mul] at e
      rw [e]; group
  · intro p hp
    have key : ∀ q : siegel k n, (q : GL (n ⊕ n) k) ∈ KO k (n ⊕ n) → ∀ i j,
        (leviGL (Equiv.refl (n ⊕ n)) q).1 i j ∈ 𝒪[k] := fun q hq i j =>
      add_mem (((SplitFlip.mem_KO_iff _).1 hq).1 _ _) (((SplitFlip.mem_KO_iff _).1 hq).1 _ _)
    have h1 : leviGL (Equiv.refl (n ⊕ n)) p ∈ KO k n :=
      (SplitFlip.mem_KO_iff _).2 ⟨key p hp, by rw [← map_inv]; exact key _ (inv_mem hp)⟩
    apply NNReal.coe_injective
    rw [coe_absRatio, nabs_det_of_mem_KO h1, nabs_det_of_mem_KO hp]
    simp

theorem sphSection_left (s : ℂ) (p : siegel k n) (h : GL (n ⊕ n) k) :
    sphSection k n s (p * h) = npow (absRatio k n p) (s + (Fintype.card n : ℂ) / 2) * sphSection k n s h := by
  rw [sphSection, isIwasawa.iwAbs_left, npow_mul, sphSection]

theorem sphSection_right (s : ℂ) (h : GL (n ⊕ n) k) {κ : GL (n ⊕ n) k} (hκ : κ ∈ KO k (n ⊕ n)) :
    sphSection k n s (h * κ) = sphSection k n s h := by
  rw [sphSection, isIwasawa.iwAbs_right _ hκ, sphSection]

theorem sphSection_one (s : ℂ) : sphSection k n s 1 = 1 := by
  rw [sphSection, isIwasawa.iwAbs_of_mem (one_mem _), one_npow]

theorem eq_sphSection {s : ℂ} {Φ : GL (n ⊕ n) k → ℂ} (h1 : Φ 1 = 1)
    (hl : ∀ (p : siegel k n) h, Φ (p * h) = npow (absRatio k n p) (s + (Fintype.card n : ℂ) / 2) * Φ h)
    (hr : ∀ h, ∀ κ ∈ KO k (n ⊕ n), Φ (h * κ) = Φ h) : Φ = sphSection k n s := funext fun g => by
  obtain ⟨p, κ, hκ, rfl⟩ := isIwasawa.1 g
  rw [hr _ _ hκ, sphSection_right _ _ hκ, ← mul_one (p : GL (n ⊕ n) k), hl, sphSection_left, h1, sphSection_one]

theorem sphSection_io_biinv (s : ℂ) (g : GL n k) {x y : GL n k} (hx : x ∈ KO k n) (hy : y ∈ KO k n) :
    sphSection k n s (io k n (x * g * y, 1)) = sphSection k n s (io k n (g, 1)) := by
  let p : siegel k n := ⟨io k n (x, x), mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)⟩
  have e : io k n (x * g * y, 1) = p * (io k n (g, 1) * io k n (y, x⁻¹)) := by
    show _ = io k n (x, x) * _
    rw [← map_mul, ← map_mul]
    simp [mul_assoc]
  rw [e, sphSection_left, sphSection_right _ _ (io_mem_KO hy (inv_mem hx)), isIwasawa.2 p (io_mem_KO hx hx),
    one_npow, one_mul]

theorem nabs_unif {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  refine (nabs_properties k).2.2.2.2.1 ⟨ϖ, hlt.le⟩ ϖ ?_ rfl
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext z
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
    Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
  rfl

variable (k n) in

def torusElt (ϖ : kˣ) (e : n → ℤ) : GL n k := diagT k n fun i => ϖ ^ e i

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_torusElt (ϖ : kˣ) (e : n → ℤ) : (torusElt k n ϖ e).1 = diagonal fun i => (ϖ : k) ^ e i := by
  simp [torusElt, val_diagT]

theorem nabs_det_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : n → ℤ) :
    nabs k (GeneralLinearGroup.det (torusElt k n ϖ e)) = (resCard k : ℝ) ^ (-∑ i, e i) := by
  have h1 : GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  have h2 := nabs_unif hϖ
  unfold nabs at h2 ⊢
  rw [h1, map_zpow, NNReal.coe_zpow, h2, _root_.inv_zpow']

theorem sphSection_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ) (e : n → ℤ) :
    sphSection k n s (io k n (torusElt k n ϖ e, 1)) =
      (resCard k : ℂ) ^ (-((Fintype.card n : ℂ) / 2 + s) * ((∑ i, |e i| : ℤ) : ℂ)) := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let B : Matrix n n k := diagonal fun i => (ϖ : k) ^ max (-e i) 0 - 1
  let C : Matrix n n k := diagonal fun i => (ϖ : k) ^ max (e i) 0 - 1
  have hBC : ∀ i, ((ϖ : k) ^ max (-e i) 0 - 1) * ((ϖ : k) ^ max (e i) 0 - 1) = 0 := fun i => by
    rcases le_total (e i) 0 with h | h <;> simp [h]
  have h : B * C = 0 := by simp only [B, C, diagonal_mul_diagonal, hBC, diagonal_zero]
  have h' : C * B = 0 := by simp only [B, C, diagonal_mul_diagonal, mul_comm ((ϖ : k) ^ max (e _) 0 - 1), hBC, diagonal_zero]
  have hint : ∀ f : n → ℤ, ∀ i j, (diagonal fun i => (ϖ : k) ^ max (f i) 0 - 1) i j ∈ 𝒪[k] := fun f i j => by
    rw [diagonal_apply]; split_ifs
    · refine sub_mem ?_ (one_mem _)
      show valuation k _ ≤ 1
      rw [map_zpow₀]
      exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (le_max_right _ _)
    · exact zero_mem _
  have hκ : shear B C h h' ∈ KO k (n ⊕ n) := shear_mem h h' (hint fun i => -e i) (hint e)
  have hv : (io k n (torusElt k n ϖ e, 1) * shear B C h h').1 =
      fromBlocks (torusElt k n ϖ e).1 ((torusElt k n ϖ e).1 * B) C 1 := by
    show fromBlocks (torusElt k n ϖ e).1 0 0 1 * fromBlocks 1 B C 1 = _
    simp [fromBlocks_multiply]
  have hL : (torusElt k n ϖ e).1 + (torusElt k n ϖ e).1 * B = (torusElt k n ϖ fun i => max (e i) 0).1 := by
    simp only [val_torusElt, B, diagonal_mul_diagonal, diagonal_add]
    congr 1
    funext i
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  let p : siegel k n := ⟨io k n (torusElt k n ϖ e, 1) * shear B C h h', mem_stabGL_diagSub.2 (by
    rw [hv]
    simp only [KeepsDiag, leviMat, Equiv.coe_refl, submatrix_id_id, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
      toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hL]
    simp only [val_torusElt, C, ← diagonal_one, diagonal_add, sub_add_cancel])⟩
  have h1 : leviGL (Equiv.refl (n ⊕ n)) p = torusElt k n ϖ fun i => max (e i) 0 := by
    ext1
    rw [val_leviGL, ← hL]
    show leviMat _ (io k n (torusElt k n ϖ e, 1) * shear B C h h').1 = _
    rw [hv]
    simp [leviMat]
  have h2 : nabs k (GeneralLinearGroup.det (p : GL (n ⊕ n) k)) =
      nabs k (GeneralLinearGroup.det (torusElt k n ϖ e)) := by
    show nabs k (GeneralLinearGroup.det (io k n (torusElt k n ϖ e, 1) * shear B C h h')) = _
    rw [map_mul, nabs_mul', nabs_det_of_mem_KO hκ, mul_one]
    congr 1
    ext
    exact (det_blkMat _ _ _).trans (by simp)
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have h3 : (absRatio k n p : ℝ) = (resCard k : ℝ) ^ (-∑ i, |e i|) := by
    rw [coe_absRatio, h1, h2, nabs_det_torusElt hϖ, nabs_det_torusElt hϖ, sq, ← zpow_add₀ hq.ne', ← zpow_sub₀ hq.ne']
    congr 1
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  rw [← sphSection_right s _ hκ, sphSection, show io k n (torusElt k n ϖ e, 1) * shear B C h h' = p from rfl,
    isIwasawa.iwAbs_coe, npow, h3, ← Real.rpow_intCast, ← Complex.cpow_mul_ofReal_nonneg hq.le]
  rw [Complex.ofReal_intCast, Complex.ofReal_natCast, Int.cast_neg]
  congr 1
  ring

variable (k n) in

def cell (ϖ : kˣ) (e : n → ℤ) : Set (GL n k) :=
  DoubleCoset.doubleCoset (torusElt k n ϖ e) (KO k n) (KO k n)

theorem isOpen_cell (ϖ : kˣ) (e : n → ℤ) : IsOpen (cell k n ϖ e) := SplitFlip.isOpen_KO.mul_left

theorem isCompact_cell (ϖ : kˣ) (e : n → ℤ) : IsCompact (cell k n ϖ e) :=
  (SplitFlip.isCompact_KO.mul isCompact_singleton).mul SplitFlip.isCompact_KO

theorem iUnion_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ⋃ e : {e : Fin N → ℤ // Antitone e}, cell k (Fin N) ϖ e = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨c, hc0, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
    (fun ij : Fin N × Fin N => g.1 ij.1 ij.2) |>.imp
      (fun c hc => And.intro (nonZeroDivisors.coe_ne_zero c) hc)
  choose G hG using hc
  obtain ⟨a, ha, k₁, h₁, k₂, h₂, e⟩ :=
    Formalism.UG.P.cartan_decomp_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (fun x hx => ⟨ord k (Units.mk0 x hx), by
        have h1 : ∀ m : ℤ, ord k (ϖ ^ m) = m := fun m => by
          let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
            rw [ord_mul, ofAdd_add]
          have := map_zpow o ϖ m
          rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
            smul_eq_mul, mul_one] at this
          exact this
        have h2 := ord_eq_zero_iff.1 (show ord k (Units.mk0 x hx * ϖ ^ (-ord k (Units.mk0 x hx))) = 0 by
          rw [ord_mul, h1, add_neg_cancel])
        rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, _root_.zpow_neg,
          mul_inv_eq_one₀ (zpow_ne_zero _ (by simp))] at h2
        exact h2⟩)
      g (c : 𝒪[k]) hc0 ⟨Matrix.of fun i j => G (i, j), by
        ext i j
        exact hG (i, j)⟩
  exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, h₁, k₂, h₂,
    Units.ext (by rw [e, Units.val_mul, Units.val_mul, val_torusElt])⟩⟩

theorem pairwise_disjoint_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    Pairwise (Function.onFun Disjoint fun e : {e : Fin N → ℤ // Antitone e} => cell k (Fin N) ϖ e) := by
  intro a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have e' : x'⁻¹ * x * torusElt k _ ϖ a * (y * y'⁻¹) = torusElt k _ ϖ b := by
    calc _ = x'⁻¹ * (x * torusElt k _ ϖ a * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) a.1 b.1 a.2 b.2 (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) ?_
  rw [← val_torusElt, ← val_torusElt, ← e', Units.val_mul (x'⁻¹ * x * _), Units.val_mul (x'⁻¹ * x)]

theorem hasSum_cell {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μ : Measure (GL (Fin N) k)) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {f : GL (Fin N) k → ℂ}
    (hf : Integrable f μ) (hb : ∀ g, ∀ x ∈ KO k (Fin N), ∀ y ∈ KO k (Fin N), f (x * g * y) = f g) :
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} =>
      (μ.real (cell k (Fin N) ϖ e) : ℂ) * f (torusElt k (Fin N) ϖ e)) (∫ g, f g ∂μ) := by
  have := hasSum_integral_iUnion (μ := μ) (f := f)
    (s := fun e : {e : Fin N → ℤ // Antitone e} => cell k (Fin N) ϖ e) (fun e => (isOpen_cell ϖ e.1).measurableSet) (pairwise_disjoint_cell hϖ)
    hf.integrableOn
  rw [iUnion_cell hϖ, Measure.restrict_univ] at this
  refine (funext fun e => ?_ : (fun e : {e : Fin N → ℤ // Antitone e} =>
    (μ.real (cell k (Fin N) ϖ e) : ℂ) * f (torusElt k (Fin N) ϖ e)) = _) ▸ this
  rw [setIntegral_congr_fun (isOpen_cell ϖ e.1).measurableSet (g := fun _ => f (torusElt k (Fin N) ϖ e))
    fun g hg => by
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      exact hb _ x hx y hy]
  simp

theorem zonal_biinv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {K : Subgroup G} {ω : G → ℂ} (h : IsZonal π K ω) (g : G) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    ω (x * g * y) = ω g := by
  obtain ⟨v, hv, l, hl, -, e⟩ := h
  have h1 : π y v = v := by simpa using hv ⟨y, hy⟩
  have h2 : π.dual x⁻¹ l = l := by simpa using hl ⟨x⁻¹, inv_mem hx⟩
  rw [e, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1]
  conv_rhs => rw [← h2]
  simp [Module.Dual.transpose_apply]

def lFactor (q : ℕ) (α : n → ℂˣ) (s : ℂ) : ℂ := ∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-s))⁻¹

def invNormFactor (q N : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(2 * s + i)))

end GlobalTheory.GLDoubling

namespace GlobalTheory.Published

open GlobalTheory.GLDoubling

def UnramifiedDoublingGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure], μ (KO k (Fin n)) = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ),
      HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        Integrable (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) μ ∧
        ∫ g, sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g ∂μ =
          lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
            invNormFactor (resCard k) n s

theorem UnramifiedDoublingGL.hasSum (H : UnramifiedDoublingGL)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin n)) = 1)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V} {α : Fin n → ℂˣ}
    (hπ : HasSatake π α) {ω : GL (Fin n) k → ℂ} (hω : IsZonal π (KO k (Fin n)) ω) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      HasSum (fun e : {e : Fin n → ℤ // Antitone e} => (μ.real (cell k (Fin n) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |e.1 i| : ℤ) : ℂ)) * ω (torusElt k (Fin n) ϖ e)))
        (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) n s) := by
  obtain ⟨s₀, h⟩ := H k n μ hμ V π α hπ ω hω
  refine ⟨s₀, fun s hs => ?_⟩
  have := hasSum_cell μ hϖ (h s hs).1 fun g x hx y hy => by
    rw [sphSection_io_biinv s g hx hy, zonal_biinv hω g hx hy]
  simp only [sphSection_torusElt hϖ, Fintype.card_fin] at this
  rwa [(h s hs).2] at this

example {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ α, HasSatake (detRep (Fin n) χ) α ∧
      IsZonal (detRep (Fin n) χ) (KO k (Fin n)) fun g => (χ (GeneralLinearGroup.det g) : ℂ) := by
  have key : ∀ g ∈ KO k (Fin n), χ (GeneralLinearGroup.det g) = 1 := fun g hg =>
    h _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hg))
  refine ⟨_, hasSatake_detRep h hϖ, 1, fun g => ?_, LinearMap.id, fun g => ?_, rfl, fun g => by simp [detRep]⟩
  · simp [detRep, key _ g.2]
  · ext
    simp [detRep, Module.Dual.transpose_apply, key _ g.2]

end GlobalTheory.Published
