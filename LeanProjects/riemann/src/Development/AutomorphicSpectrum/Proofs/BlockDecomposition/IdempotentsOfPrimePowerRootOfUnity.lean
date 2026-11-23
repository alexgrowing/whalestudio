import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTiltStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.RootsLC

section Fourier

variable {O S : Type*} [CommRing O] [IsDomain O] [CommRing S]

noncomputable def proj (φ : O →+* S) (ω : O) (q : ℕ) (z : S) (k : ℕ) : S :=
  ∑ i ∈ Finset.range q, (z * φ ω ^ k) ^ i

theorem geom_eq_zero {u : O} {q : ℕ} (hu : u ^ q = 1) (hne : u ≠ 1) :
    ∑ i ∈ Finset.range q, u ^ i = 0 := by
  have h := geom_sum_mul u q
  rw [hu, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)

variable (φ : O →+* S) {ζ ω : O} {q : ℕ} {z : S}

theorem pow_inv_eq_one (hq : ζ ^ q = 1) (hω : ζ * ω = 1) : ω ^ q = 1 := by
  have h := congrArg (· ^ q) hω
  simpa [mul_pow, hq] using h

theorem proj_mul_sub (hq : ζ ^ q = 1) (hω : ζ * ω = 1) (hz : z ^ q = 1) (k : ℕ) :
    proj φ ω q z k * (z - φ ζ ^ k) = 0 := by
  have hw : (z * φ ω ^ k) ^ q = 1 := by
    rw [mul_pow, hz, one_mul, ← pow_mul, mul_comm k q, pow_mul, ← map_pow, pow_inv_eq_one hq hω,
      map_one, one_pow]
  have h1 : proj φ ω q z k * (z * φ ω ^ k - 1) = 0 := by
    rw [proj, geom_sum_mul, hw, sub_self]
  have h3 : φ ζ ^ k * φ ω ^ k = 1 := by
    rw [← mul_pow, ← map_mul, hω, map_one, one_pow]
  have h2 : z - φ ζ ^ k = φ ζ ^ k * (z * φ ω ^ k - 1) := by
    linear_combination (-z) * h3
  rw [h2, mul_left_comm, h1, mul_zero]

theorem proj_mul_proj (hq : ζ ^ q = 1) (hω : ζ * ω = 1) (hz : z ^ q = 1) (j k : ℕ) :
    proj φ ω q z j * proj φ ω q z k =
      φ (∑ i ∈ Finset.range q, (ζ ^ k * ω ^ j) ^ i) * proj φ ω q z k := by
  have hzk : z * proj φ ω q z k = φ ζ ^ k * proj φ ω q z k := by
    have := proj_mul_sub φ hq hω hz k
    linear_combination this
  have step : ∀ i : ℕ, (z * φ ω ^ j) ^ i * proj φ ω q z k =
      φ ((ζ ^ k * ω ^ j) ^ i) * proj φ ω q z k := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : φ ((ζ ^ k * ω ^ j) ^ (i + 1)) =
          φ ((ζ ^ k * ω ^ j) ^ i) * (φ ζ ^ k * φ ω ^ j) := by
        simp [pow_succ]
      rw [pow_succ, e]
      linear_combination (z * φ ω ^ j) * ih + φ ((ζ ^ k * ω ^ j) ^ i) * φ ω ^ j * hzk
  rw [map_sum, Finset.sum_mul]
  conv_lhs => rw [proj, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => step i

theorem proj_self (hq : ζ ^ q = 1) (hω : ζ * ω = 1) (hz : z ^ q = 1) (k : ℕ) :
    proj φ ω q z k * proj φ ω q z k = (q : S) * proj φ ω q z k := by
  rw [proj_mul_proj φ hq hω hz, ← mul_pow, hω]
  simp

theorem proj_orth (hq : IsPrimitiveRoot ζ q) (hω : ζ * ω = 1) (hz : z ^ q = 1) {j k : ℕ}
    (hj : j < q) (hk : k < q) (hjk : j ≠ k) :
    proj φ ω q z j * proj φ ω q z k = 0 := by
  have hq1 := hq.pow_eq_one
  have hu : (ζ ^ k * ω ^ j) ^ q = 1 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k q, mul_comm j q, pow_mul, pow_mul, hq1,
      pow_inv_eq_one hq1 hω, one_pow, one_pow, one_mul]
  have hne : ζ ^ k * ω ^ j ≠ 1 := by
    intro h
    have h3 : ζ ^ j * ω ^ j = 1 := by rw [← mul_pow, hω, one_pow]
    have : ζ ^ j = ζ ^ k := by linear_combination (-ζ ^ j) * h + ζ ^ k * h3
    exact hjk (hq.pow_inj hj hk this)
  rw [proj_mul_proj φ hq1 hω hz, geom_eq_zero hu hne, map_zero, zero_mul]

theorem sum_proj (hq : IsPrimitiveRoot ζ q) (hq0 : 0 < q) (hω : ζ * ω = 1) :
    ∑ k ∈ Finset.range q, proj φ ω q z k = (q : S) := by
  have hq1 := hq.pow_eq_one
  have hω1 := pow_inv_eq_one hq1 hω
  have e : ∀ k, proj φ ω q z k = ∑ i ∈ Finset.range q, z ^ i * φ ((ω ^ i) ^ k) := by
    intro k
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, map_pow, map_pow, ← pow_mul, ← pow_mul, mul_comm k i]
  simp_rw [e]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← map_sum]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hq0)]
  · simp
  · intro i hi hi0
    have hi' := Finset.mem_range.1 hi
    have hu : (ω ^ i) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω1, one_pow]
    have hne : ω ^ i ≠ 1 := by
      intro h
      have h3 : ζ ^ i * ω ^ i = 1 := by rw [← mul_pow, hω, one_pow]
      rw [h, mul_one] at h3
      exact hi0 (Nat.eq_zero_of_dvd_of_lt (hq.dvd_of_pow_eq_one i h3) hi' |>.symm ▸ rfl)
    rw [geom_eq_zero hu hne, map_zero, mul_zero]

end Fourier

theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (f : ℕ → M) :
    ∑ c : ZMod q, f c.val = ∑ k ∈ Finset.range q, f k := by
  refine Finset.sum_nbij' (fun c => c.val) (fun k => (k : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_range.2 (ZMod.val_lt c)
  · intro k _; exact Finset.mem_univ _
  · intro c _; simp
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hk)
  · intro c _; rfl

theorem exists_idem {S : Type} [CommRing S] (ϖ : S) (h0 : ϖ ∈ nonZeroDivisors S) (hV : R.Val ϖ)
    (n : ℕ) (t : S) (ht : t * t = ϖ ^ n * t) : ∃ y, ϖ ^ n * y = t ∧ y * y = y := by
  let L := Localization.Away ϖ
  let v : L := IsLocalization.Away.invSelf ϖ
  have hv : algebraMap S L ϖ * v = 1 := IsLocalization.Away.mul_invSelf ϖ
  have hvn : algebraMap S L ϖ ^ n * v ^ n = 1 := by rw [← mul_pow, hv, one_pow]
  have hinj : Function.Injective (algebraMap S L) :=
    IsLocalization.injective _ (M := Submonoid.powers ϖ) (Submonoid.powers_le.2 h0)
  have htt : algebraMap S L t * algebraMap S L t = algebraMap S L ϖ ^ n * algebraMap S L t := by
    rw [← map_mul, ht, map_mul, map_pow]
  set x : L := algebraMap S L t * v ^ n with hx
  have hxx : x * x = x := by
    rw [hx]
    linear_combination v ^ n * v ^ n * htt + algebraMap S L t * v ^ n * hvn
  have hint : IsIntegral S x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      linear_combination hxx
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral ϖ h0 hV x hint
  refine ⟨y, hinj ?_, hinj ?_⟩
  · rw [map_mul, map_pow, hy, hx]
    linear_combination algebraMap S L t * hvn
  · rw [map_mul, hy, hxx]

section Teich

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem eq_of_idem {a b : A.W} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a.coeff 0 = b.coeff 0) : a = b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  set d := a - b with hd
  have hd3 : d * d * d = d := by
    rw [hd]
    linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'
  have hmem : d ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, hd, ← WittVector.constantCoeff_apply, map_sub, sub_eq_zero]
    exact h
  have hall : ∀ k : ℕ, d ∈ Ideal.span {(l : A.W)} ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← hd3, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ih) hmem
  have h0 : d = 0 := IsHausdorff.haus (A.completeW.toIsHausdorff) d fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall k
  exact sub_eq_zero.1 h0

theorem teich_sum {ι : Type*} [Fintype ι] {e : ι → A.A} (he : OrthogonalIdempotents e) :
    WittVector.teichmuller l (∑ i, e i) = ∑ i, WittVector.teichmuller l (e i) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller l (e i) :=
    ⟨fun i => by
      show _ * _ = _
      rw [← map_mul, he.idem i |>.eq],
     fun i j hij => by
      show _ * _ = _
      rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩
  refine eq_of_idem A ?_ (ho.isIdempotentElem_sum) ?_
  · have := he.isIdempotentElem_sum (s := Finset.univ)
    show _ * _ = _
    rw [← map_mul, this.eq]
  · rw [WittVector.teichmuller_coeff_zero, ← WittVector.constantCoeff_apply, map_sum]
    simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem sharp_zero : A.sharp 0 = 0 := by
  show A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem sharp_sum {ι : Type*} [Fintype ι] {e : ι → A.A} (he : OrthogonalIdempotents e) :
    A.sharp (∑ i, e i) = ∑ i, A.sharp (e i) := by
  show A.th (WittVector.teichmuller l _) = ∑ i, A.th (WittVector.teichmuller l _)
  rw [teich_sum A he, map_sum]

end Teich

theorem exists_idempotents_of_root_of_unity {l : ℕ} [Fact l.Prime] (A : PAlg l)
    (hV : R.Val (l : A.U)) (n : ℕ) (ζ : OC l) (hζ : IsPrimitiveRoot ζ (l ^ n)) (z : A.U)
    (hz : z ^ l ^ n = 1) :
    ∃ e : ZMod (l ^ n) → A.A,
      (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩;
        CompleteOrthogonalIdempotents e) ∧
      ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl : (l : A.U) ∈ nonZeroDivisors A.U := (GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).1
  have hq0 : 0 < l ^ n := Nat.pos_of_ne_zero (NeZero.ne _)
  have hq1 : ζ ^ l ^ n = 1 := hζ.pow_eq_one
  obtain ⟨ω, hω⟩ : ∃ ω : OC l, ζ * ω = 1 := ⟨ζ ^ (l ^ n - 1), by
    rw [← pow_succ', Nat.sub_add_cancel hq0, hq1]⟩
  have hc : ∀ x : A.U, (l : A.U) ^ n * x = 0 → x = 0 :=
    fun x h => mem_nonZeroDivisors_iff_left.1 (pow_mem hl n) x h
  have hcast : ((l ^ n : ℕ) : A.U) = (l : A.U) ^ n := by push_cast; rfl
  set P := proj A.oC ω (l ^ n) z with hP
  have hself : ∀ k, P k * P k = (l : A.U) ^ n * P k := fun k => by
    rw [hP, proj_self A.oC hq1 hω hz k, hcast]
  choose y hy1 hy2 using fun k => exists_idem (l : A.U) hl hV n (P k) (hself k)
  have hyo : ∀ {j k : ℕ}, j < l ^ n → k < l ^ n → j ≠ k → y j * y k = 0 := by
    intro j k hj hk hjk
    apply hc; apply hc
    have := proj_orth A.oC hζ hω hz hj hk hjk
    rw [← hP, ← hy1 j, ← hy1 k] at this
    linear_combination this
  have hys : ∑ k ∈ Finset.range (l ^ n), y k = 1 := by
    have h := sum_proj (z := z) A.oC hζ hq0 hω
    rw [← hP, hcast] at h
    rw [← sub_eq_zero]
    apply hc
    have h' : ∑ k ∈ Finset.range (l ^ n), (l : A.U) ^ n * y k = ∑ k ∈ Finset.range (l ^ n), P k :=
      Finset.sum_congr rfl fun k _ => hy1 k
    rw [mul_sub, Finset.mul_sum, mul_one, h', h, sub_self]
  have hyz : ∀ k, y k * (z - A.oC ζ ^ k) = 0 := by
    intro k
    apply hc
    rw [← mul_assoc, hy1]
    exact proj_mul_sub A.oC hq1 hω hz k
  choose e he using fun k => GlobalTheory.T.existsUnique_idempotent_lift_tilt A (y k) (hy2 k)
  have hzero : ∀ a : A.A, IsIdempotentElem a → A.sharp a = 0 → a = 0 := fun a ha hs =>
    (GlobalTheory.T.existsUnique_idempotent_lift_tilt A 0 (IsIdempotentElem.zero)).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, sharp_zero A⟩
  have hO : OrthogonalIdempotents fun c : ZMod (l ^ n) => e c.val := by
    refine ⟨fun c => (he _).1.1, fun c d hcd => ?_⟩
    refine hzero _ ((he _).1.1.mul (he _).1.1) ?_
    rw [map_mul, (he _).1.2, (he _).1.2]
    exact hyo (ZMod.val_lt c) (ZMod.val_lt d) fun h => hcd (ZMod.val_injective _ h)
  refine ⟨fun c => e c.val, ⟨hO, ?_⟩, fun c => ?_⟩
  · refine (GlobalTheory.T.existsUnique_idempotent_lift_tilt A 1 IsIdempotentElem.one).unique ⟨hO.isIdempotentElem_sum, ?_⟩
      ⟨IsIdempotentElem.one, map_one _⟩
    rw [sharp_sum A hO]
    simp_rw [fun c : ZMod (l ^ n) => (he c.val).1.2]
    rw [sum_zmod_val (l ^ n) y, hys]
  · show A.sharp (e c.val) * _ = 0
    rw [(he _).1.2]
    exact hyz _

end GlobalTheory.CompanionTheory.RootsLC
