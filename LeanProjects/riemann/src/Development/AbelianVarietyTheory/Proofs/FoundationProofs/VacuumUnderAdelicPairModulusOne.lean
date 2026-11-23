import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdealStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.VacMove

theorem hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (a b c : VC D N N') :
    Hf D T (a + b) c = Hf D T a c + Hf D T b c := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (a b c : VC D N N') :
    Hf D T a (b + c) = Hf D T a b + Hf D T a c := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem wd_wd (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), fun F => ?_⟩
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, hf_add_left, hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

theorem wd_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin d) (Fin a) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (z w : Matrix (Fin d) (Fin a) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem iop_zero (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) : Iop D T A B 0 = 0 := by
  funext z
  simp [Iop, U]

theorem iop_self (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) : Iop D T A A G = G := by
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [AddSubgroup.addSubgroupOf_self]
    exact QuotientAddGroup.subsingleton_quotient_top
  have : Unique (A ⧸ A.addSubgroupOf A) :=
    ⟨⟨((0 : A) : A ⧸ A.addSubgroupOf A)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique, hG.2 _ (Subtype.mem _)]
  simp

def MI (D : D7) (cc : Ideal (𝓞 D.host.K)) (m : ℕ) {a b : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) : Prop :=
  ∀ i j, ∃ y ∈ IhE D cc, M i j = (m : AE D) * y

section
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {a b : ℕ}

theorem MI.sub {m : ℕ} {M M' : Matrix (Fin a) (Fin b) (AE D)} (h : MI D cc m M) (h' : MI D cc m M') :
    MI D cc m (M - M') := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  obtain ⟨y', hy', e'⟩ := h' i j
  exact ⟨y - y', sub_mem hy hy', by rw [Matrix.sub_apply, e, e', mul_sub]⟩

theorem MI.add {m : ℕ} {M M' : Matrix (Fin a) (Fin b) (AE D)} (h : MI D cc m M) (h' : MI D cc m M') :
    MI D cc m (M + M') := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  obtain ⟨y', hy', e'⟩ := h' i j
  exact ⟨y + y', add_mem hy hy', by rw [Matrix.add_apply, e, e', mul_add]⟩

theorem MI.of_dvd {m k : ℕ} {M : Matrix (Fin a) (Fin b) (AE D)} (hd : m ∣ k) (h : MI D cc k M) :
    MI D cc m M := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  obtain ⟨c, rfl⟩ := hd
  exact ⟨c • y, nsmul_mem hy c, by rw [e, nsmul_eq_mul]; push_cast; ring⟩

theorem MI_one {M : Matrix (Fin a) (Fin b) (AE D)} : MI D cc 1 M ↔ ∀ i j, M i j ∈ IhE D cc := by
  simp [MI]

theorem exists_mat_denom (P : Matrix (Fin a) (Fin b) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * P i j ∈ OhE D := by
  choose m hm h using fun q : Fin a × Fin b => exists_nat_denom D (P q.1 q.2)
  refine ⟨∏ q, m q, Finset.prod_pos fun q _ => hm q, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, j))
  rw [hk, mul_comm (m _) k, Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h (i, j))

theorem MI_bound (hc : cc ≠ ⊥) (P : Matrix (Fin a) (Fin a) (AE D)) (Q : Matrix (Fin b) (Fin b) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ (m : ℕ) (M : Matrix (Fin a) (Fin b) (AE D)), MI D cc (n * m) M → MI D cc m (P * M * Q) := by
  obtain ⟨n, hn, hP⟩ := exists_mat_denom P
  obtain ⟨n', hn', hQ⟩ := exists_mat_denom Q
  refine ⟨n * n', Nat.mul_pos hn hn', fun m M hM i j => ?_⟩
  choose y hy e using hM
  refine ⟨∑ l, ∑ k, ((n : AE D) * P i k * ((n' : AE D) * Q l j)) * y k l,
    sum_mem fun l _ => sum_mem fun k _ => (GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal D cc hc).2.2 _ (mul_mem (hP _ _) (hQ _ _)) _ (hy _ _), ?_⟩
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, e]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem MI_approx (hc : cc ≠ ⊥) (M : Matrix (Fin a) (Fin b) (AE D)) (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) D.host.E, MI D cc m (z.map (inc D) - M) := by
  choose e t ht h using fun i j => (GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal D cc hc).1 (M i j) m hm
  exact ⟨Matrix.of e, fun i j => ⟨t i j, ht i j, h i j⟩⟩

end

theorem moves_unique {D : D7} {N : ℕ} {g : GL (Fin N) (AE D)} {L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D g L) (h' : Moves D g L') : L = L' := by
  ext x; rw [h x, h' x]

theorem sd_of_moves {D : D7} {N : ℕ} {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  rw [moves_unique h (h1 g).1]; exact (h1 g).2

theorem moves_mul_int {D : D7} {N : ℕ} {g k : GA D N} (hk : k ∈ intG D N)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : Moves D (g : GL (Fin N) (AE D)) L) :
    Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) L := by
  obtain ⟨Lt, h1, -, h3, -⟩ := exists_lattice_of_adelic_point D N
  rw [moves_unique h (h1 g).1, (h3 g (g * k)).2 (by simpa using hk)]
  exact (h1 _).1

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem klat {D : D7} (T : Tor D) {N N' : ℕ} {g : GA D N} {g' : GA D N'} {L₁ L₁'}
    (h : Moves D (g : GL (Fin N) (AE D)) L₁) (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    KLat D T (La D T L₁ L₁') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem wd_fix {D : D7} (h1 : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) {F : VC D N N' → ℂ}
    (hF : F ∈ ThSp D (tor0 D cc δ) A) {x : VC D N N'} (hx : x ∈ A) : Wd D (tor0 D cc δ) x F = F := by
  rw [(GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 cc δ hc N N' A hA).2.1 x hx]
  exact funext (hF.2 x hx)

theorem vac_TT {D : D7} (h1 : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) :
    e0 ∈ TT D (tor0 D cc δ) N N' :=
  ⟨he.1, 1, one_pos, fun x hx => by
    rw [one_smul]; exact wd_fix h1 hc (klat _ (moves_one D N) (moves_one D N')) he hx⟩

theorem exists_scalar {D : D7} (hI : Inp D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {e0 : VC D N N' → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {L₁ L₁'} (h : Moves D (g : GL (Fin N) (AE D)) L₁)
    (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    ∃ c : ℂ, W.Om g g' e0 = fun z => c *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  have hcc : cc ≠ ⊥ := hc.1.1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have k1 := klat (tor0 D cc δ) h h'
  have hT := vac_TT hI.g1 hc he
  obtain ⟨-, hF, -, hinv⟩ := hI.uni cc δ hc N N' _ _ k0 k1 e0 he
  have hF0 : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 ≠ 0 := by
    intro h0
    rw [h0, iop_zero] at hinv
    exact W.nz hinv.symm
  obtain ⟨hline, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 cc δ hc N N' _ k1
  suffices hG : W.Om g g' e0 ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') from hline _ hG _ hF hF0
  refine ⟨(W.maps g g' e0 hT).1, fun x hx => ?_⟩
  suffices hs : Wd D (tor0 D cc δ) x (W.Om g g' e0) = W.Om g g' e0 by
    rw [hW x hx] at hs; exact congrFun hs
  have hmul : ∀ a ∈ La D (tor0 D cc δ) L₁ L₁', ∀ b ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F,
      Wd D (tor0 D cc δ) a (Wd D (tor0 D cc δ) b F) = Wd D (tor0 D cc δ) (a + b) F := by
    intro a ha b hb F
    obtain ⟨φ, hφ⟩ := wd_wd D (tor0 D cc δ) a b
    have h2 := hφ (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0)
    rw [wd_fix hI.g1 hc k1 hF hb, wd_fix hI.g1 hc k1 hF ha, wd_fix hI.g1 hc k1 hF (add_mem ha hb)] at h2
    have h3 : φ = 1 := by
      by_contra hne
      apply hF0
      have : (φ - 1) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 = 0 := by
        rw [sub_smul, one_smul, ← h2, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    rw [hφ, h3, one_smul]
  obtain ⟨z', rfl, hz'⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hI.g1 cc δ hcc N N' g g' L₁ L₁' h h' x hx
  have hlatb := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hI.g1 cc δ hcc N N' g g' L₁ L₁' h h'
  have hlat0 := GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hI.g1 cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hlat0
  simp only [← MI_one] at hz' hlatb hlat0
  obtain ⟨m0, hm0, hl0⟩ := W.lift g g' 0 e0 hT
  rw [pt_zero, wd_zero] at hl0
  set P : Matrix (Fin N') (Fin N') (AE D) := ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP
  set P' : Matrix (Fin N') (Fin N') (AE D) :=
    (((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) with hP'
  set Q : Matrix (Fin N) (Fin N) (AE D) := ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ
  set Q' : Matrix (Fin N) (Fin N) (AE D) :=
    (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hQ'
  have ePP : P * P' = 1 := Units.mul_inv _
  have eP'P : P' * P = 1 := Units.inv_mul _
  have eQQ : Q * Q' = 1 := Units.mul_inv _
  have eQ'Q : Q' * Q = 1 := Units.inv_mul _
  have e1 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P * (P' * M * Q) * Q' = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ePP, Matrix.one_mul, Matrix.mul_assoc, eQQ, Matrix.mul_one]
  have e2 : ∀ M : Matrix (Fin N') (Fin N) (AE D), P' * (P * M * Q') * Q = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eP'P, Matrix.one_mul, Matrix.mul_assoc, eQ'Q, Matrix.mul_one]
  obtain ⟨n, hn, hb⟩ := MI_bound hcc P Q'
  obtain ⟨n', hn', hb'⟩ := MI_bound hcc P' Q
  obtain ⟨z, hz⟩ := MI_approx hcc (P' * z'.map (inc D) * Q) (n * m0) (Nat.mul_pos hn hm0)
  have hz0 : MI D cc 1 (z.map (inc D)) := by
    simpa using (hz.of_dvd (one_dvd _)).add hz'
  obtain ⟨m, hm, hl⟩ := W.lift g g' z e0 hT
  rw [wd_fix hI.g1 hc k0 he (hlat0 z hz0)] at hl
  obtain ⟨w, hw⟩ := MI_approx hcc (P * z.map (inc D) * Q') (n' * (m * m0)) (by positivity)
  have hw1 : MI D cc 1 (P' * w.map (inc D) * Q) := by
    have := ((hb' _ _ hw).of_dvd (one_dvd _)).add hz0
    rwa [Matrix.mul_sub, Matrix.sub_mul, e2, sub_add_cancel] at this
  have hd : (w - z').map (inc D) = w.map (inc D) - z'.map (inc D) := by
    ext i j; simp
  have hd' : (z' - w).map (inc D) = z'.map (inc D) - w.map (inc D) := by
    ext i j; simp
  have hdiff : MI D cc m0 ((z' - w).map (inc D)) := by
    have h1 := hb _ _ hz
    rw [Matrix.mul_sub, Matrix.sub_mul, e1] at h1
    have h2 : MI D cc m0 (0 : Matrix (Fin N') (Fin N) (AE D)) := fun i j => ⟨0, zero_mem _, by simp⟩
    have := (h2.sub h1).sub (hw.of_dvd (m := m0) ⟨n' * m, by ring⟩)
    rw [hd']
    convert this using 1
    abel
  have f1 := hl w (hw.of_dvd (m := m) ⟨n' * m0, by ring⟩)
  have f2 := hl0 (z' - w) (by
    intro i j
    have h0 : (0 : Matrix (Fin N') (Fin N) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    exact hdiff i j)
  have hdl : MI D cc 1 (P' * (z' - w).map (inc D) * Q) := by
    rw [hd', Matrix.mul_sub, Matrix.sub_mul]
    exact hz'.sub hw1
  have := hmul _ (hlatb w hw1) _ (hlatb _ hdl) (W.Om g g' e0)
  rw [← f2, ← f1, ← pt_add, add_sub_cancel] at this
  exact this.symm

theorem algebraicModulusOneAll_mul {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) : Mod1All (a * b) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  refine ⟨mul_mem h1 h3, fun σ => ?_⟩
  have : (⟨a * b, mul_mem h1 h3⟩ : Qbar) = ⟨a, h1⟩ * ⟨b, h3⟩ := rfl
  rw [this, map_mul, norm_mul, h2, h4, one_mul]

theorem algebraicModulusOneAll_zpow {a : ℂ} (ha : Mod1All a) (k : ℤ) : Mod1All (a ^ k) := by
  obtain ⟨h1, h2⟩ := ha
  refine ⟨zpow_mem h1 k, fun σ => ?_⟩
  have : (⟨a ^ k, zpow_mem h1 k⟩ : Qbar) = ⟨a, h1⟩ ^ k :=
    Subtype.ext (map_zpow₀ Qbar.val ⟨a, h1⟩ k).symm
  rw [this, map_zpow₀, norm_zpow, h2, one_zpow]

theorem mem_of_pow {a : ℂ} {k : ℕ} (hk : 0 < k) (h : a ^ k ∈ Qbar) : a ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact IsAlgebraic.of_pow hk h

theorem modulusOneAllEmbeddings_of_pow {a : ℂ} {k : ℕ} (hk : 0 < k) (ha : Mod1All (a ^ k)) : Mod1All a := by
  obtain ⟨h1, h2⟩ := ha
  refine ⟨mem_of_pow hk h1, fun σ => ?_⟩
  have h3 := h2 σ
  have : (⟨a ^ k, h1⟩ : Qbar) = ⟨a, mem_of_pow hk h1⟩ ^ k := rfl
  rw [this, map_pow, norm_pow] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3

theorem norm_lamC_of_root {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a c : ℂ} {k : ℕ} (hk : 0 < k)
    (ha : a ^ k = 1) (hc : c ∈ Qbar) (h : ‖lamC lam (a * c)‖ = 1) : ‖lamC lam c‖ = 1 := by
  have h1 : a ∈ Qbar := mem_of_pow hk (by rw [ha]; exact one_mem _)
  have h2 : (⟨a, h1⟩ : Qbar) ^ k = 1 := Subtype.ext ha
  have h3 : ‖lam ⟨a, h1⟩‖ = 1 := by
    have := congrArg (fun t => ‖lam t‖) h2
    simp only [map_pow, norm_pow, map_one, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 this
  have h4 : (⟨a * c, mul_mem h1 hc⟩ : Qbar) = ⟨a, h1⟩ * ⟨c, hc⟩ := rfl
  rw [lamC, dif_pos (mul_mem h1 hc), h4, map_mul, norm_mul, h3, one_mul] at h
  rw [lamC, dif_pos hc, h]

end GlobalTheory.NormSum.VacMove

open GlobalTheory.NormSum.VacMove in

theorem GlobalTheory.NormSum.vacuum_under_adelic_pair : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  intro D hI cc δ hc N N' hev e0 he W g g' L₁ L₁' h h'
  obtain ⟨c, hce⟩ := exists_scalar hI hc he W g g' h h'
  have hmod : Mod1All c := by
    obtain ⟨z, x, hz, hx, -⟩ := exists_splitComp D _ (det_norm D g)
    obtain ⟨z', x', hz', hx', -⟩ := exists_splitComp D _ (det_norm D g')
    obtain ⟨sg, hsg, hc2⟩ := (hI.odd4 cc δ hc N N' hev e0 he W.nz W g g' L₁ L₁' c h h' hce).1 z z' x x' hz hz' hx hx'
    refine modulusOneAllEmbeddings_of_pow (k := 2 * 2) (by norm_num) ?_
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have h4 : c ^ (2 * 2) = ((W.chV.f x' : ℂˣ) : ℂ) ^ (4 * W.ep) * ((W.chV'.f x : ℂˣ) : ℂ) ^ (4 * W.ep') := by
      rw [pow_mul, hc2, mul_pow, hs, one_mul, ← Units.val_pow_eq_pow_val, ← Units.val_zpow_eq_zpow_val,
        ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, mul_pow]
      congr 2 <;> (rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]; congr 1; push_cast; ring)
    rw [h4]
    exact algebraicModulusOneAll_mul (algebraicModulusOneAll_zpow (GlobalTheory.T.unitaryHeckeCharacter_values D N W.chV x').1 _) (algebraicModulusOneAll_zpow (GlobalTheory.T.unitaryHeckeCharacter_values D N' W.chV' x).1 _)
  refine ⟨c, hmod, hce, fun p _ lam k' hk' ht ht' => ?_⟩
  have hm1 : Moves D (k' : GL (Fin N') (AE D)) (stdL D N') := by
    simpa using moves_mul_int hk' (moves_one D N')
  obtain ⟨a, hae⟩ := exists_scalar hI hc he W 1 k' (moves_one D N) hm1
  obtain ⟨k, hk, hak⟩ : ∃ k : ℕ, 0 < k ∧ a ^ k = 1 := by
    obtain ⟨z, x, hz, hx, hxi⟩ := exists_splitComp D _ (det_norm D (1 : GA D N))
    obtain ⟨z', x', hz', hx', hxi'⟩ := exists_splitComp D _ (det_norm D k')
    obtain ⟨sg, hsg, hc2⟩ := (hI.odd4 cc δ hc N N' hev e0 he W.nz W 1 k' _ _ a (moves_one D N) hm1 hae).1
      z z' x x' hz hz' hx hx'
    obtain ⟨m, hm, hxm⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D N' W.chV' x).2.1
      (hxi (det_int D _ (((mem_ratG_intG D N).2.1 1).1 (one_mem _))))
    obtain ⟨m', hm', hxm'⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D N W.chV x').2.1
      (hxi' (det_int D _ (((mem_ratG_intG D N').2.1 k').1 hk')))
    refine ⟨2 * (2 * (m * m')), by positivity, ?_⟩
    have hs : sg ^ 2 = 1 := by rcases hsg with rfl | rfl <;> norm_num
    have key : ∀ (u : ℂˣ) (e : ℤ) (r s : ℕ), u ^ r = 1 → r ∣ s → ((u ^ 2) ^ e) ^ s = 1 := by
      rintro u e r _ hu ⟨t, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm e, zpow_mul, zpow_natCast, ← pow_mul, mul_comm 2, mul_assoc,
        pow_mul, hu, one_pow, one_zpow]
    rw [pow_mul, hc2, mul_pow, pow_mul sg, hs, one_pow, one_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      key _ _ m' _ hxm' ⟨2 * m, by ring⟩, key _ _ m _ hxm ⟨2 * m', by ring⟩, one_mul, Units.val_one]
  have hT := vac_TT hI.g1 hc he
  have hae' : W.Om 1 k' e0 = a • e0 := by
    rw [hae, show La D (tor0 D cc δ) (stdL D N) (stdL D N') = La0 D (tor0 D cc δ) N N' from rfl,
      iop_self D _ (La0 D (tor0 D cc δ) N N') he]
    rfl
  have hprod : W.Om g (g' * k') e0 = fun z => (a * c) *
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
    have := W.mul g 1 g' k' e0 hT
    rw [mul_one, hae', W.smul _ _ _ _ hT, hce] at this
    rw [this]
    funext z
    simp [mul_assoc]
  exact norm_lamC_of_root lam hk hak hmod.1
    ((hI.odd4 cc δ hc N N' hev e0 he W.nz W g (g' * k') L₁ L₁' _ h (moves_mul_int hk' h') hprod).2 p lam ht ht').2
