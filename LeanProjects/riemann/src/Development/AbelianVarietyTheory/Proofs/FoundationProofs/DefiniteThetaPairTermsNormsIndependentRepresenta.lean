import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinearStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembershipStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.RepInv

section Translates

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_nsmul (n : ℕ) (x z : VC D N N') : Hf D T (n • x) z = Hf D T x (n • z) := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem differentiable_hf (x : VC D N N') : Differentiable ℂ (fun z => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem differentiable_wd (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Wd D T x G) := by
  have h := differentiable_hf (T := T) x
  unfold Wd U
  fun_prop

theorem wd_wd_of_int {x z : VC D N N'} {G : VC D N N' → ℂ} (hx : Wd D T x G = G) (m : ℤ)
    (hm : (Hf D T x z).im = m) (w : VC D N N') : Wd D T x (Wd D T z G) w = Wd D T z G w := by
  have h1 := congrFun hx (w + z)
  have h2 : Hf D T x z = Hf D T z x + 2 * Complex.I * m := by
    rw [hf_conj x z]
    apply Complex.ext <;> simp [hm]
    ring
  have h3 : Complex.exp (-(Real.pi : ℂ) * Hf D T (w + x) z - (Real.pi : ℂ) * Hf D T z z / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w x - (Real.pi : ℂ) * Hf D T x x / 2) =
      Complex.exp (-(Real.pi : ℂ) * Hf D T (w + z) x - (Real.pi : ℂ) * Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T w z - (Real.pi : ℂ) * Hf D T z z / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hf_add_left, hf_add_left, h2]
    push_cast
    ring
  simp only [Wd, U] at h1 ⊢
  rw [← h1, add_right_comm w x z]
  linear_combination (wdPh D T x * wdPh D T z * G (w + z + x)) * h3

end Translates

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

theorem test_mem (hg : admG1 D) (hc : Crv D cc δ) (P : Pair D cc δ t0 Q) (hQ : 0 < Q) :
    P.F ∈ TT D (tor0 D cc δ) P.a P.d := by
  obtain ⟨k, r, z, hz, -, -, hF⟩ := P.pres
  obtain ⟨-, hW, hI, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨hd, he⟩ := P.vac.1
  refine ⟨?_, Q, hQ, fun x hx => ?_⟩
  · rw [hF]
    exact Differentiable.fun_sum fun i _ => (differentiable_wd _ hd).const_mul _
  · have hx' : Q • x ∈ La0 D (tor0 D cc δ) P.a P.d := AddSubgroup.nsmul_mem _ hx _
    have h0 : Wd D (tor0 D cc δ) (Q • x) P.e0 = P.e0 := by
      rw [hW _ hx']
      funext w
      exact he _ hx' w
    funext w
    have h1 : ∀ i, Wd D (tor0 D cc δ) (Q • x) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) w =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 w := fun i => by
      obtain ⟨m, hm⟩ := hI x hx _ (hz i)
      exact wd_wd_of_int h0 m (by rw [hf_nsmul, hm]) w
    rw [hF]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg ((r i : ℂ) * ·) (h1 i))
    generalize (fun i => Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) = G
    conv_lhs => rw [Wd, U]
    conv_rhs => enter [2, i]; rw [Wd, U]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem map_emb_unitary {N : ℕ} {γ : Matrix (Fin N) (Fin N) D.host.E}
    (h : γ * (γ.map D.host.conj).transpose = 1) (τ : D.what₂.Tau) :
    γ.map (embT D τ) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : star (γ.map (embT D τ)) = ((γ.map D.host.conj).transpose).map (embT D τ) := by
    ext i j
    simp only [Matrix.star_apply, Matrix.map_apply, Matrix.transpose_apply]
    exact (D.host.conjE_apply (embT D τ) (γ j i)).symm
  rw [h1, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_map_emb {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (τ : D.what₂.Tau) :
    (γ.map (embT D τ)).det = embT D τ γ.det := (RingHom.map_det (embT D τ) γ).symm

theorem norm_emb_det {N : ℕ} {γ : Matrix (Fin N) (Fin N) D.host.E}
    (h : γ * (γ.map D.host.conj).transpose = 1) (τ : D.what₂.Tau) : ‖embT D τ γ.det‖ = 1 := by
  rw [← det_map_emb]
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (map_emb_unitary h τ))

theorem isRat_one (D : D7) (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem exists_exp (P : Pair D cc δ t0 Q) :
    ∃ a' : D.what₂.Tau → ℤ, ∀ τ, 2 * a' τ = P.W.ep * P.W.chV.n τ + (P.a : ℤ) := by
  have h : ∀ τ, ∃ b : ℤ, 2 * b = P.W.ep * P.W.chV.n τ + (P.a : ℤ) := fun τ => by
    obtain ⟨c, hc⟩ := P.W.chV.par τ
    rcases P.W.ep_pm.1 with h | h <;> rw [h]
    · exact ⟨c + P.a, by linarith⟩
    · exact ⟨-c, by linarith⟩
  choose a' ha' using h
  exact ⟨a', ha'⟩

theorem differentiable_subst {a d : ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (f : VC D a d → VC D a d) (hf : ∀ τ i j, Differentiable ℂ fun z => f z τ i j) :
    Differentiable ℂ fun z => G (f z) :=
  hG.comp (differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => hf τ i j)

theorem jet_rat_left (hI : Inp D) (P : Pair D cc δ t0 Q) {γA : GA D P.a} (hγ : γA ∈ ratG D P.a)
    {G : VC D P.a P.d → ℂ} (hG : G ∈ TT D (tor0 D cc δ) P.a P.d) (T : Tup D P.a P.d P.n) :
    GL3Theta.applyAt0 D (minorPol D T) (P.W.Om γA 1 G) = GL3Theta.applyAt0 D (minorPol D T) G := by
  obtain ⟨hr, -, -, hu, -⟩ := GlobalTheory.T.rationalPoints_integralPoints_membership D P.a
  obtain ⟨γ, hγ'⟩ := (hr γA).1 hγ
  obtain ⟨a', ha'⟩ := exists_exp P
  have h := P.eqv hI P.W γA 1 γ 1 (fun τ => (P.n τ : ℤ)) a' hγ' (isRat_one D _) ha' P.wt G hG
  set u : D.what₂.Tau → Matrix (Fin P.a) (Fin P.a) ℂ := fun τ => γ.map (embT D τ) with hu'
  set G' : VC D P.a P.d → ℂ := fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ)) with hG'
  have hd : Differentiable ℂ G' := by
    refine differentiable_subst hG.1 _ fun τ i j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have h2 : P.W.Om γA 1 G = (∏ τ, embT D τ γ.det ^ (-(P.n τ : ℤ))) • G' := by
    rw [h]
    funext z
    simp only [Matrix.det_one, map_one, one_zpow, mul_one, Pi.smul_apply, smul_eq_mul, pull, tor0, hG', hu']
    simp only [Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one, Matrix.one_mul]
  rw [h2, (GlobalTheory.T.applyAtOrigin_minorProduct_linear D _ _ P.n G' hd).2.2.1, hG', (GlobalTheory.T.applyAtOrigin_minorProduct_linear D _ _ P.n G hG.1).1 u T, ← mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  intro τ _
  have h0 : embT D τ γ.det ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_emb_det (hu γA γ hγ')]
    exact one_ne_zero
  rw [hu', det_map_emb, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ h0)]

theorem om_rat_right (hI : Inp D) (P : Pair D cc δ t0 Q) {γA : GA D P.d} (hγ : γA ∈ ratG D P.d) :
    ∃ (c : ℂ) (u : D.what₂.Tau → Matrix (Fin P.d) (Fin P.d) ℂ), ‖c‖ = 1 ∧
      (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin P.d) ℂ) ∧ ∀ G ∈ TT D (tor0 D cc δ) P.a P.d,
        P.W.Om 1 γA G = c • fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)) := by
  obtain ⟨hr, -, -, hu, -⟩ := GlobalTheory.T.rationalPoints_integralPoints_membership D P.d
  obtain ⟨γ, hγ'⟩ := (hr γA).1 hγ
  obtain ⟨a', ha'⟩ := exists_exp P
  refine ⟨∏ τ, embT D τ γ.det ^ (-(a' τ)), fun τ => star (γ.map (embT D τ)), ?_,
    fun τ => Unitary.star_mem (map_emb_unitary (hu γA γ hγ') τ), fun G hG => ?_⟩
  · rw [norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, norm_emb_det (hu γA γ hγ'), one_zpow]
  · rw [P.eqv hI P.W 1 γA 1 γ (fun τ => (P.n τ : ℤ)) a' (isRat_one D _) hγ' ha' P.wt G hG]
    funext z
    simp only [Matrix.det_one, map_one, one_zpow, one_mul, Pi.smul_apply, smul_eq_mul, pull, tor0]
    simp only [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.star_eq_conjTranspose]

theorem applyAt0_sum {a d : ℕ} {ι : Type} (s : Finset ι) (c : ι → ℂ) (G : ι → VC D a d → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i)) (p : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D p (∑ i ∈ s, c i • G i) = ∑ i ∈ s, c i * GL3Theta.applyAt0 D p (G i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) 0 (differentiable_const 0)).2.2.1 0 p
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ ((hG i).const_smul (c i))).2.2.2 _ p
        (Differentiable.sum fun j _ => (hG j).const_smul (c j)), ih,
      (GlobalTheory.T.applyAtOrigin_minorProduct_linear D a d (fun _ => 0) _ (hG i)).2.2.1]

theorem term_inv (hI : Inp D) (P : Pair D cc δ t0 Q) (hF : P.F ∈ TT D (tor0 D cc δ) P.a P.d) {γ k : GA D P.a}
    (hγ : γ ∈ ratG D P.a) (hk : k ∈ intG D P.a) (x : GA D P.a) (h : GA D P.d) (T : Tup D P.a P.d P.n) :
    P.term (γ * x * k) h T = P.term x h T := by
  have h1 : P.W.Om (γ * x * k) h P.F = P.W.Om γ 1 (P.W.Om x h P.F) := by
    rw [← P.W.mul _ _ _ _ _ hF, one_mul]
    conv_rhs => rw [← P.fix k hk, ← P.W.mul _ _ _ _ _ hF, mul_one]
  unfold Pair.term
  rw [h1, jet_rat_left hI P hγ (P.W.maps _ _ _ hF)]

theorem sq_inv (hI : Inp D) (P : Pair D cc δ t0 Q) (hF : P.F ∈ TT D (tor0 D cc δ) P.a P.d) {γ j : GA D P.d}
    (hγ : γ ∈ ratG D P.d) (hj : j ∈ P.J) (h : GA D P.d) : P.sq (γ * h * j) = P.sq h := by
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  obtain ⟨c, u, hc, hu, hO⟩ := om_rat_right hI P hγ
  obtain ⟨c', hc', hE⟩ := P.eig j hj
  set f : VC D P.a P.d → VC D P.a P.d := fun z τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ) with hf
  have hm : ∀ x, P.W.Om x h P.F ∈ TT D (tor0 D cc δ) P.a P.d := fun x => P.W.maps _ _ _ hF
  have hd : ∀ x : GA D P.a, Differentiable ℂ fun z => P.W.Om x h P.F (f z) := fun x => by
    refine differentiable_subst (hm x).1 _ fun τ i j => ?_
    simp only [hf, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have h1 : ∀ x, P.W.Om x (γ * h * j) P.F = (c' * c) • fun z => P.W.Om x h P.F (f z) := fun x => by
    have e1 := P.W.mul x 1 (γ * h) j _ hF
    have e2 := P.W.mul 1 x γ h _ hF
    rw [mul_one] at e1
    rw [one_mul] at e2
    rw [e1, hE, P.W.smul _ _ _ _ hF, e2, hO _ (hm x), smul_smul]
  obtain ⟨s, w, hs⟩ : ∃ (s : Cls D P.a (intG D P.a) → GA D P.a) (w : Cls D P.a (intG D P.a) → ℂ),
      ∀ g T, P.coord g T = ∑ x, w x * P.term (s x) g T :=
    ⟨fun x => x.out, fun x => ((gam D (intG D P.a) x.out : ℂ))⁻¹, fun g T => finsum_eq_sum_of_fintype _⟩
  set G : VC D P.a P.d → ℂ := ∑ x, w x • P.W.Om (s x) h P.F with hG
  have hGd : Differentiable ℂ G := Differentiable.sum fun x _ => (hm _).1.const_smul _
  have h2 : ∀ T, P.coord h T = GL3Theta.applyAt0 D (minorPol D T) G := fun T => by
    rw [hG, applyAt0_sum _ w (fun x => P.W.Om (s x) h P.F) (fun x => (hm _).1), hs]
    rfl
  have h3 : ∀ T, P.coord (γ * h * j) T = (c' * c) * GL3Theta.applyAt0 D (minorPol D T)
      (fun z => G (f z)) := fun T => by
    have e : (fun z => G (f z)) = ∑ x, w x • fun z => P.W.Om (s x) h P.F (f z) := by
      funext z
      simp only [hG, Finset.sum_apply, Pi.smul_apply]
    rw [e, applyAt0_sum _ w (fun x z => P.W.Om (s x) h P.F (f z)) (fun x => hd _), hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pair.term, h1, (GlobalTheory.T.applyAtOrigin_minorProduct_linear D _ _ P.n _ (hd _)).2.2.1]
    ring
  unfold Pair.sq
  simp only [h2, h3, norm_mul, hc, hc', one_mul]
  exact (GlobalTheory.T.applyAtOrigin_minorProduct_linear D _ _ P.n G hGd).2.1 u hu

theorem rep_indep : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → (∀ γ ∈ ratG D P.a, ∀ k ∈ intG D P.a, ∀ x h T, P.term (γ * x * k) h T = P.term x h T) ∧ (∀ γ ∈ ratG D P.d, ∀ j ∈ P.J, ∀ h, P.sq (γ * h * j) = P.sq h) ∧ (∀ (s : Cls D P.a (intG D P.a) → GA D P.a), (∀ q, DoubleCoset.mk (ratG D P.a) (intG D P.a) (s q) = q) → ∀ h T, P.coord h T = ∑ᶠ q, ((gam D (intG D P.a) (s q) : ℂ))⁻¹ * P.term (s q) h T) ∧ (∀ (s : Cls D P.d P.J → GA D P.d), (∀ q, DoubleCoset.mk (ratG D P.d) P.J (s q) = q) → P.norm = ∑ᶠ q, ((gam D P.J (s q) : ℝ))⁻¹ * P.sq (s q)) ∧ ((∃ h T, P.coord h T ≠ 0) → 0 < P.norm) := by
  intro D hI cc δ t0 Q hc _ P hQ
  have hF := test_mem hI.g1 hc P hQ
  refine ⟨fun γ hγ k hk x h T => term_inv hI P hF hγ hk x h T, fun γ hγ j hj h => sq_inv hI P hF hγ hj h,
    fun s hs h T => ?_, fun s hs => ?_, ?_⟩
  · refine finsum_congr fun q => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 ((hs q).trans (DoubleCoset.out_eq' _ _ q).symm)
    rw [e, term_inv hI P hF hγ hk, (GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D _ _ le_rfl (s q)).2.2 γ hγ k hk]
  · refine finsum_congr fun q => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 ((hs q).trans (DoubleCoset.out_eq' _ _ q).symm)
    rw [e, sq_inv hI P hF hγ hk, (GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D _ _ P.J_le (s q)).2.2 γ hγ k hk]
  · rintro ⟨h, T, hT⟩
    haveI := ((GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.d).2.2 P.J P.J_le P.idx_ne).1
    haveI := Fintype.ofFinite (Cls D P.d P.J)
    have h0 : 0 < P.sq h :=
      Finset.sum_pos' (fun _ _ => by positivity) ⟨T, Finset.mem_univ _, by positivity⟩
    have h1 : ∀ g, 0 ≤ P.sq g := fun g => Finset.sum_nonneg fun _ _ => by positivity
    rw [Pair.norm, finsum_eq_sum_of_fintype]
    refine Finset.sum_pos' (fun q _ => mul_nonneg (by positivity) (h1 _))
      ⟨DoubleCoset.mk _ _ h, Finset.mem_univ _, ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' _ _ (DoubleCoset.mk (ratG D P.d) P.J h)).symm
    rw [e, sq_inv hI P hF hγ hk]
    have h2 := (GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D _ _ P.J_le (γ * h * k)).1
    positivity

end GlobalTheory.NormSum.RepInv
