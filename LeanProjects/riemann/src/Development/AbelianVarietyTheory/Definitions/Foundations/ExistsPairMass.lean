import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Model

theorem wd_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pres_vac (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) :
    Pres D cc δ 1 e0 e0 := by
  have h0 : pt D (tor0 D cc δ) δ (0 : Matrix (Fin d) (Fin a) D.host.E) = 0 := by
    funext τ i j
    simp [pt, embV, tor0]
  refine ⟨1, fun _ => 1, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i; rw [h0]; simp
  · intro i; simpa using isIntegral_one
  · intro ρ; simp
  · funext y; simp [h0, wd_zero]

def spherical {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    (e0 : VC D a d → ℂ) (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ))
    (hfix : ∀ k ∈ intG D a, W.Om k 1 e0 = e0)
    (heig : ∀ j ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j e0 = c • e0) : Pair D cc δ t0 1 where
  crv := crv
  pt0 := pt0
  a := a
  d := d
  a_le := had
  d_even := hd
  e0 := e0
  vac := vac
  W := W
  n := n
  wt := wt
  F := e0
  pres := pres_vac D cc δ e0
  fix := hfix
  J := intG D d
  J_le := le_rfl
  idx_ne := by simp
  idx_le := by simp
  eig := heig

theorem spherical_F_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    (e0 : VC D a d → ℂ) (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt) (hfix) (heig) :
    (spherical crv pt0 had hd e0 vac W n wt hfix heig).F ≠ 0 := W.nz

theorem mem_intG {D : D7} {N : ℕ} (k : GA D N) : k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D)) := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro i j
    have : ((1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    simpa using this
  | mul x y _ _ hx hy =>
    intro i j
    constructor
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hx i l).1 (hy l j).1
    · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hy i l).2 (hx l j).2
  | inv x _ hx =>
    intro i j
    refine ⟨?_, ?_⟩
    · exact (hx i j).2
    · rw [Subgroup.coe_inv, inv_inv]; exact (hx i j).1

theorem term_mul_int {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q)
    (hF : P.F ∈ TT D (tor0 D cc δ) P.a P.d) (x k : GA D P.a) (hk : k ∈ intG D P.a) (h : GA D P.d)
    (T : Tup D P.a P.d P.n) : P.term (x * k) h T = P.term x h T := by
  unfold Pair.term
  have := P.W.mul x k h 1 P.F hF
  rw [mul_one, P.fix k hk] at this
  rw [this]

theorem level_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) : Q ≠ 0 := by
  rintro rfl
  have h := P.idx_le
  rw [zero_pow (by omega)] at h
  exact P.idx_ne (Nat.le_zero.mp h)

instance vcUnique (D : D7) : Unique (VC D 0 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

instance gaSub (D : D7) : Subsingleton (GA D 0) :=
  ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩

theorem hf0 (D : D7) (T : Tor D) (z w : VC D 0 0) : Hf D T z w = 0 := by simp [Hf]

theorem iop0 (D : D7) (T : Tor D) (A B : AddSubgroup (VC D 0 0)) (G : VC D 0 0 → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  haveI : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  haveI : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hf0]
  simp
  congr 1
  exact Subsingleton.elim _ _

def triv (D : D7) : HeckeU D 0 where
  f := 1
  n := 0
  unitary := by simp
  cont := ⟨1, one_pos, by simp⟩
  aut := by simp
  norm := by simp
  par := by simp
  unr := by simp

def weil0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : WeilO D cc δ 0 0 (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := triv D
  chV' := triv D
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intros
    rw [iop0]; simp [triv]

theorem taylor0 (D : D7) (α : Mono D 0 0) (c : ℂ) : taylor D (fun _ => c) α = c := by
  have : α = 0 := by ext k; exact k.2.1.elim0
  subst this
  have h : ∀ (k : ℕ) (v : Fin k → VC D 0 0), k = 0 → iteratedFDeriv ℂ k (fun _ : VC D 0 0 => c) 0 v = c := by
    intro k v hk; subst hk; simp
  unfold taylor
  rw [h _ _ (by simp)]
  simp

theorem normSq0 (D : D7) (T : Tor D) (A : AddSubgroup (VC D 0 0)) : normSq D T A (fun _ => 1) = 1 := by
  have hex : ∃ Fd : Set (VC D 0 0), MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume := by
    refine ⟨Set.univ, MeasureTheory.IsAddFundamentalDomain.mk' (by simp) fun x => ⟨0, by simp, fun y _ => Subsingleton.elim _ _⟩⟩
  have hs := Classical.epsilon_spec hex
  unfold normSq
  simp only [hf0]
  set Fd := Classical.epsilon (fun Fd : Set (VC D 0 0) => MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (VC D 0 0)) Set.univ = 1 := by
    simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  have hF : Fd = Set.univ := by
    have hc := hs.ae_covers
    by_contra hne
    have he : Fd = ∅ := by
      rcases Set.eq_empty_or_nonempty Fd with h | ⟨x, hx⟩
      · exact h
      · exact absurd (Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y x]; exact hx) hne
    rw [he] at hc
    simp only [Set.mem_empty_iff_false, exists_false, Filter.eventually_false_iff_eq_bot,
      MeasureTheory.ae_eq_bot] at hc
    rw [hc] at hv; simp at hv
  rw [hF]
  simp [MeasureTheory.average_eq, MeasureTheory.Measure.real, hv]

theorem vac0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) : oddE0 D cc δ t0 0 0 (fun _ => 1) := by
  haveI : IsEmpty (Fin (fF D * 0 * 0)) := by simp only [mul_zero]; infer_instance
  have hon : OnB D (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  refine ⟨⟨differentiable_const _, fun x _ z => ?_⟩, fun α => ?_, ?_, ⟨fun _ => 0, 1, hon, ⟨one_mem _, fun σ => ?_⟩, ?_⟩, ?_⟩
  · simp [al, U, hf0]
  · rw [taylor0]; exact one_mem _
  · rw [La0, normSq0]; simp
  · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
    rw [this]; simp
  · rw [iop0]; funext z; simp [pullB]
  · intro p _ lam _
    refine ⟨fun _ => 0, 1, hon, ⟨linearIndependent_empty_type, fun i => isEmptyElim i,
      fun y _ => ⟨1, by simp, fun i => isEmptyElim i, Subsingleton.elim _ _⟩⟩, one_mem _, ?_, ?_, ?_⟩
    · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
      simp [lamC, this]
    · have hi : ((LaB D (tor0 D cc δ) (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E))).addSubgroupOf
          (La0 D (tor0 D cc δ) 0 0)).index = 1 := by
        rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
      rw [hi]; simp
    · rw [iop0]; funext z; simp [pullB]

theorem eqv0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e0 : VC D 0 0 → ℂ) : oddEq D cc δ 0 0 e0 := by
  intro W γA γA' γ γ' a a' _ _ _ _ F hF
  rw [Subsingleton.elim γA 1, Subsingleton.elim γA' 1, W.one F hF]
  funext z
  simp [pull]
  congr 1
  exact Subsingleton.elim _ _

def pair0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) : Pair D cc δ t0 1 :=
  spherical crv pt0 le_rfl (by simp) (fun _ => 1) (vac0 D cc δ t0) (weil0 D cc δ) 0
    (by simp [weil0, triv]) (fun _ _ => rfl) (fun _ _ => ⟨1, by simp, by simp [weil0]⟩)

theorem gam0 (D : D7) (J : Subgroup (GA D 0)) (g : GA D 0) : gam D J g = 1 := by
  unfold gam
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨⟨1, one_mem _, by rw [Subsingleton.elim (_ * _ * _) 1]; exact one_mem _⟩⟩⟩

instance cls0 (D : D7) (J : Subgroup (GA D 0)) : Unique (Cls D 0 J) :=
  ⟨⟨Quotient.mk'' 1⟩, fun x => by
    induction x using Quotient.inductionOn'
    congr 1
    exact Subsingleton.elim _ _⟩

theorem normSumPairRankZeroOfCurve_coord_norm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) : (pair0 D cc δ t0 crv pt0).norm = 1 := by
  have ht : ∀ x h T, (pair0 D cc δ t0 crv pt0).term x h T = 1 := by
    intro x h T
    have hm : minorPol D T = 1 := by
      unfold minorPol
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => j.elim0
    show GL3Theta.applyAt0 D (minorPol D T) (fun _ => 1) = 1
    rw [hm]
    have := taylor0 D 0 1
    simp [GL3Theta.applyAt0, MvPolynomial.support_one]
    exact this
  have hc : ∀ h T, (pair0 D cc δ t0 crv pt0).coord h T = 1 := by
    intro h T
    unfold Pair.coord
    simp only [ht]
    show ∑ᶠ x : Cls D 0 (intG D 0), ((gam D (intG D 0) x.out : ℂ))⁻¹ * 1 = 1
    rw [finsum_unique, gam0]; simp
  have hq : ∀ h, (pair0 D cc δ t0 crv pt0).sq h = 1 := by
    intro h
    unfold Pair.sq
    simp only [hc]
    haveI : Unique (Tup D (pair0 D cc δ t0 crv pt0).a (pair0 D cc δ t0 crv pt0).d (pair0 D cc δ t0 crv pt0).n) :=
      ⟨⟨fun τ j => j.elim0⟩, fun T => funext fun τ => funext fun j => j.elim0⟩
    simp
  unfold Pair.norm
  simp only [hq]
  show ∑ᶠ h : Cls D 0 (intG D 0), ((gam D (intG D 0) h.out : ℝ))⁻¹ * 1 = 1
  rw [finsum_unique, gam0]; simp

theorem exists_twoTorsionPointUnkilled_of_crv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 := by
  have hδ : δ ≠ 0 := by
    obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D h.1.1
    rintro rfl
    have h2 : (0 : ℂ) ^ 12 = discr (lamOf D cc 1) := h.2
    exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← h2]; simp)
  have hN : Odd (Ideal.absNorm cc) := Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right h.1.2)
  set N := Ideal.absNorm cc with hNd
  have hmem : δ * (N : ℂ) ∈ lamOf D cc δ :=
    AddSubgroup.subset_closure ⟨((N : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, by simp⟩
  have hint : ∀ w ∈ lamOf D cc δ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x := by
    intro w hw
    unfold lamOf at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, -, rfl⟩ := hw
      have h0 : IsIntegral ℤ (c : D.host.K) := c.2
      exact ⟨_, h0.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom, rfl⟩
    | zero => exact ⟨0, isIntegral_zero, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      exact ⟨x + y, hx.add hy, by ring⟩
    | neg a _ ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨-x, hx.neg, by ring⟩
  have half : ∀ x : ℂ, IsIntegral ℤ x → x + (starRingEnd ℂ) x = (N : ℂ) / 2 → False := by
    intro x hx h
    have h1 : IsIntegral ℤ ((starRingEnd ℂ) x) := hx.map (starRingEnd ℂ).toIntAlgHom
    have h2 : IsIntegral ℤ (algebraMap ℚ ℂ ((N : ℚ) / 2)) := by
      have : algebraMap ℚ ℂ ((N : ℚ) / 2) = (N : ℂ) / 2 := by simp
      rw [this, ← h]; exact hx.add h1
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h2)
    have h4 : (N : ℚ) = 2 * (m : ℚ) := by
      have : (m : ℚ) = (N : ℚ) / 2 := by simpa using hm
      rw [this]; ring
    have h5 : (N : ℤ) = 2 * m := by exact_mod_cast h4
    obtain ⟨k, hk⟩ := hN
    omega
  refine ⟨δ * N / 2, ?_, ?_, ?_⟩
  · have : 2 * (δ * N / 2) = δ * N := by ring
    rw [this]; exact hmem
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine half x hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
    ring
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine half x hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
    ring

theorem vac_mem_TT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) : e0 ∈ TT D (tor0 D cc δ) a d := by
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d (La0 D (tor0 D cc δ) a d)
    (Or.inr ⟨_, _, RepInv.sd_std D _, RepInv.sd_std D _, rfl⟩)
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, hW x hx]
  funext w
  exact he.2 x hx w

theorem exists_pair_of_unramified {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (crv : Crv D cc δ)
    (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    (e0 : VC D a d → ℂ) (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ))
    (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 := by
  have hT := vac_mem_TT crv vac.1
  refine ⟨spherical crv pt0 had hd e0 vac W n wt (fun k hk => ?_) (fun j hj => ?_), rfl, rfl, rfl, rfl, W.nz⟩
  · obtain ⟨x, hx, e⟩ := VacInt.om_vac_left vac.1 hT W ((mem_intG k).1 hk)
    rw [e, hu x hx]; simp
  · obtain ⟨x, -, e⟩ := VacInt.om_vac_right vac.1 hT W ((mem_intG j).1 hj)
    refine ⟨_, ?_, e⟩
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, W.chV.unitary, one_zpow]

def raise {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (Q' : ℕ) (hQ' : 0 < Q')
    (J : Subgroup (GA D P.d)) (hJ : J ≤ P.J) (h1 : J.relIndex (intG D P.d) ≠ 0)
    (h2 : J.relIndex (intG D P.d) ≤ (Q * Q') ^ (P.d ^ 2 + 4)) : Pair D cc δ t0 (Q * Q') :=
  { P with
    pres := by
      obtain ⟨k, r, z, hz, hi, hn, hF⟩ := P.pres
      refine ⟨k, r, z, fun i => ?_, fun i => ?_, fun ρ => (hn ρ).trans ?_, hF⟩
      · rw [mul_comm, mul_smul]; exact AddSubgroup.nsmul_mem _ (hz i) _
      · have : (((Q * Q' : ℕ) : Qbar)) ^ (P.a * P.d) * r i =
            (Q' : Qbar) ^ (P.a * P.d) * ((Q : Qbar) ^ (P.a * P.d) * r i) := by push_cast; ring
        rw [this]
        exact ((isIntegral_natCast Q').pow _).mul (hi i)
      · have : (Q : ℝ) ≤ ((Q * Q' : ℕ) : ℝ) := by exact_mod_cast Nat.le_mul_of_pos_right Q hQ'
        gcongr
    J := J
    J_le := hJ.trans P.J_le
    idx_ne := h1
    idx_le := h2
    eig := fun j hj => P.eig j (hJ hj) }

theorem eq_zero_of_zeroAt (D : D7) {z : AE D} (h : ∀ q : ℕ, q.Prime → ZeroAt D q z) : z = 0 := by
  obtain ⟨n, hn, hw⟩ := VacMove.exists_nat_denom D z
  have hw0 : (n : AE D) * z = 0 := by
    refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _ fun N hN => ?_
    let I : Ideal ℤ :=
      { carrier := {m | ∃ s ∈ OhE D, (m : AE D) * ((n : AE D) * z) = (N : AE D) * s}
        add_mem' := by
          rintro a b ⟨s, hs, e⟩ ⟨t, ht, e'⟩
          exact ⟨s + t, add_mem hs ht, by push_cast; rw [add_mul, e, e', mul_add]⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c a ⟨s, hs, e⟩
          exact ⟨c * s, mul_mem (intCast_mem _ c) hs, by
            rw [smul_eq_mul]; push_cast; rw [mul_assoc, e]; ring⟩ }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨Mx, hM, hle⟩ := Ideal.exists_le_maximal I hne
      have hNI : (N : ℤ) ∈ I := ⟨_, hw, by simp⟩
      obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal Mx).principal
      have hg0 : g ≠ 0 := by
        rintro rfl
        have := hle hNI
        rw [hg] at this
        simp at this
        omega
      have hp : Prime g := by
        have := hM.isPrime
        rw [hg] at this
        exact (Ideal.span_singleton_prime hg0).1 this
      have hq : g.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hp
      obtain ⟨k, N', hN', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' g.natAbs hq.ne_one
      obtain ⟨m, -, hm, s, hs, e⟩ := h _ hq k
      have hmI : ((m * N' : ℕ) : ℤ) ∈ I := ⟨n * s, mul_mem (natCast_mem _ n) hs, by
        push_cast; linear_combination (N' : AE D) * (n : AE D) * e⟩
      have := hle hmI
      rw [hg] at this
      have hd : g.natAbs ∣ m * N' := by
        have := Ideal.mem_span_singleton.1 this
        exact Int.natAbs_dvd_natAbs.2 this
      rcases (Nat.Prime.dvd_mul hq).1 hd with h1 | h1
      · exact (Nat.Prime.coprime_iff_not_dvd hq).1 hm.symm h1
      · exact hN' h1
    have h1 : (1 : ℤ) ∈ I := hI ▸ Submodule.mem_top
    obtain ⟨s, hs, e⟩ := h1
    exact ⟨s, hs, by simpa using e⟩
  have hu : IsUnit (n : AE D) := by
    have : (n : AE D) = inc D n := by simp
    rw [this]
    exact (IsUnit.mk0 _ (by exact_mod_cast hn.ne')).map _
  exact (hu.mul_right_eq_zero).1 hw0

theorem hecke_eq_one {D : D7} {N : ℕ} (χ : HeckeU D N) (x : (AE D)ˣ) (hx : x = sgU D x)
    (hi : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) : χ.f x = 1 := by
  obtain ⟨ε, -, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have hx' : sgA D x = x := (congrArg Units.val hx).symm
  have hz : (1 - (ε + sgA D ε)) * ((x : AE D) - 1) = 0 := by
    refine eq_zero_of_zeroAt D fun q hq => ?_
    by_cases h : InertQ D q
    · rw [mul_comm]; exact VacMove.zeroAt_mul D hq (hi q hq h) _
    · exact VacMove.zeroAt_mul D hq ((h3 q hq).2 h) _
  have hu : (x : AE D) * (x⁻¹ : (AE D)ˣ) = 1 := x.mul_inv
  have hy : ((1 - ε) + ε * x) * ((1 - ε) + ε * (x⁻¹ : (AE D)ˣ)) = 1 := by
    linear_combination (1 - x - (x⁻¹ : (AE D)ˣ) + x * (x⁻¹ : (AE D)ˣ)) * h1 + ε * hu
  let y : (AE D)ˣ := ⟨_, _, hy, by rw [mul_comm, hy]⟩
  have e : x = y * sgU D y := by
    ext
    change (x : AE D) = ((1 - ε) + ε * x) * sgA D ((1 - ε) + ε * x)
    rw [map_add, map_mul, map_sub, map_one, hx']
    linear_combination hz - (1 - x) ^ 2 * h2
  rw [e, χ.norm]

instance vcUniqueD (D : D7) (d : ℕ) : Unique (VC D 0 d) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

theorem hfD (D : D7) (T : Tor D) {d : ℕ} (z w : VC D 0 d) : Hf D T z w = 0 := by simp [Hf]

theorem iopD (D : D7) (T : Tor D) {d : ℕ} (A B : AddSubgroup (VC D 0 d)) (G : VC D 0 d → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  haveI : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  haveI : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hfD]
  simp
  congr 1
  exact Subsingleton.elim _ _

def weilD (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {d : ℕ} (χ : HeckeU D d) :
    WeilO D cc δ 0 d (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := triv D
  chV' := χ
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intro g g' x x' L₁ L₁' _ _ hi hx _ _ _
    have hd : Matrix.GeneralLinearGroup.det (g : GL (Fin 0) (AE D)) = 1 := by
      ext; simp [Matrix.det_isEmpty]
    rw [hd, one_mul] at hx
    rw [iopD, hecke_eq_one χ x hx fun q hq h => (hi q hq h).1]; simp [triv]

theorem taylorD (D : D7) {d : ℕ} (α : Mono D 0 d) (c : ℂ) : taylor D (fun _ => c) α = c := by
  have : α = 0 := by ext k; exact k.2.2.elim0
  subst this
  have h : ∀ (k : ℕ) (v : Fin k → VC D 0 d), k = 0 → iteratedFDeriv ℂ k (fun _ : VC D 0 d => c) 0 v = c := by
    intro k v hk; subst hk; simp
  unfold taylor
  rw [h _ _ (by simp)]
  simp

theorem normSqD (D : D7) (T : Tor D) {d : ℕ} (A : AddSubgroup (VC D 0 d)) : normSq D T A (fun _ => 1) = 1 := by
  have hex : ∃ Fd : Set (VC D 0 d), MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume := by
    refine ⟨Set.univ, MeasureTheory.IsAddFundamentalDomain.mk' (by simp) fun x => ⟨0, by simp, fun y _ => Subsingleton.elim _ _⟩⟩
  have hs := Classical.epsilon_spec hex
  unfold normSq
  simp only [hfD]
  set Fd := Classical.epsilon (fun Fd : Set (VC D 0 d) => MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (VC D 0 d)) Set.univ = 1 := by
    simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  have hF : Fd = Set.univ := by
    have hc := hs.ae_covers
    by_contra hne
    have he : Fd = ∅ := by
      rcases Set.eq_empty_or_nonempty Fd with h | ⟨x, hx⟩
      · exact h
      · exact absurd (Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y x]; exact hx) hne
    rw [he] at hc
    simp only [Set.mem_empty_iff_false, exists_false, Filter.eventually_false_iff_eq_bot,
      MeasureTheory.ae_eq_bot] at hc
    rw [hc] at hv; simp at hv
  rw [hF]
  simp [MeasureTheory.average_eq, MeasureTheory.Measure.real, hv]

theorem vacD (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (d : ℕ) : oddE0 D cc δ t0 0 d (fun _ => 1) := by
  haveI : IsEmpty (Fin (fF D * 0 * d)) := by simp only [mul_zero, zero_mul]; infer_instance
  have hon : OnB D (fun _ : Fin (fF D * 0 * d) => (0 : Matrix (Fin d) (Fin 0) D.host.E)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  refine ⟨⟨differentiable_const _, fun x _ z => ?_⟩, fun α => ?_, ?_, ⟨fun _ => 0, 1, hon, ⟨one_mem _, fun σ => ?_⟩, ?_⟩, ?_⟩
  · simp [al, U, hfD]
  · rw [taylorD]; exact one_mem _
  · rw [La0, normSqD]; simp
  · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
    rw [this]; simp
  · rw [iopD]; funext z; simp [pullB]
  · intro p _ lam _
    refine ⟨fun _ => 0, 1, hon, ⟨linearIndependent_empty_type, fun i => isEmptyElim i,
      fun y _ => ⟨1, by simp, fun i => isEmptyElim i, Subsingleton.elim _ _⟩⟩, one_mem _, ?_, ?_, ?_⟩
    · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
      simp [lamC, this]
    · have hi : ((LaB D (tor0 D cc δ) (fun _ : Fin (fF D * 0 * d) => (0 : Matrix (Fin d) (Fin 0) D.host.E))).addSubgroupOf
          (La0 D (tor0 D cc δ) 0 d)).index = 1 := by
        rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
      rw [hi]; simp
    · rw [iopD]; funext z; simp [pullB]

theorem exists_pair_mass (D : D7) (d m : ℕ) (hd : Even d) :
    ∃ (δ t0 : ℂ) (P : Pair D ⊤ δ t0 1), P.a = 0 ∧ P.d = d ∧ (∀ τ, P.n τ = m) ∧ (∀ h T, P.coord h T = 1) ∧
      P.norm = ∑ᶠ h : Cls D d (intG D d), ((gam D (intG D d) h.out : ℝ))⁻¹ ∧ 0 < P.norm := by
  obtain ⟨δ, hδ⟩ := exists_crv_top D
  obtain ⟨t0, ht⟩ := exists_twoTorsionPointUnkilled_of_crv hδ
  obtain ⟨c, hc⟩ := hd
  obtain ⟨χ, hχ, -⟩ := exists_unramified_heckeU D d (c + m) ⟨c, hc⟩
  let P : Pair D ⊤ δ t0 1 := spherical hδ ht (Nat.zero_le d) ⟨c, hc⟩ (fun _ => 1) (vacD D ⊤ δ t0 d) (weilD D ⊤ δ χ)
    (fun _ => m) (fun τ => by
      show 2 * (m : ℤ) = 1 * χ.n τ - d
      rw [hχ, hc]; push_cast; ring) (fun _ _ => rfl) (fun _ _ => ⟨1, by simp, by simp [weilD]⟩)
  have htm : ∀ x h T, P.term x h T = 1 := by
    intro x h T
    have hm : minorPol D T = 1 := by
      unfold minorPol
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
      exact Matrix.det_isEmpty (n := Fin 0)
    show GL3Theta.applyAt0 D (minorPol D T) (fun _ => 1) = 1
    rw [hm]
    have := taylorD D (d := d) 0 1
    simp [GL3Theta.applyAt0, MvPolynomial.support_one]
    exact this
  have hco : ∀ h T, P.coord h T = 1 := by
    intro h T
    unfold Pair.coord
    simp only [htm]
    show ∑ᶠ x : Cls D 0 (intG D 0), ((gam D (intG D 0) x.out : ℂ))⁻¹ * 1 = 1
    rw [finsum_unique, gam0]; simp
  have hq : ∀ h, P.sq h = 1 := by
    intro h
    unfold Pair.sq
    simp only [hco]
    haveI : Unique (Tup D P.a P.d P.n) :=
      ⟨⟨fun τ j => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩,
        fun T => funext fun τ => funext fun j => Subtype.ext (funext fun i => i.elim0)⟩
    simp
  have hn : P.norm = ∑ᶠ h : Cls D d (intG D d), ((gam D (intG D d) h.out : ℝ))⁻¹ := by
    unfold Pair.norm
    simp only [hq, mul_one]
    rfl
  refine ⟨δ, t0, P, rfl, rfl, fun _ => rfl, hco, hn, ?_⟩
  rw [hn]
  haveI := (cls_finite_card_le D d).1
  haveI := Fintype.ofFinite (Cls D d (intG D d))
  haveI : Nonempty (Cls D d (intG D d)) := ⟨Quotient.mk'' 1⟩
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_pos (fun h _ => ?_) Finset.univ_nonempty
  have := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D d (intG D d) le_rfl h.out).1
  positivity

example (D : D7) (T : Tup D 2 2 (fun _ => 1)) :
    minorPol D T = ∏ τ, (MvPolynomial.X (τ, (T τ 0).1 0, 0) * MvPolynomial.X (τ, (T τ 0).1 1, 1) -
      MvPolynomial.X (τ, (T τ 0).1 0, 1) * MvPolynomial.X (τ, (T τ 0).1 1, 0)) := by
  simp [minorPol, Matrix.det_fin_two]

end GlobalTheory.NormSum.Model
