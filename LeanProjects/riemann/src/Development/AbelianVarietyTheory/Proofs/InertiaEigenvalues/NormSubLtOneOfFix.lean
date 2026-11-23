import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct Topology

namespace GlobalTheory.UnramifiedCrys

section Abstract

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {R : Type} [CommRing R] [IsDomain R] [CharP R p]
  (ρ : G →* (R ≃+* R))

def fixedPow (p : ℕ) (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {y | y ^ p ^ m = y}
  one_mem' := one_pow _
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]

def fixer (p : ℕ) (m : ℕ) : Subgroup G where
  carrier := {g | ∀ y : R, y ^ p ^ m = y → ρ g y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, RingAut.mul_apply, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]

omit [IsDomain R] [CharP R p] hp in
theorem pow_pow_mul {y : R} {a : ℕ} (h : y ^ p ^ a = y) (b : ℕ) : y ^ p ^ (a * b) = y := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

omit [CharP R p] in
theorem finite_fixedPow {m : ℕ} (hm : 0 < m) : {y : R | y ^ p ^ m = y}.Finite := by
  classical
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hne : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R) ≠ 0 :=
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)).ne_zero
  refine (Polynomial.roots (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R)).toFinset.finite_toSet.subset ?_
  intro y hy
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  exact sub_eq_zero.2 hy

omit [CharP R p] [CompactSpace G] in
theorem isOpen_fixer (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {m : ℕ} (hm : 0 < m) : IsOpen (fixer ρ p m : Set G) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact ((finite_fixedPow (p := p) (R := R) hm).eventually_all.2
    (fun y hy => hopen y m hm hy)).mono fun g hg y hy => hg y hy

theorem exists_coboundary
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (e : G → R) (he : ∀ g h, e (g * h) = e g + ρ g (e h))
    (h0 : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, e g = 0) :
    ∃ β : R, ∀ g, e g = ρ g β - β := by
  classical
  obtain ⟨U, hU, hJU, hUe⟩ := mem_nhdsSet_iff_exists.1 h0
  obtain ⟨⟨m, hm⟩, hmU⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro g hg hg'
      exact hg (hJU fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))
    (by
      intro a b
      refine ⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg y hy => hg y ?_⟩
      have := pow_pow_mul hy a.1
      rwa [mul_comm] at this)
  set N := fixer ρ p m with hN
  have heN : ∀ g ∈ N, e g = 0 := fun g hg => hUe (by
    by_contra hc
    exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hmU) hc hg)
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N (isOpen_fixer ρ hopen hm)
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  obtain ⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by
    by_contra hc
    push Not at hc
    have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      funext θ
      simp only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]
      exact hc θ) (QuotientGroup.mk 1)
    exact one_ne_zero this
  have hθm : (θ : R) ^ p ^ m = θ := θ.2

  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  set t := ∑ x : G ⧸ N, ρ x.out θ with ht
  have hθN : ∀ g, ∀ n ∈ N, ρ (g * n) θ = ρ g θ := fun g n hn => by
    rw [map_mul, RingAut.mul_apply, hn θ hθm]
  have htg : ∀ g, ρ g t = t := fun g => by
    rw [ht, map_sum, ← hsum (fun g => ρ g θ) hθN g]
    simp only [map_mul, RingAut.mul_apply]
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  refine ⟨-(t ^ (p ^ m - 2) * ∑ x : G ⧸ N, e x.out * ρ x.out θ), fun g => ?_⟩
  have h2 := hsum (fun g => e g * ρ g θ) (fun g n hn => by
    simp only [he, heN n hn, map_zero, add_zero, hθN g n hn]) g
  have h3 : ρ g (∑ x : G ⧸ N, e x.out * ρ x.out θ) =
      ∑ x : G ⧸ N, e x.out * ρ x.out θ - e g * t := by
    conv_rhs => rw [← h2, ← htg g, ht]
    rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [he, map_mul, RingAut.mul_apply]
    ring
  rw [map_neg, map_mul, map_pow, htg, h3]
  linear_combination (-e g) * hu

end Abstract

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {R : Type} [CommRing R] [IsDomain R] [CharP R p]
  [PerfectRing R p] (ρ : G →* (R ≃+* R))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
  [PerfectRing R p] in
theorem wittMap_mul (g h : G) (x : WittVector p R) :
    WittVector.map (ρ (g * h)).toRingHom x =
      WittVector.map (ρ g).toRingHom (WittVector.map (ρ h).toRingHom x) := by
  ext n
  simp [WittVector.map_coeff]

theorem approx_step
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (c : G → ℤ_[p]) (hc : Continuous c) (hadd : ∀ g h, c (g * h) = c g + c h)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → c g = 0) (n : ℕ) (b : WittVector p R)
    (hb : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, WittVector.map (ρ g).toRingHom b = b)
    (hd : ∀ g, (p : WittVector p R) ^ n ∣ WittVector.map (ρ g).toRingHom b - b - zlW p R (c g)) :
    ∃ b' : WittVector p R, (p : WittVector p R) ^ n ∣ b - b' ∧
      (∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m},
        WittVector.map (ρ g).toRingHom b' = b') ∧
      ∀ g, (p : WittVector p R) ^ (n + 1) ∣
        WittVector.map (ρ g).toRingHom b' - b' - zlW p R (c g) := by
  choose d hd using hd
  have hp0 : (p : WittVector p R) ^ n ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p R)
  have hdc : ∀ g h, d (g * h) = d g + WittVector.map (ρ g).toRingHom (d h) := by
    intro g h
    apply mul_left_cancel₀ hp0
    have h1 := congrArg (WittVector.map (ρ g).toRingHom) (hd h)
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, map_zlW, ← wittMap_mul] at h1
    rw [mul_add, ← hd, ← hd, ← h1, hadd, map_add]
    ring
  have hsmall : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m},
      (p : ℤ_[p]) ^ (n + 1) ∣ c g := by
    rw [eventually_nhdsSet_iff_forall]
    intro x hx
    have h1 : ∀ᶠ g in 𝓝 x, ‖c g‖ < (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      apply hc.norm.continuousAt.eventually_lt continuousAt_const
      rw [hJ x hx, norm_zero]
      have := hp.out.pos
      positivity
    refine h1.mono fun g hg => ?_
    exact Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hg.le)
  have he0 : ∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, (d g).coeff 0 = 0 := by
    filter_upwards [hb, hsmall] with g h1 h2
    obtain ⟨z, hz⟩ := h2
    have h3 := hd g
    rw [h1, hz, map_mul, map_pow, map_natCast] at h3
    have h4 : d g = (p : WittVector p R) * -(zlW p R z) := by
      apply mul_left_cancel₀ hp0
      rw [← h3]; ring
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton]
    exact ⟨_, h4⟩
  obtain ⟨β, hβ⟩ := exists_coboundary ρ hopen (fun g => (d g).coeff 0) (fun g h => by
    have := congrArg WittVector.constantCoeff (hdc g h)
    rw [map_add] at this
    simpa [WittVector.map_coeff] using this) he0
  refine ⟨b - (p : WittVector p R) ^ n * WittVector.teichmuller p β, ⟨_, sub_sub_cancel _ _⟩, ?_,
    fun g => ?_⟩
  · filter_upwards [hb, he0] with g h1 h2
    have h3 : (ρ g).toRingHom β = β := by
      have := hβ g
      rw [h2] at this
      exact sub_eq_zero.1 this.symm
    rw [map_sub, map_mul, map_pow, map_natCast, h1, WittVector.map_teichmuller, h3]
  · have h1 : (p : WittVector p R) ∣ d g - (WittVector.teichmuller p ((ρ g).toRingHom β) -
        WittVector.teichmuller p β) := by
      rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      rw [← WittVector.constantCoeff_apply, map_sub, map_sub]
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      exact sub_eq_zero.2 (hβ g)
    obtain ⟨w, hw⟩ := h1
    refine ⟨w, ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, WittVector.map_teichmuller, pow_succ, mul_assoc,
      ← hw, mul_sub, ← hd]
    ring

theorem exists_witt_coboundary
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (c : G → ℤ_[p]) (hc : Continuous c) (hadd : ∀ g h, c (g * h) = c g + c h)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → c g = 0) :
    ∃ b : WittVector p R, ∀ g, WittVector.map (ρ g).toRingHom b - b = zlW p R (c g) := by
  let P : ℕ → WittVector p R → Prop := fun n b =>
    (∀ᶠ g in 𝓝ˢ {g : G | ∀ m, 0 < m → g ∈ fixer ρ p m}, WittVector.map (ρ g).toRingHom b = b) ∧
      ∀ g, (p : WittVector p R) ^ n ∣ WittVector.map (ρ g).toRingHom b - b - zlW p R (c g)
  have hstep : ∀ n (b : {b // P n b}), ∃ b' : {b // P (n + 1) b},
      (p : WittVector p R) ^ n ∣ b.1 - b'.1 := fun n b => by
    obtain ⟨b', h1, h2, h3⟩ := approx_step ρ hopen c hc hadd hJ n b.1 b.2.1 b.2.2
    exact ⟨⟨b', h2, h3⟩, h1⟩
  choose F hF using hstep
  let s : ∀ n, {b // P n b} := fun n => Nat.rec (motive := fun n => {b // P n b})
    ⟨0, Filter.Eventually.of_forall fun g => map_zero _, fun g => by simp⟩ F n
  have hs : ∀ n, (p : WittVector p R) ^ n ∣ (s n).1 - (s (n + 1)).1 := fun n => hF n (s n)
  have hsm : ∀ (n : ℕ) (x y : WittVector p R),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p R)} ^ n • ⊤ : Submodule (WittVector p R) _)] ↔
        (p : WittVector p R) ^ n ∣ x - y := fun n x y => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => (s n).1) (by
    intro m n hmn
    rw [hsm]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_add ih ((pow_dvd_pow _ hmn).trans (hs n))
      rwa [sub_add_sub_cancel] at this)
  refine ⟨L, fun g => sub_eq_zero.1 (hcomp.toIsHausdorff.haus _ fun n => ?_)⟩
  rw [hsm, sub_zero]
  have h1 := (hsm _ _ _).1 (hL n)
  have h2 := map_dvd (WittVector.map (ρ g).toRingHom) h1
  rw [map_pow, map_natCast, map_sub] at h2
  have h3 := dvd_add (dvd_sub ((s n).2.2 g) h2) h1
  convert h3 using 1
  ring

end Witt

section Tilt

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem mem_OC {x : ℂ_[l]} : x ∈ PadicComplexInt l ↔ ‖x‖ ≤ 1 := GlobalTheory.RingBasics.mem_OC x

theorem eq_of_coeff_zero {m : ℕ} (hm : 0 < m) {y y' : OCb l} (hy : y ^ l ^ m = y)
    (hy' : y' ^ l ^ m = y') (h : PreTilt.coeff 0 y = PreTilt.coeff 0 y') : y = y' := by
  have key : ∀ (z : OCb l) (n : ℕ), PreTilt.coeff n z ^ l ^ n = PreTilt.coeff 0 z := by
    intro z n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', pow_mul, ← ih]
      congr 1
      exact Perfection.coeff_pow_p' (R := ModP (OC l) l) z n
  have key2 : ∀ (z : OCb l), z ^ l ^ m = z → ∀ n : ℕ,
      PreTilt.coeff n z = PreTilt.coeff 0 z ^ l ^ ((m - 1) * n) := by
    intro z hz n
    rw [← key z n, ← pow_mul, ← pow_add, ← map_pow,
      show n + (m - 1) * n = m * n by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring, pow_pow_mul hz]
  refine Perfection.ext (R := ModP (OC l) l) fun n => ?_
  rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, key2 y hy, key2 y' hy', h]

theorem norm_lt_one_of_mk_eq {a b : OC l}
    (h : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) a =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) b) : ‖(a : ℂ_[l]) - b‖ < 1 := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h1 := congrArg (fun t : OC l => (t : ℂ_[l])) hw
  push_cast at h1
  rw [h1, norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) GlobalTheory.ResidueRoot.norm_p_lt_one
    (mem_OC.1 w.2)

theorem eventually_actT_eq (y : OCb l) (m : ℕ) (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∀ᶠ g in 𝓝 (1 : GQ l), AI.actT g y = y := by
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {((l : ℕ) : OC l)})
    (PreTilt.coeff 0 y)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)) (z : ℂ_[l]) _ (norm_pos_iff.2 hl0)
  rw [dist_eq_norm] at hx
  have hw : ‖((z : ℂ_[l]) - x) / l‖ ≤ 1 := by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.2 hl0)).2 hx.le
  let w : OC l := ⟨_, mem_OC.2 hw⟩
  have hx' : ((z - (l : OC l) * w : OC l) : ℂ_[l]) = (x : ℂ_[l]) := by
    push_cast
    simp only [w]
    field_simp
    ring
  have hy0 : PreTilt.coeff 0 y =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z - (l : OC l) * w) := by
    rw [← hz]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨w, by ring⟩)
  filter_upwards [(stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).mem_nhds (one_mem _)] with g hg
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ hy0
  have hg' : g x = x := hg
  rw [hx', AI.actC_ext, hg', ← hx'] at h1
  refine eq_of_coeff_zero hm (by rw [← map_pow, hy]) hy ?_
  rw [h2, hy0, Subtype.ext h1]

theorem norm_sub_lt_one_of_fix (g : GQ l)
    (hg : ∀ m, 0 < m → ∀ y : OCb l, y ^ l ^ m = y → AI.actT g y = y) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖g x - x‖ < 1 := by
  have hgx : ‖g x‖ = ‖x‖ := by
    rw [← PadicComplex.norm_extends, ← AI.actC_ext, AI.actC_norm, PadicComplex.norm_extends]
  rcases hx.lt_or_eq with h | h
  · rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hgx ▸ h) (by rwa [norm_neg]))
  obtain ⟨n, hn, hyn⟩ := GlobalTheory.ResidueRoot.exists_pow_alg x h
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  have h3 : ‖((x : ℂ_[l]) ^ m) ^ l ^ k - 1‖ < 1 := by
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
      ← PadicComplex.coe_eq] at hyn
    rwa [← pow_mul, mul_comm]
  have h4 := GlobalTheory.ResidueRoot.sub_one_lt_of_pow_p_pow k
    (by rw [norm_pow, PadicComplex.norm_extends, h, one_pow]) h3
  obtain ⟨ζ, hζ, h5⟩ := GlobalTheory.ResidueRoot.exists_root hm0 h4
  have hζ1 : ‖ζ‖ ≤ 1 := by
    have := congrArg norm hζ
    rw [norm_pow, norm_one] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 this).le
  let Z : OC l := ⟨ζ, mem_OC.2 hζ1⟩
  have hZm : Z ^ m = 1 := Subtype.ext hζ
  have hZ : Z ^ l ^ m.totient = Z := by
    have h6 := Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)
    rw [pow_eq_pow_mod _ hZm, h6, ← pow_eq_pow_mod _ hZm, pow_one]
  obtain ⟨r, hr⟩ : ∃ r, m.totient = r + 1 := ⟨m.totient - 1, by
    have := Nat.totient_pos.2 hm0
    omega⟩
  rw [hr] at hZ
  let y : OCb l := ⟨fun j => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j)),
    fun j => by
      show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * (j + 1)))) ^ l = _
      rw [← map_pow, ← pow_mul, ← pow_succ, show r * (j + 1) + 1 = (r + 1) + r * j by ring,
        pow_add, pow_mul, hZ]⟩
  have hyc : ∀ j, PreTilt.coeff j y =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j)) := fun j => rfl
  have hy : y ^ l ^ (r + 1) = y := by
    refine Perfection.ext (R := ModP (OC l) l) fun j => ?_
    rw [← PreTilt.coeff_def, ← PreTilt.coeff_def, map_pow, hyc]
    show (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (Z ^ l ^ (r * j))) ^ l ^ (r + 1) = _
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hZ]
  have hy0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) Z := by
    rw [hyc]; simp
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ hy0
  rw [hg _ (Nat.succ_pos r) y hy, hy0] at h2
  have h7 := norm_lt_one_of_mk_eq h2
  rw [h1] at h7
  have h8 : ‖AI.actC g ((x : ℂ_[l]) - ζ)‖ < 1 := by rwa [AI.actC_norm]
  rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq,
    ← PadicComplex.coe_eq, ← AI.actC_ext]
  have h9 := GlobalTheory.ResidueRoot.norm_add_lt_one h8
    (GlobalTheory.ResidueRoot.norm_add_lt_one (by rw [norm_neg]; exact h7 : ‖-(ζ - AI.actC g ζ)‖ < 1)
      (by rw [norm_neg]; exact h5 : ‖-((x : ℂ_[l]) - ζ)‖ < 1))
  convert h9 using 2
  rw [map_sub]
  ring

end Tilt

section Main

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

open scoped Formalism.Per in

theorem ιA_zlW (T : LocTied l P AI) (z : ℤ_[l]) :
    AI.ιA (zlW l (OCb l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  apply T.eB.injective
  rw [T.ιA, T.zB]
  exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI := K.2
  exact isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

theorem exists_int (T : LocTied l P AI) (K : FinExt l) (c : ↥(GK K) → ℤ_[l]) (hc : Continuous c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hI : ∀ g ∈ IK K, c g = 0) :
    ∃ b : P.R.B, ∀ g : ↥(GK K), P.actQ g b - b = algebraMap ℚ_[l] P.R.B (c g : ℚ_[l]) := by
  haveI := compactSpace_GK K
  obtain ⟨b, hb⟩ := exists_witt_coboundary (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) c hc hadd
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx))
  refine ⟨AI.ιA b, fun g => ?_⟩
  rw [← AI.ιA_act, ← map_sub, ← ιA_zlW AI T, ← hb g]
  rfl

theorem exists_rat (T : LocTied l P AI) (K : FinExt l) (c : ↥(GK K) → ℚ_[l]) (hc : Continuous c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hI : ∀ g ∈ IK K, c g = 0) :
    ∃ b : P.R.B, ∀ g : ↥(GK K), P.actQ g b - b = algebraMap ℚ_[l] P.R.B (c g) := by
  haveI := compactSpace_GK K
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max C 1)⁻¹) (by positivity)
  have ha1 : ∀ g, ‖a * c g‖ ≤ 1 := fun g => by
    rw [norm_mul]
    have h1 : ‖c g‖ ≤ max C 1 := (hC _ ⟨g, rfl⟩).trans (le_max_left _ _)
    calc ‖a‖ * ‖c g‖ ≤ (max C 1)⁻¹ * max C 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  obtain ⟨b, hb⟩ := exists_int AI T K (fun g => ⟨a * c g, ha1 g⟩)
    ((continuous_const.mul hc).subtype_mk _)
    (fun g h => Subtype.ext (by
      change a * c (g * h) = a * c g + a * c h
      rw [hadd, mul_add]))
    (fun g hg => Subtype.ext (by
      change a * c g = 0
      rw [hI g hg, mul_zero]))
  refine ⟨a⁻¹ • b, fun g => ?_⟩
  rw [map_smul, ← smul_sub, hb g, Algebra.smul_def, ← map_mul]
  congr 1
  exact inv_mul_cancel_left₀ ha' _

end Main

theorem unramified_mem_Z1f : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    ∀ c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K),
      c ∈ finiteCocycles ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro D l _ K LL c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : (D.loc l).R.B, ∀ g : ↥(GK K),
      (D.loc l).actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    exists_rat (D.locA l) (D.locT l) K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] (D.loc l).actQ g (b i) := by
    rw [← (D.loc l).PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

end GlobalTheory.UnramifiedCrys
