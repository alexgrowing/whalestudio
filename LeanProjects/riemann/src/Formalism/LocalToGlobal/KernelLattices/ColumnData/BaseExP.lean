import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerPerPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KernelLatticeT0Exists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerFourSq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerExtC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSelfDual
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetFin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerTens
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerLocIso
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical IntermediateField

namespace Formalism.L2.Ker.Cd

open Formalism.MainNotions Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_b : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = conj (φ x) :=
  H.conjE_apply φ x

theorem d_pos : 0 < H.d := H.hyp.2.1.pos

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem bE_ne : H.sqd ≠ 0 := by
  intro h0
  have h := bE_sq H
  rw [h0] at h
  have hd : (H.d : H.E) ≠ 0 := Nat.cast_ne_zero.mpr (d_pos H).ne'
  apply hd
  have : -(H.d : H.E) = 0 := by rw [← h]; simp
  simpa using this

theorem conj_b : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  rw [phi_conj, map_neg, phi_b]
  simp

theorem b_mem_K : H.sqd ∈ H.K := mem_adjoin_simple_self ℚ _

def bK : H.K := ⟨H.sqd, b_mem_K H⟩

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  have hint : IsIntegral ℚ H.sqd := .of_finite ℚ _
  have hp : minpoly ℚ H.sqd = Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [Polynomial.natDegree_X_pow_add_C]
        simp
      · intro x hx
        simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] at hx
        have hd : (0 : ℚ) < H.d := by exact_mod_cast d_pos H
        nlinarith [sq_nonneg x]
    · simp [bE_sq H]
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  show Module.finrank ℚ ℚ⟮H.sqd⟯ = 2
  rw [IntermediateField.adjoin.finrank hint, hp, Polynomial.natDegree_X_pow_add_C]

theorem K_induction {p : H.E → Prop} (hb : p (H.sqd)) (hq : ∀ r : ℚ, p (algebraMap ℚ H.E r))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hinv : ∀ x, p x → p x⁻¹) (hmul : ∀ x y, p x → p y → p (x * y))
    (k : H.K) : p (k : H.E) := by
  obtain ⟨k, hk⟩ := k
  show p k
  have hk' : k ∈ IntermediateField.adjoin ℚ {H.sqd} := hk
  clear hk
  induction hk' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact hb
  | algebraMap r => exact hq r
  | add x y _ _ hx hy => exact hadd x y hx hy
  | inv x _ hx => exact hinv x hx
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem conj_mem_K (k : H.K) : H.conj (k : H.E) ∈ H.K := by
  refine K_induction H (p := fun x => H.conj x ∈ H.K) ?_ ?_ ?_ ?_ ?_ k
  · rw [conj_b]; exact neg_mem (b_mem_K H)
  · intro r; rw [AlgEquiv.commutes]; exact H.K.algebraMap_mem r
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_inv₀]; exact inv_mem hx
  · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem isConj : PI.KerIso.IsConj H.K H.conj := by
  refine ⟨conj_conj H, fun k => ⟨⟨H.conj (k : H.E), conj_mem_K H k⟩, rfl⟩, ⟨bK H, ?_⟩⟩
  intro h
  have h1 : H.conj (H.sqd) = H.sqd := h
  rw [conj_b] at h1
  have h2 : (2 : H.E) * H.sqd = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero h3
  · exact bE_ne H h3

theorem tr_pos (x : H.E) (hx : x ≠ 0) : 0 < Algebra.trace ℚ H.E (x * H.conj x) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := H.E) ℂ (x := x * H.conj x)
  have h2 : ∀ σ : H.E →ₐ[ℚ] ℂ, σ (x * H.conj x) = ((Complex.normSq (σ x) : ℝ) : ℂ) := by
    intro σ
    have h3 := phi_conj H (σ : H.E →+* ℂ) x
    rw [map_mul]
    have h4 : σ (H.conj x) = conj (σ x) := h3
    rw [h4, Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ), ← Complex.ofReal_sum] at h
  have h5 : ((Algebra.trace ℚ H.E (x * H.conj x) : ℚ) : ℝ) = ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    apply Complex.ofReal_injective
    rw [← h]
    simp
  have h6 : 0 < ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    have : Nonempty (H.E →ₐ[ℚ] ℂ) := ⟨(H.φ₀ : H.E →+* ℂ).toRatAlgHom⟩
    apply Finset.sum_pos
    · intro σ _
      exact Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)
    · exact Finset.univ_nonempty
  rw [← h5] at h6
  exact_mod_cast h6

theorem finrank_E_K : Module.finrank H.K H.E = 2 * R.ord := by
  have h1 := Module.finrank_mul_finrank ℚ H.K H.E
  rw [finrank_K H, H.finrank_cmField] at h1
  omega

theorem emb_on_K (g : R.GG) (hg : g ∈ R.Psi) (k : H.K) : H.emb g (k : H.E) = H.φ₀ (k : H.E) := by
  have hs : (H.sigmaOf g) H.sqd = H.sqd := by
    rw [H.gal_sqd (H.sigmaOf g)]
    have h1 : H.gal (H.sigmaOf g) = g := by
      simp [Formalism.BasicNotions.Host.sigmaOf]
    have h2 : g.1.2 = 1 := hg
    rw [h1, h2]
    simp
  apply K_induction H (p := fun x => H.emb g x = H.φ₀ x)
  · simp [Formalism.BasicNotions.Host.emb, hs]
  · intro r
    simp [Formalism.BasicNotions.Host.emb]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro x hx
    rw [map_inv₀, map_inv₀, hx]
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]

theorem phi_nonreal : ∃ k : H.K, (H.φ₀ (k : H.E)).im ≠ 0 := by
  refine ⟨bK H, ?_⟩
  show (H.φ₀ H.sqd).im ≠ 0
  rw [phi_b H]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast d_pos H
  simp [(Real.sqrt_pos.mpr hd).ne']

theorem d_mod_eight_eq_seven : H.d % 8 = 7 := by
  have := H.hyp.2.2.2.1
  omega

theorem bK_mul : bK H * bK H = -(H.d : H.K) := by
  apply Subtype.ext
  have h := bE_sq H
  rw [sq] at h
  simpa [bK] using h

theorem sqrt_in_K : ∃ s : H.K, s * s = -(H.d : H.K) ∧
    H.conj (algebraMap H.K H.E s) = -algebraMap H.K H.E s :=
  ⟨bK H, bK_mul H, conj_b H⟩

theorem theta_integral : IsIntegral ℤ ((1 + bK H) / 2 : H.K) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := d_mod_eight_eq_seven H; omega⟩
  refine ⟨Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (m : ℤ)), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (b := ((1 : ℕ) : WithBot ℕ)) ?_ (by norm_num)
    compute_degree
    exact le_rfl
  · have hb := bK_mul H
    have hm' : (H.d : H.K) + 1 = 4 * (m : H.K) := by exact_mod_cast congrArg (Nat.cast : ℕ → H.K) hm
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_neg, Polynomial.eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    field_simp
    linear_combination hb - hm'

def thetaK : 𝓞 H.K := ⟨(1 + bK H) / 2, theta_integral H⟩

theorem phi_thetaK : H.φ₀ (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
  have h : (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + H.sqd) / 2 := by
    simp [thetaK, bK]
    rfl
  rw [h, map_div₀, map_add, map_one, phi_b, map_ofNat]

theorem conj_ideal (B : Ideal (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ H.conj • B ↔ ∃ y ∈ B, H.conj (y : H.E) = (x : H.E) := by
  constructor
  · intro hx
    refine ⟨H.conj⁻¹ • x, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hx, ?_⟩
    show H.conj (H.conj.symm (x : H.E)) = _
    exact H.conj.apply_symm_apply _
  · rintro ⟨y, hy, hxy⟩
    have : x = H.conj • y := by
      apply RingOfIntegers.ext
      rw [← hxy]
      rfl
    rw [this]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hy

theorem host_selfDual : PI.KerIso.SelfDualI H.K H.conj H.AA0 :=
  kernel_self_dual_of_different H.K H.E H.conj H.𝔟 (H.conj • H.𝔟) (isConj H) (conj_ideal H H.𝔟) H.𝔟_spec.1

theorem host_splits (p : ℕ) (hp : p.Prime) (hs : p = 2 ∨ jacobiSym (-(H.d : ℤ)) p = 1) : PI.KerIso.SplitsAt H.K H.conj p :=
  kernel_split_of_jacobi H.K H.E H.conj H.d p (bK H) (d_mod_eight_eq_seven H) (bK_mul H) (conj_b H) hp hs

end Host

section Facts

variable (D : Car)

theorem kQuad : KQuad D := finrank_K D.host
theorem conjOnK : ConjOnK D := isConj D.host
theorem trPos : TrPos D := tr_pos D.host

theorem cardTau : CardTau D := by
  unfold CardTau
  rw [D.what₂.card_Tau, finrank_E_K D.host]
  rfl

theorem embInj : EmbInj D := fun _ _ h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embOnK : EmbOnK D := fun τ k => emb_on_K D.host _ (D.eTau τ).2 k

theorem phiNonReal : PhiNonReal D := phi_nonreal D.host
theorem dMod8 : DMod8 D := d_mod_eight_eq_seven D.host
theorem sqrtInK : SqrtInK D := sqrt_in_K D.host

theorem latStable : LatStable D := by
  intro cc δ w hw
  refine AddSubgroup.closure_induction (p := fun w _ => thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨c, hc, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨thetaK D.host * c, cc.mul_mem_left _ hc, ?_⟩
    have h : (((thetaK D.host * c : 𝓞 D.host.K) : D.host.K) : D.host.E)
        = (((thetaK D.host : 𝓞 D.host.K) : D.host.K) : D.host.E) * (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      push_cast; rfl
    rw [h, map_mul, phi_thetaK]
    unfold thetaC
    ring
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro x _ hx; rw [mul_neg]; exact neg_mem hx

theorem conjIdeal : ConjIdeal D := conj_ideal D.host D.host.𝔟

theorem hostFacts : HostFacts D :=
  ⟨kQuad D, conjOnK D, trPos D, cardTau D, embInj D, embOnK D, phiNonReal D, dMod8 D, sqrtInK D, latStable D, conjIdeal D⟩

end Facts

section Exist

variable {D : Car}

theorem periodExists_of (h2 : KQuad D) (hn : PhiNonReal D) : PeriodExists D :=
  fun cc δ hcc hδ =>
    exists_periodPairOfIdeal D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) cc δ h2 hn hcc hδ

theorem tZeroExists_of (hP : PeriodExists D) (hd : DMod8 D) (hst : LatStable D) : TZeroExists D := by
  intro cc δ hcc hδ
  obtain ⟨L, hL⟩ := hP cc δ hcc hδ
  have hmem : ∀ w : ℂ, w ∈ L.lattice ↔ w ∈ TaylorLogMetric.lamOf D cc δ := fun w => by rw [← hL]; rfl
  obtain ⟨t, h1, h2, h3⟩ := kernel_lattice_t0_exists L D.host.d hd
    (fun w hw => (hmem _).mpr (hst cc δ w ((hmem w).mp hw)))
  exact ⟨t, (hmem _).mp h1, fun h => h2 ((hmem _).mpr h), fun h => h3 ((hmem _).mpr h)⟩

theorem gammaZeroExists_of (h2 : KQuad D) (hc : CardTau D) (hj : ConjOnK D) (hpos : TrPos D) (hi : EmbInj D)
    (hk : EmbOnK D) : GammaZeroExists D := by
  obtain ⟨g, hg⟩ := kernel_four_squares D.host.K D.host.E D.host.conj D.what₂.Tau h2 hc hj hpos
  obtain ⟨gC, hC⟩ := kernel_extension_c D.host.K D.host.E D.what₂.Tau (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (TaylorLogMetric.embT D) hi hk hc g
  exact ⟨⟨g, hg⟩, gC, hC⟩

theorem mmSelfDual_of (hj : ConjOnK D) (hb : ConjIdeal D) : MMSelfDual D :=
  kernel_self_dual_of_different D.host.K D.host.E D.host.conj D.host.𝔟 (D.host.conj • D.host.𝔟) hj hb D.host.𝔟_spec.1

theorem splitKSplits_of (hd : DMod8 D) (hs : SqrtInK D) : SplitKSplits D := by
  obtain ⟨s, h1, h2⟩ := hs
  exact fun p hp hsp => kernel_split_of_jacobi D.host.K D.host.E D.host.conj D.host.d p s hd h1 h2 hp hsp

theorem gammaPExists_of (hLoc : PI.KerIso.LocIso) (h2 : KQuad D) (hj : ConjOnK D) (hsp : SplitKSplits D) (hsd : MMSelfDual D)
    (h0 : GammaZeroExists D) : GammaPExists D := by
  obtain ⟨γ₀, -, -⟩ := h0
  intro p hp hs
  obtain ⟨g, hg, hat⟩ := hLoc D.host.K D.host.E D.host.conj D.what₂.Tau D.host.AA0 p h2 hj hp (hsp p hp hs) hsd
    ⟨γ₀.g, γ₀.isom⟩
  exact ⟨⟨g, hg⟩, hat⟩

theorem baseExists_of_four (hP : PeriodExists D) (hT : TZeroExists D) (h0 : GammaZeroExists D) (hp : GammaPExists D) :
    BaseExists D :=
  fun cc hcc δ hδ => Base.nonempty_of cc δ (hP cc δ hcc.1 hδ) (hT cc δ hcc.1 hδ) h0 hp

theorem baseExists_of (hF : HostFacts D) (hp : GammaPExists D) : BaseExists D := by
  obtain ⟨h2, hj, hpos, hc, hi, hk, hn, hd, -, hst, -⟩ := hF
  have hP := periodExists_of h2 hn
  exact baseExists_of_four hP (tZeroExists_of hP hd hst) (gammaZeroExists_of h2 hc hj hpos hi hk) hp

end Exist

section Final

variable (D : Car)

theorem periodExists : PeriodExists D := periodExists_of (kQuad D) (phiNonReal D)
theorem gammaZeroExists : GammaZeroExists D :=
  gammaZeroExists_of (kQuad D) (cardTau D) (conjOnK D) (trPos D) (embInj D) (embOnK D)
theorem mmSelfDual : MMSelfDual D := mmSelfDual_of (conjOnK D) (conjIdeal D)
theorem splitKSplits : SplitKSplits D := splitKSplits_of (dMod8 D) (sqrtInK D)

theorem baseExists_of_gammaP (hp : GammaPExists D) : BaseExists D := baseExists_of (hostFacts D) hp

theorem gammaPExists : GammaPExists D :=
  gammaPExists_of kernel_local_iso (kQuad D) (conjOnK D) (splitKSplits D) (mmSelfDual D) (gammaZeroExists D)

theorem baseExists : BaseExists D := baseExists_of_gammaP D (gammaPExists D)

end Final

namespace Test

open Formalism.BasicNotions.Examples₂

theorem tr_one : 0 < Algebra.trace ℚ H0.E (1 * H0.conj 1) := tr_pos H0 1 one_ne_zero

theorem example_ideal_self_dual : PI.KerIso.SelfDualI H0.K H0.conj H0.AA0 := host_selfDual H0
theorem two_splits : PI.KerIso.SplitsAt H0.K H0.conj 2 := host_splits H0 2 Nat.prime_two (Or.inl rfl)

end Test

end Formalism.L2.Ker.Cd
