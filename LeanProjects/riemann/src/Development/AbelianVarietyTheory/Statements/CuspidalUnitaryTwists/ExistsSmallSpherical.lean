import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPairSpherical
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsPairPoint

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.NormSum

def IntegralOver (D : D7) {N : ℕ} (p : ℕ) (h : GA D N) : Prop :=
  ∃ k ∈ intG D N, TrivAt D p ((h * k : GA D N) : GL (Fin N) (AE D))

def intBound (C : ℝ) (f N : ℕ) (B L : ℝ) (Q : ℕ) : ℝ :=
  C * f * (2 * (N : ℝ)) * Real.log ((f : ℝ) * (2 * (N : ℝ))) + C * f * (2 * (N : ℝ)) * B * L +
    C * f * (2 * (N : ℝ)) ^ 2 * B * Real.log Q

def Exponents (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) : Prop :=
  (∀ l ∈ S, l.Prime) ∧ (∀ l, 0 ≤ del_vp l) ∧ (∀ l, l ∉ S → del_vp l = 0) ∧ ∑ l ∈ S, del_vp l * Real.log l ≤ b

def CoordInt (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (del_vp : ℕ → ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (p : ℕ) [Fact p.Prime] (Q' : ℕ), padicValNat p Q' ≤ padicValNat p Q →
    ∀ P : Pair D ⊤ δ t0 Q', P.Small N B →
      (∀ q : Cls D P.d P.J, ∃ h, DoubleCoset.mk (ratG D P.d) P.J h = q ∧ IntegralOver D p h) ∧
      (∀ h, gam D P.J h ≠ 0 ∧ (padicValNat p (gam D P.J h) : ℝ) ≤ del_vp p) ∧
      ∀ h, IntegralOver D p h → ∀ T, P.coord h T ∈ Qbar ∧
        ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (P.coord h T)‖ ≤ (p : ℝ) ^ del_vp p

def NormInt (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type)
    (P P' : ι → Pair D ⊤ δ t0 Q) (zA zA' : ι → K),
    (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
    (∀ i, (∃ h T, (P i).coord h T ≠ 0) ∧ ∃ h T, (P' i).coord h T ≠ 0) →
    (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
    NonArchimedeanDefectBound (Formalism.PairingDivisionLocalBalance.wt S del_vp) zA zA' b

def IntSt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (Q N : ℕ) (B L : ℝ), GoodLevel D Q → 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Exponents S del_vp (intBound C (fF D) N B L Q) ∧
      CoordInt D N B Q del_vp ∧ NormInt D N B Q S del_vp (intBound C (fF D) N B L Q)

def ArchSt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (Q : ℕ), Crv D cc δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type) (N : ℕ) (B L : ℝ)
      (P P' : ι → Pair D cc δ t0 Q) (zA zA' : ι → K),
      1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L →
      (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
      (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
      ArchimedeanHeightBound zA zA'
        (C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
          C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q)

def IntNormSt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type) (N : ℕ) (B L : ℝ)
      (P P' : ι → Pair D ⊤ δ t0 Q) (zA zA' : ι → K),
      1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L →
      (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
      (∀ i, (∃ h T, (P i).coord h T ≠ 0) ∧ ∃ h T, (P' i).coord h T ≠ 0) →
      (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
      ∃ dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ, NonArchimedeanDefectBound dl zA zA'
        (C * fF D * (2 * (N : ℝ)) * Real.log ((fF D : ℝ) * (2 * (N : ℝ))) + C * fF D * (2 * (N : ℝ)) * B * L +
          C * fF D * (2 * (N : ℝ)) ^ 2 * B * Real.log Q)

theorem IntSt.norms (h : IntSt) : IntNormSt := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun D δ t0 Q _ _ hQ K _ _ _ σ ι N B L P P' zA zA' hN hB h1 hL hs hc hn => ?_⟩
  obtain ⟨S, del, -, -, h3⟩ := h D Q N B L hQ hN hB h1 hL
  let : StarRing K := starRingOfComm
  exact ⟨_, h3 δ t0 K σ ι P P' zA zA' hs hc hn⟩

section Places

open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Finset ℕ} {del : ℕ → ℝ} {b : ℝ}

theorem Exponents.wt_eq (h : Exponents S del b) {p : ℕ} (hp : p.Prime) (w : Pl K) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    wt S del w = del p * (vw w (p : K) : ℝ) := by
  unfold wt
  refine Finset.sum_eq_single p (fun l hl hne => ?_) fun hS => by rw [h.2.2.1 p hS, zero_mul]
  have hn : (l : 𝓞 K) ∉ w.asIdeal := fun hm => by
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (h.1 l hl) hp).2 hne)).map
      (Int.castRingHom (𝓞 K))
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm)) (Ideal.mul_mem_left _ _ (by simpa using hw))
  have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
  simp only [map_natCast] at this
  rw [this]; simp

theorem Exponents.wt_size [IsTotallyComplex K] (h : Exponents S del b) :
    (∀ w : Pl K, 0 ≤ wt S del w) ∧ ∀ F : Finset (Pl K), ∑ w ∈ F, Formalism.DivisionValues.lw w * wt S del w ≤ b := by
  obtain ⟨h1, h2, h3⟩ := Formalism.PairingDivisionLocalBalance.weight_sum' K S del
  have h0 := h3 fun l _ => h.2.1 l
  refine ⟨h0, fun F => le_trans ?_ (h2 ▸ h.2.2.2)⟩
  rw [finsum_eq_sum_of_support_subset (s := F ∪ h1.toFinset) _
    (fun w hw => Finset.mem_coe.2 (Finset.mem_union_right _ (h1.mem_toFinset.2 hw)))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun w _ _ =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (h0 w)

example [IsTotallyComplex K] (h : Exponents S del b) :
    NonArchimedeanDefectBound (K := K) (ι := Unit) (wt S del) (fun _ => 1) (fun _ => 1) b := by
  refine ⟨h.wt_size.1, h.wt_size.2, fun _ => ⟨one_ne_zero, one_ne_zero, fun w => ?_⟩⟩
  have := h.wt_size.1 w
  simp only [Formalism.DivisionValues.ValuationRepresentative.vw_one, Int.cast_zero, and_self]
  linarith

theorem wt_conjPl (S : Finset ℕ) (del : ℕ → ℝ) (w : Pl K) : wt S del (conjPl w) = wt S del w := by
  unfold wt
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Formalism.DivisionValues.ValuationRepresentative.vw_star, star_natCast]

def conjQbar : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar fun x =>
    mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 x.2).algHom ((starRingEnd ℂ).toRatAlgHom))

theorem conj_bound {p : ℕ} [Fact p.Prime] {z : ℂ} {r : ℝ} (hz : z ∈ Qbar) (h : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam z‖ ≤ r)
    (lam : Qbar →+* ℂ_[p]) : ‖lamC lam ((starRingEnd ℂ) z)‖ ≤ r := by
  have h1 := h (lam.comp conjQbar)
  have hz' : (starRingEnd ℂ) z ∈ Qbar := (conjQbar ⟨z, hz⟩).2
  rw [lamC, dif_pos hz] at h1
  rw [lamC, dif_pos hz']
  exact h1

theorem CoordInt.at_place {D : D7} {N Q : ℕ} {B : ℝ} (hE : Exponents S del b) (h : CoordInt D N B Q del) (σ : K →+* ℂ)
    {p : ℕ} (hp : p.Prime) (w : Pl K) (hw : (p : 𝓞 K) ∈ w.asIdeal) {δ t0 : ℂ} {Q' : ℕ}
    (hQ : padicValNat p Q' ≤ padicValNat p Q) (P : Pair D ⊤ δ t0 Q') (hP : P.Small N B) (g : GA D P.d) :
    -wt S del w ≤ (vw w ((1 : K) / (gam D P.J g : K)) : ℝ) ∧
      (IntegralOver D p g → ∀ T (x : K), σ x = P.coord g T ∨ σ x = (starRingEnd ℂ) (P.coord g T) →
        -wt S del w ≤ (vw w x : ℝ) ∧ -wt S del w ≤ (vw (conjPl w) x : ℝ)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, h2, h3⟩ := h δ t0 p Q' hQ P hP
  have key : ∀ (v : Pl K), (p : 𝓞 K) ∈ v.asIdeal → ∀ x : K,
      (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (σ x)‖ ≤ (p : ℝ) ^ del p) → -wt S del v ≤ (vw v x : ℝ) := by
    intro v hv x hx
    rw [hE.wt_eq hp v hv]
    rcases eq_or_ne x 0 with rfl | h0
    · have := GlobalTheory.Square.TwoStep.vw_natCast_nonneg v p
      have := hE.2.1 p
      rw [Formalism.DivisionValues.ValuationRepresentative.vw_zero]
      simp only [Int.cast_zero, Left.neg_nonpos_iff]
      positivity
    · exact GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p v (del p) h0 hv hx
  constructor
  · refine key w hw _ fun lam => ?_
    obtain ⟨h0, hv⟩ := h2 g
    have e : σ ((1 : K) / (gam D P.J g : K)) = (((gam D P.J g : Qbar)⁻¹ : Qbar) : ℂ) := by simp
    have hn : ‖((gam D P.J g : ℕ) : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p (gam D P.J g) : ℝ) := by
      have h1 : ((gam D P.J g : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (gam D P.J g : ℚ_[p]) := by simp
      rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_natCast]
      simp
    rw [e, lamC, dif_pos (Subtype.property _), Subtype.coe_eta, map_inv₀, map_natCast, norm_inv, hn]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) hv
  · intro hg T x hx
    obtain ⟨hm, hb⟩ := h3 g hg T
    have hx' : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (σ x)‖ ≤ (p : ℝ) ^ del p := by
      rcases hx with e | e <;> rw [e]
      · exact hb
      · exact conj_bound hm hb
    refine ⟨key w hw x hx', ?_⟩
    rw [← wt_conjPl]
    refine key _ ?_ x hx'
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) hw
    rwa [map_natCast] at this

end Places

theorem CoordInt.one_le_two {D : D7} {N Q : ℕ} {B : ℝ} {del : ℕ → ℝ} (h : CoordInt D N B Q del) (hN : 1 ≤ N) (hB : 0 ≤ B) :
    1 ≤ del 2 := by
  obtain ⟨δ, t0, P, -, hd, hn, hJ, -⟩ := Mass.exists_pairPoint D 1 0
  obtain ⟨h0, hv⟩ := (h δ t0 2 1 (by simp) P ⟨by omega, fun τ => by rw [hn]; simpa using hB⟩).2.1 1
  rw [hJ] at h0 hv
  have := one_le_padicValNat_of_dvd h0 (Mass.two_dvd_gam D (d := P.d) (by omega))
  exact le_trans (by exact_mod_cast this) hv

theorem reps_and_stabilisers {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (p : ℕ)
    [hp : Fact p.Prime] :
    (∀ q : Cls D P.d P.J, ∃ h, DoubleCoset.mk (ratG D P.d) P.J h = q ∧ IntegralOver D p h) ∧
      ∀ h, gam D P.J h ≠ 0 ∧ padicValNat p (gam D P.J h) ≤
        padicValNat p (8 ^ (2 * fF D * P.d) * (2 * (2 * fF D * P.d)).factorial) := by
  constructor
  · intro q
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := exists_rep_trivial_at D P.d p hp.out q.out
    refine ⟨γ * q.out, ?_, k, (mem_intG k).2 h2, h3⟩
    rw [← DoubleCoset.out_eq' (ratG D P.d) P.J q, DoubleCoset.eq]
    exact ⟨γ⁻¹, inv_mem ((mem_ratG γ).2 ⟨γ', h1⟩), 1, one_mem _, by simp [DoubleCoset.out_eq']⟩
  · intro h
    obtain ⟨h0, hd, -⟩ := GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le h
    exact ⟨h0, (padicValNat_dvd_iff_le (by positivity)).1 (pow_padicValNat_dvd.trans hd)⟩

example {p : ℕ} [hp : Fact p.Prime] (e : ℝ) (he : 0 ≤ e) (lam : Qbar →+* ℂ_[p]) :
    (1 : ℂ) ∈ Qbar ∧ ‖lamC lam 1‖ ≤ (p : ℝ) ^ e := by
  have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
  refine ⟨one_mem _, ?_⟩
  rw [lamC, dif_pos (one_mem _), this, map_one, norm_one]
  exact Real.one_le_rpow (by exact_mod_cast hp.out.one_le) he

example {K : Type} [Field K] [NumberField K] (b : ℝ) (hb : 0 ≤ b) :
    ArchimedeanHeightBound (K := K) (ι := Unit) (fun _ => 1) (fun _ => 1) b := by
  intro i
  simp [Formalism.PairingDivisionLocalBalance.meanInf, hb]

end GlobalTheory.NormSum
