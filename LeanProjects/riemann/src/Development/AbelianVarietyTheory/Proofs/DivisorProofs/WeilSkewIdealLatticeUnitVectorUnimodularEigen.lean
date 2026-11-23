import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryMovingToSelfDualSkewLStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem norm_eq_one_of_modulusOneAll {c : ℂ} (h : Mod1All c) : ‖c‖ = 1 := by
  obtain ⟨hx, h2⟩ := h
  simpa using h2 Qbar.val

theorem int_of_inc {b : D.host.E} (hb : inc D b ∈ OhE D) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = b := by
  have h := (VacMove.moves_one D 1 (fun _ => b)).2 (fun i => by simpa using hb)
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h 0)
  exact ⟨o, ho⟩

theorem exists_nat_clear {N : ℕ} (P : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ s : Fin N → AE D, (∀ j, s j ∈ OhE D) →
      ∀ i, P.mulVec (fun j => (n : AE D) * s j) i ∈ OhE D := by
  obtain ⟨n, hn, hP⟩ := VacMove.exists_mat_denom P
  refine ⟨n, hn, fun s hs i => ?_⟩
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => ?_
  have : P i j * ((n : AE D) * s j) = ((n : AE D) * P i j) * s j := by ring
  rw [this]
  exact mul_mem (hP i j) (hs j)

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem lam_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h : GL (Fin N) (AE D)}
    (hL : Moves D h (skewLat D 𝔫 N)) {k : Matrix (Fin N) (Fin N) (AE D)} (hk : ∀ i j, k i j ∈ OhE D)
    (u : Fin N → AE D)
    (hu : ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec u i ∈ OhE D) :
    ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec (k.mulVec u) i ∈ OhE D := by
  obtain ⟨n, hn, hcl⟩ := exists_nat_clear (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.FunObj.CosetTT.skewLat_smul (D := D) 𝔫 N
  choose y s hs e using fun j => GlobalTheory.TrueTheta.approx D (u j) hn
  have hy : y ∈ skewLat D 𝔫 N := by
    rw [hL y]
    intro i
    have : (fun j => inc D (y j)) = u + fun j => (n : AE D) * s j := funext fun j => e j
    rw [this, Matrix.mulVec_add]
    exact add_mem (hu i) (hcl s hs i)
  choose b t ht eb using fun q : Fin N × Fin N => GlobalTheory.TrueTheta.approx D (k q.1 q.2) (Nat.mul_pos hn hM)
  have hb : ∀ q, ∃ o : 𝓞 D.host.E, (o : D.host.E) = b q := fun q =>
    int_of_inc (by rw [eb q]; exact add_mem (hk _ _) (mul_mem (natCast_mem _ _) (ht q)))
  choose o ho using hb
  have hzL : (fun i => ∑ j, b (i, j) * y j) ∈ skewLat D 𝔫 N := by
    have hy' := hy
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_implies] at hy' ⊢
    intro i
    refine sum_mem fun j _ => ?_
    rw [← ho (i, j)]
    have : ((o (i, j) : 𝓞 D.host.E) : D.host.E) * y j = o (i, j) • y j := (Algebra.smul_def _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (hy' j)
  have hMy : ∀ j, inc D ((M : D.host.E) * y j) ∈ OhE D := by
    intro j
    have h1 := hMs y hy
    simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h1
    obtain ⟨o', ho'⟩ := Submodule.mem_one.1 (h1 j)
    have : ((M : 𝓞 D.host.E) • y) j = (M : D.host.E) * y j := by simp [Algebra.smul_def]
    rw [← this, ← ho']
    exact VacMove.inc_int D o'
  have hw : ∀ i, (∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) ∈ OhE D := fun i =>
    sum_mem fun j _ => mul_mem (ht _) (hMy j)
  have hks : ∀ i, k.mulVec s i ∈ OhE D := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hk _ _) (hs j)
  have key : k.mulVec u = (fun i => inc D (∑ j, b (i, j) * y j)) -
      (fun i => (n : AE D) * ∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) -
      (fun i => (n : AE D) * k.mulVec s i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, map_sum, map_mul, map_natCast, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := e j
    have e2 := eb (i, j)
    push_cast at e2
    linear_combination (-inc D (y j)) * e2 - k i j * e1
  rw [key]
  intro i
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  exact sub_mem (sub_mem ((hL _).1 hzL i) (hcl _ hw i)) (hcl _ hks i)

theorem moves_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h k : GA D N}
    (hL : Moves D (h : GL (Fin N) (AE D)) (skewLat D 𝔫 N)) (hk : k ∈ intG D N) :
    Moves D ((k * h : GA D N) : GL (Fin N) (AE D)) (skewLat D 𝔫 N) := by
  have hk' := (mem_intG k).1 hk
  intro x
  rw [hL x, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
  constructor
  · intro hx i
    rw [← Matrix.mulVec_mulVec]
    exact lam_int_mul 𝔫 hL (fun i j => (hk' i j).2) _ hx i
  · intro hx i
    rw [← Matrix.mulVec_mulVec] at hx
    have := lam_int_mul 𝔫 hL (k := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
      (fun i j => (hk' i j).1) _ hx i
    have hkk : ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
        ((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
          (fun j => inc D (x j))) = fun j => inc D (x j) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rwa [hkk] at this

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

theorem om_unitVec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  have hI : Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied D
  have hev : Even (a * d) := hd.mul_left a
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h2, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨h, -, -, hmv, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) hcop' d
  obtain ⟨c1, hc1, he1, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W 1 h (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) (VacMove.moves_one D a) hmv
  have hg1 : Moves D (g : GL (Fin a) (AE D)) (stdL D a) := by
    simpa using VacMove.moves_mul_int hg (VacMove.moves_one D a)
  have hmv2 := moves_int_mul (D.host.conj • 𝔪) hmv hg'
  obtain ⟨c2, hc2, he2, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W g (g' * h) (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) hg1 hmv2
  have n1 := norm_eq_one_of_modulusOneAll hc1
  have n2 := norm_eq_one_of_modulusOneAll hc2
  have c1ne : c1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n1; exact zero_ne_one n1
  set F := Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0
    with hF
  have hF1 : F = c1⁻¹ • W.Om 1 h e0 := by
    rw [he1]; funext z; simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ c1ne, one_mul]
  refine ⟨c1⁻¹ * c2, by rw [norm_mul, norm_inv, n1, n2]; norm_num, ?_⟩
  have hm2 := W.mul g 1 g' h e0 hT
  rw [mul_one] at hm2
  conv_lhs => rw [hF1, W.smul _ _ _ _ (W.maps 1 h e0 hT), ← hm2, he2]
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.BotPairSmall.CvEig
