import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisFamily
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.VacRatio

theorem det_int {D : D7} {N N' r : ℕ} (p : ℕ) {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb₁ : OnB D b₁) (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁)
    (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    ∃ S : ℕ, Nat.Coprime S p ∧
      IsIntegral ℤ ((S : D.host.E) * (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E)) := by
  have key : ∀ j, ∃ t : ℕ, Nat.Coprime t p ∧ ∃ c : Fin r → 𝓞 D.host.K,
      ∀ i, (t : D.host.K) * hYY D (b₂ j) (b₁ i) = (c i : D.host.K) := by
    intro j
    obtain ⟨s, hs, hmem⟩ := h₂.2.1 j
    obtain ⟨s', hs', c, hc⟩ := h₁.2.2 _ hmem
    refine ⟨s' * s, Nat.Coprime.mul hs' hs, c, fun i => ?_⟩
    have e1 : hYY D ((s' : D.host.E) • (s : D.host.E) • b₂ j) (b₁ i) =
        ((s' * s : ℕ) : D.host.K) * hYY D (b₂ j) (b₁ i) := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      rw [map_nsmul, nsmul_eq_mul]
      rfl
    have e2 : hYY D (∑ k, (((c k : D.host.K) : D.host.E)) • b₁ k) (b₁ i) = (c i : D.host.K) := by
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      rw [map_sum]
      have : ∀ k, GlobalTheory.NormSum.hYYLeft D (b₁ i) ((((c k : D.host.K) : D.host.E)) • b₁ k) =
          if k = i then (c i : D.host.K) else 0 := by
        intro k
        rw [show (((c k : D.host.K) : D.host.E)) • b₁ k = (c k : D.host.K) • b₁ k from
          algebraMap_smul D.host.E (c k : D.host.K) (b₁ k), map_smul]
        change (c k : D.host.K) • hYY D (b₁ k) (b₁ i) = _
        rw [hb₁.1 k i]
        split_ifs with h
        · subst h; simp
        · simp
      simp only [this]
      simp
    rw [← e1, hc, e2]
  choose t ht c hc using key
  refine ⟨∏ j, t j, Nat.Coprime.prod_left fun j _ => ht j, ?_⟩
  let M' : Matrix (Fin r) (Fin r) (𝓞 D.host.K) := Matrix.of fun i j => c j i
  have hM : (algebraMap (𝓞 D.host.K) D.host.K).mapMatrix M' =
      Matrix.of fun i j => (t j : D.host.K) * hYY D (b₂ j) (b₁ i) := by
    ext i j
    simp [M', hc]
  have hdet : ((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det =
      algebraMap (𝓞 D.host.K) D.host.K M'.det := by
    rw [RingHom.map_det, hM]
    have h := Matrix.det_mul_row (fun j => ((t j : ℕ) : D.host.K)) (Matrix.of fun i j => hYY D (b₂ j) (b₁ i))
    simp only [Matrix.of_apply] at h
    rw [h, Nat.cast_prod]
  have hint : IsIntegral ℤ (((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det) := by
    rw [hdet]
    exact M'.det.isIntegral_coe
  have := hint.algebraMap (B := D.host.E)
  simpa using this

theorem det_unit {D : D7} (hG : admG1 D) {N N' r : ℕ} (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb₁ : OnB D b₁) (hb₂ : OnB D b₂)
    (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁) (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) ∈ Qbar ∧
      ‖lamC lam (D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E))‖ = 1 := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set y : D.host.E := (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) with hy
  obtain ⟨S, hS, hint⟩ := det_int p hb₁ h₁ h₂
  rw [← hy] at hint
  have hn : y * D.host.conj y = 1 := GlobalTheory.NormSum.det_onB_mul_conj D hG N N' r b₁ b₂ hb₁ hb₂
  set x : ℂ := D.host.φ₀ y
  have hx1 : x * starRingEnd ℂ x = 1 := by
    have := congrArg D.host.φ₀ hn
    rwa [map_mul, hc, map_one] at this
  have hi1 : IsIntegral ℤ ((S : ℂ) * x) := by
    have := hint.map (D.host.φ₀ : D.host.E →+* ℂ).toIntAlgHom
    simpa [x] using this
  have hi2 : IsIntegral ℤ ((S : ℂ) * starRingEnd ℂ x) := by
    have := hi1.map (starRingEnd ℂ : ℂ →+* ℂ).toIntAlgHom
    simpa using this
  have hS0 : (S : ℂ) ≠ 0 := by
    have : S ≠ 0 := by
      rintro rfl
      have := Nat.Prime.one_lt (Fact.out : p.Prime)
      simp at hS
      omega
    exact_mod_cast this
  have a1 : GlobalTheory.ProductJets.AlgLe lam x 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi1)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  have a2 : GlobalTheory.ProductJets.AlgLe lam (starRingEnd ℂ x) 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi2)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  refine ⟨a1.1, ?_⟩
  have hprod : lamC lam x * lamC lam (starRingEnd ℂ x) = 1 := by
    rw [← GlobalTheory.BotFormula.lamC_mul lam a1.1 a2.1, hx1]
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have hn2 := congrArg norm hprod
  rw [norm_mul, norm_one] at hn2
  have u1 := a1.2
  have u2 := a2.2
  have h0 := norm_nonneg (lamC lam x)
  have h0' := norm_nonneg (lamC lam (starRingEnd ℂ x))
  nlinarith

theorem qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar :=
  mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h))

theorem ratio_local {D : D7} (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) {a d : ℕ} {e₁ e₂ : VC D a d → ℂ}
    (h₁ : oddE0 D ⊤ δ t0 a d e₁) (h₂ : oddE0 D ⊤ δ t0 a d e₂) (hne : e₁ ≠ 0) {κ : ℂ} (hκ : e₂ = κ • e₁)
    (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hG : admG1 D := hI.g1
  have hcop : Nat.Coprime (Ideal.absNorm (⊤ : Ideal (𝓞 D.host.K))) p := by simp
  obtain ⟨b₁, ε₁, hb₁, hl₁, hε₁, hn₁, -, he₁⟩ := h₁.2.2.2.2 p lam hcop
  obtain ⟨b₂, ε₂, hb₂, hl₂, hε₂, hn₂, -, he₂⟩ := h₂.2.2.2.2 p lam hcop
  have hP : pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0) ∈
      ThSp D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := by
    obtain ⟨hd, hth⟩ := GlobalTheory.RatEquiv.theta_signed_translation D hG ⊤ δ hC t0 ht
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG ⊤ δ a d _ b₁ hb₁
    exact GlobalTheory.ProdTheta.pullB_mem_ThSp D _ a d _ b₁ _ hpar hmem hd hth
  have hK1 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := Or.inl ⟨_, b₁, hb₁, rfl⟩
  have hK2 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₂) := Or.inl ⟨_, b₂, hb₂, rfl⟩
  have hK0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D a, GlobalTheory.NormSum.VacInt.sd_std D d, rfl⟩
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht a d _ b₁ b₂ hb₁ hb₂
  obtain ⟨μ, hμ, hIμ⟩ := hI.mu ⊤ δ hC a d _ _ _ hK1 hK2 hK0 _ hP
  have E2 : e₂ = fun z => ε₂ * (c * (μ * Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z)) := by
    rw [he₂, hpull, GlobalTheory.RatEquiv.Iop_smul, hIμ]
  obtain ⟨z, hz⟩ : ∃ z, e₁ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hz' := hz
  rw [he₁] at hz'
  have hJ : Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z ≠ 0 := right_ne_zero_of_mul hz'
  have hε0 : ε₁ ≠ 0 := left_ne_zero_of_mul hz'
  have key : κ * ε₁ = ε₂ * c * μ := by
    have h := congrFun hκ z
    rw [Pi.smul_apply, smul_eq_mul, E2, he₁] at h
    apply mul_right_cancel₀ hJ
    linear_combination -h
  have hκe : κ = ε₂ * c * μ / ε₁ := by rw [eq_div_iff hε0, key]

  obtain ⟨hxQ, hx1⟩ := det_unit hG p lam hb₁ hb₂ hl₁ hl₂
  have hζQ : ζ ∈ Qbar := qbar_of_pow hm (by rw [hζ]; exact one_mem _)
  have hcQ : c ∈ Qbar := qbar_of_pow two_pos (by rw [hc]; exact mul_mem hζQ hxQ)
  have hμQ : μ ∈ Qbar := qbar_of_pow (n := 8) (by norm_num) (by rw [hμ]; exact one_mem _)
  have hκQ : κ ∈ Qbar := by rw [hκe]; exact div_mem (mul_mem (mul_mem hε₂ hcQ) hμQ) hε₁
  refine ⟨hκQ, ?_⟩

  have L := fun {u v : ℂ} (hu : u ∈ Qbar) (hv : v ∈ Qbar) => GlobalTheory.BotFormula.lamC_mul lam hu hv
  have one : lamC lam 1 = 1 := by
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have pw : ∀ {u : ℂ} (hu : u ∈ Qbar) (n : ℕ), lamC lam (u ^ n) = lamC lam u ^ n := by
    intro u hu n
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, L (pow_mem hu n) hu, ih, pow_succ]
  have nμ : ‖lamC lam μ‖ = 1 := by
    have := congrArg norm (pw hμQ 8)
    rw [hμ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have nζ : ‖lamC lam ζ‖ = 1 := by
    have := congrArg norm (pw hζQ m)
    rw [hζ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  have nc : ‖lamC lam c‖ = 1 := by
    have := congrArg norm (pw hcQ 2)
    rw [hc, L hζQ hxQ, norm_mul, nζ, hx1, one_mul, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm
  have hk : ‖lamC lam (κ * ε₁)‖ = ‖lamC lam (ε₂ * c * μ)‖ := by rw [key]
  rw [L hκQ hε₁, L (mul_mem hε₂ hcQ) hμQ, L hε₂ hcQ, norm_mul, norm_mul, norm_mul, hn₁, hn₂, nc, nμ] at hk
  simpa using hk

theorem vacuum_ratio_isAlgUnit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
    ∀ {a d : ℕ} {e₁ e₂ : VC D a d → ℂ},
    oddE0 D ⊤ δ t0 a d e₁ → oddE0 D ⊤ δ t0 a d e₂ → ∃ ζ : ℂ, IsAlgUnit ζ ∧ e₂ = ζ • e₁ := by
  intro D hI δ t0 hC ht a d e₁ e₂ h₁ h₂
  have hG : admG1 D := hI.g1
  have hne : e₁ ≠ 0 := by
    intro h
    have hn := h₁.2.2.1
    rw [h] at hn
    have h0 : TaylorLogMetric.normSq D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) 0 = 0 := by simp [TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG ⊤ δ t0 hC ht) hn.symm
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC h₁ h₂ hne
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hκ1
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let lam2 : Qbar →+* ℂ_[2] := (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom
  refine ⟨κ, ⟨hκ0, (ratio_local hI hC ht h₁ h₂ hne hκ 2 lam2).1, fun p _ lam => ?_⟩, hκ⟩
  exact (ratio_local hI hC ht h₁ h₂ hne hκ p lam).2

end GlobalTheory.VacRatio

end
