import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomEq

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.Ker.I3.JetMomA

section Clauses

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

def TranslateJetMomentLawAnyIdempotentLevel : Prop :=
  ∀ (n m : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam m ε → 2 * n ≤ m → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (k : ℕ) (y : Fin k → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) (B.eNat χ N N' L L'))) = μ g

def LocallyConstantJetMomentLawAnyIdempotentLevel : Prop :=
  ∀ (n m : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam m ε → 2 * n ≤ m →
    ∀ Φ : LocallyConstant (Fin r → ℤ_[q]) ℂ, (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
    ∀ (k : ℕ) (y : Fin k → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (XiF D B.tor δ q n ε b Φ (B.eNat χ N N' L L'))) = μ g

end Clauses

section Stmts

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q])

def MomB : Prop :=
  ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D B.tor δ q L L' b →
      ∃ μ : Meas q r, TranslateJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ ∧ LocallyConstantJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ

def MomBN : Prop :=
  ∃ Ω : ℂ_[q], IsOmP lam B.tor.abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D B.tor δ q L L' b →
      ∃ μ : Meas q r, ‖μ‖ ≤ 1 ∧ TranslateJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ ∧ LocallyConstantJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ

def LiftIndep : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), admitted D N N' L L' → NNBasis D B.tor δ q L L' b →
    ∀ (n m m' : ℕ) (ε ε' : 𝓞 D.host.K), IsIdem D lam m ε → IsIdem D lam m' ε' → 2 * n ≤ m → 2 * n ≤ m' →
    ∀ yt : Fin r → Fin (q ^ n),
      Wop D B.tor q (liftY D B.tor δ q n ε b yt) (B.eNat χ N N' L L') =
        Wop D B.tor q (liftY D B.tor δ q n ε' b yt) (B.eNat χ N N' L L') ∧
      (∀ a : Fin r → ℤ_[q], kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt) =
        kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε' b yt)) ∧
      (∀ a : Fin r → Fin (q ^ n), kap D B.tor (vecN D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt) =
        kap D B.tor (vecN D B.tor δ q n b a) (liftY D B.tor δ q n ε' b yt))

variable (D) in

def IdemEx : Prop := ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε

end Stmts

section Zero

variable {D : D7} {q : ℕ} [Fact q.Prime]

theorem lamC_one (lam : Qbar →+* ℂ_[q]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dif_pos (one_mem _)]
  exact map_one lam

theorem isIdem_zero_one (lam : Qbar →+* ℂ_[q]) : IsIdem D lam 0 (1 : 𝓞 D.host.K) := by
  constructor <;> simp [lamC_one]

theorem isIdem_mono (lam : Qbar →+* ℂ_[q]) {m m' : ℕ} (ε : 𝓞 D.host.K) (h : IsIdem D lam m ε) (hm : m' ≤ m) :
    IsIdem D lam m' ε := by
  have hp : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  have hmono : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(m' : ℤ)) := zpow_le_zpow_right₀ hp (by omega)
  exact ⟨h.1.trans hmono, h.2.trans hmono⟩

theorem hf_zero_right (T : Tor D) {N N' : ℕ} (z : VC D N N') : Hf D T z 0 = 0 := by
  simp [Hf]

theorem kap_zero_right (T : Tor D) {N N' : ℕ} (x : VC D N N') : kap D T x 0 = 1 := by
  simp [kap, hf_zero_right]

theorem qH_zero (T : Tor D) {N N' : ℕ} : qH D T (0 : VC D N N') = 0 := by
  simp [qH, hf_zero_right]

theorem wPh_zero (T : Tor D) {N N' : ℕ} : wPh D T q (0 : VC D N N') = 1 := by
  unfold wPh
  rw [qH_zero]
  split_ifs
  · simp
  · have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (q : ℝ) ^ k * (0 : ℝ) = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
      ⟨1, 0, 0, by simp⟩
    obtain ⟨k, m, hm, hs⟩ := Classical.epsilon_spec hex
    rw [hs]
    have hm0 : m = 0 := by
      have h0 : (m : ℝ) = 0 := by rw [← hm, mul_zero]
      exact_mod_cast h0
    rw [hm0]
    simp

theorem wPh_of_int (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    wPh D T q x = Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) := by
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) = (-1 : ℂ) ^ m := by
    rw [h, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold wPh
  split_ifs with hq
  · rfl
  · rw [hE]
    have hex : ∃ s : ℂ, ∃ (k : ℕ) (m' : ℤ), (q : ℝ) ^ k * qH D T x = (m' : ℝ) ∧ s = (-1 : ℂ) ^ m' :=
      ⟨(-1 : ℂ) ^ m, 0, m, by rw [h]; simp, rfl⟩
    obtain ⟨k, m', hm', hs⟩ := Classical.epsilon_spec hex
    rw [hs]
    rw [h] at hm'
    have hm'' : m' = (q : ℤ) ^ k * m := by exact_mod_cast hm'.symm
    have hodd : Odd ((q : ℤ) ^ k) := by
      have := ((Fact.out : q.Prime).odd_of_ne_two hq).pow (n := k)
      exact_mod_cast this
    rw [hm'', zpow_mul, hodd.neg_one_zpow]

theorem wop_zero (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : Wop D T q (0 : VC D N N') G = G := by
  funext z
  simp [Wop, U, wPh_zero, hf_zero_right]

theorem liftY_zero {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' r : ℕ} (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (yt : Fin r → Fin (q ^ 0)) :
    liftY D (tor0 D cc δ) δ q 0 ε b yt = 0 := by
  have hy : ∀ i, ((yt i : ℕ)) = 0 := fun i => by
    have := (yt i).isLt
    simp at this
    omega
  funext τ i j
  simp [liftY, embV, tor0, hy]

end Zero

section Imp

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

theorem momE_of_translateJetMomentLaw (h : TranslateJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ) : MomE B χ lam Ω L L' b μ := by
  intro k y g hg
  have := h 0 0 1 (isIdem_zero_one lam) le_rfl (fun _ => 0) k y g (fun a => by
    rw [hg a, liftY_zero, kap_zero_right, lamC_one, one_mul])
  rwa [liftY_zero, wop_zero] at this

theorem firstMoment_of_idempotentLaw (h : TranslateJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ) : TranslateJetMomentLaw B χ lam Ω L L' b μ := by
  intro n ε hε yt k y g hg
  exact h n (2 * n + 2) ε hε (by omega) yt k y g hg

theorem secondMoment_of_idempotentLaw (h : LocallyConstantJetMomentLawAnyIdempotentLevel B χ lam Ω L L' b μ) : LocallyConstantJetMomentLaw B χ lam Ω L L' b μ := by
  intro n ε hε Φ hΦ hF k y g hg
  exact h n (2 * n + 2) ε hε (by omega) Φ hΦ hF k y g hg

theorem momSplit_of_momBN (h : MomBN B χ lam) : MomSplit D cc δ B χ q lam := by
  obtain ⟨Ω, hΩ, H⟩ := h
  refine ⟨Ω, hΩ, fun N N' L L' r b hA hB => ?_⟩
  obtain ⟨μ, hμ, h1, h2⟩ := H N N' L L' r b hA hB
  exact ⟨μ, hμ, momE_of_translateJetMomentLaw B χ lam Ω L L' b μ h1, firstMoment_of_idempotentLaw B χ lam Ω L L' b μ h1,
    secondMoment_of_idempotentLaw B χ lam Ω L L' b μ h2⟩

theorem momB_of_momBN (h : MomBN B χ lam) : MomB B χ lam := by
  obtain ⟨Ω, hΩ, H⟩ := h
  refine ⟨Ω, hΩ.1, fun N N' L L' r b hA hB => ?_⟩
  obtain ⟨μ, -, h1, h2⟩ := H N N' L L' r b hA hB
  exact ⟨μ, h1, h2⟩

theorem momBN_of_momSplit (hL : LiftIndep B χ lam) (hE : IdemEx D lam) (h : MomSplit D cc δ B χ q lam) :
    MomBN B χ lam := by
  obtain ⟨Ω, hΩ, H⟩ := h
  refine ⟨Ω, hΩ, fun N N' L L' r b hA hB => ?_⟩
  obtain ⟨μ, hμ, -, h1, h2⟩ := H N N' L L' r b hA hB
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro n m ε hε hm yt k y g hg
    obtain ⟨ε', hε'⟩ := hE (2 * n + 2)
    obtain ⟨hW, hk1, -⟩ := hL N N' L L' r b hA hB n m (2 * n + 2) ε ε' hε hε' hm (by omega) yt
    rw [hW]
    exact h1 n ε' hε' yt k y g (fun a => by rw [hg a, hk1 a])
  · intro n m ε hε hm Φ hΦ hF k y g hg
    obtain ⟨ε', hε'⟩ := hE (2 * n + 2)
    have hX : XiF D B.tor δ q n ε b Φ (B.eNat χ N N' L L') =
        XiF D B.tor δ q n ε' b Φ (B.eNat χ N N' L L') := by
      funext z
      simp only [XiF]
      refine congrArg (fun s => ((q : ℂ) ^ (n * r))⁻¹ * s) (Finset.sum_congr rfl fun a _ => ?_)
      refine congrArg (fun s => Φ (fun i => (((a i : ℕ) : ℤ_[q]))) * s)
        (Finset.sum_congr rfl fun yt _ => ?_)
      obtain ⟨hW, -, hk2⟩ := hL N N' L L' r b hA hB n m (2 * n + 2) ε ε' hε hε' hm (by omega) yt
      rw [hW, hk2 a]
    rw [hX]
    exact h2 n ε' hε' Φ hΦ hF k y g hg

theorem momSplit_iff_momBN (hL : LiftIndep B χ lam) (hE : IdemEx D lam) :
    MomSplit D cc δ B χ q lam ↔ MomBN B χ lam :=
  ⟨momBN_of_momSplit B χ lam hL hE, momSplit_of_momBN B χ lam⟩

end Imp

section Rec

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)

theorem packetMoment_of_splitMoments
    (h : ∀ (q : ℕ) [Fact q.Prime], JetMomA.SplitK D q → Nat.Coprime (Ideal.absNorm cc) q →
      ∀ lam : Qbar →+* ℂ_[q], MomSplit D cc δ B χ q lam) :
    mom22 D cc δ (B.eNat χ) := by
  intro p _ lam hs hcop
  obtain ⟨Ω, hΩ, H⟩ := h p hs hcop lam
  refine ⟨Ω, hΩ, fun N N' L L' r b hA hB => ?_⟩
  obtain ⟨μ, hμ, hE, -, h2⟩ := H N N' L L' r b hA hB
  exact ⟨μ, hμ, hE, fun n ε Φ hε hΦ hF m y g hg => h2 n ε hε Φ hΦ hF m y g hg⟩

theorem momentLawUnderBasisChange_iff_largerSupportMomentCondition :
    (∀ (q : ℕ) [Fact q.Prime], JetMomA.SplitK D q → Nat.Coprime (Ideal.absNorm cc) q →
      ∀ lam : Qbar →+* ℂ_[q], MomentLawUnderBasisChange B χ lam) ↔ LargerSupportMomentCondition D cc δ (B.eNat χ) := by
  constructor
  · intro h p _ lam hs hcop
    exact h p hs hcop lam
  · intro h q _ hs hcop lam
    exact h q lam hs hcop

theorem moments_of_jetMoments (h : JetMomT) (hc : IsCurveIdeal D cc) (hd : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : IsChi D χ) :
    B.MomP χ := by
  exact ⟨packetMoment_of_splitMoments B χ (fun q _ hs hcop lam => (h D cc δ B hc hd χ hχ q hs hcop lam).2.1),
    (momentLawUnderBasisChange_iff_largerSupportMomentCondition B χ).mp (fun q _ hs hcop lam => (h D cc δ B hc hd χ hχ q hs hcop lam).2.2)⟩

theorem splitIntegrality_of_packetIntegrality (h : int22 D B.tor (B.eNat χ)) {q : ℕ} [Fact q.Prime] (lam : Qbar →+* ℂ_[q])
    (hs : JetMomA.SplitK D q) (hd : q ≠ D.host.d) : IntSplit D cc δ B χ q lam := by
  intro N N' L L' hA F hF
  obtain ⟨-, h2, h3⟩ := (h q lam N N' L L' hA).1 hd F hF
  exact ⟨h3 hs, h2⟩

end Rec

section Merged

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)
  (G : VC D N N' → ℂ)

def MomEG : Prop :=
  ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
    (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) → jet D lam y (pSer D lam G) = μ g

def FirstMomentVectorLaw : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) G)) = μ g

def LocallyConstantJetMomentLawForVector : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε →
    ∀ Φ : LocallyConstant (Fin r → ℤ_[q]) ℂ, (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (XiF D B.tor δ q n ε b Φ G)) = μ g

end Merged

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q])

def MomComb : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    ∀ (m : ℕ) (t : Fin m → VC D N N') (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      (∀ k, TorsPrime D q (La D B.tor L L') (t k)) →
      (∀ k, admitted D N N' (L₁ k) (L₁' k) ∧ EqAt D q L (L₁ k) ∧ EqAt D q L' (L₁' k)) →
      ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ ∀ c : Fin m → ℂ, (∀ k, c k ∈ Qbar ∧ ‖lamC lam (c k)‖ ≤ 1) →
        ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D B.tor δ q L L' b →
          (∀ i, ∃ x ∈ La D B.tor L L', δ • embV D B.tor (b i) = s • x) →
          ∃ μ : Meas q r, ‖μ‖ ≤ 1 ∧
            MomEG lam Ω b μ (fun z => ∑ k, c k * U D B.tor (t k) (B.eNat χ N N' (L₁ k) (L₁' k)) z) ∧
            FirstMomentVectorLaw B lam Ω b μ (fun z => ∑ k, c k * U D B.tor (t k) (B.eNat χ N N' (L₁ k) (L₁' k)) z) ∧
            LocallyConstantJetMomentLawForVector B lam Ω b μ (fun z => ∑ k, c k * U D B.tor (t k) (B.eNat χ N N' (L₁ k) (L₁' k)) z)

def MomSplitR : Prop :=
  ∃ Ω : ℂ_[q], IsOmP lam B.tor.abelian₂ Ω ∧
    (∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D B.tor δ q L L' b →
      ∃ μ : Meas q r, ‖μ‖ ≤ 1 ∧ MomE B χ lam Ω L L' b μ ∧ TranslateJetMomentLaw B χ lam Ω L L' b μ ∧ LocallyConstantJetMomentLaw B χ lam Ω L L' b μ) ∧
    MomComb D cc δ B χ q lam Ω

def JetMomR : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (q : ℕ) [Fact q.Prime], JetMomA.SplitK D q → Nat.Coprime (Ideal.absNorm cc) q →
    ∀ lam : Qbar →+* ℂ_[q],
      IntSplit D cc δ B χ q lam ∧ MomSplitR D cc δ B χ q lam ∧ MomentLawUnderBasisChange B χ lam

theorem momSplit_of_momSplitR (h : MomSplitR D cc δ B χ q lam) : MomSplit D cc δ B χ q lam := by
  obtain ⟨Ω, hΩ, H, -⟩ := h
  exact ⟨Ω, hΩ, H⟩

theorem jetMomT_of_jetMomR (h : JetMomR) : JetMomT := by
  intro D cc δ B hc hd χ hχ q _ hs hcop lam
  obtain ⟨hI, hR, hM3⟩ := h D cc δ B hc hd χ hχ q hs hcop lam
  exact ⟨hI, momSplit_of_momSplitR D cc δ B χ q lam hR, hM3⟩

theorem firstMomentVectorLaw_iff {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r) :
    FirstMomentVectorLaw B lam Ω b μ (B.eNat χ N N' L L') ↔ TranslateJetMomentLaw B χ lam Ω L L' b μ := Iff.rfl

end Formalism.L2.Ker.I3.JetMomEq
