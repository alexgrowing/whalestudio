import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical
open Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.IndefiniteRowSideFullHecke.MomentCombSplitting

section Good

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

def InMul (N₀ : ℕ) (x : VC D N N') : Prop := ∃ x' ∈ La D (tor0 D cc δ) L L', x = N₀ • x'

def GoodLift (N₀ n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  AdmLift D lam cc δ L L' n A ∧ ∃ k : ℕ, InMul D cc δ L L' N₀ (p ^ k • vecOf D cc δ A)

def GoodBasis (p N₀ : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  NNBasis D (tor0 D cc δ) δ p L L' b ∧ ∀ i, InMul D cc δ L L' N₀ (vecOf D cc δ (b i))

def CombShape (p : ℕ) {m : ℕ} (t : Fin m → VC D N N')
    (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∀ k, TorsPrime D p (La D (tor0 D cc δ) L L') (t k) ∧ admitted D N N' (L₁ k) (L₁' k) ∧
    EqAt D p L (L₁ k) ∧ EqAt D p L' (L₁' k)

def CombCoef {m : ℕ} (c : Fin m → ℂ) : Prop := ∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))

end Good

section Clauses

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)
  {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

def comb {m : ℕ} (c : Fin m → ℂ) (t : Fin m → VC D N N')
    (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : VC D N N' → ℂ :=
  fun z => ∑ k, c k * U D B.tor (t k) (B.eNat χ N N' (L₁ k) (L₁' k)) z

def IsMeasOf (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) (μ : Meas p r) : Prop :=
  IsRMeas μ ∧ IsTransform D lam Ω b μ (pSer D lam G) ∧
  ∀ μ' : Meas p r, IsTransform D lam Ω b μ' (pSer D lam G) → μ' = μ

def GoodTranslate (N₀ : ℕ) (G : VC D N N' → ℂ) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), GoodLift D lam cc δ L L' N₀ n A →
    AlgEntire D (Wop D B.tor p (vecOf D cc δ A) G) ∧
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
      ∀ (r' : ℕ) (b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b' →
        ∃ c' : Fin r' → D.host.K, IsCoords D lam cc b' A c' ∧
          IsTranslate D lam cc δ C wq b' (pSer D lam G)
            (fun i => parPt lam B.L C (δ * D.host.φ₀ (c' i : D.host.E)))
            (atLog D lam (lamOf D cc δ) C wq b' (pSer D lam (Wop D B.tor p (vecOf D cc δ A) G)))

def GoodChar (N₀ : ℕ) (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) (μ : Meas p r) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), GoodLift D lam cc δ L L' N₀ n A →
    ∃ ψ : C(Fin r → ℤ_[p], ℂ_[p]),
      (∀ a : Fin r → ℤ, ψ (fun i => (a i : ℤ_[p])) =
        lamC lam (kap D B.tor (vecOf D cc δ (∑ i, (a i : D.host.E) • b i)) (vecOf D cc δ A))) ∧
      IsTransform D lam Ω b (wt ψ μ) (pSer D lam (Wop D B.tor p (vecOf D cc δ A) G))

def XiAlgOf (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) (μ : Meas p r) : Prop :=
  ∀ Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ, (∀ a, Φ a ∈ Qbar) → ∀ n : ℕ, FactorsMod n Φ →
    ∀ ε : 𝓞 D.host.K, IsIdem D lam (2 * n) ε →
      AlgEntire D (XiF D B.tor δ p n ε b Φ G) ∧
      XiMoments D lam Ω b μ (Φ.map (lamC lam)) (pSer D lam (XiF D B.tor δ p n ε b Φ G))

def XiPadicOf (_B : Base D cc δ) (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ)
    (μ : Meas p r) : Prop :=
  ∀ Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ_[p], ∀ n : ℕ, FactorsModP n Φ →
    ∀ ε : 𝓞 D.host.K, IsIdem D lam (2 * n) ε → XiMoments D lam Ω b μ Φ (XiP D lam cc δ n ε b Φ G)

def MomOf (N₀ : ℕ) (Ω : ℂ_[p]) (G : VC D N N' → ℂ) : Prop :=
  AlgEntire D G ∧ GoodTranslate B lam L L' N₀ G ∧
  ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D B.tor δ p L L' b →
    ∃ μ : Meas p r, IsMeasOf lam Ω b G μ ∧ GoodChar B lam L L' N₀ Ω b G μ ∧
      (GoodBasis D cc δ L L' p N₀ b → XiAlgOf B lam Ω b G μ ∧ XiPadicOf lam B Ω b G μ)

def CombMom (Ω : ℂ_[p]) : Prop :=
  ∀ (m : ℕ) (t : Fin m → VC D N N') (L₁ : Fin m → Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Fin m → Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), CombShape D cc δ L L' p t L₁ L₁' →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      ∀ c : Fin m → ℂ, CombCoef lam c → MomOf B lam L L' N₀ Ω (comb B χ c t L₁ L₁')

end Clauses

def MomCombAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ Ω : ℂ_[p], IsPeriod lam B Ω ∧
    ∀ N N' L L', admitted D N N' L L' →
      MomTranslate B χ lam L L' ∧ MomIndicator B χ lam L L' ∧
      (∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D B.tor δ p L L' b →
        ∃ μ : Meas p r, IsMeasE B χ lam L L' Ω b μ ∧ MomChar B χ lam L L' Ω b μ ∧
          MomXiAlg B χ lam L L' Ω b μ ∧ MomXiPadic B χ lam L L' Ω b μ) ∧
      CombMom B χ lam L L' Ω

def IntMomCombSplit : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (χ : IdE D → ℂ), IsChi D χ →
      ∀ (p : ℕ) [Fact p.Prime], SplitK D p → Nat.Coprime (Ideal.absNorm cc) p →
        ∀ lam : Qbar →+* ℂ_[p], HidaSetting B lam ∧ IntAt B χ lam ∧ MomCombAt B χ lam

theorem IntMomCombSplit.intMomSplit (h : IntMomCombSplit) : IntMomSplit := by
  intro D cc hc δ hδ B χ hχ p _ hs hp lam
  obtain ⟨h1, h2, Ω, hΩ, h3⟩ := h D cc hc δ hδ B χ hχ p hs hp lam
  exact ⟨h1, h2, Ω, hΩ, fun N N' L L' hA =>
    ⟨(h3 N N' L L' hA).1, (h3 N N' L L' hA).2.1, (h3 N N' L L' hA).2.2.1⟩⟩

theorem ne_zero_of_coprime {p N₀ : ℕ} [hp : Fact p.Prime] (h : Nat.Coprime N₀ p) : N₀ ≠ 0 := by
  rintro rfl
  exact hp.out.one_lt.ne' (by simpa using h)

theorem vecOf_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (n : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : vecOf D cc δ ((n : D.host.E) • A) = n • vecOf D cc δ A := by
  funext τ i j
  simp [vecOf, embV, tor0]
  ring

theorem goodBasis_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime] {N N' r N₀ : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₀ : Nat.Coprime N₀ p) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : NNBasis D (tor0 D cc δ) δ p L L' b) :
    GoodBasis D cc δ L L' p N₀ (fun i => (N₀ : D.host.E) • b i) := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hb
  have hne : (N₀ : D.host.K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_zero_of_coprime h₀)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · have := h1.units_smul (fun _ => Units.mk0 (N₀ : D.host.K) hne)
    convert this using 2 with i
    simp only [Pi.smul_apply', Units.smul_mk0, Nat.cast_smul_eq_nsmul]
  · intro i
    obtain ⟨s, hs, hm⟩ := h2 i
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hm _
  · intro y hy
    obtain ⟨s, hs, c, hc⟩ := h3 y hy
    refine ⟨N₀ * s, Nat.Coprime.mul_left h₀ hs, c, ?_⟩
    rw [Nat.cast_mul, mul_smul, hc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · intro i
    change vecOf D cc δ ((N₀ : D.host.E) • b i) ∈ _
    rw [vecOf_nsmul]
    exact nsmul_mem (h4 i) _
  · intro i
    exact ⟨vecOf D cc δ (b i), h4 i, vecOf_nsmul D cc δ N₀ (b i)⟩

theorem goodLift_one (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (n : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : GoodLift D lam cc δ L L' 1 n A ↔ AdmLift D lam cc δ L L' n A :=
  ⟨fun h => h.1, fun h => ⟨h, h.1.imp fun _ hk => ⟨_, hk, (one_nsmul _).symm⟩⟩⟩

theorem goodLift_smul (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (N₀ s n : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) (h : AdmLift D lam cc δ L L' n A) :
    GoodLift D lam cc δ L L' N₀ n (((N₀ * s : ℕ) : D.host.E) • A) := by
  obtain ⟨⟨k, hk⟩, ⟨s₁, h1, h1'⟩, ⟨s₂, h2, h2'⟩⟩ := h
  refine ⟨⟨⟨k, ?_⟩, ⟨s₁, h1, ?_⟩, ⟨s₂, h2, ?_⟩⟩, k, s • (p ^ k • vecOf D cc δ A), nsmul_mem hk _, ?_⟩
  · rw [vecOf_nsmul, smul_comm]
    exact nsmul_mem hk _
  · rw [smul_comm _ ((N₀ * s : ℕ) : D.host.E), smul_comm _ ((N₀ * s : ℕ) : D.host.E), Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h1' _
  · rw [smul_comm _ ((N₀ * s : ℕ) : D.host.E), smul_comm _ ((N₀ * s : ℕ) : D.host.E), Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h2' _
  · rw [vecOf_nsmul, smul_comm, mul_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.MomentCombSplitting
