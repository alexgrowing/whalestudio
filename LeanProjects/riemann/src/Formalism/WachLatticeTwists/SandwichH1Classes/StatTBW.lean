import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForScalarTwist

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

def StatTBW : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (U : Finset ℤ) (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r M0 h0 → R.TateX r → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    R.Tt.HTdec (VmW R L W) R.w U →
    ∀ (e d : ℕ) (D : TBData ℓ)
      (X : LLRest ℓ (e + 1) (fun k => ModuleCat.of ℤ_[ℓ] (H1 (repT R L (0 + k)))))
      (infm : ∀ k : ℕ, (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repD R L W (0 + k)))
      (infX : ∀ k : ℕ, (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repD R L W (0 + k)))
      (K : XiAdicFiltrationData ℓ) (T : Twist ℓ D.HGe) (_ : D.HYL ≃ₗ[ℤ_[ℓ]] X.HK) (_ : D.HWe ≃ₗ[ℤ_[ℓ]] K.H e), d ≠ 0 →

      (∀ k : ℕ, InfPin R L W (0 + k) (infm k) (infX k) ∧
        (pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)).InfRes ∧
        (pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)).T4) →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)).LES →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)).T5 →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (0 + k) (infm k) (infX k)).CorRes
        (ℓ ^ (mOf ℓ R.s (M0 + h0) - R.s)) →

      K.Inputs (R.χ R.γ) e → T.InfRes 1 → T.T4 → T.T3 → (∀ x : D.HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →

      ∀ (Gs : Type) [Group Gs] [TopologicalSpace Gs] [IsTopologicalGroup Gs]
        (M : Type) [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M] [T2Space M] [ContinuousAdd M]
        [ContinuousSMul ℤ_[ℓ] M]
        (MB : Type) [AddCommGroup MB] [Module ℤ_[ℓ] MB] [TopologicalSpace MB] [ContinuousAdd MB]
        [ContinuousSMul ℤ_[ℓ] MB]
        (aM : Representation ℤ_[ℓ] Gs M) (aB : Representation ℤ_[ℓ] Gs MB) (Fj : EqMap aM aB)
        (Hs : Subgroup Gs) (γs : Gs) (lg : Gs → ℤ_[ℓ]) (ε : ℤ_[ℓ]ˣ)
        (iGe : D.HGe ≃ₗ[ℤ_[ℓ]] H1 aM) (iB : D.HB ≃ₗ[ℤ_[ℓ]] H1 aB)
        (Os : Type) [AddCommGroup Os] [Module ℤ_[ℓ] Os] (cupL : Os →ₗ[ℤ_[ℓ]] D.HB)
        (embB : Os →ₗ[ℤ_[ℓ]] MB),
      Continuous lg → (∀ g h, lg (g * h) = lg g + lg h) → (∀ h ∈ Hs, lg h = 0) →
      (∀ S : Subgroup Gs, IsClosed (S : Set Gs) → Hs ≤ S → γs ∈ S → S = ⊤) →
      lg γs = (ε : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ R.s →
      (∀ x, iB (D.bW (D.gE x)) = Fj.onH (iGe x)) →
      (∀ y, ∃ c' : Z1 aB, (∀ σ, c'.1 σ = lg σ • embB y) ∧ iB (cupL y) = H1.mk aB c') →
      (∀ x : T.Wm, ∃ c : Z1 aM, H1.mk aM c = iGe (T.infm x) ∧ (∀ g, aM g (c.1 γs) = c.1 γs) ∧
        (∀ h ∈ Hs, c.1 h = 0) ∧ ((ℓ : ℤ_[ℓ]) ^ ceilE ℓ e) • Fj.f (c.1 γs) ∈ LinearMap.range embB) →

      D.La0 = LinearMap.range cupL → RVal D R.s e cupL →

      ∀ [Module ℚ_[ℓ] D.HV] [Module ℚ_[ℓ] D.HB] [FiniteDimensional ℚ_[ℓ] D.HV]
        [FiniteDimensional ℚ_[ℓ] D.HB] (exQ : D.HV →ₗ[ℚ_[ℓ]] D.HB) (Hfs : Submodule ℚ_[ℓ] D.HV) (δ : ℕ),
      (∀ z, exQ z = D.ex z) → (∀ (t : ℤ_[ℓ]) (x : D.HB), (t : ℚ_[ℓ]) • x = t • x) →
      Submodule.span ℚ_[ℓ] (D.La0 : Set D.HB) = ⊤ →
      Module.finrank ℚ_[ℓ] D.HV = Module.finrank ℚ_[ℓ] D.HB + δ →
      (∃ Lu : Submodule ℚ_[ℓ] D.HV, Lu ≤ Hfs ∧ Lu ≤ LinearMap.ker exQ ∧ Module.finrank ℚ_[ℓ] Lu = δ) →
      (∀ z ∈ Hfs, D.cor (D.pr z) ∈ D.HfK) → (∀ x, D.cor (D.res x) = d • x) →

      D.Comm → D.LES → D.DeRham → D.tateDualityKillsH2 R.s e →
      ((ℓ : ℤ_[ℓ]) ^ cTB ℓ R.s (mOf ℓ R.s (M0 + h0)) e (padicValNat ℓ d) U) • D.yK ∈ D.HfK

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
