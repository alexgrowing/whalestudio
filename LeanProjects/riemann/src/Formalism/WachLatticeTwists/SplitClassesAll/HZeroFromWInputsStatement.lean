import Formalism.WachLatticeTwists.SplitClassesAll.HZeroFromWFull
import Formalism.WachLatticeTwists.DenseTopActions.StatementC

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Matrix Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JW Polynomial
open scoped TensorProduct

def TBWIn {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ) (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) : Prop :=
  ∀ P : Prop, (∀ (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
      (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
      (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
      (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
      R.Facts r M0 h0 → R.TateX r → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
      A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
      Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
      R.Tt.HTdec (VmW R L W) R.w U →
      ∀ (X : LLRest ℓ (e + 1) (fun k => ModuleCat.of ℤ_[ℓ] (H1 (repT R L (0 + k)))))
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
        u = R.χ R.γ → w = R.w → s = R.s → m = mOf ℓ R.s (M0 + h0) → P
) → P

def hZeroFromWInputs {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (Uτ : Finset ℤ) : Prop :=
  ∀ P : Prop, (∀ (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
      (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
      (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
      (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
      R.Facts r M0 h0 → R.FactsH → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
      A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
      Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
      ∀ (ρ : ℕ) (Sτ : SL R.actO ρ) (Pp : Matrix (Fin r) (Fin ρ) R.OC) (Sp : Matrix (Fin ρ) (Fin r) R.OC)
        (Cm : Matrix (Fin ρ) (Fin r) R.Tt.Om) (Bm : Matrix (Fin r) (Fin ρ) R.Tt.Om),
      R.TateX ρ → (∀ g, Pp.map (R.actO g) * Sτ.Mx g = (L.sl R.actO).Mx g * Pp) → Sp * Pp = 1 →
      A.map R.ϑ * Pp = Bm.map R.eOh * (Cm.map R.eOh * (A.map R.ϑ * Pp)) →
      R.Tt.HTdec (Cm * VmW R L W * Bm) R.w Uτ → 0 ∉ Uτ → Uτ.Nonempty →
      ∀ (infm : (Fin ρ → R.Tt.Om) →ₗ[ℤ_[ℓ]]
          H1 (repU R (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh) 0))
        (infX : (Fin ρ → R.Tt.Xm) →ₗ[ℤ_[ℓ]]
          H1 (repU R (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh) 0))
        (X : InvariantsRemainingGroups ℓ (ModuleCat.of ℤ_[ℓ] (H1 (repS R Sτ 0))) (ModuleCat.of ℤ_[ℓ] (inv0 R Sτ))),
      (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX).InfRes →
      (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX).T4 →
      (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).Union →
      (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).Flat →
      (X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX)).LES →
      D = X.toH0 (pieceB R Sτ (fun g => (Cm.map R.eOh).map (R.actO g) * UmW R L W g * Bm.map R.eOh)
        (Cm * VmW R L W * Bm) (Cm.map R.eOh * (A.map R.ϑ * Pp)) (Sp * Y' * Bm.map R.eOh) 0 infm infX) →
      w = R.w → m = mOf ℓ R.s (M0 + h0) → P
) → P

def StatTBWIn : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (D : TBData ℓ) (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ),
    TBWIn D u w s m e d U → TBFullIn D u w s m e d U

def HZeroFromWInputsStatement : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (Uτ : Finset ℤ),
    hZeroFromWInputs D w m Uτ → HZeroHypotheses D w m Uτ

def hZeroFromWJumps {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (J : Multiset ℤ) : Prop :=
  (-1 : ℤ) ∉ J ∧ J ≠ 0 ∧ hZeroFromWInputs D w m (jumpsDualTwist J)

def HZeroFromWJumpsStatement : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ) (w : ℤ_[ℓ]ˣ) (m : ℕ) (J : Multiset ℤ),
    hZeroFromWJumps D w m J → HZeroHypothesesJumps D w m J

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def RowInW (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    [SMulCommClass A O M] (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) (deg : ℕ) : Prop :=
  F ≤ Hc ∧
  (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
      (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
      ∃ B : TBBridge ℓ F.toAddSubgroup
          (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)),
        TBWIn B.D u w s m e d U) ∧
  QuotShape Hc F deg

end Defs

def StatRowInW : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) (deg : ℕ),
    RowInW ℓ M r χ E Dw Hc F u w s m e d U deg → RowIn ℓ M r χ E Dw Hc F u w s m e d U deg

def WFromFirstPredicates : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (Lt : Lat ℓ R.Gg r)
    (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Algebra ℤ_[ℓ] O]
    (S : HidaSetting O A)
    (ι : Type) [Finite ι] (pr : Equiv.Perm ι) (D : Type) [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] (W : NData S ι pr D) [Algebra ℤ_[ℓ] R.As] (jS : R.As →+* (ι → A))
    (φs : R.As →+* R.As)
    (C : Cmp W jS R.jA R.ι R.φ R.Hs R.act Lt.ρ) (M h : ι → ℕ) (M0 h0 : ℕ)
    (κ : Type) [Fintype κ] (e : Module.Basis κ ℤ_[ℓ] O) (Ψ : TensorProduct ℤ_[ℓ] R.As O ≃+ (ι → A))
    (r₀ : ℕ) (c : ι → Fin r₀ → D) (eq : κ × Fin r₀ ≃ Fin r) (EO : O → Matrix (Fin r) (Fin r) ℤ_[ℓ]),
    R.ξ = xiOf S.ℓ S.s R.πs →
    (∀ i, jS R.πs i = S.π) → (∀ a i, jS (φs a) i = S.φ (jS a (pr i))) →
    (∀ a o, Ψ (a ⊗ₜ o) = jS a * fun _ => algebraMap O A o) →
    (∀ i m, c i m ∈ W.N i) →
    (∀ i, ∀ x ∈ W.N i, ∃ a : Fin r₀ → A, x = ∑ m, a m • c i m) →
    (∀ i (a : Fin r₀ → A), ∑ m, a m • c i m = 0 → a = 0) →
    W.P5 M h → (∀ i, M i ≤ M0) → (∀ i, h i ≤ h0) → GammaTrivialModUniformizers C R.πs →
    ComparisonMatrixInvertible C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2) → OLin C EO →
    ∃ Y : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r Lt.ρ (Set.range EO) R.πs R.ξ M0 h0,
      Y.Xx = xMat C (fun k i => e (eq.symm k).1 • c i (eq.symm k).2)

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
