import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaAtEqProdAhG
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOrientedModelEqOfRealAdelicPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdCharSymplecticRealAdelicPointsModelFormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnsMemPeriodLatticeIffFinitePartMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem modelW_of_tieIn {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (h : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) :
    ∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) := by
  subst hσ
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, hk⟩ := h.laws.modelW _ hj T.σ₀ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (_ : V = Wc D i) (hr' : V.rank = D.R.r) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r),
      ModelW V hr' X → ModelW (Wc D i) (rank_Wc i) X := by
    rintro V rfl hr' X hX
    exact hX
  exact fun k => key _ hV hr _ (hk k)

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.FinTranslate

theorem heis_law_of_periods : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.IsThP → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), IsONLatBasis (Vc D i) b →
    (∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k)) →
    ∀ (γ g : GA D (Wc D i)) (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt),
      PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E, (∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) →
      heisO R.ψ (Vc D i) (Wc D i) (-(ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr))
          (R.ωP i A.μ0 (1, γ * g) (R.vacP i)) =
        (∏ a, Y.χl (perVec Wt (colB b Yr a))) • R.ωP i A.μ0 (1, γ * g) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A T _ R hT i σ hV ph b hb hM γ g hx Wt Y hp Yr hcol
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hψ : IsStdChar D R.ψ (-1) := hW.std
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set Θ := R.ωP i A.μ0 (1, γ * g) (R.vacP i) with hΘdef
  have hΘ : IsThetaFunO R.ψ (Vc D i) (Wc D i) Θ := hW.om_pres _ _ hf
  choose α hα using hcol
  refine GlobalTheory.T.thetaFunction_orientedModel_eq_of_realAdelicPoints D R.ψ hψ (Vc D i) (Wc D i) _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hΘ _)
    (theta_smul _ hΘ) fun X => ?_
  have hth : ∀ w, thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * g) w = Θ w := fun w => thetaAt_eq _ _ _ _ _
  have e1 := theta_realPt_add hΘ X Yr
  have e2 := thetaAt_eq_prod_ahG hp (X + Yr)
  have e3 := thetaAt_eq_prod_ahG hp X
  rw [hth] at e2 e3
  have hcolAdd : ∀ a, perVec Wt (colB b (X + Yr) a) = pv Wt (colB b X a) + Wt.Pm (α a) := fun a => by
    rw [hα a]
    have : colB b (X + Yr) a = colB b X a + colB b Yr a := by
      funext m; simp only [colB, Matrix.add_apply, add_mul, Finset.sum_add_distrib, Pi.add_apply]
    rw [this]
    exact (pvHom Wt).map_add _ _
  have hG : ∀ a, ahG Y (perVec Wt (colB b (X + Yr) a)) = Y.χl (perVec Wt (colB b Yr a)) *
      Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).ξ0 *
        ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).Gm (colB b X a) (colB b Yr a)) : ℚ) : ℂ)) *
      ahG Y (perVec Wt (colB b X a)) := fun a => by
    rw [hcolAdd a, ahG_add_period, hα a]
    have him := im_hermForm_pv Wt Y (colB b X a) (colB b Yr a)
    change _ * Complex.exp (_ * ((hermForm Y.Hm (pv Wt (colB b X a)) (pv Wt (colB b Yr a))).im : ℂ)) * _ = _
    rw [him]
    push_cast
    rfl
  have hL : R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
      Complex.exp (Real.pi * Complex.I * ∑ a, ((Algebra.trace ℚ D.host.E
        (-((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).ξ0 *
        ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).Gm (colB b X a) (colB b Yr a)) : ℚ) : ℂ)) :=
    GlobalTheory.T.stdChar_symplectic_realAdelicPoints_modelForm D R.ψ hψ (Vc D i) (Wc D i) b hb D.R.r (rank_Wc i) _ (hM (dictW T i σ hV g).1) X Yr
  have hs : R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) ≠ 0 := by
    intro h0
    have := AddChar.map_add_eq_mul R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr))
      (-(symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have key : Θ (realPt (Vc D i) (Wc D i) (X + Yr)) = R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X)
      (realPt (Vc D i) (Wc D i) Yr)) * ((∏ a, Y.χl (perVec Wt (colB b Yr a))) * Θ (realPt (Vc D i) (Wc D i) X)) := by
    rw [e2, e3, hL, Finset.prod_congr rfl (fun a _ => hG a), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Complex.exp_sum, Finset.mul_sum]
    ring
  apply mul_left_cancel₀ hs
  rw [← e1, key, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.AHPhase

namespace GlobalTheory.AHPhase

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem psi_realPt_eq_exp_im : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.IsThP → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), IsONLatBasis (Vc D i) b →
    (∀ k, ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k)) →
    ∀ (g : GA D (Wc D i)) (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩) (Y : UnitAt Wt)
      (X Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
        Complex.exp (Real.pi * Complex.I *
          ∑ a, ((hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b Yr a))).im : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R hT i σ hV b hb hM g hx Wt Y X Yr
  have hψ : IsStdChar D R.ψ (-1) := (hT.ωP i A.μ0).std
  rw [GlobalTheory.T.stdChar_symplectic_realAdelicPoints_modelForm D R.ψ hψ (Vc D i) (Wc D i) b hb D.R.r (rank_Wc i) _ (hM (dictW T i σ hV g).1) X Yr]
  refine congrArg Complex.exp (congrArg (fun t => (Real.pi : ℂ) * Complex.I * t) (Finset.sum_congr rfl fun a _ => ?_))
  have h := im_hermForm_pv Wt Y (colB b X a) (colB b Yr a)
  change _ = (((hermForm Y.Hm (pv Wt (colB b X a)) (pv Wt (colB b Yr a))).im : ℝ) : ℂ)
  rw [h]
  push_cast
  rfl

theorem frame_phase : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (ph : ℂ)
    (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → IsONLatBasis (Vc D i) b →
    ∀ γ ∈ GQ (Wc D i), ∀ (g : GA D (Wc D i)), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ g →
    ∀ (hx : (dictW T i σ hV g).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV g).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV g).1 ⟨(dictW T i σ hV g).2, hx⟩)
      (Y : UnitAt Wt), PinAt T R i σ hV ph b γ g hx Wt Y →
    ∀ Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      ((∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) ↔
        actO (Vc D i) (Wc D i) 1 (γ * g)⁻¹ (ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) ∧
      ((∀ a, perVec Wt (colB b Yr a) ∈ Set.range Wt.Pm) →
        heisO R.ψ (Vc D i) (Wc D i) (-(ratW (Wc D i) (Vc D i) Yr - realPt (Vc D i) (Wc D i) Yr))
            (R.ωP i A.μ0 (1, γ * g) (R.vacP i)) =
          (∏ a, Y.χl (perVec Wt (colB b Yr a))) • R.ωP i A.μ0 (1, γ * g) (R.vacP i)) ∧
      ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
        R.ψ (symplOH (Vc D i) (Wc D i) (realPt (Vc D i) (Wc D i) X) (realPt (Vc D i) (Wc D i) Yr)) =
          Complex.exp (Real.pi * Complex.I *
            ∑ a, ((hermForm Y.Hm (perVec Wt (colB b X a)) (perVec Wt (colB b Yr a))).im : ℂ)) := by
  intro D hHP hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hL hGr hFa hMo hT hTie i σ hσ hV ph b hph hb γ hγ g hFr hx Wt Y hp Yr
  have hM := modelW_of_tieIn hTie i σ hσ hV
  exact ⟨GlobalTheory.T.columns_mem_periodLattice_iff_finitePart_movedLattice D hHP hSL hVF G Pl0 T0 A T R F κ v₀ hL hGr hFa hMo hT hTie i σ hσ hV ph b hph hb γ hγ g hFr hx Wt Y
      hp Yr,
    heis_law_of_periods D G Pl0 T0 A T R hT i σ hV ph b hb hM γ g hx Wt Y hp Yr,
    fun X => psi_realPt_eq_exp_im D G Pl0 T0 A T R hT i σ hV b hb hM g hx Wt Y X Yr⟩

end GlobalTheory.AHPhase
