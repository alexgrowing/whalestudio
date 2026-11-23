import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdFstFix

variable {D : D7}

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = x := Matrix.ext fun i j => hx i j
  have e1 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    conv_rhs => rw [← hx']
    rw [Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  exact congrFun (congrFun e1 i) j

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem finCong_of_mem_GinfC {V : HSp D} (N : ℕ) {k : GA D V} (hk : k ∈ GinfC V) : GlobalTheory.Member.FinCong V N k := by
  have h1 : finHom V k = finHom V 1 := by rw [map_one]; exact hk
  have := GlobalTheory.Member.PrincLevel.finCong_one V N
  unfold GlobalTheory.Member.FinCong at this ⊢
  rw [h1]
  exact this

end GlobalTheory.StdFstFix

namespace GlobalTheory.StdFstFix

set_option maxHeartbeats 2000000 in

theorem stdFst_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  intro D T L sc G W i j A A' WW X hX t
  classical
  have hI := hX.is
  have hν : Continuous (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) := (hI.weil' t).hecT.1
  have he := hI.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hI.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hsdS.1.fg hsdT.1.fg X.rA.β X.rW.β
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A) hsdS.1 hsdT.1 X.rA.β X.rW.β
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D _ hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t :=
    ⟨_, Nat.pos_of_ne_zero fun h => GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t (Ideal.absNorm_eq_zero_iff.1 h),
      Ideal.absNorm_mem _⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ locPl G t, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ locPl G t, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  obtain ⟨m, hm⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (K * (n₀ * (n * c) * M)) (Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM))

  have key : ∀ g ∈ GfC (GlobalTheory.Grid.neg A), GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g → ∀ x : WO A WW,
      (IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
                   (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
                   (actO (GlobalTheory.Grid.neg A) WW g 1 x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
          (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
    intro g hg hgc x hx
    obtain ⟨l, hl', e1⟩ := hm g hg hgc (K • x) (hC x (GlobalTheory.PlaceDatum.infPart_of_half hinf hx.1) hx.2.1)
    have e2 : actO (GlobalTheory.Grid.neg A) WW g 1 x = x + (n₀ * (n * c) * M) • l := by
      have e3 : K • actO (GlobalTheory.Grid.neg A) WW g 1 x = K • (x + (n₀ * (n * c) * M) • l) := by
        rw [← actO_nsmul, e1, smul_add, smul_smul]
      rw [← GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK (actO (GlobalTheory.Grid.neg A) WW g 1 x), e3,
        GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK]
    refine StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_shift he hnI hl hcS A WW X.rA.β X.rW.β
      (W := fun i j => (M : Lev.EAf D) * frMapO A WW X.rA.β X.rW.β l i j)
      ⟨fun _ => hx.1, fun _ => isHalf_actO g 1 hx.1⟩ (fun i j => hB l hl' i j) fun i j => ?_
    rw [e2, GlobalTheory.PlaceDatum.frMapO_add]
    push_cast
    ring
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (GlobalTheory.Grid.neg A) m.factorial).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _
      (GlobalTheory.VacFixTarget.isOpen_congGroup (GlobalTheory.Grid.neg A) m.factorial_pos), fun k hk => ?_, fun k hkU hkf => ?_⟩
  · show GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k)
    refine finCong_of_mem_GinfC _ ?_
    rw [GlobalTheory.SgnIdent.mem_GinfC_sgn, MulEquiv.apply_symm_apply]
    exact hk
  · have hκf : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]
      exact hkf
    have hκc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k) := hkU
    refine ⟨fun u => ⟨fun hu => ?_, fun hu => ?_⟩, fun x => ?_⟩
    · obtain ⟨l, hl', e⟩ := hm _ hκf hκc u hu
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · obtain ⟨l, hl', e⟩ := hm _ (inv_mem hκf) (GlobalTheory.Member.PrincLevel.finCong_inv hκc) _ hu
      have e' := GlobalTheory.WeilVacMove.actO_inv_actO ((GlobalTheory.Grid.ofSgn true A).symm k) (1 : GA D WW) u
      rw [inv_one] at e'
      rw [e'] at e
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · rw [inv_one]
      set g := ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ with hgdef
      have hg : g ∈ GfC (GlobalTheory.Grid.neg A) := inv_mem hκf
      have hgc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g := GlobalTheory.Member.PrincLevel.finCong_inv hκc
      by_cases hx : IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
          ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)
      · exact key g hg hgc x hx
      · by_cases hx' : IsHalf (X.e t) (actO (GlobalTheory.Grid.neg A) WW g 1 x) ∧
            IsIntM (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x)) ∧
            ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t)
              (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x) i j)
        · have h2 := key g⁻¹ (inv_mem hg) (GlobalTheory.Member.PrincLevel.finCong_inv hgc) _ hx'
          have e' := GlobalTheory.WeilVacMove.actO_inv_actO g (1 : GA D WW) x
          rw [inv_one] at e'
          rw [e'] at h2
          exact h2.symm
        · unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
          rw [if_neg hx, if_neg hx']

end GlobalTheory.StdFstFix
