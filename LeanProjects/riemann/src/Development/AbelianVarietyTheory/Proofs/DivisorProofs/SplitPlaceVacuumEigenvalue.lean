import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAlStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentConjugateToSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLift

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairVacSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chr_det_eq_one {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (χ : Chr F E) (v : Pl F)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w)
    (t : GL (Fin d) (AE F E)) (ht : At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  obtain ⟨ht1, ht2⟩ := ht
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  haveI : Submodule.IsLattice E W.L := hL
  obtain ⟨P0, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame W.L v
  have hP := GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2
  set T := Formalism.UG.bc (compFin F E v) t with hTdef
  have hT : ∀ y ∈ latLoc F W.L v, T.1 *ᵥ y ∈ latLoc F W.L v :=
    GlobalTheory.SplitDetChr.mulVec_mem_latLoc W v _ (fun z hz => (ht2 z hz).1)
  have hT' : ∀ y ∈ latLoc F W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F W.L v := by
    rw [hTdef, ← map_inv]
    exact GlobalTheory.SplitDetChr.mulVec_mem_latLoc W v _ (fun z hz => (ht2 z hz).2)
  have hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T := by
    refine Units.ext ?_
    show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have hy := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT
  have hy' := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'
  rw [e1]
  show GlobalTheory.Doubling.charAt χ v _ = 1
  rw [hd]
  exact GlobalTheory.LFun.charAt_eq_one_of_unrAt χ v _ hy (by rwa [← map_inv]) hunr

theorem inlD_mem_closure {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl F)
    (hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈
      Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) := by
  intro k hk
  obtain ⟨c, hcσ, hcAt, hc2, hcL⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hsp
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ _ W v h2 c hcσ hcAt (hcL _ W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ _ W v h2 c hcσ (hcL _ W) k hk
  have hg := GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer F E σ _ W v k hk
  have hKK' : mat k * mat k⁻¹ = 1 := congrArg (fun g : UA σ W.J => g.1.1) (mul_inv_cancel k)
  have hK'K : mat k⁻¹ * mat k = 1 := congrArg (fun g : UA σ W.J => g.1.1) (inv_mul_cancel k)
  have hAtK : At (evFin F v) (mat k - 1) := hk.1
  have hAtK' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [Matrix.mul_sub, hK'K, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hAtK u hu, Matrix.mul_zero, neg_zero]
  have hc2M : ∀ M : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) M → (c * c) • M = M := by
    intro M hM
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc2 _ (fun u hu => by
      have h0 := congrFun (congrFun (hM u hu) i) j
      simpa using h0)
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k) (mat k⁻¹) hKK' (hc2M _ hAtK)
  have ht' := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k⁻¹) (mat k) hK'K (hc2M _ hAtK')
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E _ c (mat k) (mat k⁻¹) hKK' hK'K (hc2M _ hAtK)
  let T : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, ht'⟩
  have hinv : GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD n = 1 := GlobalTheory.DblVacFlip.matD_inv_mul n
  have hq : n⁻¹ * p * GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.ParD σ W v := by
    refine ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.inv_mem_KD hn.1) hp.1) hg, T, ?_⟩
    show GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD p * GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ W k) *
        diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    have h3 := congrArg (fun M => GlobalTheory.InertDbl.matD n⁻¹ * M) hid
    simp only [← Matrix.mul_assoc] at h3
    rw [GlobalTheory.InertDbl.matD_inlD, hpm]
    refine h3.trans ?_
    rw [← hnm, hinv]
    exact congrArg (· * GlobalTheory.SplitDblGen.tMat c (mat k)) (Matrix.one_mul _)
  have e : GlobalTheory.InertDbl.inlD σ W k = p⁻¹ * n * (n⁻¹ * p * GlobalTheory.InertDbl.inlD σ W k) := by group
  rw [e]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (s _ (Or.inl hp))) (s _ (Or.inr hn))) (s _ (Or.inl hq))

section Pair

variable {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem dbl_line (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (hψ : PsiUnr B.ψ v)
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd)
    (hS : IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd)
    (R : (Fin n × Fin d → AF F) → ℂ) (hR : Rest (evFin F v) (M.vac v) R) :
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R) :=
  fun g hg => GlobalTheory.DblVacLine.dbl_line hP.base.std v hψ hP.herm.lat hP.skew.lat
    (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hP.base hP.herm hP.skew v)
    M _ (hP.good.vac v) dd omd hdd hS R hR g hg

theorem parD_fix (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (hψ : PsiUnr B.ψ v)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w)
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ))
    (hdc : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd)
    (hws : IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd)
    (R : (Fin n × Fin d → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hRv : Rest (evFin F v) (M.vac v) R) :
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R) := by
  intro p hp
  set Ψ := tens (evFin F v) (M.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hP.good.vac v
  obtain ⟨y, hy⟩ : ∃ y, M.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := dbl_line hP v hψ dd omd hdc hws.2.1 R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ W v p hp t ht
  have ha := chr_det_eq_one W hP.skew.lat χX v hunr t htp
  have hb := GlobalTheory.IntegralDetModule.modu_norm_det W hP.skew.lat v t htp.1 htp.2
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]

theorem nabD_fix (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v)
    (hψ : PsiUnr B.ψ v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w)
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d))
    (omd : UG (cA σ) (dbl (incM F W.J)) →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ))
    (hdc : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd)
    (hws : IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd)
    (R : (Fin n × Fin d → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hRv : Rest (evFin F v) (M.vac v) R) :
    ∀ m ∈ GlobalTheory.InertDbl.NabD σ W v, omd m (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R) := by
  intro m hm
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (M.vac v) R) with hΦdef
  obtain ⟨c, hc⟩ := dbl_line hP v hψ dd omd hdc hws.2.1 R hRv m hm.1
  obtain ⟨u, hu, hun⟩ := GlobalTheory.T.adelicSchwartzSpace_le_span_pureTensors F E σ B hP.base d W v hsp h2 m hm
  have hs1 : omd u Φ = Φ := parD_fix hP v hψ hunr dd omd hdc hws R hR0 hRv u hu
  have hs2 : omd u⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e1 : omd (u * m * u⁻¹) Φ = c • Φ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs2, hc, map_smul, hs1]
  have e2 : omd (m * m) Φ = (c * c) • Φ := by
    rw [map_mul, Module.End.mul_apply, hc, map_smul, hc, smul_smul]
  rw [hun, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd m⁻¹ (omd m Φ) = Φ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hc, h0, zero_smul, map_zero]
  · rw [hc, h1, one_smul]

end Pair

theorem scalar_eq_one_split : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v (t : E →ₐ[F] Fv F v), GlobalTheory.PairVac.GoodPlace B M χX v →
      ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, ∀ c : ℂ, Acts (evFin F v) (om (1, g)) (M.vac v) (c • M.vac v) → c = 1 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t hG k hk c hc
  have hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := GlobalTheory.LFun.SplitChart.isSplit_of_algHom hP.base.cm t
  obtain ⟨-, dd, omd, hdc, hws, hres⟩ := hP.weil.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have hV := hP.good.vac v
  have hSB : M.vac v ∈ SB _ := hV.1
  have hne : M.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (M.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ W) :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := inlD_mem_closure B hP.base W v hsp hG.two k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact parD_fix hP v hG.psi hG.unr dd omd hdc hws R hR0 hRv g hg
    · exact nabD_fix hP v hsp hG.psi hG.two hG.unr dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om (1, k) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, M.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin n × Fin d → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin n × Fin d → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'

end GlobalTheory.PairVacSplit

end
