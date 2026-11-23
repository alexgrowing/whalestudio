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
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalConjToSquareInertPlaceStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairVacInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem chr_det_eq_one {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (χ : Chr F E) (v : Pl F)
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

set_option maxHeartbeats 1000000 in

private theorem exists_skew_cayley {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (hlat : W.L.IsLattice E)
    (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hin : Formalism.UG.IsInertAt F E v w) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ Y : Matrix (Fin d) (Fin d) (AE F E),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro k hk
  obtain ⟨h2v, h3, -⟩ := hB.inert v w hin
  have hp0 : 0 < Ideal.absNorm v.asIdeal := by omega
  have hpv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨β, b, up, um, hβat, hβσ, hsc⟩ := GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place F E σ B hB d W v w hin
  have hKK : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have hKiK : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hKk : ∀ z ∈ GlobalTheory.InertSph.latAt W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := fun z hz => (hk.2 z hz).1
  have hKik : ∀ z ∈ GlobalTheory.InertSph.latAt W v, mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := fun z hz => (hk.2 z hz).2
  have hfk : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (mat k + mat k⁻¹ + 1 + 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem (add_mem (add_mem (hKk z hz) (hKik z hz)) hz) hz
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime F E d W hlat v _ hp0 hpv _ hfk
  obtain ⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1 := ⟨N - 1, by omega⟩
  have hh : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v :=
    fun z hz => by rw [algebraMap_smul]; exact GlobalTheory.DblVacGauss.invOf_two_smul_mem_latAt W v h2v hz
  have hh2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      (algebraMap (AF F) (AE F E) ⅟(2 : AF F) + algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z = z := by
    intro z _
    rw [← map_add, ← two_mul, mul_invOf_self', map_one, one_smul]
  obtain ⟨hYk, s1, s2, s3⟩ := GlobalTheory.TwoFacCore.units_mod (GlobalTheory.InertSph.latAt W v) (Ideal.absNorm v.asIdeal) (mat k) (mat k⁻¹) β b up um
    (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) N₀ hKK hKiK hKk hKik
    (fun z hz => ⟨(hsc z hz).1, (hsc z hz).2.1, (hsc z hz).2.2.1, (hsc z hz).2.2.2.1, hh z hz⟩)
    (fun z hz => (hsc z hz).2.2.2.2.1) hh2 (fun z hz => (hsc z hz).2.2.2.2.2.1) (fun z hz => (hsc z hz).2.2.2.2.2.2)
    hN _ rfl
  set Y := β • (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) with hYdef
  have hYat : At (evFin F v) Y := by
    intro u hu
    rw [hYdef, ← smul_assoc, hβat u hu, zero_smul]
  have hKat : At (evFin F v) (mat k - 1) := hk.1
  have keepAdd : ∀ {A C : Matrix (Fin d) (Fin d) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (A + C) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v :=
    fun hA hC z hz => by rw [Matrix.add_mulVec]; exact add_mem (hA z hz) (hC z hz)
  have keepSub : ∀ {A C : Matrix (Fin d) (Fin d) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (A - C) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v :=
    fun hA hC z hz => by rw [Matrix.sub_mulVec]; exact sub_mem (hA z hz) (hC z hz)
  have keepMul : ∀ {A C : Matrix (Fin d) (Fin d) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (A * C) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v :=
    fun hA hC z hz => by rw [← Matrix.mulVec_mulVec]; exact hA _ (hC z hz)
  have keepOne : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈
      GlobalTheory.InertSph.latAt W v := fun z hz => by rw [Matrix.one_mulVec]; exact hz
  refine ⟨Y, hYat, hYk, ?_, ?_, ?_, ?_⟩
  ·
    have hsa : GlobalTheory.TwoFacCore.SelfAdj σ (incM F W.J) (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) :=
      GlobalTheory.TwoFacCore.selfAdj_sub (GlobalTheory.TwoFacCore.selfAdj_one σ _) (GlobalTheory.TwoFacCore.selfAdj_pow (GlobalTheory.TwoFacCore.sa_gen k.2 (k⁻¹).2 hKK hKiK) _)
    unfold GlobalTheory.TwoFacCore.SelfAdj at hsa
    rw [hYdef, Matrix.transpose_smul, Matrix.smul_mul, hsa, GlobalTheory.TwoFacCore.smul_map, hβσ, Matrix.mul_smul, ← AlgHom.mapMatrix_apply,
      neg_smul, add_neg_cancel]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E d W hlat v _ hpv 1 isUnit_one _ ?_ (keepAdd keepOne hYk) s1
    rw [one_smul, add_sub_cancel_left]; exact hYat
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E d W hlat v _ hpv 1 isUnit_one _ ?_ (keepSub keepOne hYk) s2
    intro u hu
    rw [one_smul, sub_sub_cancel_left, smul_neg, hYat u hu, neg_zero]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E d W hlat v _ hpv 2 (isUnit_of_invertible _) _ ?_
      (keepAdd (keepAdd keepOne hYk) (keepMul hKk (keepSub keepOne hYk))) s3
    intro u hu
    have e : 1 + Y + mat k * (1 - Y) - (2 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) =
        Y + (mat k - 1) - mat k * Y := by
      rw [two_smul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, smul_sub, smul_add, ← Matrix.mul_smul, hYat u hu, hKat u hu, Matrix.mul_zero, add_zero, sub_zero]

private theorem twoFac {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (hlat : W.L.IsLattice E)
    (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hin : Formalism.UG.IsInertAt F E v w) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ W v,
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧ k = k₁ * k₂ := by
  intro k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    exists_skew_cayley B hB W hlat v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ d W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, GlobalTheory.InertTwoFac.mul_mem_KAt hk hh, h⁻¹, GlobalTheory.InertTwoFac.inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E d W v h2 _ (intY1 _ (hh.2 z hz).1)

private theorem inlD_mem_closure {σ : E →ₐ[F] E} (B : Base F E) (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (hlat : W.L.IsLattice E)
    (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hin : Formalism.UG.IsInertAt F E v w) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈
      Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) := by
  intro k hk
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hin).1
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M₁, a₁, b₁, c₁⟩, ⟨M₂, a₂, b₂, c₂⟩, rfl⟩ := twoFac B hB W hlat v w hin k hk
  rw [map_mul]
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := GlobalTheory.InertBigCell.inlD_eq_nab_mul_par h2 k₁ hk₁ M₁ a₁ b₁ c₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := GlobalTheory.InertBigCell.inlD_eq_nab_mul_par h2 k₂ hk₂ M₂ a₂ b₂ c₂
  rw [e₁, e₂]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s _ (Or.inr hn₁)) (s _ (Or.inl hp₁)))
    (Subgroup.mul_mem _ (s _ (Or.inr hn₂)) (s _ (Or.inl hp₂)))

section Pair

variable {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

private theorem dbl_line (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (hψ : PsiUnr B.ψ v)
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

private theorem parD_fix (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (hψ : PsiUnr B.ψ v)
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

private theorem nabD_fix (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w)
    (hψ : PsiUnr B.ψ v)
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
  obtain ⟨u, hu, hun⟩ := GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace F E σ B hP.base d W v w hin m hm
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

private theorem scalar_eq_one_inert : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v w, Formalism.UG.IsInertAt F E v w → GlobalTheory.PairVac.GoodPlace B M χX v →
      ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, ∀ c : ℂ, Acts (evFin F v) (om (1, g)) (M.vac v) (c • M.vac v) → c = 1 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v w hin hG k hk c hc
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
  have hgen := inlD_mem_closure B hP.base W hP.skew.lat v w hin k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ W v ∪ GlobalTheory.InertDbl.NabD σ W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact parD_fix hP v hG.psi hG.unr dd omd hdc hws R hR0 hRv g hg
    · exact nabD_fix hP v w hin hG.psi hG.unr dd omd hdc hws R hR0 hRv g hg
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

end GlobalTheory.PairVacInert

end

theorem _root_.GlobalTheory.T.inert_place_vacuum_eigenvalue : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v w, Formalism.UG.IsInertAt F E v w → GlobalTheory.PairVac.GoodPlace B M χX v →
      ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, ∀ c : ℂ, Acts (evFin F v) (om (1, g)) (M.vac v) (c • M.vac v) → c = 1 := GlobalTheory.PairVacInert.scalar_eq_one_inert
