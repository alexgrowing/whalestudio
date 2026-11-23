import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.CgMod

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

def restr (S : AddSubgroup M) (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) : S ≃ₜ+ S where
  toFun s := ⟨U s.1, hU _ s.2⟩
  invFun s := ⟨U.symm s.1, hU' _ s.2⟩
  left_inv s := Subtype.ext (U.left_inv s.1)
  right_inv s := Subtype.ext (U.right_inv s.1)
  map_add' x y := Subtype.ext (map_add U x.1 y.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

def dbl [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M) (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0)
    (h3 : ∀ x, P x + L (P (L.symm x)) = x) : (S × S) ≃ₜ+ M where
  toFun p := p.1.1 + L p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨P (L.symm x), hPm _⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + L p.2.1) = p.1.1
      rw [map_add, hPs _ p.1.2, h1 _ p.2.2, add_zero]
    · change P (L.symm (p.1.1 + L p.2.1)) = p.2.1
      have hl : L.symm (L p.2.1) = p.2.1 := L.left_inv _
      rw [map_add, map_add, h2 _ p.1.2, zero_add, hl, hPs _ p.2.2]
  right_inv x := h3 x
  map_add' p q := by
    change (p.1.1 + q.1.1) + L (p.2.1 + q.2.1) = (p.1.1 + L p.2.1) + (q.1.1 + L q.2.1)
    rw [map_add]; abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := (hPc.subtype_mk _).prodMk ((hPc.comp L.symm.continuous).subtype_mk _)

theorem char_sq [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M)
    (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0) (h3 : ∀ x, P x + L (P (L.symm x)) = x)
    (U : M ≃ₜ+ M) (hUL : ∀ x, U (L x) = L (U x)) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) :
    addEquivAddHaarChar (restr S U hU hU') ^ 2 = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  set Ψ := dbl S P hPc hPm hPs L h1 h2 h3 with hΨ
  set T := restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T T)).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T T (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + L (U p.2.1) = U (p.1.1 + L p.2.1)
    rw [map_add, hUL]
  rw [sq, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ (GlobalTheory.ModuLR.prodCE T T), e]

end Abstract

theorem exists_anti {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, hc, -, hs⟩ := h
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hv : v.IsComplex := hc.isComplex v
  have hsq : ∀ x, σ (σ x) = x := fun x => v.embedding.injective (by rw [hs, hs]; simp)
  have hx : ∃ x, σ x ≠ x := by
    by_contra hn
    push_neg at hn
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hv
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hs v.embedding x
    rw [hn] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hx
  exact ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, hsq]; abel⟩

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol

variable {D : D7} {n : ℕ}

theorem cA_incA (D : D7) (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [cA, sigR, incA, inclR]

theorem hermPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ hermA D n) :
    hermPart D n (c • s) = 0 := by
  have h : adj s = s := hs
  rw [hermPart, adj_smul, h, hc, neg_smul, add_neg_cancel, smul_zero]

theorem hermPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    hermPart D n x + d • hermPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [hermPart, hermPart, adj_smul, he, neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  exact (add_add_sub_cancel _ _ _).trans (half_smul_add x)

set_option synthInstance.maxHeartbeats 400000 in

def mulCE (d e : AE D) (hde : d * e = 1) : Mx D n n ≃ₜ+ Mx D n n where
  toFun x := d • x
  invFun x := e • x
  left_inv x := by
    change e • d • x = x
    rw [smul_smul, mul_comm, hde, one_smul]
  right_inv x := by
    change d • e • x = x
    rw [smul_smul, hde, one_smul]
  map_add' := smul_add d
  continuous_toFun := continuous_const_smul d
  continuous_invFun := continuous_const_smul e

def hermPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (hermPart D n) hermPart_add

set_option maxHeartbeats 400000 in
theorem val_det_ad_inv (a : GL (Fin n) (AE D)) :
    ((Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) : AE D) = cA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  change (adj a.1 : Mx D n n).det = cA D a.1.det
  rw [adj, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem absA_det_ad_inv (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  have h : (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := Units.ext (val_det_ad_inv a)
  rw [h]
  exact GlobalTheory.DiagThetaRule.absA_conj D _

theorem exists_anti_units (D : D7) : ∃ d e : AE D, d * e = 1 ∧ cA D d = -d ∧ cA D e = -e := by
  obtain ⟨δ, hδ, hσ⟩ := exists_anti _ (isCMExt_host D)
  refine ⟨incA D δ, incA D δ⁻¹, ?_, ?_, ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  · rw [cA_incA, hσ, map_neg]
  · rw [cA_incA, map_inv₀, hσ, inv_neg, map_neg]

theorem lr_herm (a : GL (Fin n) (AE D)) : ∀ s ∈ hermA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ hermA D n :=
  fun s hs => (cg a ⟨s, hs⟩).2

theorem lr_herm_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ hermA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ hermA D n :=
  fun s hs => (cg a⁻¹ ⟨s, hs⟩).2

theorem lr_smul (a : GL (Fin n) (AE D)) (d e : AE D) (hde : d * e = 1) (x : Mx D n n) :
    GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ (mulCE d e hde x) = mulCE d e hde (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ x) := by
  change a.1 * (d • x) * ((ad a)⁻¹ : GL (Fin n) (AE D)).1 = d • (a.1 * x * ((ad a)⁻¹ : GL (Fin n) (AE D)).1)
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem integral_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  intro D n lam hlam a f
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (isClosed_hermA (D := D) (r := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h : ∫ c, f (cg a c) ∂lam = _ := integral_comp_char lam (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) f
  rw [h, hT, npow_neg_nat (absA_pos _) n]

end GlobalTheory.CompanionTheory.CgMod
