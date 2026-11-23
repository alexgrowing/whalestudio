import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionSplitProductDatumIsPureTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsLocalLevelAtPrimeOfLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumValueEqProdLocalResidueValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistDatumValueEqProdLocalResidueValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLevelDatumEqFunctionOfResidueReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTwistDatumEqFunctionOfResidueReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitHalfResidueReductionFunctionEqFrameLocalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdResidueFunctionsHalfSumIdempotentsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infPart_idemAt {a : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a PP) : infPart D a = 0 := by
  classical
  have hs : IsIdemSum a {PP} := ⟨⟨fun _ => a, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact h, by simp⟩, h.1.2.1⟩
  exact GlobalTheory.PlaceDatum.infPart_idemSum hs

theorem prime_eq_of_idem {a : AE D} {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a P)
    (h' : Formalism.L2.NTheta.IsIdemAt a P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · exact (h.2 x hx).trans (h'.2 x hx).symm

set_option maxHeartbeats 2000000 in
theorem stepVecLocal : ∀ D : D7, StepVecLocal D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f μ 𝓕 t ht Hl cl hP hB hC _ _ hdisj hv
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, hth⟩ := hv
  have hSd : IsSelfDualC S ΛS := hB.2.2.1
  have hTd : IsSelfDualC T ΛT := hB.2.2.2.1
  have hψ : IsStdChar D ψ (-1) := base_std hB

  generalize hs : LS.Pg ∪ Q = s at *
  have hPs : ∀ PP, PP ∈ LS.Pg → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_left _ h
  have hQs : ∀ PP, PP ∈ Q → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_right _ h
  have hsum := GlobalTheory.T.splitIdempotent_prime_projection_correspondence D
  choose vP φP hφ hpr using fun i : ↥s => hsum.1 (es i.1) i.1 (hes i.1 i.2)
  choose rP hrP using fun i : ↥s => (show ∃ r, IsRedMap (φP i) i.1 r from
    let ⟨r, h⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).1; ⟨r, h⟩)

  let ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ := fun PP =>
    if h : PP ∈ LS.Pg then gLoc LS PP (Hl ⟨PP, h⟩) (cl ⟨PP, h⟩) (χ PP) else qLoc LS.r PP (ξ PP)
  let Φ : ↥s → WO S T → ℂ := fun i => locFn S T βS βT (es i.1) i.1 (ω i.1)
  have hPi : ∀ i : ↥s, (Formalism.L2.NTheta.IsIdemAt (es i.1) i.1) := fun i => hes i.1 i.2
  have hsplit : ∀ i : ↥s, IsSplitIdem D (es i.1) ∧ es i.1 + cA D (es i.1) = idem D (.inl (vP i)) := fun i =>
    ⟨(hφ i).1, (hφ i).2.1⟩
  obtain ⟨K, hK, hKC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hSd.1 hTd.1 βS βT
  have hsb : ∀ i : ↥s, IsSBHalf (es i.1) (latO S T ΛS ΛT fun _ => True) (Φ i) := fun i =>
    GlobalTheory.PlaceDatum.isSBHalf_of_red (es i.1) _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO hSd.1.fg hTd.1.fg βS βT)
      ⟨K, hK, fun t ht => hKC t (GlobalTheory.PlaceDatum.infPart_of_half (infPart_idemAt (hPi i)) ht)⟩ {i.1}
      (fun y => ω i.1 (y i.1)) (fun y y' h => by rw [h i.1 (Finset.mem_singleton_self _)])

  have hcmpG : ∀ (i : ↥s) (hi : i.1 ∈ LS.Pg) (J : Subgroup (GL (Fin S.rank) ((vP i).adicCompletionIntegers D.host.F)))
      (lam : J →* ℂˣ) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), IsLocLevel (φP i) i.1 LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩) J lam →
      LiftsChar (φP i) i.1 mu (χ i.1) →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = Φ i := by
    intro i hi J lam mu hJ hmu
    have h1 : (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = viaRed (rP i) (ω i.1) := by
      funext y
      rw [GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ t ht LS _ _ J lam hJ mu (χ i.1) hmu y]
      simp only [ω, dif_pos hi]
    rw [h1]
    exact GlobalTheory.T.splitHalf_residueReduction_function_eq_frameLocal D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)
  have hcmpQ : ∀ (i : ↥s) (hi : i.1 ∈ Q) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), LiftsChar (φP i) i.1 mu (ξ i.1)⁻¹ →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (phiQ (vP i) LS.r mu) = Φ i := by
    intro i hi mu hmu
    have hn : i.1 ∉ LS.Pg := fun h => Finset.disjoint_left.1 hdisj h hi
    have h1 : phiQ (vP i) LS.r mu = viaRed (b := T.rank) (a := S.rank) (rP i) (ω i.1) := by
      funext y
      rw [GlobalTheory.T.thetaTwistDatum_eq_function_of_residueReduction D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ LS.r mu (ξ i.1) hmu y]
      simp only [ω, dif_neg hn]
    rw [h1]
    exact GlobalTheory.T.splitHalf_residueReduction_function_eq_frameLocal D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)

  have hunder : ∀ i : ↥s, (i.1).asIdeal.under (𝓞 D.host.F) = (vP i).asIdeal := fun i => (hsum.2 _ _ _ (hpr i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es s
    (fun i hi => (hes i hi).1.1) hce
  have hinj : Function.Injective vP := by
    intro i j hij
    have h1 := (hsplit i).2
    have h2 := (hsplit j).2
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes i.1 i.2).1.1 (hes i.1 i.2).1.2.1 (hes j.1 j.2).1.1 (hes j.1 j.2).1.2.1
      (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (prime_eq_of_idem (hes i.1 i.2) (h3 ▸ hes j.1 j.2))

  have hid : ∀ (i : ↥s) (v : FinPl D) (φ : SplitProj D v) (e' : AE D), IsIdemOf φ e' → IsProjAt φ i.1 →
      ∃ hv : v = vP i, e' = es i.1 ∧ hv ▸ φ = φP i := by
    intro i v φ e' h1 h2
    obtain ⟨hu, -, h3⟩ := hsum.2 v φ i.1 h2
    have hv : v = vP i := HeightOneSpectrum.ext (hu.symm.trans (hunder i))
    subst hv
    obtain ⟨-, h4, h5⟩ := h3 e' h1
    have h6 := h4 _ (hPi i)
    refine ⟨rfl, h6.symm, (h5 _ (h6 ▸ hφ i)).symm⟩

  have hmodel : ∀ i : ↥s, ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm :=
    fun i => (GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB (vP i) (es i.1) (hsplit i).1 (hsplit i).2).1
  choose xθ hxθ using fun i : ↥s => GlobalTheory.PlaceDatum.exists_isThetaAt hψ hSd hTd (hes i.1 i.2).1.1
    (infPart_idemAt (hPi i)) (hmodel i) (hsb i)
  refine ⟨?_, ?_⟩
  · let x : Place D → WO S T → ℂ :=
      Sum.elim (fun v => if h : ∃ i, vP i = v then xθ h.choose else f₀) fun _ => f₀
    have hxi : ∀ i, x (.inl (vP i)) = xθ i := by
      intro i
      have h : ∃ j, vP j = vP i := ⟨i, rfl⟩
      show (if h : ∃ j, vP j = vP i then xθ h.choose else f₀) = xθ i
      rw [dif_pos h, hinj h.choose_spec]
    refine ⟨x, ⟨fun τ => rfl, fun v hv => ?_⟩, ?_⟩
    · show (if h : ∃ i, vP i = v then xθ h.choose else f₀) = f₀
      refine dif_neg ?_
      rintro ⟨i, rfl⟩
      exact hv i.1 i.2 (hunder i)
    · intro v φ e' he' mu
      refine ⟨fun PP hpp hmu J lam hJ => ?_, fun PP hq hpp hmu => ?_⟩
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP.1, hPs _ PP.2⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP.1, hPs _ PP.2⟩ := hφ'
        rw [hcmpG ⟨PP.1, hPs _ PP.2⟩ PP.2 J lam mu hJ hmu, hxi]
        exact hxθ _
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP, hQs _ hq⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP, hQs _ hq⟩ := hφ'
        rw [hcmpQ ⟨PP, hQs _ hq⟩ hq mu hmu, hxi]
        exact hxθ _
  · rintro x ⟨⟨hx1, hx2⟩, hloc⟩
    have hθ : ∀ i : ↥s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i)
        (x (.inl (vP i))) := by
      intro i
      by_cases hi : i.1 ∈ LS.Pg
      · obtain ⟨mu, hmu⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).2 (χ i.1)
        obtain ⟨J, lam, hJ⟩ := GlobalTheory.T.exists_isLocalLevelAtPrimeOfLevelDatum D (vP i) (φP i) i.1 (rP i) (hrP i) _ LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩)
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).1 ⟨i.1, hi⟩ (hpr i) hmu J lam hJ
        rwa [hcmpG i hi J lam mu hJ hmu] at h
      · have hq : i.1 ∈ Q := (Finset.mem_union.1 (hs ▸ i.2)).resolve_left hi
        obtain ⟨mu, hmu⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).2 (ξ i.1)⁻¹
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).2 i.1 hq (hpr i) hmu
        rwa [hcmpQ i hq mu hmu] at h
    have hoff : ∀ p, (∀ i ∈ (Finset.univ : Finset ↥s), p ≠ .inl (vP i)) → x p = f₀ := by
      rintro (v | τ) h
      · refine hx2 v fun PP hPP hu => h ⟨PP, hPP⟩ (Finset.mem_univ _) ?_
        exact congrArg Sum.inl (HeightOneSpectrum.ext (hu.symm.trans (hunder ⟨PP, hPP⟩)))
      · exact hx1 τ
    have hsumes : ∑ i : ↥s, es i.1 = ∑ PP ∈ s, es PP := Finset.sum_coe_sort s es
    have hprod : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP),
        omegaG LS χ y * omegaQ Q LS.r ξ 1 y = ∏ PP ∈ s, ω PP (y PP) := by
      intro y
      rw [← hs, Finset.prod_union hdisj, GlobalTheory.T.levelDatumValue_eq_prod_localResidueValues D _ _ LS χ Hl cl hP y, GlobalTheory.T.twistDatumValue_eq_prod_localResidueValues D _ _ LS.r Q ξ y,
        ← Finset.prod_coe_sort LS.Pg fun PP => ω PP (y PP)]
      congr 1
      · refine Finset.prod_congr rfl fun PP _ => ?_
        simp only [ω, dif_pos PP.2]
      · refine Finset.prod_congr rfl fun PP hq => ?_
        simp only [ω, dif_neg fun h => Finset.disjoint_left.1 hdisj h hq]
    rw [← hsumes] at hth
    refine GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC ↥s Finset.univ vP (fun i => es i.1) (fun i _ => hsplit i)
      hinj.injOn Φ (fun i _ => hsb i) x f _ (fun i _ => hθ i) hoff ?_ ?_ hth
    · intro t' ht'
      have h := GlobalTheory.T.prod_residueFunctions_half_sum_idempotents D S T βS βT s es hes ω t' (hsumes ▸ ht')
      have h2 : ∏ i : ↥s, Φ i (es i.1 • t') = ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t') :=
        Finset.prod_coe_sort s fun PP => locFn S T βS βT (es PP) PP (ω PP) (es PP • t')
      show (if _ then _ else _) = ∏ i : ↥s, Φ i (es i.1 • t')
      rw [h2, ← h]
      by_cases hI : IsIntM (frMapO S T βS βT t')
      · rw [if_pos ⟨ht', hI⟩, if_pos hI]
        exact hprod _
      · rw [if_neg fun h => hI h.2, if_neg hI]
    · intro t' ht'
      exact if_neg fun h => ht' h.1

end GlobalTheory.StepVec

end
