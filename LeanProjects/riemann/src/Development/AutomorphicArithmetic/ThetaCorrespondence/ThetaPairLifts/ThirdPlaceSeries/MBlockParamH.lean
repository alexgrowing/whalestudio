import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.One.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.SplitRead.BlockParam GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne (WD Weil ineIncl)
section Local
variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
theorem charPol_unr_twist' {rc : ∀ n, Irr k n → WD h} (hrc : _root_.UpperTheory.One.M.RecLawsH rc) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (σ : Ine (F := E) B) (c : ℂ) (hc : (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C c)
    (n : ℕ) (π : Irr k n) (hn : n = 1) (α : ℂˣ)
    (e : Nonempty (π.π.Equiv (detRep (Fin n) (χ * unrChar k α)))) :
    (rc n π).charPol (ineIncl h σ) = X - C c := by
  subst hn
  let u : Irr k 1 := detIrr 1 (unrChar k α) (isSmoothChar_of_isUnram (isUnram_unrChar k α))
  have he : detRep (Fin 1) (χ * unrChar k α) = twist u.π (detChar (Fin 1) χ) := by
    show _ = twist (detRep (Fin 1) (unrChar k α)) (detChar (Fin 1) χ)
    unfold detRep ofChar
    rw [twist_twist]
    rfl
  have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc 1 χ (detIrr 1 χ hχ) u π (good_of_one _ rfl) ⟨.refl _⟩ (he ▸ e)
  rw [h1, charPol_lpChar_of_unr _ _ ((hrc.sph 1 u).2 (isSpherical_detRep (isUnram_unrChar k α))) σ c hc,
    hrc.dim, pow_one]
theorem split_local_of_blockVec {rc : ∀ n, Irr k n → WD h} (hB : BlockSplit k) (hrc : _root_.UpperTheory.One.M.RecLawsH rc) (hs : RecSupp rc)
    {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (ht : IsTame χ) (π : Irr k (r + t)) (v : π.V) (hv : v ≠ 0)
    (hvb : IsBlockVec χ π.π v) (c : Ine (F := E) B → ℂ)
    (hc : ∀ σ, (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C (c σ)) (γ : Ine (F := E) B)
    (hm : ((rc _ π).charPol (ineIncl h γ)).rootMultiplicity (c γ) ≤ t) :
    ∃ a b : WD h, rc _ π = a.lpSum b ∧ a.lpDim = r ∧ b.lpDim = t ∧ b.mono0 ∧
      ∀ σ, b.charPol (ineIncl h σ) = (X - C (c σ)) ^ t := by
  classical
  rcases hB r t χ π v hχ ht hv hvb with ⟨π₁, π₂, hsph, e⟩ | ⟨s, d, σ, hsupp, hcard⟩
  · have hg : GoodI π₂ := GlobalTheory.AVGood.good_of_isSpherical GlobalTheory.T.bernstein_zelevinsky_finiteness _
      (fixed_ne_bot_of_equiv (equivRep ⟨π₂.V, π₂.π, π₂.smooth, π₂.irr⟩) hsph)
    have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc t χ (detIrr 1 χ hχ) π₂ (twistIrr π₂ χ hχ) hg ⟨.refl _⟩ ⟨.refl _⟩
    have hu := (hrc.sph t π₂).2 hsph
    refine ⟨rc r π₁, rc t (twistIrr π₂ χ hχ), hrc.prod r t π₁ _ π e, hrc.dim _ _, hrc.dim _ _, ?_, fun σ => ?_⟩
    · rw [h1, WD.monomial_char_iff _ _ (hrc.dim _ _)]
      exact WD.unr_mono0 _ hu
    · rw [h1, charPol_lpChar_of_unr _ _ hu σ _ (hc σ), hrc.dim]
  · exfalso
    set U := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} with hU
    have hdvd : (X - C (c γ)) ^ U.toFinset.card ∣ (rc _ π).charPol (ineIncl h γ) := by
      rw [hs _ s π d σ hsupp, ← Finset.prod_const]
      refine dvd_trans (dvd_of_eq (Finset.prod_congr rfl fun a ha => ?_))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ U.toFinset))
      obtain ⟨h1, α, e⟩ := Set.mem_toFinset.1 ha
      exact (_root_.UpperTheory.One.M.charPol_unr_twist' hrc hχ γ _ (hc γ) _ _ h1 α e).symm
    have := (le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero).2 hdvd
    rw [Set.ncard_eq_toFinset_card'] at hcard
    omega
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem split_param_of_typeBlock : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), BlockSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → TypeBlock S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t → ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hB hL hS hT hchi P hm
  haveI : CharZero (w.adicCompletion H.E) := charZero_compl w
  obtain ⟨v, hv, hvb⟩ := hT.2 P
  have hμ := (S i w hw).mu_ok.1
  rw [T.inePol w _ _ (N.locNd_chebotarevPlace_mem i w), (S i w hw).locV, WD.inePol_of_mem_Ine _ (N.locNd_chebotarevPlace_mem i w)] at hm
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := _root_.UpperTheory.One.M.split_local_of_blockVec (hB w) (hL i w hw) (hS i w hw) hμ hT.1 _ v hv hvb
    (fun σ => iotaO N A i (chi1 N i σ.1)) (fun σ => by
      rw [← hchi σ.1 σ.2, T.inePol w _ _ σ.2, (S i w hw).locMu (detIrr 1 _ hμ) ⟨.refl _⟩,
        WD.inePol_of_mem_Ine _ σ.2]) ⟨_, N.locNd_chebotarevPlace_mem i w⟩ hm
  obtain ⟨a, rfl⟩ := (T.e w).surjective a
  obtain ⟨b, rfl⟩ := (T.e w).surjective b
  refine ⟨a, b, (T.e w).injective ?_, ?_, ?_, (T.mono0 w b).2 h4, fun σ hσ => ?_⟩
  · rw [(S i w hw).locV, h1, T.sum]
  · rw [← T.dim, h2]
  · rw [← T.dim, h3]
  · rw [T.inePol w _ _ hσ, WD.inePol_of_mem_Ine _ hσ, h5]
end UpperTheory.One.M
end
end
