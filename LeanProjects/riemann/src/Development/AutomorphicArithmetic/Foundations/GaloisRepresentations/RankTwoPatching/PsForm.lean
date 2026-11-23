import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open private UpperTheory.V.Z.Win.MonodromyFreeReciprocity.isL_chars UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_sum_list UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_of_character
  UpperTheory.V.Z.Win.MonodromyFreeReciprocity.tor_sum from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
open private UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.link_iff from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff

namespace UpperTheory.Gal.SV

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem psForm {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (w.adicCompletion E) → WD h}
    (L : LawsT a ha rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ξ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hξ : ∀ i, IsSmoothChar (ξ i)) (hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ)) (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) :
    rc (algNorm σ) = (sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i)))).lpTw ((1 - (n : ℝ)) / 2) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hl : Unl (GroundTheory.LocalField.residueCard (w.adicCompletion E)) (GlobalTheory.RoadU.chars ξ hξ) :=
    fun χ ⟨c, hc⟩ χ' ⟨b, hb⟩ h1 e => hu _ hb _ hc ((UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.link_iff b c).2 ⟨h1, e⟩)
  obtain ⟨e⟩ := unlFull (w.adicCompletion E) n σ.V σ.ρ ξ hξ hs' hl
  have hL := (UpperTheory.V.Z.Win.MonodromyFreeReciprocity.isL_chars σ.ρ σ.irred ξ hξ hu e).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, GlobalTheory.LocLanglands.Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr]

theorem gdOf : GdOf := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hA := psForm L σ ξ hξ (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm) hu
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.tor_sum _ _ _ (by rw [← hA, L.dim]; rfl)
  · rw [hA, WD.monomial_twist_iff]
    exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_sum_list _ fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact UpperTheory.V.Z.Win.MonodromyFreeReciprocity.monodromy_free_of_character _ _

theorem recTr (hG : GlobalTheory.Published.GlobalArtinReciprocity) {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {u : HeightOneSpectrum (𝓞 K)} {h' : IsPlaceOver A u} {j : E →+* K} {i : w.adicCompletion E ≃+* u.adicCompletion K}
    (P : PlaceIso A w A u (RingEquiv.refl Ω) j i) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin n) (u.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V)
    (he : ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))
    {rc : IrrGL (w.adicCompletion E) → WD h} {rc' : IrrGL (u.adicCompletion K) → WD h'} (hrc : IsRecT h rc) (hrc' : IsRecT h' rc')
    (hP : GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) :
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) := by
  obtain ⟨a, ha, L⟩ := hrc
  obtain ⟨a', ha', L'⟩ := hrc'
  have hi := P.cont
  have hi' : Continuous i.symm := GlobalTheory.LocalFieldIso.continuous_symm i hi
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hρ : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  let ξ' : Fin n → (u.adicCompletion K)ˣ →* ℂˣ := fun k => (ξ k).comp (Units.map i.symm.toRingHom.toMonoidHom)
  have hξ' : ∀ k, IsSmoothChar (ξ' k) := fun k =>
    IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') (hξ k)
  have h5 : ∀ t, Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t := fun t =>
    Units.ext (i.symm_apply_apply _)
  have hg : ∀ g : GL (Fin n) (u.adicCompletion K),
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) σ'.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change e (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (e x)
      rw [he, hg]⟩ e.bijective
  have h3 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hρ).of_equiv φ
  have h4 : (GlobalTheory.RoadU.chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') = GlobalTheory.RoadU.chars ξ' hξ' := by
    rw [GlobalTheory.RoadU.chars, GlobalTheory.RoadU.chars, Multiset.map_map]
    exact Multiset.map_congr rfl fun k _ => GlobalTheory.DegOneChar.trGL_ofChar i hi' (ξ k) (hξ k) (hξ' k)
  rw [h4] at h3
  have hu' : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ' hξ') := by
    intro y hy z hz heq
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at heq
    refine hu _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)) _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)) ?_
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    refine MonoidHom.ext fun t => ?_
    have h6 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5, GlobalTheory.LocalFieldIso.absPow_map i hi] at h6
    exact h6
  obtain ⟨S, hS, -, h0, hsum, -, hSt, -, -, hch⟩ := GlobalTheory.WDTransport.exists_equiv_wd E Ω A w h K Ω A u h' (RingEquiv.refl Ω) j i P
  have hl : ∀ l : List (WD h), S (sumList l) = sumList (l.map S) := fun l => by
    induction l with
    | nil => exact h0
    | cons b l ih => exact (hsum b (sumList l)).trans (congrArg (WD.lpSum (S b)) ih)
  refine (hS _ _).2 ?_
  rw [psForm L σ ξ hξ hρ hu, psForm L' σ' ξ' hξ' h3 hu', hSt, hl, List.map_ofFn]
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => hch _ _ _ _ fun s s' hss => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    GlobalTheory.T.localArtinMap_unique_transport_placeIso hG GlobalTheory.Published.chevalleyUnits' E Ω A w h K Ω A u h' _ j i P a a' ha ha' s s' hss]
  exact (congrArg (ξ k) (h5 _)).symm

def RatioT : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion K) → WD h), IsRecT h rc →
    ∀ (a : ℕ) (π : CuspSub K a) (t : ℝ), WinAt π t w → ∀ σ, π.IsLocComp w σ → UpperTheory.GalN.V.RatioW (rc (algNorm σ))

end UpperTheory.Gal.SV
