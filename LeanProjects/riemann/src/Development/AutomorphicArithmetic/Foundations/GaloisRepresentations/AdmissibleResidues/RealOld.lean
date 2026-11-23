import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem RatioW.of_pol {x y : WD h} (hp : ∀ g : ↥(Weil h), x.charPol g = y.charPol g) (hy : RatioW y) : RatioW x := by
  intro φ hφ α hα β hβ
  rw [WD.eig, hp] at hα hβ
  exact hy φ hφ α hα β hβ

theorem RatioW.noRatio {x : WD h} (hx : RatioW x) {g : ↥(Weil h)} (hg : deg g = 1) : NoRatio x g := by
  intro α hα hβ
  have k := hx g hg _ hβ α hα
  rw [hg, zpow_one, norm_mul, Complex.norm_natCast] at k
  exact lt_irrefl _ k

theorem eig_lpTw (x : WD h) (s : ℝ) {φ : ↥(Weil h)} (hφ : deg φ = 1) {α : ℂ} (hα : α ∈ x.eig φ) :
    α * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) ∈ (x.lpTw s).eig φ := by
  rw [GlobalTheory.RowTie.EigTwist.eig_lpTw x hφ s]
  exact Multiset.mem_map_of_mem _ hα

theorem RatioW.of_tempered {x : WD h} {s : ℝ} (hm : x.mono0) (ht : (x.lpTw s).tempered) : RatioW x := by
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV w
  have key : ∀ y : WD h, y.mono0 → y.tempered → ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ y.eig φ, ‖α‖ = 1 := by
    intro y hm ht φ hφ α hα
    induction y using WD.ind with
    | hP n b =>
      rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hm
      rw [WD.tempered_mk] at ht
      rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
      have top := ht.norm_eq_one hm hφ
      by_contra hne
      have d := Module.End.eigenspaces_iSupIndep (b.ρ φ) α
      have le : (⊤ : Submodule ℂ (Fin n → ℂ)) ≤ ⨆ (β) (_ : β ≠ α), Module.End.eigenspace (b.ρ φ) β := by
        rw [← top]
        exact iSup₂_le fun β hβ => le_iSup₂_of_le β (fun e => hne (e ▸ hβ)) le_rfl
      exact hα (disjoint_top.1 (d.mono_right le))
  intro φ hφ α hα β hβ
  have hm' := (WD.monomial_twist_iff x s).2 hm
  have e1 := key _ hm' ht φ hφ _ (eig_lpTw x s hφ hα)
  have e2 := key _ hm' ht φ hφ _ (eig_lpTw x s hφ hβ)
  rw [norm_mul] at e1 e2
  have hc : ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ ≠ 0 := fun e => by rw [e, mul_zero] at e1; exact zero_ne_one e1
  have e3 : ‖α‖ = ‖β‖ := mul_right_cancel₀ hc (e1.trans e2.symm)
  have hb : 0 < ‖β‖ := lt_of_le_of_ne (norm_nonneg _) fun e => by rw [← e, zero_mul] at e2; exact zero_ne_one e2
  rw [e3]
  exact lt_mul_of_one_lt_left hb hq

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem pol_of_rel {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : ↥(Weil h)} {σ' : ↥(Weil h')} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

theorem monodromyFree_iff_related {y : WD h} {y' : WD h'} (hy : WDRel φ y y') : y.mono0 ↔ y'.mono0 := by
  obtain ⟨n, b, b', rfl, rfl, hN, -⟩ := hy
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff]
  exact hN ▸ Iff.rfl

theorem pol_descend (P : PlaceIso A w A' w' φ j i) {x y : WD h} {x' y' : WD h'} (hx : WDRel φ x x') (hy : WDRel φ y y')
    (k : ∀ g, x'.charPol g = y'.charPol g) (g : ↥(Weil h)) : x.charPol g = y.charPol g := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  rw [pol_of_rel hx ((hc g (c g)).2 rfl), pol_of_rel hy ((hc g (c g)).2 rfl), k]

theorem AwR.descend (P : PlaceIso A w A' w' φ j i) {x y : WD h} {x' y' : WD h'} (hx : WDRel φ x x') (hy : WDRel φ y y')
    (k : AwR x' y') : AwR x y := by
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  exact ⟨pol_descend P hx hy k.pol, fun m => S.injective (by
    rw [(hS _ _).1 hx, (hS _ _).1 hy]; exact k.n0 ((monodromyFree_iff_related hy).1 m))⟩

theorem RatioW.descend (P : PlaceIso A w A' w' φ j i) {x : WD h} {x' : WD h'} (hx : WDRel φ x x') (k : RatioW x') :
    RatioW x := by
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  intro g hg α hα β hβ
  rw [WD.eig, pol_of_rel hx ((hc g (c g)).2 rfl)] at hα hβ
  rw [← hq]
  exact k (c g) (by rw [hdeg, hg]) α hα β hβ

theorem RatioW.ascend (P : PlaceIso A w A' w' φ j i) {x : WD h} {x' : WD h'} (hx : WDRel φ x x') (k : RatioW x) :
    RatioW x' := by
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  intro g hg α hα β hβ
  obtain ⟨g, rfl⟩ := c.surjective g
  rw [WD.eig, ← pol_of_rel hx ((hc g (c g)).2 rfl)] at hα hβ
  rw [hq]
  exact k g (by rw [← hdeg, hg]) α hα β hβ

theorem exists_rel (P : PlaceIso A w A' w' φ j i) (y' : WD h') : ∃ y : WD h, WDRel φ y y' := by
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  exact ⟨S.symm y', (hS _ _).2 (S.apply_symm_apply _)⟩
end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ} {π : TR.CuspSub F a} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (F →+* Qbar l) → Multiset ℤ}

theorem IsGalRU.of_old (H : IsGalRepOfR π ι r wt HT) : IsGalRU π ι r wt HT where
  cont := H.cont
  ss := H.ss
  away w hl A h rc hrc σ hσ := .of_eq ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl)
  ratio w hl A h rc hrc σ hσ hm := by
    obtain ⟨x, hx, ht⟩ := H.pure w hl A h
    rw [← hx.wdOf_eq hl] at ht
    exact .of_tempered (by rwa [(H.away w hl A h rc hrc σ hσ).wdOf_eq hl]) ht
  weights := H.weights
  weights_sym := H.weights_sym
  above P AI T w A h O _ _ _ Bw hj :=
    have k := H.above P AI T w A h O Bw hj
    ⟨k.1, k.2.1, fun σ hσ hi _ rc hrc => by rw [(k.2.2.1 σ hσ hi).2 rc hrc]; exact ⟨fun _ => rfl, id⟩, k.2.2.2⟩

theorem IsGalRU.sat (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {A : ValuationSubring Ω} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion F))} (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := by
  rw [← (H.away w hl A h rc hrc σ hσ).eq_unr (unr_algNorm hrc σ S hS)]
  exact isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp H.cont)

theorem IsGalRU.ratio_sat (H : IsGalRU π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {A : ValuationSubring Ω} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion F))} (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : RatioW (wdOf h hl ι r) :=
  H.ratio w hl A h rc hrc σ hσ (WD.unr_mono0 _ (unr_algNorm hrc σ S hS))
end Real

theorem galRN (h : GaloisRepReal) : GaloisRepRealN := fun F Ω _ _ _ _ _ _ l _ ι a ha π χ h1 h2 =>
  let ⟨r, wt, HT, H⟩ := h F Ω l ι a ha π χ h1 h2
  ⟨r, wt, HT, .of_old H⟩
theorem galRN' (h : GaloisRepRealN) : GaloisRepRealN := h

theorem gr2N (h : UpperTheory.V.Z.Bc.GaloisRepRankTwoReal) : GaloisRepRankTwo := fun F Ω _ _ _ _ _ _ l _ ι a _ ha π χ h1 h2 =>
  let ⟨r, wt, HT, H⟩ := h F Ω l ι a ha π χ h1 h2
  ⟨r, wt, HT, .of_old H⟩
theorem gr2N' (h : GaloisRepRankTwo) : GaloisRepRankTwo := h

theorem exRN (h : ExR) : ExRN := fun F Ω _ _ _ _ _ _ l _ ι n _ hn π χ h1 h2 =>
  let ⟨r, wt, HT, H, a, b⟩ := h F Ω l ι n hn π χ h1 h2
  ⟨r, wt, HT, .of_old H, a, fun r' x y => .of_old (b r' x y)⟩
theorem exRN' (h : ExRN) : ExRN := h

end UpperTheory.GalN.V
