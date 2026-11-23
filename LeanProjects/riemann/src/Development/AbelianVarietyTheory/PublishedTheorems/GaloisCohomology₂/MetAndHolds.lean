import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterCrystalline
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoldsFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharCrysModel

theorem of_above (H : HeckeLAdicCharacterAbove) : HeckeLAdicCharacterCrystalline :=
  fun E Ω _ _ _ _ _ l _ P AI hT ι art ha χ n μ h1 h2 h3 w A h O _ _ _ Bw hj =>
    (H E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj).2.2.1

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem met_and_holds (hA : GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (m : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (hw : w ∈ placesOver E l) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧ ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (Model.absPow E m) (fun _ => (m : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (Model.absPow E m) (fun _ => (m : ℤ)) μ ∧
      ∃ (A : ValuationSubring Ω), IsPlaceOver A w ∧ ∃ (LL : FinExt l)
        (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧ (Model.absPow E m).UnrAt w ∧
        IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) := by
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨art, ha⟩ := hA E Ω
  obtain ⟨μ, h1, h2, h3, A, h, LL, Bw, hj, -⟩ := CharAboveModel.hypotheses_met ι art ha m w hw
  exact ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, (Model.absPow_isAbsPow E m).1 w,
    (CharAboveModel.conclusion_absPow P AI hT ι art ha m μ h2 h3 A _ Bw).2.2.1⟩

theorem isUnram_iff (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) : IsUnram (χ.loc w) ↔ χ.UnrAt w := by
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem finite_iff (P : LocPrime l) (ι : Qbar l ≃+* ℂ)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {χ : HChar E} {k : ℕ} (hk : 0 < k)
    (hχ : χ.OrderDvd k) {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι χ 0 μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ↔ χ.UnrAt w := by
  have hξ := ParamAboveModel.isComp_loc (w := w) χ
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, CharWDModel.holds_finite P ι Bw h hj ha hk hχ hμ hL hr hξ ha',
    GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
  exact isUnram_iff χ w

theorem of_classicalTheorems (hD : HeckeLAdicCharacterDeRham) (hB : DeRhamPotSemistable) (hW : AlgebraicCharacterWD)
    (hL : LocalLanglandsGL) : HeckeLAdicCharacterCrystalline := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art ha χ n μ h1 h2 h3 w A h O _ _ _ Bw hj hu
  obtain ⟨rc, ⟨a, ha', -⟩, -⟩ := hL.1 E Ω A w h
  have hξ := ParamAboveModel.isComp_loc (w := w) χ
  have hc : Continuous fun g : ↥(Dec (F := E) A) =>
      (((rk1 μ).comp (Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    have e : (fun g : ↥(Dec (F := E) A) =>
      (((rk1 μ).comp (Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      fun g : ↥(Dec (F := E) A) => ((μ g : (Om l)ˣ) : Om l) := by
      funext g
      rw [Subsingleton.elim i j]
      simp [rk1]
    rw [e]
    exact Units.continuous_val.comp (h2.comp continuous_subtype_val)
  have hr := hB.isPstAt hT.some Bw _ hc (hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj).1
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr,
    hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha',
    GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
  exact (isUnram_iff χ w).2 hu

end GlobalTheory.Published.CharCrysModel

end
