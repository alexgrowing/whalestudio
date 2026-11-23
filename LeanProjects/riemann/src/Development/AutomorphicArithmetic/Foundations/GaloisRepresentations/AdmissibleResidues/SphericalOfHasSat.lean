import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepOfPolarizedPairOfHyps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

theorem exists_ladic (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (hr : (CG.mk π).IsRegAlg) (hp : GlobalTheory.ContraPair.PolarizedPair π χ) :
    ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ := by
  obtain ⟨n, hn⟩ := GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair E a ha π χ hr hp
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨art, hart, hL⟩ :=
    (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1
      (maximalRealSubfield E) Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hL l ι χ n hn
  exact ⟨μ, hμc, art, n, hart, hn, hμ⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eq_of_unr {x y : WD h} (hy : y.unr) (hp : ∀ g : ↥(Weil h), x.charPol g = y.charPol g) (hm : x.mono0) : x = y := by
  have hd : x.lpDim = y.lpDim := by rw [← WD.charPol_natDegree x 1, hp, WD.charPol_natDegree]
  have hx : x.unr := (WD.unr_iff_ine x).2 ⟨hm, fun σ hσ => by
    have := ((WD.unr_iff_ine y).1 hy).2 σ hσ
    rw [WD.inePol_of_mem_Ine _ hσ] at this ⊢
    rw [hp, this, hd]⟩
  rw [WD.unr_eq_lpUnr x hx, WD.unr_eq_lpUnr y hy, WD.frobEig, WD.frobEig, WD.eig, WD.eig, hp]

theorem unr_algNorm {a : ℕ} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (algNorm σ)).unr := by
  rw [rec_algNorm hrc, WD.unr_tw]
  exact unr_rec_of_hasSat hrc σ S hS

theorem spherical_of_hasSat {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : SmGL.IsSpherical σ.ρ := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨x, hx0, hx, -⟩ := hS.exists_vec
  exact (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k (hK.le hk), hx0⟩

variable [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

theorem isWDOf_of_hasSat (H : IsGalU π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) : IsWDOf ι r (rc (algNorm σ)) := by
  rw [← (H.away w hl A h rc hrc σ hσ).n0 (WD.unr_mono0 _ (unr_algNorm hrc σ S hS))]
  exact isWDOf_wdOf (h := h) hl ι (Units.continuous_val.comp H.cont)

theorem wdAt_eq_of_hasSat {P : LocPrime l} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    {Bw : LocBridge l E Ω (Dec (F := E) A) O} {hj : Pst.Induces Bw} (H : AboveU π ι r HT P h Bw hj)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) {S : Multiset ℂˣ}
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) (hi : PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥)
    (rc : IrrGL (w.adicCompletion E) → WD h) (hrc : IsRec h rc) :
    wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ) :=
  have k := (H.iwahori σ hσ hi (spherical_of_hasSat σ S hS)).2 rc hrc
  have u := unr_algNorm hrc σ S hS
  eq_of_unr u k.1 (k.2 (WD.unr_mono0 _ u))

end UpperTheory.GalN.V
