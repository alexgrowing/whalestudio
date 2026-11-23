import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

def compG {a : ℕ} (π : HostCGu H a) (w : PlE H) : IrrGL (w.adicCompletion H.E) :=
  haveI := host_isCMField H; ⟨a, ParLaws.toCl (π.1.loc w)⟩

def AllGood {a : ℕ} (π : HostCGu H a) : Prop := ∀ w : PlE H, Good (compG π w)

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGR (rc : RecFam) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) : WD (pl.2 w) :=
  rc (pl.2 w) (compG π w)

theorem locGR_locRec (hL : GlobalTheory.Published.LocalLanglandsGL) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a)
    (w : PlE H) : locGR (fun h => ParLaws.locRec hL h) pl π w = ParLaws.locG hL pl π w := rfl

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

structure CGTrueT (rc : RecFam) (D : D7) (T : WDTie D.nd D.naut) where
  isRecT : ∀ w, IsRecT (D.nd.plOm.2 w) (rc (D.nd.plOm.2 w))
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → ∀ π : HostCGu D.host a, AllGood π → ∃ σ, e a σ = π
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, Good (compG (e a π) w) → T.e w (D.naut.locG π w) = locGR rc D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

variable {rc : RecFam} {D : D7} {T : WDTie D.nd D.naut}

def cgTrueT_of_cgTrue (hD : GlobalTheory.Published.DepthZeroTypeInertia) {hL : GlobalTheory.Published.LocalLanglandsGL} (C : CGTrue hL D T) :
    CGTrueT (fun h => ParLaws.locRec hL h) D T where
  isRecT w := (isRecT_iff _).2 (UpperTheory.Zero.LLC.isRecT_of_isRec hD (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)))
  e := C.e
  surj a ha π _ := C.surj a ha π
  zero := C.zero
  loc a π w _ := C.loc a π w
  tw := C.tw
  inf := C.inf
  csd := C.csd

theorem cgTrueT_of_cgTrue_e (hD : GlobalTheory.Published.DepthZeroTypeInertia) {hL : GlobalTheory.Published.LocalLanglandsGL} (C : CGTrue hL D T) :
    (cgTrueT_of_cgTrue hD C).e = C.e := rfl

set_option maxHeartbeats 2000000 in

def trueCGT (hD : GlobalTheory.Published.DepthZeroTypeInertia) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (hE : IsEmpty D.nd.Loc) (T : WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧
      (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) :
    CGTrueT (fun h => ParLaws.locRec hL h) (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) :=
  cgTrueT_of_cgTrue hD (trueCG hL hF D hE T η η' h1 h2 h3 h4)

theorem trueCGT_e_surj (hD hL hF D hE T η η' h1 h2 h3 h4) (a : ℕ) (ha : 0 < a) :
    Function.Surjective ((trueCGT hD hL hF D hE T η η' h1 h2 h3 h4).e a) :=
  (trueCG hL hF D hE T η η' h1 h2 h3 h4).surj a ha

def CGTrueT.equivGood (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) :
    {σ : D.naut.CG a // AllGood (C.e a σ)} ≃ {π : HostCGu D.host a // AllGood π} :=
  Equiv.ofBijective (fun σ => ⟨C.e a σ.1, σ.2⟩)
    ⟨fun σ τ hst => Subtype.ext ((C.e a).injective (congrArg Subtype.val hst)),
     fun π => let ⟨σ, hσ⟩ := C.surj a h π.1 π.2; ⟨⟨σ, hσ ▸ π.2⟩, Subtype.ext hσ⟩⟩

@[simp] theorem CGTrueT.equivGood_apply (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) (σ) :
    (C.equivGood a h σ : HostCGu D.host a) = C.e a σ.1 := rfl

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

def recMapT {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : WDTie N A)
    (rc : RecFam) : RecMap A :=
  fun w _ σ => (T.e w).symm (rc (N.plOm.2 w) (cls (ParLaws.toRep σ)))

theorem recMapT_locRec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (T : WDTie N A) (hL : GlobalTheory.Published.LocalLanglandsGL) :
    recMapT T (fun h => ParLaws.locRec hL h) = GlobalTheory.FormDict.recT T hL := rfl

def CuspReadT {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd →
    (∀ w : PlE H, ∃ σ, P.IsLocComp w σ ∧ Good (cls (ParLaws.toRep σ))) → ∃ π : A.CG a, A.csd π ∧
    (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

theorem cuspReadT_of_cuspRead {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {rc : RecMap A} (h : CuspRead rc) : CuspReadT rc :=
  fun a P ha hP _ => h a P ha hP

theorem compG_eq {D : D7} {a : ℕ} (P : CuspSub D.host.E a) (hu : haveI := host_isCMField D.host; (CG.mk P).IsUnitary)
    {w : PlE D.host} {σ : SmIrr (GL (Fin a) (w.adicCompletion D.host.E))} (hσ : P.IsLocComp w σ) :
    compG (H := D.host) ⟨CG.mk P, hu⟩ w = cls (ParLaws.toRep σ) := by
  haveI := host_isCMField D.host
  have h1 : (CG.mk P).IsLoc w (Quotient.mk _ σ) := hσ
  simp only [compG]
  rw [CG.IsLoc.unique D.host.E a _ w _ _ h1.loc h1]
  rfl

theorem cuspReadT_recMapT : ∀ (rc : RecFam) (D : D7) (T : WDTie D.nd D.naut),
    CGTrueT rc D T → CuspReadT (recMapT T rc) := by
  intro rc D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  have hgood : AllGood (H := D.host) ⟨CG.mk P, hu⟩ := fun w => by
    obtain ⟨σ, hσ, hg⟩ := hg w
    rw [compG_eq P hu hσ]; exact hg
  obtain ⟨π, hπ⟩ := C.surj a ha ⟨CG.mk P, hu⟩ hgood
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc a π w (by rw [hπ]; exact hgood w)]
    simp only [recMapT, Equiv.apply_symm_apply, locGR, hπ]
    rw [compG_eq P hu hσ]
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

theorem nonempty_equivGoodAll : ∀ (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : WDTie D.nd D.naut),
    GlobalTheory.HeightCounting.CGTrueT hT D T → ∀ a : ℕ, 0 < a →
      Nonempty (D.naut.CG a ≃ {ρ : HostCGu D.host a // GlobalTheory.HeightCounting.GoodAll ρ}) := by
  intro hT D T C a ha
  exact ⟨Equiv.ofBijective (fun π => ⟨C.e a π, C.good a π⟩)
    ⟨fun x y h => (C.e a).injective (congrArg Subtype.val h),
     fun ρ => let ⟨π, hπ⟩ := C.surj a ha ρ.1 ρ.2; ⟨π, Subtype.ext hπ⟩⟩⟩

def ofShared {hT : UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : WDTie D.nd D.naut} (C : GlobalTheory.HeightCounting.CGTrueT hT D T) :
    GlobalTheory.RecT.CGTrueT (fun h => ParLawsT.locRecT hT h) D T where
  isRecT w := (GlobalTheory.RecT.isRecT_iff _).2 (ParLawsT.isRecT_locRecT hT (D.nd.plOm.2 w))
  e := C.e
  surj a ha π hπ := C.surj a ha π hπ
  zero := C.zero
  loc a π w _ := C.loc a π w
  tw := C.tw
  inf := C.inf
  csd := C.csd

end GlobalTheory.RecT

end
