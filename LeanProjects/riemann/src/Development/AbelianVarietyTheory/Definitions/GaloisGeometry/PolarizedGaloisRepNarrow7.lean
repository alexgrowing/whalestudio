import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OddOrSlightlyRegIffOfEven

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalNarrow7

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

def SqIntSomewhere (π : CuspSub E a) : Prop :=
  ∃ (x : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (x.adicCompletion E))), GlobalTheory.UnitaryBC.IsSplitAt x ∧ π.IsLocComp x σ ∧
    UnitaryDual.IsSquareIntegrable (IrrGL.of σ.ρ σ.smooth σ.irred)

def IsWeightOf (π : CuspSub E a) (wt : ℤ) : Prop :=
  ∀ τ : E →+* ℂ, (CG.mk π).infChar (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
    ((CG.mk π).infChar τ).map fun z => (a : ℂ) - 1 - (wt : ℂ) - z

structure AboveN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) → IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
      (∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
      ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0)

  oddIwa : Odd a → ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
      wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

  sizeAbove : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) → ∀ (wt : ℤ) (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).lpTw ((wt : ℝ) / 2)).eig g,
    IsWeightOf π wt → ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧
      ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

section API

variable {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)}
  {HT : (E →+* Qbar l) → Multiset ℤ} {P : LocPrime l} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
  {h : IsPlaceOver A w} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Bw : LocBridge l E Ω (Dec (F := E) A) O} {hj : Pst.Induces Bw}

end API

example (q : ℝ) (hq : 1 < q) (d : ℤ) (hd : d ≠ 0) (a : ℕ) (ha : 1 ≤ a) :
    q ^ (-(|(d : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < q ^ ((|(d : ℤ)| : ℝ) * (a : ℝ) / 2) := by
  have h1 : (0 : ℝ) < |(d : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  have h2 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h3 : (0 : ℝ) < |(d : ℝ)| * a := mul_pos h1 h2
  rw [norm_one]
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith), Real.one_lt_rpow hq (by linarith)⟩

example (π : CuspSub E 3) (p : Prop) : GlobalTheory.CBGal.OddOrSlightlyReg π ∨ p := Or.inl (Or.inl ⟨1, rfl⟩)

example (π : CuspSub E 2) (p : Prop) :
    ¬ (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ p) ↔ ¬ GlobalTheory.CBGal.SlightlyReg π ∧ ¬ p := by
  rw [GlobalTheory.CBGal.oddOrSlightlyReg_iff_of_even π ⟨1, rfl⟩, not_or]

structure PropsN (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ

  awaySS : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g

  awayFromResidueChar : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      wdOf h hl ι r = rc (algNorm σ)

  awayIne : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
    ∀ (n : ℕ) (x y : WDRep h (Fin n → ℂ)), WD.mk x = wdOf h hl ι r → WD.mk y = rc (algNorm σ) →
    ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y.ρ (ineIncl h s) v = χ s • v) → y.N v = 0) →
      ∀ v, (∀ s, x.ρ (ineIncl h s) v = χ s • v) → x.N v = 0

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∃ σ, π.IsLocComp w σ ∧ ¬ SmGL.IsSpherical σ.ρ) → ∀ (g : Weil h), deg g ≠ 0 →
      ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  pureUnr : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ) → ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  pureDegreeZero : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0) →
      ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  sqInt : SqIntSomewhere π → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w), (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
      wdOf h hl ι r = rc (algNorm σ)) ∧ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveN π ι r HT P h Bw hj

end GlobalTheory.GalNarrow7

namespace GlobalTheory.Published

def PolarizedGaloisRepNarrow7 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        GalNarrow7.PropsN π χ ι r wt HT

end GlobalTheory.Published

end
