import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow7

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut7

open GlobalTheory.GalCut GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

inductive Clause7
  | n0 | ine | sizeAway | pureUnr | pureDegreeZero | sqInt | iwa | oddIwa | sizeAbove

def Clause7At (c : Clause7) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  match c with
  | .n0 => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
        wdOf h hl ι r = rc (algNorm σ)
  | .ine => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
      ∀ (n : ℕ) (x y : WDRep h (Fin n → ℂ)), WD.mk x = wdOf h hl ι r → WD.mk y = rc (algNorm σ) →
      ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y.ρ (ineIncl h s) v = χ s • v) → y.N v = 0) →
        ∀ v, (∀ s, x.ρ (ineIncl h s) v = χ s • v) → x.N v = 0
  | .sizeAway => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      (∃ σ, π.IsLocComp w σ ∧ ¬ SmGL.IsSpherical σ.ρ) → ∀ (g : Weil h), deg g ≠ 0 →
      ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
        ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)
  | .pureUnr => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      (∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ) → ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered
  | .pureDegreeZero => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0) →
        ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered
  | .sqInt => GlobalTheory.GalNarrow7.SqIntSomewhere π → ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → wdOf h hl ι r = rc (algNorm σ)) ∧
      ∀ wt : ℤ, IsWeight π wt → ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered
  | .iwa => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
        (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) →
        IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
          (∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
          ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0)
  | .oddIwa => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      Odd a → ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
        IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
          wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)
  | .sizeAbove => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
      (GlobalTheory.CBGal.OddOrSlightlyReg π ∨ SmGL.IsSpherical σ.ρ) →
      ∀ (wt : ℤ), IsWeight π wt → ∀ (g : Weil h), deg g ≠ 0 →
      ∀ z ∈ ((wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).lpTw ((wt : ℝ) / 2)).eig g,
        ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

def ClauseValidAtLevel (s : Level) (c : Clause7) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → Clause7At c π ι r w

def Packages : Prop :=
  Ex .csd ∧ Holds .csd .ss ∧ Holds .csd .dR ∧ Holds .csd .crys ∧ ∀ c, ClauseValidAtLevel .csd c

example (π : CuspSub E 3) (p : Prop) : GlobalTheory.CBGal.OddOrSlightlyReg π ∨ p := Or.inl (Or.inl ⟨1, rfl⟩)

example (q : ℝ) (hq : 1 < q) (d : ℤ) (hd : d ≠ 0) (a : ℕ) (ha : 1 ≤ a) :
    q ^ (-(|(d : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < q ^ ((|(d : ℤ)| : ℝ) * (a : ℝ) / 2) := by
  have h1 : (0 : ℝ) < |(d : ℝ)| := abs_pos.2 (by exact_mod_cast hd)
  have h2 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h3 : (0 : ℝ) < |(d : ℝ)| * a := mul_pos h1 h2
  rw [norm_one]
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith), Real.one_lt_rpow hq (by linarith)⟩

example {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt0 : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : GlobalTheory.GalNarrow7.PropsN π χ ι r wt0 HT) (w : HeightOneSpectrum (𝓞 E)) :
    Clause7At .sizeAbove π ι r w := by
  intro P AI hAI A h O _ _ _ Bw hj σ hσ hI hg wt hw g hdeg z hz
  exact (H.above P AI hAI w A h O Bw hj).sizeAbove σ hσ hI hg wt g hdeg z hz hw

example {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt0 : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : GlobalTheory.GalNarrow7.PropsN π χ ι r wt0 HT) (w : HeightOneSpectrum (𝓞 E)) :
    Clause7At .iwa π ι r w := by
  intro P AI hAI A h O _ _ _ Bw hj σ hσ hI hg
  exact (H.above P AI hAI w A h O Bw hj).iwahori σ hσ hI hg

example {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt0 : ℤ}
    (H : ∀ w, Clause7At .pureDegreeZero π ι r w) (hw : IsWeight π wt0) :
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0) →
        ((wdOf h hl ι r).lpTw ((wt0 : ℝ) / 2)).tempered :=
  fun w hl A h hm => H w hl A h wt0 hw hm

example {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} (w : HeightOneSpectrum (𝓞 E))
    (H : Clause7At .pureDegreeZero π ι r w)
    (hN : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc →
      ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0) :
    ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered :=
  fun hl A h wt hw => H hl A h wt hw (hN A h)

example (H : Packages) : ClauseValidAtLevel .csd .pureDegreeZero := H.2.2.2.2 .pureDegreeZero

end GlobalTheory.GalCut7

end
