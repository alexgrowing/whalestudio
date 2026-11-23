import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem wn (k : Lev.WO ι r y) : WDN ι r y := .of_isWDOf k
theorem woOf (k : IsWDOf ι r y) : Lev.WO ι r y := k
theorem woConj (k : Lev.WO ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : Lev.WO ι r' y := IsWDOf.of_conj hl P hP k
theorem woSum (hA : Gu.SumAway) {m : ℕ} {r' : G E Ω →* GL (Fin m) (Qbar l)} (hc : Continuous r) (hc' : Continuous r')
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {y' : WD h} (k : Lev.WO ι r y) (k' : Lev.WO ι r' y') :
    Lev.WO ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (y.lpSum y') := hA E Ω l ι n m r r' hc hc' w hl A h _ _ k k'
theorem woChar (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)} {z : WD h} (hz : z.lpDim = 1)
    (e : IsWDOf ι r' ((wdOf h hl ι r).lpChar z)) (k : Lev.WO ι r y) : Lev.WO ι r' (y.lpChar z) := by
  rwa [IsWDOf.wdOf_eq hl k] at e
theorem galEx (H : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (hr : (CG.mk π).IsRegAlg) (hp : IsPolarized π χ) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalU π χ ι r wt HT ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → Lev.WO ι r (rc (algNorm σ)) := by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, .of_old k, k.away⟩

theorem realAway (H : ExR) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)] (hn : 1 ≤ n) (π : TR.CuspSub F n) (χ : HChar F)
    (hreg : π.IsRegAlg) (hpol : π.Polarized χ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hatt : AttR ι r π)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A v)
    (rc : IrrGL (v.adicCompletion F) → WD h) (hrc : IsRec h rc) (σ) (hσ : π.IsLocComp v σ) : Lev.WO ι r (rc (algNorm σ)) := by
  obtain ⟨-, wt, HT, -, -, hG⟩ := H F Ω l ι n hn π χ hreg hpol
  exact (hG r hr hatt).away v hv A h rc hrc σ hσ

theorem realAway' (H : ExRN) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)] (hn : 1 ≤ n) (π : TR.CuspSub F n) (χ : HChar F)
    (hreg : π.IsRegAlg) (hpol : π.Polarized χ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hatt : AttR ι r π)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A v)
    (rc : IrrGL (v.adicCompletion F) → WD h) (hrc : IsRec h rc) (σ) (hσ : π.IsLocComp v σ) : WDN ι r (rc (algNorm σ)) := by
  obtain ⟨-, wt, HT, -, -, hG⟩ := H F Ω l ι n hn π χ hreg hpol
  exact .of_aw hv hr ⟨((hG r hr hatt).away v hv A h rc hrc σ hσ).pol, ((hG r hr hatt).away v hv A h rc hrc σ hσ).n0⟩

theorem satFrobW (P : Hypotheses₂) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ)
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
      Lev.WO ι r (rc (algNorm σ))) : FrobEig ι r w (algSat n (normV w) B) :=
  satFrob P F Ω l ι n r hc w hw σ B hB fun A h rc hrc => (wn (H A h rc hrc)).of_hasSat hrc hB

end UpperTheory.GalN.V
