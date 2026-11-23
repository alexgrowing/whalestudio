import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.MonodromyFreeOfNoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwR (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwR.of_eq {x y : WD h} (e : x = y) : AwR x y := ⟨fun _ => by rw [e], fun _ => e⟩

theorem AwR.of_aw {x y : WD h} (k : Aw x y) : AwR x y := ⟨k.pol, k.n0⟩

theorem AwR.eq_unr {x y : WD h} (k : AwR x y) (hy : y.unr) : x = y := k.n0 (WD.unr_mono0 _ hy)

theorem AwR.eq_of_noRatio {x y : WD h} (k : AwR x y) {g : ↥(Weil h)} (hx : NoRatio x g) : x = y :=
  k.n0 (monodromyFree_of_noRatio (g := g) (by simpa only [NoRatio, WD.eig, k.pol] using hx))

def RatioW (x : WD h) : Prop :=
  ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖
end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRU (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → AwR (wdOf h hl ι r) (rc (algNorm σ))
  ratio : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      RatioW (wdOf h hl ι r)
  weights : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z
  weights_sym : ∀ τ : F →+* Qbar l, HT τ = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsdRAt P Bw (r.comp (Dec (F := F) A).subtype) ∧
      (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)) ∧
      (∀ σ, π.IsLocComp w σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin a)) ≠ ⊥ →
        GlobalTheory.SmGL.IsSpherical σ.ρ → ∀ rc, IsRec h rc →
          (∀ g : ↥(Weil h), (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
          ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).mono0)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)
end Real

def GaloisRepRealN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
      ∃ (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT

def GaloisRepRankTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) [Fact (a = 2)], 1 ≤ a →
    ∀ (π : TR.CuspSub F a) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
      ∃ (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT

def ExRN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT ∧ AttR ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttR ι r' π → IsGalRU π ι r' wt HT

theorem galoisRepRankTwo_of_real (h : GaloisRepRealN) : GaloisRepRankTwo := fun F Ω _ _ _ _ _ _ l _ ι a _ => h F Ω l ι a

end UpperTheory.GalN.V
