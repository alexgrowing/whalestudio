import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.RowDefOfOdd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

def DgFacts : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (t : ℕ) (a : Fin t → Γ →* kˣ), IsSSRep (dg a) ∧ ∀ g, cp (dg a) g = lin a g

def CpFacts : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ), (∀ (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) g, cp (sumRep r s) g = cp r g * cp s g) ∧
    (∀ (c : Γ →* kˣ) g, cp (rk1 c) g = X - C (c g : k)) ∧
    ∀ r r' : Γ →* GL (Fin a) k, RepIso r r' → ∀ g, cp r' g = cp r g

def EigTransfer : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] [IsAlgClosed k] [CharZero k] (N N' : ℕ) (ρ : Γ →* GL (Fin N) k) (ρ' : Γ →* GL (Fin N') k), IsSSRep ρ → IsSSRep ρ' → (∀ g, cp ρ g = cp ρ' g) →
    ∀ c : Γ →* kˣ, (∃ v : Fin N' → k, v ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin N') (Fin N') k).mulVec v = (c g : k) • v) →
      ∃ v : Fin N → k, v ≠ 0 ∧ ∀ g, (ρ g : Matrix (Fin N) (Fin N) k).mulVec v = (c g : k) • v

def EigSum : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (m t : ℕ) (r : Γ →* GL (Fin m) k) (a : Fin t → Γ →* kˣ) (c : Γ →* kˣ),
    ((∃ i, a i = c) → ∃ v : Fin (m + t) → k, v ≠ 0 ∧
      ∀ g, (sumRep r (dg a) g : Matrix (Fin (m + t)) (Fin (m + t)) k).mulVec v = (c g : k) • v) ∧
    ((∀ i, a i ≠ c) → (∃ v : Fin (m + t) → k, v ≠ 0 ∧
      ∀ g, (sumRep r (dg a) g : Matrix (Fin (m + t)) (Fin (m + t)) k).mulVec v = (c g : k) • v) →
      ∃ v : Fin m → k, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin m) (Fin m) k).mulVec v = (c g : k) • v)

def SplitLine : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (m : ℕ) (r : Γ →* GL (Fin (m + 1)) k), IsSSRep r → ∀ c : Γ →* kˣ,
    (∃ v : Fin (m + 1) → k, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v = (c g : k) • v) →
    ∃ s : Γ →* GL (Fin m) k, RepIso r (sumRep s (rk1 c))

def SSLeft : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ), (∀ (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k), IsSSRep (sumRep r s) → IsSSRep r) ∧
    (∀ r r' : Γ →* GL (Fin a) k, RepIso r r' → IsSSRep r → IsSSRep r') ∧
    ∀ (r : Γ →* GL (Fin a) k) (c : Γ →* kˣ), IsSSRep r → IsSSRep (tw r c)

def ContLeft : Prop :=
  ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k] [IsTopologicalRing k] (a b : ℕ),
    (∀ (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k), Continuous (sumRep r s) → Continuous r) ∧
    (∀ r r' : Γ →* GL (Fin a) k, RepIso r r' → Continuous r → Continuous r') ∧
    (∀ (r : Γ →* GL (Fin a) k) (c : Γ →* kˣ), Continuous r → Continuous c → Continuous (tw r c)) ∧
    ∀ c : Γ →* kˣ, Continuous c → Continuous (rk1 c)

def PeelOne : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] [IsAlgClosed k] [CharZero k] (m m' t t' : ℕ) (r : Γ →* GL (Fin (m + 1)) k) (r' : Γ →* GL (Fin m') k) (a : Fin (t + 1) → Γ →* kˣ)
    (a' : Fin t' → Γ →* kˣ), IsSSRep r → IsSSRep r' → (∀ i j, a i ≠ a' j) → (∀ g, cp r g * lin a' g = cp r' g * lin a g) →
    ∃ s : Γ →* GL (Fin m) k, IsSSRep s ∧ RepIso r (sumRep s (rk1 (a (Fin.last t)))) ∧
      ∀ g, cp s g * lin a' g = cp r' g * lin (fun i : Fin t => a i.castSucc) g

def DenseId : Prop :=
  ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (l : ℕ) [Fact l.Prime] (m m' t t' : ℕ) (r : Γ →* GL (Fin m) (Qbar l))
    (r' : Γ →* GL (Fin m') (Qbar l)) (a : Fin t → Γ →* (Qbar l)ˣ) (a' : Fin t' → Γ →* (Qbar l)ˣ), Continuous r → Continuous r' →
    (∀ i, Continuous (a i)) → (∀ j, Continuous (a' j)) → ∀ D : Set Γ, Dense D →
    (∀ g ∈ D, cp r g * lin a' g = cp r' g * lin a g) → ∀ g, cp r g * lin a' g = cp r' g * lin a g

def PstOfDR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)), Continuous r → IsdRAt P Bw r → IsPstAt P Bw r

def SumDR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (s : ↥(Dec (F := E) A) →* GL (Fin b) (Qbar l)), IsdRAt P Bw (sumRep r s) →
    IsdRAt P Bw r ∧ IsdRAt P Bw s ∧ ∀ (τ : E →+* Qbar l) (J J' : Multiset ℤ),
      IsJumpsAt P Bw (sumRep r s) τ (J + J') → IsJumpsAt P Bw s τ J' → IsJumpsAt P Bw r τ J

def TwJumps : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (c : ↥(Dec (F := E) A) →* (Qbar l)ˣ), Continuous r → Continuous c →
    ∀ (τ : E →+* Qbar l) (J : Multiset ℤ) (m : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 c) τ {m} →
      IsJumpsAt P Bw (tw r c) τ (J.map (· + m))

def WDFacts : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h),
    ((x.lpSum y).unr → x.unr) ∧ (∀ g, (x.lpSum y).charPol g = x.charPol g * y.charPol g) ∧
    (x.unr → y.unr → (x.lpChar y).unr) ∧
    ∀ (g : Weil h) (S : Multiset ℂ) (c : ℂ), x.charPol g = unrPol S (deg g) → y.charPol g = unrPol {c} (deg g) →
      (x.lpChar y).charPol g = unrPol (S.map (· * c)) (deg g)

def FrobSub : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ) (c : ℂ) (μ : G E Ω →* (Qbar l)ˣ), FrobEig ι (rk1 μ) w {c} →
    (∀ s : G E Ω →* GL (Fin a) (Qbar l), FrobEig ι (sumRep s (rk1 μ)) w (S + {c}) → FrobEig ι s w S) ∧
    ∀ s : G E Ω →* GL (Fin a) (Qbar l), FrobEig ι s w S → FrobEig ι (tw s μ) w (S.map (· * c))

def ClConj : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → RepIso r r' → ∀ (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
    Cl ι r w S J → Cl ι r' w S J

def ClSub : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (s : G E Ω →* GL (Fin a) (Qbar l)) (μ : G E Ω →* (Qbar l)ˣ), Continuous s → Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ) (c : ℂ) (J : (E →+* Qbar l) → Multiset ℤ) (m : (E →+* Qbar l) → ℤ), Cl ι (rk1 μ) w {c} (fun τ => {m τ}) →
    Cl ι (sumRep s (rk1 μ)) w (S + {c}) (fun τ => J τ + {m τ}) → Cl ι s w S J

def ClTw : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (s : G E Ω →* GL (Fin a) (Qbar l)) (μ : G E Ω →* (Qbar l)ˣ), Continuous s → Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ) (c : ℂ) (J : (E →+* Qbar l) → Multiset ℤ) (m : (E →+* Qbar l) → ℤ), Cl ι (rk1 μ) w {c} (fun τ => {m τ}) →
    Cl ι s w S J → Cl ι (tw s μ) w (S.map (· * c)) (fun τ => (J τ).map (· + m τ))

def ClAway : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (S : Multiset ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
    Cl ι r w S J ↔ FrobEig ι r w S

def PeelAll : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n m' t' : ℕ) (r' : G E Ω →* GL (Fin m') (Qbar l)) (a' : Fin t' → G E Ω →* (Qbar l)ˣ), IsSSRep r' →
    ∀ (t : ℕ) (r : G E Ω →* GL (Fin (n + t)) (Qbar l)) (a : Fin t → G E Ω →* (Qbar l)ˣ), Continuous r → IsSSRep r → (∀ i, Continuous (a i)) →
    (∀ i j, a i ≠ a' j) → (∀ g, cp r g * lin a' g = cp r' g * lin a g) →
    ∃ s : G E Ω →* GL (Fin n) (Qbar l), Continuous s ∧ IsSSRep s ∧ ∀ (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂ) (c : Fin t → ℂ) (J : (E →+* Qbar l) → Multiset ℤ)
      (m : Fin t → (E →+* Qbar l) → ℤ), (∀ i, Cl ι (rk1 (a i)) w {c i} fun τ => {m i τ}) →
      Cl ι r w (S + Finset.univ.val.map c) (fun τ => J τ + Finset.univ.val.map fun i => m i τ) → Cl ι s w S J

def CharFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → χ.UnrAt w → FrobEig ι (rk1 μ) w {((χ.val w : ℂˣ) : ℂ)}

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)), χ.UnrAt w →
      Above ι (rk1 μ) w {((χ.val w : ℂˣ) : ℂ)} fun τ => {-n (ι.toRingHom.comp τ)}

def CharInj : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ χ' : HChar E) (n n' : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsLAdicOf art ι χ n μ → IsLAdicOf art ι χ' n' μ → χ = χ'

def CharEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ),
    (∀ χ n, IsAlgPos χ n → Continuous (L χ n) ∧ ∀ w, χ.UnrAt w →
      Cl ι (rk1 (L χ n)) w {((χ.val w : ℂˣ) : ℂ)} fun τ => {-n (ι.toRingHom.comp τ)}) ∧
    ∀ χ n χ' n', IsAlgPos χ n → IsAlgPos χ' n' → L χ n = L χ' n' → χ = χ'

def SatAE : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, SatU U w B

def WeakIso : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ r r' : G E Ω →* GL (Fin a) (Qbar l), WeakU ι U r → WeakU ι U r' → RepIso r r'

def FrobId : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (d t : ℕ) (r r' : G E Ω →* GL (Fin d) (Qbar l)) (a a' : Fin t → G E Ω →* (Qbar l)ˣ), Continuous r → Continuous r' →
    (∀ i, Continuous (a i)) → (∀ j, Continuous (a' j)) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ (S : Multiset ℂ) (c c' : Fin t → ℂ),
      FrobEig ι r w (S + Finset.univ.val.map c) ∧ FrobEig ι r' w (S + Finset.univ.val.map c') ∧
      (∀ i, FrobEig ι (rk1 (a i)) w {c i}) ∧ ∀ j, FrobEig ι (rk1 (a' j)) w {c' j}) →
    ∀ g, cp r g * lin a' g = cp r' g * lin a g

def AtPlace : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), (∀ d, Odd d → RowAt E Ω ι d) → TwoUp E n →
    ∀ (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight n, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∀ w₀, IsSplitAt w₀ → ∃ r : G E Ω →* GL (Fin n) (Qbar l), WeakU ι U r ∧
      ∀ B, SatU U w₀ B → Cl ι r w₀ (algSat n (normV w₀) B) (GlobalTheory.GalDef.jumpsOf ι lam)

def SplitEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w

def SatPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (g : Weil h),
    (GlobalTheory.RoadU.satWD h a B).charPol g = unrPol (algSat a (normV w) B) (deg g)

def TwLoc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (c : ↥(Dec (F := E) A) →* (Qbar l)ˣ),
    (IsdRAt P Bw r → IsdRAt P Bw (rk1 c) → IsdRAt P Bw (tw r c)) ∧
    (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 c) → IsCrysAt P Bw (tw r c))

def HCharExt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E),
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ x, χ.loc w x = 1) → χ = 1

theorem subtract_of (h1 : AtPlace) (h2 : SplitEx) (h3 : WeakIso) (h4 : ClConj) : Subtract := by
  intro E Ω _ _ _ _ _ _ l _ ι n hO hT U hU lam hl
  refine ⟨?_, fun r hr w hw B hB => ?_⟩
  · obtain ⟨w, hw⟩ := h2 E
    obtain ⟨r, hr, -⟩ := h1 E Ω l ι n hO hT U hU lam hl w hw
    exact ⟨r, hr⟩
  · obtain ⟨s, hs, hc⟩ := h1 E Ω l ι n hO hT U hU lam hl w hw
    exact h4 E Ω l ι n s r hs.1 (h3 E Ω l ι n U hU s r hs hr) w _ _ (hc B hB)

end UpperTheory.Gal.TP.Sub

end
