import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.InsideRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)

namespace UpperTheory.Gal.Int.Div

def SubSplit : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ) (r : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin (a + b)) k), IsSSRep ρ → Inside r ρ →
    ∃ s : Γ →* GL (Fin b) k, RepIso ρ (sumRep r s)

def SSBlock : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a m n : ℕ) (e : (Σ _ : Fin m, Fin a) ≃ Fin n) (r : Γ →* GL (Fin a) k), IsSSRep r →
    IsSSRep (blockRep (a := fun _ : Fin m => a) e fun _ => r)

def CoverIn : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a d : ℕ) (r : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin d) k), Covers r ρ →
    ∃ (m n : ℕ) (e : (Σ _ : Fin m, Fin a) ≃ Fin n), Inside ρ (blockRep (a := fun _ : Fin m => a) e fun _ => r)

def IsoMove : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a d : ℕ) (r r' : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin d) k), RepIso r r' →
    (Inside r ρ → Inside r' ρ) ∧ (Covers r ρ → Covers r' ρ)

def InFacts : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a d : ℕ) (r : Γ →* GL (Fin a) k) (ρ : Γ →* GL (Fin d) k), Inside r ρ →
    a ≤ d ∧ (∀ g, ρ g = 1 → r g = 1) ∧
      ∀ (g : Γ) (Q : k[X]), aeval (ρ g : Matrix (Fin d) (Fin d) k) Q = 0 → aeval (r g : Matrix (Fin a) (Fin a) k) Q = 0

def SepPin : Prop :=
  ∀ (k : Type) [Field k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (Q : k[X]), Q.Monic → Q.natDegree = a → aeval M Q = 0 →
    M.charpoly.Separable → M.charpoly = Q

def RootPin : Prop :=
  ∀ (p : ℂ[X]) (s : Multiset ℂ) (m : ℕ), p.Monic → p.natDegree = s.card → p ∣ rootPol s ^ m → p.roots.prod = s.prod →
    GenericMul s → p = rootPol s

def AlgGen : Prop :=
  ∀ (a q : ℕ) (B : Multiset ℂˣ), q ≠ 0 → GenericMul B → GenericMul (algSat a q B)

def GenPin : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (M : Matrix (Fin a) (Fin a) (Qbar l)) (s : Multiset ℂ), s.card = a → GenericMul s →
    aeval M (((s.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0 → ι M.det = s.prod →
    M.charpoly.map ι.toRingHom = (s.map fun b => X - C b).prod

def DGenMul : Prop :=
  ∀ (a q : ℕ) (B : Multiset ℂˣ), 1 ≤ a → B.card = a → GlobalTheory.CongW.GenOf DGen a q B → GenericMul B

def LocConj : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a : ℕ) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)),
    (IsCrysAt P Bw r → IsdRAt P Bw r ∧ IsPstAt P Bw r) ∧ (RepIso r r' →
      (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧ (IsdRAt P Bw r → IsdRAt P Bw r') ∧
      (∀ τ J, IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J) ∧
      ∀ (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hj : Induces Bw), IsCrysAt P Bw r →
        wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r)

def LocSum : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (s : ↥(Dec (F := E) A) →* GL (Fin b) (Qbar l)),
    (IsCrysAt P Bw (sumRep r s) → IsCrysAt P Bw r ∧ IsCrysAt P Bw s) ∧
      ∀ (τ : E →+* Qbar l) (J J' : Multiset ℤ), IsJumpsAt P Bw (sumRep r s) τ J → IsJumpsAt P Bw r τ J' → J' ≤ J

def JumpCard : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)), IsdRAt P Bw r →
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      ∃ J : Multiset ℤ, IsJumpsAt P Bw r τ J ∧ J.card = a

def SubLoc : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a d : ℕ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (ρ : G E Ω →* GL (Fin d) (Qbar l)), IsSSRep ρ → Inside r ρ →
    ∀ (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)), ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
      (IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g ∣
          (wdAt P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype)).charPol g) ∧
      ∀ (τ : E →+* Qbar l) (J J' : Multiset ℤ), IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J →
        IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J' → J' ≤ J

def JumpCondition : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a dd : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)) (r : G E Ω →* GL (Fin a) (Qbar l)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), IsSSRep r → Covers r ρ →
    ∀ w : HeightOneSpectrum (𝓞 E), CrysAt r w → JumpsOcc U ι ρ w → CrysDRU U ι r w

def LacBridge : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a dd : ℕ)
    (ρ : G E Ω →* GL (Fin dd) (Qbar l)), HTRichEx ρ a → HTLac ρ a

def RichEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a dd : ℕ)
    (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (v : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → HTRichAt ρ a v → HTRichEx ρ a

def DenseUs : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a d : ℕ), ImQ E d →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ X : Finset (HeightOneSpectrum (𝓞 E)),
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ X ∧ UsPl d w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      (∃ B, SatU U w B) ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g}

def DetFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)) (ψ : G E Ω →* (Qbar l)ˣ), IsDetChar ι U ψ →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B →
    ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ψ s = 1) ∧
      ∀ σ : G E Ω, IsFrob A (normV w) σ → ι ((ψ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (algSat a (normV w) B).prod

def DivSet : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a dd : ℕ)
    (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Continuous ρ → IsSSRep ρ → HTRichEx ρ a →
    ∀ ψ : G E Ω →* (Qbar l)ˣ, Continuous ψ →
    Dense {g : G E Ω | ∃ Q : (Qbar l)[X], Q.Monic ∧ Q.natDegree = a ∧ aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0} →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧ Inside r ρ ∧ Covers r ρ ∧
      IsOpen {g : G E Ω | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable} ∧
      Dense {g : G E Ω | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable}

def DivOne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a d : ℕ), ImQ E d →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ ψ : G E Ω →* (Qbar l)ˣ, IsDetChar ι U ψ →
    ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), IsDivRep ι d U r ∧ Inside r ρ ∧ Covers r ρ

def DivUniq : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a d : ℕ), ImQ E d →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ (r r' : G E Ω →* GL (Fin a) (Qbar l)),
    IsDivRep ι d U r → IsDivRep ι d U r' → RepIso r r'

def DivDet : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a d : ℕ), ImQ E d →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ ψ : G E Ω →* (Qbar l)ˣ, IsDetChar ι U ψ →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)), IsDivRep ι d U r →
    ∀ g, (r g : Matrix (Fin a) (Fin a) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)

def FrobeniusCondition : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a dd : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)) (ψ : G E Ω →* (Qbar l)ˣ), IsDetChar ι U ψ →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), Inside r ρ →
    (∀ g, (r g : Matrix (Fin a) (Fin a) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B : Multiset ℂˣ, SatU U w B → GenericMul B →
      ESAt ι ρ w (algSat a (normV w) B) → FrobEig ι r w (algSat a (normV w) B)

def CentU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U →
    ∃ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ B : Multiset ℂˣ, SatU U w B →
      χ.UnrAt w ∧ χ.val w = B.prod

theorem phiOfDiv_of (h1 : DetEx) (h2 : DivDet) (h3 : PhiSeed) : PhiOfDiv := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd U hU r hr dd ρ hc hs hin w hw B hB hg hk
  obtain ⟨ψ, hψ⟩ := h1 E Ω l ι a ha U hU
  exact h3 E Ω l ι a dd U ψ hψ r ρ hc hs hin (h2 E Ω l ι a d hd U hU ψ hψ r hr) w hw B hB hg hk

theorem divAll_of (h1 : DetEx) (h2 : DivDet) (h3 : PhiSeed) (h4 : DivOne) (h5 : DivUniq) (h6 : IsoMove) (h7 : FrobeniusCondition)
    (h8 : JumpCondition) (h9 : SubLoc) : DivAll := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd U hU ⟨d₀, ρ₀, h₀⟩
  obtain ⟨ψ, hψ⟩ := h1 E Ω l ι a ha U hU
  obtain ⟨r, hr, -, -⟩ := h4 E Ω l ι a d hd U hU ψ hψ d₀ ρ₀ h₀
  have hdet := h2 E Ω l ι a d hd U hU ψ hψ r hr
  refine ⟨r, hr, fun dd ρ hρ w => ?_⟩
  obtain ⟨r', hr', hin', hco'⟩ := h4 E Ω l ι a d hd U hU ψ hψ dd ρ hρ
  obtain ⟨m1, m2⟩ := h6 _ _ a dd r' r ρ (h5 E Ω l ι a d hd U hU r' r hr' hr)
  refine ⟨fun hw hl B hB hg he => h7 E Ω l ι a dd U ψ hψ r ρ (m1 hin') hdet w hw hl B hB hg he, fun hc hj => ?_,
    fun hw B hB hg hk => h3 E Ω l ι a dd U ψ hψ r ρ hρ.1 hρ.2.1 (m1 hin') hdet w hw B hB hg hk⟩
  refine h8 E Ω l ι a dd U r ρ hr.2.1 (m2 hco') w (fun P AI hT A h O _ _ _ Bw hBw => ?_) hj
  exact ((h9 E Ω l a dd r ρ hρ.2.1 (m1 hin') ι w P AI hT A h O Bw hBw).1 (hc P AI hT A h O Bw hBw)).1

end UpperTheory.Gal.Int.Div

end
