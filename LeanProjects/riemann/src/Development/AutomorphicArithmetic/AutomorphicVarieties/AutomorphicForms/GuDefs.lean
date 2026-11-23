import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (Ω) in

abbrev Par (w : HeightOneSpectrum (𝓞 E)) : Type 1 :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w), (IrrGL (w.adicCompletion E) → WD h) → WD h

abbrev cl {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : IrrGL (w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

def ParAt {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (p : Par Ω w) : Prop :=
  ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → Lev.WO ι r (p A h rc)) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) ∧
        Lev.SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (p A h rc)

theorem locGlob_iff {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : LocGlob ι r w σ ↔ ParAt ι r w fun _ _ rc => rc (algNorm σ) := Iff.rfl

theorem ParAt.congr {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {p p' : Par Ω w}
    (H : ParAt ι r w p) (e : ∀ A h rc, IsRec h rc → p A h rc = p' A h rc) : ParAt ι r w p' :=
  fun A h rc hrc => e A h rc hrc ▸ H A h rc hrc

structure Compat {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (p : ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  ht : HasHT r HT
  par : ∀ w, ParAt ι r w (p w)

def ex (n d k : ℕ) : ℤ := (d : ℤ) - 2 * k - n

def totPar (n : ℕ) {c : ℕ} {a : Fin c → ℕ} (d : Fin c → ℕ) {w : HeightOneSpectrum (𝓞 E)}
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) : Par Ω w := fun _ _ rc =>
  sumList (List.ofFn fun i => sumList (List.ofFn fun k : Fin (d i) => (rc (cl (ρ i))).lpTw ((ex n (d i) k : ℝ) / 2)))

def satTot (w : HeightOneSpectrum (𝓞 E)) {c : ℕ} (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) : Multiset ℂˣ :=
  ∑ i, ∑ k : Fin (d i), (S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))

end Defs

def SumAway : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x x' : WD h),
      IsWDOf ι r x → IsWDOf ι r' x' → IsWDOf ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (x.lpSum x')

def SumHT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)), Continuous r → Continuous r' →
    ∀ HT HT', HasHT r HT → HasHT r' HT' → HasHT (Formalism.MainNotions.SumRepresentations.At.sumRep r r') fun τ => HT τ + HT' τ

def SumTwo : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a b : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (r' : G E Ω →* GL (Fin b) (Qbar l)) p p' HT HT',
    Compat ι r p HT → Compat ι r' p' HT' →
      Compat ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (fun w A h rc => (p w A h rc).lpSum (p' w A h rc)) fun τ => HT τ + HT' τ

def SumRed : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a b : ℕ) (r : Γ →* GL (Fin a) k) (r' : Γ →* GL (Fin b) k), 1 ≤ a → 1 ≤ b →
    ¬ IsIrr (Formalism.MainNotions.SumRepresentations.At.sumRep r r')

def SumFam : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : ℕ), 1 ≤ c → ∀ (N : Fin c → ℕ), (∀ i, 1 ≤ N i) → ∀ (n : ℕ), ∑ i, N i = n →
    ∀ (r : ∀ i, G E Ω →* GL (Fin (N i)) (Qbar l)) (p : Fin c → ∀ w : HeightOneSpectrum (𝓞 E), Par Ω w)
      (HT : Fin c → (E →+* Qbar l) → Multiset ℤ), (∀ i, Compat ι (r i) (p i) (HT i)) →
      ∃ R : G E Ω →* GL (Fin n) (Qbar l),
        Compat ι R (fun w A h rc => sumList (List.ofFn fun i => p i w A h rc)) (fun τ => ∑ i, HT i τ) ∧
        (IsIrr R → c = 1 ∧ ∀ i, IsIrr (r i))

def Eta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (f : ℤ), ∃ (ξ : HChar E) (m : (E →+* ℂ) → ℤ), ξ.IsAlg m ∧
    compNorm E (GlobalTheory.HeightCounting.Blocks.resReal (GlobalTheory.HeckeGal.Model.absPow E ((f : ℝ) / 2) * ξ)) = 1

def TwistLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (P : CuspSub E a) (t : ℝ) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∃ σ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E t)).IsLocComp w σ ∧ cl σ = (cl ρ).nu (t : ℂ)

def CompatPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ξ : HChar E) (m : (E →+* ℂ) → ℤ),
    (CG.mk P).IsRegAlg → IsPolarized P χ → ξ.IsAlg m → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) →
    ∀ σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E)), (∀ w, P.IsLocComp w (σ w)) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => rc (algNorm (σ w))) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) =
          ((CG.mk P).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

def Half : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (P : CuspSub E a), P.IsCsd →
    ∀ (ρ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin a) (w.adicCompletion E))), (∀ w, P.IsLocComp w (ρ w)) →
    ∀ (m : (E →+* ℂ) → Multiset ℂ), (∀ τ, P.HasInfChar τ (m τ)) → ∀ e : ℤ,
      (∀ τ, (m τ).Nodup ∧ ∀ z ∈ m τ, ∃ j : ℤ, z + (e : ℂ) / 2 = j) →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (HT : (E →+* Qbar l) → Multiset ℤ),
        Compat ι r (fun w _ _ rc => (rc (cl (ρ w))).lpTw ((e : ℝ) / 2)) HT ∧
        ∀ τ : E →+* Qbar l, (HT τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map fun z => -(z + (e : ℂ) / 2)

def Strings : Prop :=
  ∀ (n c : ℕ) (d : Fin c → ℕ) (m : Fin c → Multiset ℂ) (lam : DomWeight n),
    ∑ i, GlobalTheory.DefiniteBC.spehInf (d i) (m i) = infOfWeight lam →
    (∀ i (k : Fin (d i)), (m i).Nodup ∧ ∀ z ∈ m i, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j) ∧
      ∑ i, ∑ k : Fin (d i), (m i).map (fun z => -(z + (ex n (d i) k : ℂ) / 2)) =
        (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z

def CompUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ₁ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ₂ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₁ →
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) ρ₂ → Nonempty (ρ₁.Equiv ρ₂)

def RecTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (n c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (w : HeightOneSpectrum (𝓞 E))
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (σ : ∀ i, SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))),
    (∀ i, 1 ≤ a i ∧ 1 ≤ d i) → (∀ i, (P i).IsLocComp w (ρ i)) →
    (∀ i, GlobalTheory.SmGL.IsUnitarisable (ρ i).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (σ i).ρ ∧ IsSpeh (cl (ρ i)) (d i) (σ i).ρ) →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
      totPar n d ρ A h rc = rc (algNorm τ)

def FrobTot : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n c : ℕ) (a d : Fin c → ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ), (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) →
      ParAt ι r w (totPar n d ρ) → FrobEig ι r w (algSat n (normV w) (satTot w d S))

def PolOfFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → IsSSRep r →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : Multiset ℂˣ,
      FrobEig ι r w (algSat n (normV w) (B.map (·⁻¹))) ∧ FrobEig ι r (Bc.cPl w) (algSat n (normV (Bc.cPl w)) B)) →
    ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c r (cycBar E Ω l ^ (1 - (n : ℤ))) P

def SatLink : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (P : CuspSub E a),
    (∀ (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w ρ →
      ∀ B, (CG.mk P).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w ρ.ρ B) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    (∀ (a : ℕ) (P : CuspSub E a), P.IsCsd → ∀ B, (CG.mk P).HasSat (Bc.cPl w) B → (CG.mk P).HasSat w (B.map (·⁻¹))) ∧
    ∀ (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ),
      satTot w d (fun i => (S i).map (·⁻¹)) = (satTot (Bc.cPl w) d S).map (·⁻¹)

def IrrCase : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (hn : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (m : Fin c → (E →+* ℂ) → Multiset ℂ),
      GlobalTheory.BcSpeh.Parts π a d hn P ρ m → c = 1 → (∀ i, d i = 1) → ∀ r : G E Ω →* GL (Fin n) (Qbar l), IsSSRep r →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
        FrobEig ι r w (algSat n (normV w) (satTot w d S))) →
      ∃ Q : CuspSub E n, (CG.mk Q).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj Q ∧ AttC ι r Q ∧
        ∀ φ lam, HasWeightAt π φ lam → Q.HasInfChar φ (infOfWeight lam)

end UpperTheory.V.Af.Gu
