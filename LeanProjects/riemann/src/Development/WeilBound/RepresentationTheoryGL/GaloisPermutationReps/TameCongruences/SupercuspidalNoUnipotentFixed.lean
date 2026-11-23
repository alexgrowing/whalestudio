import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.CongruenceClosedIdempotent
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitaryStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.UnitaryBC GlobalTheory.CuspRep
open PositivityTheory.Rg.DzCount (FinCusp IsTypeMap Fwd)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCong

structure In : Prop where
  llc : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  multi : GlobalTheory.Published.LanglandsMultisegments
  cos : GlobalTheory.Published.StandardCosocleGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  geo : GlobalTheory.Published.GeometricLemma
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  bcs : GlobalTheory.BcSpeh.BcSpeh
  gal : GlobalTheory.Published.PolarizedGaloisRepPublished
  gk : GlobalTheory.Published.GelfandKazhdanDual

def StF : Prop :=
  ∀ (K W : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (n : ℕ), 2 ≤ n → ∀ τ : Representation ℂ (GL (Fin n) K) W, FinCusp τ →
    (∀ g, (¬ ∃ m : ℕ, g ^ p ^ m = 1) → LinearMap.trace ℂ W (τ g) = 0) → Subsingleton W

def MobiusInductionFull : Prop := StableSubspaceMobius → StF

def Core : Prop :=
  ∀ (K X I : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) [MulAction (GL (Fin n) K) X] [Fintype X]
    (T : I → Matrix X X ℤ), 2 ≤ n → Free (GL (Fin n) K) X → Fam (GL (Fin n) K) T → ∀ W : (I → ℂ) → Prop,
    (∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∃ ι : Qbar l ≃+* ℂ, ∀ θ θ', Eig T θ ≠ ⊥ → Eig T θ' ≠ ⊥ →
      (∀ i, ‖ι.symm (θ i) - ι.symm (θ' i)‖ < 1) → W θ → W θ') →
    (∀ θ, W θ → ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad K e ≠ ⊥ →
      ∀ f ∈ Eig T θ, (∀ u ∈ unipRad K e, permRep (GL (Fin n) K) X u f = f) → f = 0) →
    ∀ θ, Eig T θ ≠ ⊥ → ¬ W θ

def StCore : Prop := StF → FreeActionIdempotentTrace → CongruenceClosedIdempotent → Core

section Glob

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Ix (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {u : HeightOneSpectrum (𝓞 E) // IsSplitAt u ∧ u ∉ S} × Fin (n + 1)

def hk (u : HeightOneSpectrum (𝓞 E)) (k : ℕ) (φ : UA E n → ℂ) : UA E n → ℂ :=
  GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n u).subtype) ((GlobalTheory.LFun.KGL u n).comap ((cLoc u).comp (locU n u).subtype))
    (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E u) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k))
      ((cLoc u).comp (locU n u).subtype x)) φ

def SphAt (u : HeightOneSpectrum (𝓞 E)) (φ : UA E n → ℂ) : Prop :=
  ∀ x ∈ locU n u, cLoc u x ∈ GlobalTheory.LFun.KGL u n → RU E n x φ = φ

def SatSys (S : Set (HeightOneSpectrum (𝓞 E))) (π : Submodule ℂ (UA E n → ℂ)) (θ : Ix E n S → ℂ) : Prop :=
  ∀ (u : HeightOneSpectrum (𝓞 E)) (hu : IsSplitAt u ∧ u ∉ S), IsUnramU π u ∧
    ∃ (σ : SmIrr (GL (Fin n) (u.adicCompletion E))) (B : Multiset ℂˣ),
      IsCompAlong π (locU n u) ((cLoc u).comp (locU n u).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL u σ.ρ B ∧
      ∀ k : Fin (n + 1), θ (⟨u, hu⟩, k) = GlobalTheory.LFun.satEig (Formalism.UG.qV E u) n B k

def EquiAt (w : HeightOneSpectrum (𝓞 E)) {X : Type} [MulAction (GL (Fin n) 𝓀[w.adicCompletion E]) X]
    (ψ : (X → ℂ) →ₗ[ℂ] (UA E n → ℂ)) : Prop :=
  ∀ x ∈ locU n w, ∀ g : KO (w.adicCompletion E) (Fin n), cLoc w x = (g : GL (Fin n) (w.adicCompletion E)) →
    ∀ f, ψ (permRep _ X (redK (w.adicCompletion E) (Fin n) g) f) = RU E n x (ψ f)

end Glob

def SmallLevelClassSet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (_ : MulAction (GL (Fin n) 𝓀[w.adicCompletion E]) X)
      (S : Set (HeightOneSpectrum (𝓞 E))) (T : Ix E n S → Matrix X X ℤ) (Φ : (X → ℂ) →ₗ[ℂ] (UA E n → ℂ)),
      S.Finite ∧ Free (GL (Fin n) 𝓀[w.adicCompletion E]) X ∧ Fam (GL (Fin n) 𝓀[w.adicCompletion E]) T ∧
      Function.Injective Φ ∧ (∀ f, IsAutFormU (Φ f)) ∧ EquiAt w Φ ∧
      ∀ (i : Ix E n S) f, SphAt i.1.1 (Φ f) ∧ Φ (((T i).map (Int.cast : ℤ → ℂ)).mulVec f) = hk i.1.1 i.2 (Φ f)

def AutomorphicFormNonzeroImage : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → φ ≠ 0 →
    ∃ (π : Submodule ℂ (UA E n → ℂ)) (pr : (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ)), IsAutRepU π ∧ pr φ ≠ 0 ∧
      ∀ φ', IsAutFormU φ' → pr φ' ∈ π ∧ ∀ x, pr (RU E n x φ') = RU E n x (pr φ')

def LocalComponentNonzero : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → ∀ v ∈ π, v ≠ 0 →
      ∃ q : (UA E n → ℂ) →ₗ[ℂ] σ.V, q v ≠ 0 ∧ ∀ x ∈ locU n w, ∀ v' ∈ π, q (RU E n x v') = σ.ρ (cLoc w x) (q v')

def Pack : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ), 1 ≤ n → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (_ : MulAction (GL (Fin n) 𝓀[w.adicCompletion E]) X)
      (S : Set (HeightOneSpectrum (𝓞 E))) (T : Ix E n S → Matrix X X ℤ),
      S.Finite ∧ Free (GL (Fin n) 𝓀[w.adicCompletion E]) X ∧ Fam (GL (Fin n) 𝓀[w.adicCompletion E]) T ∧
      ∀ θ, ∀ f ∈ Eig T θ, f ≠ 0 → ∃ (π : Submodule ℂ (UA E n → ℂ)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
        (q : (X → ℂ) →ₗ[ℂ] σ.V), IsAutRepU π ∧ SatSys S π θ ∧
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ q f ≠ 0 ∧
        ∀ (g : KO (w.adicCompletion E) (Fin n)) f', q (permRep _ X (redK (w.adicCompletion E) (Fin n) g) f') =
          σ.ρ (g : GL (Fin n) (w.adicCompletion E)) (q f')

def StPack : Prop := In → SmallLevelClassSet → AutomorphicFormNonzeroImage → LocalComponentNonzero → Pack

def GalCusp : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ f : ℂ, (∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, f - z = k) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      (∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ →
        ∀ s : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (s : G E Ω) →
          (r (s : G E Ω)).val.charpoly.map ι.toRingHom = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol s

def GaloisCuspidalOfInput : Prop := In → GalCusp

def GalU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    ∃ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r ∧ GlobalTheory.GalDef.FrobSat ι π (-1) (fun g => (r g).val.charpoly) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
        ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ →
        ∀ s : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (s : G E Ω) →
          (r (s : G E Ω)).val.charpoly.map ι.toRingHom = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol s

def GaloisUnitaryOfCuspidal : Prop := In → LocalComponentNonzero → GalCusp → GalU

def Cong {l : ℕ} [Fact l.Prime] (P Q : (Qbar l)[X]) : Prop := ∀ i, ‖P.coeff i - Q.coeff i‖ < 1

def CongruenceSplitFrobenius : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r r' : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → Continuous r' → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    (∀ u, IsSplitAt u → u ∉ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B u → IsFrob (F := E) B (normV u) g →
      Cong (r (g ^ (-1 : ℤ))).val.charpoly (r' (g ^ (-1 : ℤ))).val.charpoly) →
    ∀ g, Cong (r g).val.charpoly (r' g).val.charpoly

def WildUnipotentCharpoly : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (y : WD h) (s : Weil h), Formalism.MainNotions.BlochKatoReduction.IsWild A (s : G E Ω) → ∀ P : (Qbar l)[X], P.map ι.toRingHom = y.charPol s →
      Cong P ((X - 1) ^ y.lpDim) → y.charPol s = (X - 1) ^ y.lpDim

def CongruentHeckePolynomials : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (q n : ℕ), q ≠ 0 → ∀ B B' : Multiset ℂˣ, B.card = n → B'.card = n →
    (∀ k ≤ n, ‖ι.symm (GlobalTheory.LFun.satEig q n B k) - ι.symm (GlobalTheory.LFun.satEig q n B' k)‖ < 1) →
    Cong (B.map fun z : ℂˣ => X - C (ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod
      (B'.map fun z : ℂˣ => X - C (ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def TameCong : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ), 1 ≤ n → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → ∀ (π π' : Submodule ℂ (UA E n → ℂ)) (θ θ' : Ix E n S → ℂ),
    IsAutRepU π → IsAutRepU π' → SatSys S π θ → SatSys S π' θ' → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ i, ‖ι.symm (θ i) - ι.symm (θ' i)‖ < 1) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
      ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ σ σ' : SmIrr (GL (Fin n) (w.adicCompletion E)),
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ →
        IsCompAlong π' (locU n w) ((cLoc w).comp (locU n w).subtype) σ'.ρ →
        IsTameWD (rc (IrrGL.of σ.ρ σ.smooth σ.irred)) → IsTameWD (rc (IrrGL.of σ'.ρ σ'.smooth σ'.irred))

def StC : Prop := GalU → CongruenceSplitFrobenius → WildUnipotentCharpoly → CongruentHeckePolynomials → TameCong

def SupercuspidalNoUnipotentFixed : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (π : IrrRep (GL (Fin n) k)), IsCuspidal π.ρ → ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
    unipRad 𝓀[k] e ≠ ⊥ → ∀ v : π.V,
    (∀ g : KO k (Fin n), redK k (Fin n) g ∈ unipRad 𝓀[k] e → π.ρ (g : GL (Fin n) k) v = v) → v = 0

def NonSupercuspidalTame : Prop :=
  In → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
    ∀ x : IrrGL (w.adicCompletion E), ¬ x.IsCusp → fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ →
    (∀ y : IrrGL (w.adicCompletion E), y.IsCusp → y.1 < x.1 → fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ →
      IsTameWD (rc y)) → IsTameWD (rc x)

def DepthZeroContainsCuspidal : Prop :=
  SupercuspidalNoUnipotentFixed → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (π : IrrRep (GL (Fin n) k)), IsCuspidal π.ρ → fixed π.ρ (KOne k (Fin n)) ≠ ⊥ →
    ∃ (τ : FDRep ℂ (GL (Fin n) 𝓀[k])) (j : τ →ₗ[ℂ] π.V), Representation.IsIrreducible τ.ρ ∧ FinCusp τ.ρ ∧ IsTypeMap τ.ρ π.ρ j

def SameCuspidalTypeDiffer : Prop :=
  ∀ (k W : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (n : ℕ), 0 < n →
    ∀ τ : Representation ℂ (GL (Fin n) 𝓀[k]) W, τ.IsIrreducible → FinCusp τ →
    ∀ (π π' : IrrRep (GL (Fin n) k)) (j : W →ₗ[ℂ] π.V) (j' : W →ₗ[ℂ] π'.V), IsTypeMap τ π.ρ j → IsTypeMap τ π'.ρ j' →
    ∃ χ hχ, IsUnram χ ∧ cls π' = (cls π).tw χ hχ

def UnramifiedTwistTame : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
    ∀ (x : IrrGL (w.adicCompletion E)) χ hχ, IsUnram χ → IsTameWD (rc x) → IsTameWD (rc (x.tw χ hχ))

def FwdAt (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc → ∀ x : IrrGL (w.adicCompletion E), x.IsCusp →
      fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)

def StZ : Prop :=
  In → Core → StOcc → Pack → TameCong → SupercuspidalNoUnipotentFixed → NonSupercuspidalTame → DepthZeroContainsCuspidal → SameCuspidalTypeDiffer → UnramifiedTwistTame →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → FwdAt E w

def CompletionAtSplitCMPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (w' : HeightOneSpectrum (𝓞 E'))
      (i : w.adicCompletion E ≃+* w'.adicCompletion E'),
      (∀ u : HeightOneSpectrum (𝓞 E'), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E')) u.asIdeal) ∧ IsSplitAt w' ∧
      Continuous i ∧ Continuous i.symm

def CompletionIsoTransport : Prop :=
  In → ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] (w : HeightOneSpectrum (𝓞 E))
    (w' : HeightOneSpectrum (𝓞 E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → Continuous i.symm →
    FwdAt E' w' → FwdAt E w

end PositivityTheory.Rg.DzCong

end
