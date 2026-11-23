import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

abbrev Levels (E : Type) [Field E] [NumberField E] (a : ℕ) : Type :=
  ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin a) (w.adicCompletion E))

def HasLevel (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (π : CuspSub E a) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (Kw w) ≠ ⊥

structure Adapted (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (π : CuspSub E a) : Prop where
  isOpen : ∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E)))
  compact : ∀ w, IsSplitAt w → Apart w w₀ → IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))
  level : HasLevel w₀ Kw π
  sph : ∀ w, IsSplitAt w → Apart w w₀ → ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → Kw w = GlobalTheory.LFun.KGL w a
  iwa : ∀ w, IsSplitAt w → Apart w w₀ → IwaAt π w → ∃ g : GL (Fin a) (w.adicCompletion E),
    ∀ x ∈ SmGL.iwahori (w.adicCompletion E) (Fin a), g * x * g⁻¹ ∈ Kw w

structure Nbr (l : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (π π' : CuspSub E a) : Prop where
  scope : InScope .csd l π' (quadChar E ^ a)
  inf : ∀ τ, (CG.mk π').infChar τ = (CG.mk π).infChar τ
  level : HasLevel w₀ Kw π'
  sc : ScAt π' w₀

structure LocOps (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (Kw : Levels E a) (J : Type) where

  pl : J → HeightOneSpectrum (𝓞 E)
  split : ∀ j, IsSplitAt (pl j)
  away : ∀ j, ((l : ℕ) : 𝓞 E) ∉ (pl j).asIdeal

  f : ∀ j, GL (Fin a) ((pl j).adicCompletion E) →₀ ℂ
  int : ∀ j g, ‖ι.symm (f j g)‖ ≤ 1

  z : ∀ j, SmIrr (GL (Fin a) ((pl j).adicCompletion E)) → ℂ
  act : ∀ j σ, ∀ v ∈ PRep.fixed σ.ρ (Kw (pl j)), opOf σ.ρ (f j) v = z j σ • v

def LocOps.IsSys {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (T : LocOps l ι Kw J) (π : CuspSub E a) (θ : J → Qbar l) : Prop :=
  ∀ j σ, π.IsLocComp (T.pl j) σ → θ j = ι.symm (T.z j σ)

def CongGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) → ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ Kw : Levels E a, Adapted w₀ Kw π ∧ ∀ (J : Type) (T : LocOps l ι Kw J) (θ : J → Qbar l), T.IsSys π θ →
      PolyApprox θ {θ' | ∃ π', Nbr l w₀ Kw π π' ∧ T.IsSys π' θ'} ∧
      ((∀ j g, ∃ q : ℚ, T.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

def SeedRep (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (π : CuspSub E a)
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∃ π', Nbr l w₀ Kw π π' ∧ SplitAtt π' ι ρ ∧ ∀ w, IsSplitAt w → Apart w w₀ →
    ClauseAt .ss π' ι ρ w ∧ ClauseAt .dR π' ι ρ w ∧ ClauseAt .crys π' ι ρ w ∧ (IwaAt π' w → SstAt ρ w)

def LimitEx : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ (Kw : Levels E a) (r : G E Ω →* GL (Fin a) (Qbar l)), Adapted w₀ Kw π ∧ SplitAtt π ι r ∧ LinApprox r {ρ | SeedRep ι w₀ Kw π ρ}

def SplitSS : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r → ∀ w, IsSplitAt w → ClauseAt .ss π ι r w

def DRIwa : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, IsSplitAt w → IwaAt π w → ClauseAt .dR π ι r w

def SphOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ),
    (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a) ≠ ⊥ → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ n : ℤ, ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w a), opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum • v

def ResDR : Prop :=
  ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (a : ℕ) (π : CuspSub E a) (π' : CuspSub M a), (∀ τ : M →+* ℂ, (CG.mk π').infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))) →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r → ∀ (w' : HeightOneSpectrum (𝓞 M)) (A : ValuationSubring Ω), IsPlaceOver A w' →
    ClauseAt .dR π' ι (GlobalTheory.AboveL.resTo M r) w' →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J

structure Up (Ω : Type) [Field Ω] (l : ℕ) {E M : Type} [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [Field M] [NumberField M]
    [IsCMField M] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {a : ℕ} (π : CuspSub E a) (π' : CuspSub M a) : Prop where
  scope : ∀ l' : ℕ, InScope .csd l' π (quadChar E ^ a) → InScope .csd l' π' (quadChar M ^ a)
  self : InScope .csd l π (quadChar E ^ a)
  inf : ∀ τ : M →+* ℂ, (CG.mk π').infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))
  weak : ∀ (l' : ℕ) [Fact l'.Prime] (ι : Qbar l' ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l')), Weak π ι r → Weak π' ι (GlobalTheory.AboveL.resTo M r)

def LocOps.empty (ι : Qbar l ≃+* ℂ) (Kw : Levels E a) : LocOps l ι Kw Empty where
  pl j := j.elim
  split j := j.elim
  away j := j.elim
  f j := j.elim
  int j := j.elim
  z j := j.elim
  act j := j.elim

end GlobalTheory.Cong

end
