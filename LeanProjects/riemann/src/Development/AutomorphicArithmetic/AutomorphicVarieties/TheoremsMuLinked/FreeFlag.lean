import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base
open UpperTheory.V.Alg

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

namespace UpperTheory.V.Th

def FreeFlag : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → Af.IsAutCsd ι r →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ),
      W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ → StrictAnti m → 0 < k →
      (∀ i (g : Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (ψ i g * cycBar F Ω l g ^ (-m i)) ^ k = 1) →
      ((∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ Af.PotCrysAt r A) →
      ∃ g : Dec (F := F) A, cycZ F Ω l g = 1 ∧ Pr.FreeRatios fun i => ψ i g

def FreeC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (a : ℤ) (M : ℕ) (m : Fin n → ℤ), Continuous r →
      Af.IsAutCsd ι (Af.tw r (cycBar F Ω l ^ a)) → 1 ≤ M → StrictAnti m → Af.LevelAt l M m r → FreeAt l r

def FreeQ : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (M : ℕ) (m : Fin n → ℤ),
      1 ≤ M → StrictAnti m → Af.AdmR ι M m wt r → FreeAt l r

def BkOrd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ →
    ∀ (n : ℕ) (ρ : H →* GL (Fin n) (Qbar l)) (ψ : Fin n → H →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ), Continuous ρ → W.HasFlag ρ ψ →
      StrictAnti m → 0 < k →
      (∀ i j g, φ g ∈ Loc.Iq l → (ψ i g / ψ j g * Loc.cycA l l (Qbar l) (φ g) ^ (m j - m i)) ^ k = 1) →
      (∃ g, Loc.cycA l l (Qbar l) (φ g) = 1 ∧ Pr.FreeRatios fun i => ψ i g) →
      ∀ y ∈ Loc.finiteCocycles φ (Loc.adGL ρ), OrdAt ((Loc.Iq l).comap φ) ρ ψ y

def AdDown : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K L : Type) [Field K] [NumberField K] [IsCMField K]
    [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω], Module.finrank ℚ K = 2 →
    galOf ℚ L Ω ≤ galOf ℚ K Ω → ∀ (s : W.HidaSetting l L Ω) (V : s.Lev) (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l))
      (μ : G K Ω →* (Qbar l)ˣ) (R : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l))), Continuous r →
      Af.IsAdOf r μ R → ∀ (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (ka : G L Ω →* (Qbar l)ˣ),
      (∀ (g : G L Ω) (t : G K Ω), galEmb ℚ L Ω g = galEmb ℚ K Ω t → W.mat ρ (V.pr g) = (ka g : Qbar l) • W.mat r t) →
      (∀ (g g' : G L Ω) (t : G K Ω), W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ → galEmb ℚ L Ω g = galEmb ℚ K Ω t →
        ka g * ka g' * μ t = cycBar L Ω l g ^ (1 - (n : ℤ))) → AdZero V ρ → Af.BlochKatoSelmerVanishes l R

def RigEnd3 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω)
    (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 →
    Pr.HasFrame c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B M →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
      Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r →
      (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 → η.ker = galOf ℚ K Ω →
      ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) →
      Af.IsAutCsd ι (Af.tw ρ (cycBar K Ω l)⁻¹) → FreeAt l ρ → Af.BlochKatoSelmerVanishes l (adRep (UnitaryThreeInertia.push A.val r))

def AdZero2 {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (η : G ℚ Ω →* ℤˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ θ : G ℚ Ω →* (Qbar l)ˣ, (∀ g, (θ g : Qbar l) = ((η g : ℤˣ) : ℤ)) →
    ∀ R : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin 2) (Fin 2) (Qbar l)),
      Af.IsAdOf (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) R →
      Af.BlochKatoSelmerVanishes l R

def RigEnd2 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω)
    (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 →
    Pr.HasFrame c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B M →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A),
      Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 → η.ker = galOf ℚ K Ω →
      ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (∀ g, (W g).val.det = ((η g : ℤˣ) : ℤ)) →
      (∃ π : GlobalTheory.CuspRep.CuspSub K 2, (GlobalTheory.CuspRep.CG.mk π).IsRegAlg ∧
        Af.AttC ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) π) → FreeAt l W → AdZero2 K η W

def RigI : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc}
    {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f →
    ∀ (hr : HasMult D.η (push f S.r.hom)) (ι : Qbar l ≃+* ℂ), U3.TypeI D.η (push f S.r.hom) → D.IsAutI ι (push f S.r.hom) hr →
      Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom))

def RigII : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc}
    {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f →
    ∀ ι : Qbar l ≃+* ℂ, TypeII D.η (push f S.r.hom) → ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), Continuous W →
      D.IsExt (push f S.r.hom) W → (∀ g, (W g).val.det = ((D.η g : ℤˣ) : ℤ)) → D.IsModular ι W → AdZero2 K D.η W

def RigSp4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : GradeZeroInterpolatingElement.Raw Ω c),
    Ws.Ctx2 D ∨ Ws.Ctx3 D → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) r, D.EPt r → GradeZeroInterpolatingElement.Irr r → Aut.IsAut4 ι r → D.RigidAt r

structure InpT : Prop extends U3.CohInp where
  lemM : LemmaM
  lemM' : LemmaM'
  lemP : LemmaP
  kato : Lit.KatoUseN
  rigI : RigI
  rigII : RigII
  newAut : Af.NewformAut
  number : Af.CongruenceNumberRankThree

end UpperTheory.V.Th

end
