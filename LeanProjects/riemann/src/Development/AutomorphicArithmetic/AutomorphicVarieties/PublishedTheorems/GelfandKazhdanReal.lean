import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V.Af
open CategoryTheory
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def ClozelCohC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (Ξ : GlobalTheory.GKCoh.AlgRep E a),
      (∀ τ, ∃ m, π.HasInfChar τ m ∧ AlgInfChar Ξ τ (m.map Neg.neg)) → GlobalTheory.GKCoh.IsCohFor π Ξ

def ClozelCohR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a) (Ξ : TR.AlgRep F a),
      (∀ v, ∃ m, π.HasInfChar v m ∧ Ξ.HasInfChar v (m.map Neg.neg)) → TR.IsCohFor π Ξ

def ClozelConjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
      ∃ (π' : CuspSub E a) (τ τ' : SmIrr (GL (Fin a) (Af E))), IsFinComp π τ ∧ IsFinComp π' τ' ∧ IsConjBy σ τ τ' ∧
        ∀ (φ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar φ m → π'.HasInfChar (σ.toRingHom.comp φ) m

def ClozelConjR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a), π.IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
      ∃ (π' : TR.CuspSub F a) (τ τ' : SmIrr (GL (Fin a) (Af F))), π.IsFinComp τ ∧ π'.IsFinComp τ' ∧ IsConjBy σ τ τ' ∧
        ∀ (φ : F →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk φ) m →
          π'.HasInfChar (InfinitePlace.mk (σ.toRingHom.comp φ)) m

def BorelInjC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) →
    ∀ (Ξ : GlobalTheory.GKCoh.AlgRep E a) (S : Finset (CuspSub E a)), (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
      (∀ π ∈ S, GlobalTheory.GKCoh.IsCohFor π Ξ ∧ HasFixed π.finPart U) → (S.card : Cardinal) ≤ cohDim ⊤ U (ratC Ξ)

def BorelInjR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a →
    ∀ (U : Subgroup (GL (Fin a) (Af F))), IsOpen (U : Set (GL (Fin a) (Af F))) → IsCompact (U : Set (GL (Fin a) (Af F))) →
    ∀ (Ξ : TR.AlgRep F a) (S : Finset (TR.CuspSub F a)), (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
      (∀ π ∈ S, TR.IsCohFor π Ξ ∧ HasFixed π.finPart U) → (S.card : Cardinal) ≤ cohDim (TR.GLplus F a) U Ξ.rat

def IsFL (Γ : Type) [Group Γ] : Prop :=
  ∃ r : ℕ → ℕ, (∀ᶠ i in Filter.atTop, r i = 0) ∧ ∃ P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ),
    ∀ i, Nonempty (P.complex.X i ≅ Rep.free ℂ Γ (Fin (r i)))

def BorelSerreFL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : ℕ) (Γ : Subgroup (GL (Fin a) F)),
    Subgroup.Commensurable Γ (Matrix.GeneralLinearGroup.map (n := Fin a) (algebraMap (𝓞 F) F)).range →
    (∀ γ ∈ Γ, IsOfFinOrder γ → γ = 1) → IsFL ↥Γ

section Real

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRepOfR (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι r (rc (algNorm σ))
  pure : ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered
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
        IsSstAt P Bw (r.comp (Dec (F := F) A).subtype) ∧
          ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype) = rc (algNorm σ)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)

end Real

def GaloisRepReal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : TR.CuspSub F a) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
      ∃ (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRepOfR π ι r wt HT

def StrongMultOneReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ π π' : TR.CuspSub F a,
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) → π.Iso π'

def GelfandKazhdanReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a),
    ∃ B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
      (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af F) k)) ψ) = B φ ψ) ∧
      (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ) ∧
      ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0

def AdmissibleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a)
    (U : Subgroup (GL (Fin a) (Af F))), IsOpen (U : Set (GL (Fin a) (Af F))) →
    ∀ (d : ℕ) (ξ : TR.Kinf F a →* Matrix (Fin d) (Fin d) ℂ), ∃ W : Submodule ℂ π.V, FiniteDimensional ℂ W ∧
      ∀ f : (Fin d → ℂ) →ₗ[ℂ] π.V, (∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)) → (∀ u ∈ U, ∀ v, π.finPart u (f v) = f v) →
        LinearMap.range f ≤ W

section BC

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {a : ℕ}

def IsoTwist (π : TR.CuspSub F a) (η : HChar F) : Prop :=
  ∃ T : π.V ≃ₗ[ℂ] π.V, (∀ k φ, T (π.op (.fin k) φ) = ((chiDet a η (finGL F a k) : ℂˣ) : ℂ) • π.op (.fin k) (T φ)) ∧
    (∀ k φ, T (π.op (.cpt k) φ) = ((chiDet a η (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • π.op (.cpt k) (T φ)) ∧
    ∀ X φ, T (π.op (.lie X) φ) = π.op (.lie X) (T φ)

variable (E) in
omit [IsTotallyReal F] [IsTotallyComplex E] in

def IsQuadCharOf (η : HChar F) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) →
      η.UnrAt v ∧ η.val v = if normV w = normV v then 1 else -1

structure IsBC (π : TR.CuspSub F a) (P : CuspSub E a) : Prop where
  inf : ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m
  split : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)
  unr : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → ∀ f : ℕ, normV w = normV v ^ f →
      ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

end BC

def QuadBaseChange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ π : TR.CuspSub F a,
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E a, IsBC π P

def ThorneAdjoint : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (n : ℕ), 2 ≤ n →
    ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
    ∀ (r : G F Ω →* GL (Fin n) (Qbar p)), Continuous r → AttC ι r π → IsIrr (r.comp (cycBar F Ω p).ker.subtype) →
    ∀ (μ : G (maximalRealSubfield F) Ω →* (Qbar p)ˣ), IsLAdicCharOf ι χ μ →
    ∀ ρ : Representation (Qbar p) (G (maximalRealSubfield F) Ω) (Matrix (Fin n) (Fin n) (Qbar p)),
      IsAdOf r (cycBar F Ω p ^ (1 - (n : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield F))) ρ →
      BlochKatoSelmerVanishes p ρ

def NewformRep : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (j : ℤ), ∃ π : TR.CuspSub ℚ 2,
    (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) ∧
    ∀ w : HeightOneSpectrum (𝓞 ℚ), ¬ normV w ∣ f.M → ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

end UpperTheory.V.Published
