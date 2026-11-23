import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

section Finite

variable {F : Type} [Field F]

def detc (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) : GL (Fin t) F → ℂ :=
  fun x => θ (algebraMap F (AlgebraicClosure F) (x : Matrix (Fin t) (Fin t) F).det) ^ k

def JD (θ : AlgebraicClosure F →* ℂ) (D L : List (ℕ × ℕ)) : (n : ℕ) → GL (Fin n) F → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → GL (Fin n) F → ℂ) (J θ L)
    (fun p D ih n => hc p.1 (deg D + deg L) (detc θ p.1 p.2) (ih (deg D + deg L)) n) D

theorem JD_nil (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) : JD θ [] L = J θ L := rfl

theorem JD_cons (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (D L : List (ℕ × ℕ)) (n : ℕ) :
    JD θ (p :: D) L n = hc p.1 (deg D + deg L) (detc θ p.1 p.2) (JD θ D L (deg D + deg L)) n := rfl

def Meets {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Y : G → ℂ) : Prop :=
  ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) ≠ 0

def Inj {K : Type} [Field K] (θ : K →* ℂ) : Prop := ∀ x y : K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y

end Finite

structure Lbl where
  q : ℕ
  D : List (ℕ × ℕ)
  L : List (ℕ × ℕ)

instance : Inhabited Lbl := ⟨⟨2, [], []⟩⟩

namespace Lbl

def rk (a : Lbl) : ℕ := deg a.D + deg a.L

def Ok (a : Lbl) : Prop := 2 ≤ a.q ∧ (∀ p ∈ a.D, 0 < p.1) ∧ ∀ p ∈ a.L, 0 < p.1 ∧ Reg a.q p.1 p.2

def lift (a : Lbl) (l : ℕ) : Lbl :=
  ⟨a.q ^ l, a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i), liftAll a.q l a.L⟩

def Le (a b : Lbl) : Prop := Relation.ReflTransGen (fun a b => ∃ l : ℕ, l.Prime ∧ b = a.lift l) a b

def blocks (a : Lbl) (Q : ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  ((a.D.map fun p => (p.1, ((p.2 * ((Q - 1) / (a.q - 1)) : ℕ) : ZMod (Q - 1))) : List _) : Multiset _) +
    (a.L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * a.q ^ j * ((Q - 1) / (a.q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))).sum

def Splits (a : Lbl) (Q : ℕ) : Prop := ∃ f : ℕ, 0 < f ∧ Q = a.q ^ f ∧ ∀ p ∈ a.L, p.1 ∣ f

def pol (a : Lbl) (Q : ℕ) (x : ℂ) : ℂ[X] := ((a.blocks Q).map fun b => (X - C (x ^ b.2.val)) ^ b.1).prod

def Sep (a : Lbl) (Q : ℕ) : Prop := ((a.blocks Q).map Prod.snd).Nodup

end Lbl

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def HasLbl (θ : AlgebraicClosure 𝓀[k] →* ℂ) (π : Representation ℂ (GL (Fin n) k) V) (a : Lbl) : Prop :=
  a.Ok ∧ a.q = Nat.card 𝓀[k] ∧ n = a.rk ∧ Meets (levelZero π) (JD θ a.D a.L n)

def Mixed (x : IrrGL k) : Prop :=
  UpperTheory.Zero.LLC.DZ x ∧ ∃ s, HasSupport x.rep s ∧ GlobalTheory.RoadU.Unlinked s ∧
    (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z

end Local

section Place

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

def ResEmb (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K))
    (e : AlgebraicClosure 𝓀[w.adicCompletion K] →+* IsLocalRing.ResidueField A) : Prop :=
  ∀ (x : 𝓞 K) (y : 𝒪[w.adicCompletion K]) (z : A), (y : w.adicCompletion K) = algebraMap K _ (x : K) →
    (z : Ω) = algebraMap K Ω (x : K) →
    e (algebraMap _ _ (IsLocalRing.residue 𝒪[w.adicCompletion K] y)) = IsLocalRing.residue A z

end Place

structure Pt (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (n : ℕ) : Type 1 where
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [cx : IsTotallyComplex K]
  [algE : Algebra E K]
  [algΩ : Algebra K Ω]
  [tower : IsScalarTower E K Ω]
  [closure : IsAlgClosure K Ω]
  π : CuspSub K n

attribute [instance] Pt.field Pt.numberField Pt.cx Pt.algE Pt.algΩ Pt.tower Pt.closure

section Tower

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {n : ℕ}

def Pt.base [NumberField E] [IsTotallyComplex E] (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (π : CuspSub E n) : Pt E Ω n :=
  { K := E, π := π }

def Step (X Y : Pt E Ω n) : Prop :=
  ∃ (_ : Algebra X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), IsGalois X.K Y.K ∧ (Module.finrank X.K Y.K).Prime ∧
    WeakBC (Cusp.cx X.π).sat (Cusp.cx Y.π).sat

def Lifts (X Y : Pt E Ω n) : Prop := Relation.ReflTransGen Step X Y

end Tower

def FinTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E], (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v),
      ¬ UpperTheory.ConvolutionTheory.GM.Split E v → UpperTheory.ConvolutionTheory.GM.Unr E v →
    ∀ (τ : SmIrr (GL (Fin n) (v.adicCompletion F))) (τ' : SmIrr (GL (Fin n) (w.1.adicCompletion E))),
      π.IsLocComp v τ → P.IsLocComp w.1 τ' →
    ∀ [Algebra 𝓀[v.adicCompletion F] 𝓀[w.1.adicCompletion E]],
      (∀ (x : 𝒪[v.adicCompletion F]) (y : 𝒪[w.1.adicCompletion E]), (y : w.1.adicCompletion E) = completionMap v w.1 x →
        IsLocalRing.residue _ y = algebraMap 𝓀[v.adicCompletion F] 𝓀[w.1.adicCompletion E] (IsLocalRing.residue _ x)) →
    ∀ s : 𝓀[w.1.adicCompletion E] ≃ₐ[𝓀[v.adicCompletion F]] 𝓀[w.1.adicCompletion E],
      (∀ z, s z = z ^ Nat.card 𝓀[v.adicCompletion F]) →
    ∀ f : GL (Fin n) 𝓀[v.adicCompletion F] → ℂ, IsCl f →
      ∑ᶠ γ, f γ * LinearMap.trace ℂ _ (levelZero τ.ρ γ) ≠ 0 → ∑ᶠ δ, shLift s f δ • levelZero τ'.ρ δ ≠ 0

def KillsAll : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 →
    ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ),
    (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L →
    Kills (shLift s (J (pullθ ι θ) L n)) (J θ (liftAll (Nat.card F) (Module.finrank F F') L) n)

def LblBC : Prop :=
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (n : ℕ), 0 < n → ∀ X Y : Pt E Ω n, Lifts X Y →
    ∀ (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ), Inj Θ →
    (∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ (v : HeightOneSpectrum (𝓞 X.K)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v → IsPlaceOver A w →
    ∀ e e', ResEmb A v e → ResEmb A w e' → ∀ τ τ', X.π.IsLocComp v τ → Y.π.IsLocComp w τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → ∃ b, a.Le b ∧ HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ b

def ToralOver {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω]
    [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}
    {w : HeightOneSpectrum (𝓞 M)} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) {n : ℕ}
    (x : IrrGL (v.adicCompletion E)) (τ' : SmIrr (GL (Fin n) (w.adicCompletion M)))
    (ξ : Fin n → ((w.adicCompletion M)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) : Prop :=
  (∀ j, UpperTheory.Zero.LLC.TameChar (ξ j)) ∧ HasSupport τ'.ρ (GlobalTheory.RoadU.chars ξ hξ) ∧
    ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → ∀ a', IsLocalArtin h' a' → ∀ t : Ine (F := M) A,
      (rc x).inePol (AlgEquiv.restrictScalars E (t : G M Ω)) = ∏ j, (X - C ((ξ j (a' (ineIncl h' t)) : ℂˣ) : ℂ))

def SuppBC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)) (h : IsPlaceOver A v)
      (h' : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → UpperTheory.Zero.LLC.DZ (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∃ ξ hξ, ToralOver h h' (IrrGL.of τ.ρ τ.smooth τ.irred) τ' ξ hξ ∧
        (Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) → GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ))

end UpperTheory.Gal.InertialTypesAlt
