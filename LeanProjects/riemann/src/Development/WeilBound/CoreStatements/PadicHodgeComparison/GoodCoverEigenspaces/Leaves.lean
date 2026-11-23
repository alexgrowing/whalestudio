import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.LocalHodgeTateComplexTower
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

def HodgeBC : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k'),
    ∃ β : ∀ {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X), IsPullback g s' s (spMap φ) →
        ∀ a b : ℕ, hodgeH s a b →ₛₗ[φ] hodgeH s' a b,
      (∀ {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) [IsProper s]
        (a b : ℕ) {I : Type} (c : Module.Basis I k (hodgeH s a b)),
          ∃ c' : Module.Basis I k' (hodgeH s' a b), ∀ i, c' i = β s s' g h a b (c i)) ∧
      (∀ {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ))
        (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ))
        (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ a b : ℕ,
          (∀ x, β r r' e he a b (hodgePull hf a b x) = hodgePull hf' a b (β s s' g h a b x)) ∧
          ∀ [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b),
            β s s' g h a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (β r r' e he a b y))

def TraceSplit : Prop :=
  ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (q : Z ⟶ Sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) [IsFinite c] [Etale c]
    {I : Type} [Fintype I] (σ : I → (W ⟶ Y)) (hσ : ∀ i, σ i ≫ (s ≫ q) = c ≫ q), Splits s c σ → ∀ (a b : ℕ) (y : hodgeH (s ≫ q) a b),
      hodgePull (s := q) (s' := c ≫ q) rfl a b (hodgeTrace (s := q) (s' := s ≫ q) rfl a b y) = ∑ i, hodgePull (hσ i) a b y

def CoverOp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : HTower ↥K.1) [IsProper H.q] (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
    (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (I : Type) [Fintype I]
    (σ : I → (W ⟶ H.Y g)) (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q), IsGalois c G a → Splits (H.s g) c σ →
    (∃ T, IsCorrOp l (H.sΩ (Qbar l) g) (H.tΩ (Qbar l) g) T) → ∀ n : ℕ,
      Function.Injective (etPull (K := K) (q := H.q) (q' := c ≫ H.q) rfl n) ∧
      ∃ T : EtV (K := K) H.q n →ₗ[ℚ_[l]] EtV (K := K) H.q n,
        (∀ x, hop l H (Qbar l) g (DirectSum.lof ℚ_[l] ℤ _ (n : ℤ) x) = DirectSum.lof ℚ_[l] ℤ _ (n : ℤ) (T x)) ∧
        etPull (K := K) (q := H.q) (q' := c ≫ H.q) rfl n ∘ₗ T = ∑ i, etPull (K := K) (hσ i) n

def HasOps (l : ℕ) [Fact l.Prime] {k : Type} [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] {J : Type}
    (ι : J → H.Γ) : Prop := ∀ j, ∃ T, IsCorrOp l (H.sΩ Ω (ι j)) (H.tΩ Ω (ι j)) T

def LocalHTOperatorTowers : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ιC : Qbar l ≃+* ℂ) (H : HTower ↥K.1) [IsProper H.q] (J : Type) (ι : J → H.Γ)
    (H' : HTower ℂ) (ι' : J → H'.Γ) [∀ j, IsFinite (H'.s (ι' j))] [∀ j, Etale (H'.s (ι' j))]
    (_ : TowerBC (ιC.toRingHom.comp (algebraMap ↥K.1 (Qbar l))) H H' ι ι') (θ : J → Qbar l) (a : ℕ),
    (∀ j, IsFinite (H.s (ι j)) ∧ Etale (H.s (ι j))) → HasOps l H (Qbar l) ι → (∀ n, HTCover H ι n) → HodgeOcc H' ι' (fun j => ιC (θ j)) a →
    ∀ (d : ℕ) (ρ : (Qbar l ≃ₐ[↥K.1] Qbar l) → Matrix (Fin d) (Fin d) (Qbar l)), IsRepOf H (Qbar l) ι θ ρ →
      HTOcc (K := K) (fun σ => ρ (IntermediateField.fixingSubgroupEquiv K.1 σ)) a

def HodgeTateSmoothTowers : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ιC : Qbar l ≃+* ℂ) (H : HTower E) [IsProper H.q] [Smooth H.q] (J : Type) (ι : J → H.Γ) (θ : J → Qbar l) (a : ℕ)
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (τK : E →+* ↥Bw.Kw.1), (∀ x, (τK x : Qbar l) = Bw.j (algebraMap E Ω x)) →
    ∀ (HK : HTower ↥Bw.Kw.1) (ιK : J → HK.Γ) (_ : TowerBC τK H HK ι ιK)
      (H' : HTower ℂ) (ι' : J → H'.Γ) [∀ j, IsFinite (H'.s (ι' j))] [∀ j, Etale (H'.s (ι' j))]
      (_ : TowerBC (ιC.toRingHom.comp (Bw.j.comp (algebraMap E Ω))) H H' ι ι'),
    (∀ j, IsFinite (H.s (ι j)) ∧ Etale (H.s (ι j))) → HasOps l H Ω ι → (∀ n, HTCover HK ιK n) → HodgeOcc H' ι' (fun j => ιC (θ j)) a →
    ∀ (d : ℕ) (ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin d) (Qbar l)), IsRepOf H Ω ι θ (fun σ => (ρ σ).val) →
      HTOcc (K := Bw.Kw) (fun σ => (ρ (Bw.e.symm σ : Gw)).val) a

def GeomBC : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (H : HTower E) [IsProper H.q] [Smooth H.q] (J : Type) (ι : J → H.Γ) (θ : J → Qbar l)
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (τK : E →+* ↥Bw.Kw.1), (∀ x, (τK x : Qbar l) = Bw.j (algebraMap E Ω x)) →
    ∀ (HK : HTower ↥Bw.Kw.1) (ιK : J → HK.Γ) (_ : TowerBC τK H HK ι ιK), (∀ j, IsFinite (H.s (ι j)) ∧ Etale (H.s (ι j))) →
    HasOps l H Ω ι → HasOps l HK (Qbar l) ιK ∧ ∀ (d : ℕ) (ρ : (Ω ≃ₐ[E] Ω) → Matrix (Fin d) (Fin d) (Qbar l)), IsRepOf H Ω ι θ ρ →
      IsRepOf HK (Qbar l) ιK θ fun σ => ρ (Bw.e.symm ((IntermediateField.fixingSubgroupEquiv Bw.Kw.1).symm σ) : Gw)

def LocOf : Prop := HodgeBC → TraceSplit → CoverOp → LocalHTOperatorTowers

def HTOf : Prop := LocalHTOperatorTowers → GeomBC → HodgeTateSmoothTowers

def GeomBCOf : Prop := GlobalTheory.EtC.E2 → GlobalTheory.EtC.E3 → GeomBC

def IsConj {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O O' : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (γ : GQ l) (Bw : LocBridge l E Ω Gw O) (Bw' : LocBridge l E Ω Gw O') : Prop :=
  (∀ x, Bw'.j x = γ (Bw.j x)) ∧ ∀ g : ↥Gw, ((Bw'.e g : ↥(GK Bw'.Kw)) : GQ l) = γ * ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) * γ⁻¹

def ConjBridge : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    ∃ (γ : GQ l) (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l E Ω Gw O'),
      IsConj γ Bw Bw' ∧ Bw'.j.comp (algebraMap E Ω) = τ

def JumpOfHT2 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O']
      [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω Gw O) (Bw' : LocBridge l E Ω Gw O') (γ : GQ l),
      IsConj γ Bw Bw' → ∀ (d : ℕ) (r : ↥Gw →* GL (Fin d) (Qbar l)) (a : ℤ) (Jm : Multiset ℤ),
      HTOcc (K := Bw'.Kw) (fun σ => (r (Bw'.e.symm σ)).val) a → IsJumpsAt P Bw r (Bw'.j.comp (algebraMap E Ω)) Jm → a ∈ Jm

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
