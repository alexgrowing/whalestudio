import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.HTSpecAllHodge
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

structure TowerBC {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (H : HTower k) (H' : HTower k') {J : Type}
    (ι : J → H.Γ) (ι' : J → H'.Γ) where
  z : H'.Z ⟶ H.Z
  hz : IsPullback z H'.q H.q (spMap φ)
  y : ∀ j, H'.Y (ι' j) ⟶ H.Y (ι j)
  hs : ∀ j, IsPullback (y j) (H'.s (ι' j)) (H.s (ι j)) z
  ht : ∀ j, y j ≫ H.t (ι j) = H'.t (ι' j) ≫ z

def HodgeOcc {k : Type} [Field k] (H : HTower k) {J : Type} (ι : J → H.Γ) [∀ j, IsFinite (H.s (ι j))]
    [∀ j, Etale (H.s (ι j))] (θ : J → k) (a : ℕ) : Prop :=
  ∃ b : ℕ, (⨅ j, Module.End.maxGenEigenspace
    (hodgeTrace (s := H.q) (s' := H.s (ι j) ≫ H.q) rfl a b ∘ₗ hodgePull (s := H.q) (H.comm (ι j)) a b) (θ j)) ≠ ⊥

variable {l : ℕ} [Fact l.Prime]

def IsRepOf {k : Type} [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] {J : Type} (ι : J → H.Γ)
    (θ : J → Qbar l) {d : ℕ} (ρ : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Qbar l)) : Prop :=
  ∃ b : Module.Basis (Fin d) (Qbar l) (V l H Ω (Qbar l) ι θ),
    ∀ σ q, galV l H Ω (Qbar l) σ (b q) = ∑ p, ρ σ p q • (b p).1

def HTCover {K : FinExt l} (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ) (n : ℕ) : Prop :=
  ∃ (F : Frame (K := K) H.q n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]), F.IsHT Φ ∧
    ∀ j, ∃ (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (I : Type) (_ : Fintype I)
      (σ : I → (W ⟶ H.Y (ι j))) (hσ : ∀ i, (σ i ≫ H.t (ι j)) ≫ H.q = c ≫ H.q), IsGalois c G a ∧ Splits (H.s (ι j)) c σ ∧
      ∃ (F' : Frame (K := K) (c ≫ H.q) n) (Φ' : Matrix (Fin F'.d) F'.Col ℂ_[l]),
        F.etMat F' rfl * Φ = Φ' * F.hodgeMat F' rfl ∧ ∀ i, F.etMat F' (hσ i) * Φ = Φ' * F.hodgeMat F' (hσ i)

def HTOcc {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (Qbar l)) (a : ℤ) : Prop :=
  ∃ (S : Finset (Qbar l)) (z : Fin d → ℂ_[l]), z ≠ 0 ∧ ∀ σ : ↥(GK K), (∀ x ∈ S, (σ : GQ l) x = x) →
    ((ρ σ).map (algebraMap (Qbar l) ℂ_[l])).mulVec (fun q => Formalism.Per.σC (σ : GQ l) (z q)) = chiPow (σ : GQ l) (-a) • z

def LocalHodgeTateComplexTower : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ιC : Qbar l ≃+* ℂ) (H : HTower ↥K.1) [IsProper H.q] (J : Type) (ι : J → H.Γ)
    (H' : HTower ℂ) (ι' : J → H'.Γ) [∀ j, IsFinite (H'.s (ι' j))] [∀ j, Etale (H'.s (ι' j))]
    (_ : TowerBC (ιC.toRingHom.comp (algebraMap ↥K.1 (Qbar l))) H H' ι ι') (θ : J → Qbar l) (a : ℕ),
    (∀ j, IsFinite (H.s (ι j)) ∧ Etale (H.s (ι j))) → (∀ n, HTCover H ι n) → HodgeOcc H' ι' (fun j => ιC (θ j)) a →
    ∀ (d : ℕ) (ρ : (Qbar l ≃ₐ[↥K.1] Qbar l) → Matrix (Fin d) (Fin d) (Qbar l)), IsRepOf H (Qbar l) ι θ ρ →
      HTOcc (K := K) (fun σ => ρ (IntermediateField.fixingSubgroupEquiv K.1 σ)) a

def HodgeTateTowerNumberField : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ιC : Qbar l ≃+* ℂ) (H : HTower E) [IsProper H.q] (J : Type) (ι : J → H.Γ) (θ : J → Qbar l) (a : ℕ)
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (τK : E →+* ↥Bw.Kw.1), (∀ x, (τK x : Qbar l) = Bw.j (algebraMap E Ω x)) →
    ∀ (HK : HTower ↥Bw.Kw.1) (ιK : J → HK.Γ) (_ : TowerBC τK H HK ι ιK)
      (H' : HTower ℂ) (ι' : J → H'.Γ) [∀ j, IsFinite (H'.s (ι' j))] [∀ j, Etale (H'.s (ι' j))]
      (_ : TowerBC (ιC.toRingHom.comp (Bw.j.comp (algebraMap E Ω))) H H' ι ι'),
    (∀ j, IsFinite (H.s (ι j)) ∧ Etale (H.s (ι j))) → (∀ n, HTCover HK ιK n) → HodgeOcc H' ι' (fun j => ιC (θ j)) a →
    ∀ (d : ℕ) (ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin d) (Qbar l)), IsRepOf H Ω ι θ (fun σ => (ρ σ).val) →
      HTOcc (K := Bw.Kw) (fun σ => (ρ (Bw.e.symm σ : Gw)).val) a

def JumpOfHT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
      (d : ℕ) (r : ↥Gw →* GL (Fin d) (Qbar l)) (a : ℤ) (Jm : Multiset ℤ),
      HTOcc (K := Bw.Kw) (fun σ => (r (Bw.e.symm σ)).val) a → IsJumpsAt P Bw r (Bw.j.comp (algebraMap E Ω)) Jm → a ∈ Jm

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
