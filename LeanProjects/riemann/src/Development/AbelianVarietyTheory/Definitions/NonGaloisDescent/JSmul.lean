import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated

noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

def DΔ (T : LocLat G Qp LL O) : AddSubgroup (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add, ha δ hδ, hb δ hδ]
  neg_mem' := fun ha δ hδ => by rw [map_neg, ha δ hδ]

def Onto (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) : Prop :=
  Function.Surjective q ∧ ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x)

structure Pres {l n : ℕ} {R : RingPG k l} (F : DFun R n G) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (τ : ZMod n → ZMod n₀)
    (γ : W.Gam) where
  ι_v : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)
  obj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A

  j : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → ZMod n → (↥(DΔ W T) →+ Vc k A.m)
  j_surj : ∀ T A q, Onto T A q → ∀ i, Function.Surjective (j T A q i)
  j_smul : ∀ T A q, Onto T A q → ∀ i (a : LetA O n₀) (c : k⟦X⟧) (x y : ↥(DΔ W T)),
    ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (a (τ i)) : k⟦X⟧) : k⸨X⸩) →
    (y : W.DD T) = a • (x : W.DD T) → j T A q i y = c • j T A q i x
  j_φ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.φD T x →
    j T A q i y = (F.D A).φ i (j T A q (i - 1) x)
  j_γ : ∀ T A q, Onto T A q → ∀ i (x y : ↥(DΔ W T)), (y : W.DD T) = W.γD T γ x →
    j T A q i y = (F.D A).γ i (j T A q i x)
  j_ker : ∀ T A q, Onto T A q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f →
    (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i (x : ↥(DΔ W T)),
    j T A q i x = 0 ↔ ∃ y, W.map f y = (letE (τ i) : LetA O n₀) • (x : W.DD T)
  j_map : ∀ T A q T' A' q', Onto T A q → Onto T' A' q' → ∀ (f : LatHom T.L T'.L)
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), IsHom A A' g →
    (∀ (x : ↥T.L.T) (x' : ↥T'.L.T), (x' : T'.V) = f.f x → q' x' = g (q x)) →
    ∀ i (x : ↥(DΔ W T)) (y : ↥(DΔ W T')), (y : W.DD T') = W.map f x → j T' A' q' i y = F.map A A' g i (j T A q i x)
  j_unit : ∀ q, Onto W.one (chr 1 : Ob k G) q → ∀ x : ↥(DΔ W W.one),
    W.N W.one = Submodule.span (LetA O n₀) {(x : W.DD W.one)} → ∀ i,
    Submodule.span k⟦X⟧ {j W.one (chr 1) q i x} = Submodule.span k⟦X⟧ {F.unit i}

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

abbrev W (H : LocHW l P) := H.W S.K 1 S.LL S.hyp.1.2.1.2.2

def RealD (H : LocHW l P) : Prop :=
  ∀ (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k →
    ∃ (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι ∧
    ∃ (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam),
      (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧
      Nonempty (Pres (S.W H) F ι τ γ)

end GlobalTheory.TopSteps.TopSit
