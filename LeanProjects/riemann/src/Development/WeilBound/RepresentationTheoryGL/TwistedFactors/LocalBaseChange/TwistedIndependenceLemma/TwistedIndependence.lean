import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace PositivityTheory.Lbc

def cycShift (W : Type) [AddCommGroup W] [Module ℂ W] (l : ℕ) :
    (⨂[ℂ] _ : Fin l, W) ≃ₗ[ℂ] (⨂[ℂ] _ : Fin l, W) :=
  PiTensorProduct.reindex ℂ (fun _ : Fin l => W) (finRotate l)

def revProd {W : Type} [AddCommGroup W] [Module ℂ W] {l : ℕ} (T : Fin l → Module.End ℂ W) : Module.End ℂ W :=
  (List.ofFn T).reverse.prod

def CyclicTrace : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (l : ℕ), 1 ≤ l →
    ∀ T : Fin l → Module.End ℂ W,
      LinearMap.trace ℂ (⨂[ℂ] _ : Fin l, W)
          ((cycShift W l : (⨂[ℂ] _ : Fin l, W) →ₗ[ℂ] (⨂[ℂ] _ : Fin l, W)) ∘ₗ PiTensorProduct.map T) =
        LinearMap.trace ℂ W (revProd T)

def IsHeckeOpG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G)
    (g : G) (T : Module.End ℂ (fixed π K)) : Prop :=
  ∀ (v : fixed π K) (f : Module.Dual ℂ V), (∀ x ∈ K, f ∘ₗ π x = f) → f (π g (v : V)) = f ((T v : fixed π K) : V)

def IsoRep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ (g : G) (v : V), e (π g v) = σ g (e v)

def HeckeExistsUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
      ∀ g : G, ∃! T : Module.End ℂ (fixed π K), IsHeckeOpG π K g T

def HeckeDensity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ G (V i)), (∀ i, IsAdmissible (π i)) → (∀ i, (π i).IsIrreducible) →
        (∀ i j, i ≠ j → ¬ IsoRep (π i) (π j)) →
        ∀ T : ∀ i, G → Module.End ℂ (fixed (π i) K), (∀ i g, IsHeckeOpG (π i) K g (T i g)) →
          Submodule.span ℂ (Set.range fun (g : G) (i : ι) => T i g) = ⊤

def TwistedIndependence : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ G (V i)), (∀ i, IsAdmissible (π i)) → (∀ i, (π i).IsIrreducible) →
        (∀ i j, i ≠ j → ¬ IsoRep (π i) (π j)) →
        ∀ T : ∀ i, G → Module.End ℂ (fixed (π i) K), (∀ i g, IsHeckeOpG (π i) K g (T i g)) →
          ∀ A : ∀ i, Module.End ℂ (fixed (π i) K),
            (∀ g : G, ∑ i, LinearMap.trace ℂ (fixed (π i) K) (T i g * A i) = 0) → ∀ i, A i = 0

def tpow {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (l : ℕ) :
    Representation ℂ (Fin l → G) (⨂[ℂ] _ : Fin l, V) :=
  piTensor (fun _ : Fin l => π)

def powSub {G : Type} [Group G] (K : Subgroup G) (l : ℕ) : Subgroup (Fin l → G) :=
  Subgroup.pi Set.univ fun _ => K

def SplitIdentity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π →
      ∀ (l : ℕ), 1 ≤ l →
        (∃ A : Module.End ℂ (fixed (tpow π l) (powSub K l)), ∀ v, ((A v : fixed (tpow π l) (powSub K l)) :
            ⨂[ℂ] _ : Fin l, V) = cycShift V l (v : ⨂[ℂ] _ : Fin l, V)) ∧
        ∀ (A : Module.End ℂ (fixed (tpow π l) (powSub K l))), (∀ v, ((A v : fixed (tpow π l) (powSub K l)) :
            ⨂[ℂ] _ : Fin l, V) = cycShift V l (v : ⨂[ℂ] _ : Fin l, V)) →
          ∀ (g : Fin l → G) (TP : Module.End ℂ (fixed (tpow π l) (powSub K l))),
            IsHeckeOpG (tpow π l) (powSub K l) g TP →
            ∀ T : Fin l → Module.End ℂ (fixed π K), (∀ i, IsHeckeOpG π K (g i) (T i)) →
              LinearMap.trace ℂ _ (A * TP) = LinearMap.trace ℂ _ (revProd T)

end PositivityTheory.Lbc

end
