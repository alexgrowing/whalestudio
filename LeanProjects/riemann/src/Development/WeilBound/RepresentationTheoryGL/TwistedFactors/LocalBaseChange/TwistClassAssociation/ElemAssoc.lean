import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap

noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

def V1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [μG.IsOpenPosMeasure] [SFinite μG]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [μH.IsInvInvariant] [SFinite μH]
      (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
    ∀ (F : G → ℝ≥0∞), (∀ h ∈ H, ∀ g, F (h * g) = F g) → (∀ g, ∀ j ∈ J, F (g * j) = F g) →
    ∀ R : Set G, (∀ g, ∃ x ∈ R, ∃ h ∈ H, ∃ j ∈ J, g = h * x * j) →
      (∀ x ∈ R, ∀ y ∈ R, (∃ h ∈ H, ∃ j ∈ J, y = h * x * j) → x = y) →
      quotLIntegral μG H μH F = ∑' x : R, F x * μG J / μH {h : H | (x : G)⁻¹ * (h : G) * x ∈ J}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def fixT (N : ℕ) (θ : MulAut (GL (Fin N) k)) : Subgroup (Tor k N) :=
  (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).comap (Tor k N).subtype

variable (k) in

def orbSet (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (t δ : GL (Fin N) k) :
    Set (Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) :=
  {q | ∃ s : Tor k N, (s : Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) = q ∧
    ∃ κ ∈ J ⊓ Tor k N, (s : GL (Fin N) k)⁻¹ * δ * θ s = t * κ}

variable (k) in

def V2 : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
      [MeasurableMul₂ (GL (Fin N) k)] [MeasurableInv (GL (Fin N) k)]
      (μG : Measure (GL (Fin N) k)) [μG.IsHaarMeasure] [SFinite μG],
    ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ (μδ : Measure (twCent θ.toMonoidHom δ)) [μδ.IsHaarMeasure],
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) =
        ((orbSet k N J θ t δ).encard : ℝ≥0∞) * μG J / μδ {x | (x : GL (Fin N) k) ∈ J}

variable (k) in

def TwistClassVanishing : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] (μG : Measure (GL (Fin N) k)) (δ : GL (Fin N) k)
      (μδ : Measure (twCent θ.toMonoidHom δ)),
      (¬ ∃ g : GL (Fin N) k, ∃ κ ∈ J ⊓ Tor k N, twConj θ.toMonoidHom g δ = t * κ) →
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) = 0

def sigmaAut {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (σ : E ≃ₐ[F] E) :
    MulAut (GL (Fin n) E) where
  toFun := sigmaGL σ
  invFun := sigmaGL σ.symm
  left_inv g := by ext i j; simp [sigmaGL_val]
  right_inv g := by ext i j; simp [sigmaGL_val]
  map_mul' := map_mul _

def ElemAssoc : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (J' : Subgroup (GL (Fin n) E)) (J : Subgroup (GL (Fin n) F))
      (t' : GL (Fin n) E) (t : GL (Fin n) F),
      admitted E n J' (sigmaAut n σ) (Module.finrank F E) → admitted F n J 1 1 →
      GoodT E n J' (sigmaAut n σ) (Module.finrank F E) t' → GoodT F n J 1 1 t →
      incl (E := E) t = normGL σ t' →
      (∀ s ∈ Tor F n, s ∈ J ↔ ∃ s' ∈ J' ⊓ Tor E n, incl (E := E) s = normGL σ s') →
    ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
      (μE : Measure (GL (Fin n) E)) (μF : Measure (GL (Fin n) F)),
      μE.IsHaarMeasure → μF.IsHaarMeasure →
      (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F) (h : GL (Fin n) E)
          (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → normGL σ δ = h * incl γ * h⁻¹ →
          μδ.IsHaarMeasure → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
            Measure.map (fun s : Subgroup.centralizer {γ} => incl (s : GL (Fin n) F)) μγ →
          orbIntegral μF γ μγ (fun g => μE J' / μF J * Set.indicator (dcos J t) 1 g) =
            twOrbIntegral (sigmaGL σ) μE δ μδ (Set.indicator (dcos J' t') 1)) ∧
      (∀ (γ : GL (Fin n) F) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure →
          orbIntegral μF γ μγ (Set.indicator (dcos J t) 1) = 0)

end PositivityTheory.Lbc

end
