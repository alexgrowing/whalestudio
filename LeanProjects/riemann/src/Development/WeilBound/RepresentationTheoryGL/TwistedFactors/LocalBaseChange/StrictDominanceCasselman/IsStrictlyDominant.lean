import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace PositivityTheory.Lbc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Bl {h : ℕ} (d : Fin h → ℕ) : Fin h → Type := fun a => Fin (d a)

def IsHeckeOp {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (J : Subgroup (GL (Fin N) k)) (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)) : Prop :=
  ∀ (v : fixed π J) (l : Module.Dual ℂ V), (∀ x ∈ J, l ∘ₗ π x = l) →
    l (π g (v : V)) = l ((T v : fixed π J) : V)

variable (k) in

def HasIwahoriFact (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Prop :=
  ∀ x ∈ J, ∃ a ∈ J ⊓ unipRadLower k (stdBlocks d hd), ∃ b ∈ J ⊓ (leviEmb k (stdBlocks d hd)).range,
    ∃ c ∈ J ⊓ unipRad k (stdBlocks d hd), x = a * b * c

variable (k) in

def KN (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Subgroup (GL (Fin N) k) :=
  J ⊓ unipRad k (stdBlocks d hd)

variable (k) in

def KNl (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Subgroup (GL (Fin N) k) :=
  J ⊓ unipRadLower k (stdBlocks d hd)

variable (k) in

def KM (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Subgroup (Levi k (Bl d)) :=
  (J).comap (leviEmb k (stdBlocks d hd))

variable (k) in

def IsDominant (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : Levi k (Bl d)) : Prop :=
  (∀ n ∈ KN k N J d hd, leviEmb k (stdBlocks d hd) t * n * (leviEmb k (stdBlocks d hd) t)⁻¹ ∈ KN k N J d hd) ∧
  (∀ n ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) t)⁻¹ * n * leviEmb k (stdBlocks d hd) t ∈ KNl k N J d hd) ∧
  (∀ x ∈ KM k N J d hd, t * x * t⁻¹ ∈ KM k N J d hd ∧ t⁻¹ * x * t ∈ KM k N J d hd)

variable (k) in

def IsStrictlyDominant (N : ℕ) (J : Subgroup (GL (Fin N) k)) {h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : Levi k (Bl d)) : Prop :=
  IsDominant k N J d hd t ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U →
    ∃ j : ℕ, ∀ n ∈ KN k N J d hd,
      leviEmb k (stdBlocks d hd) t ^ j * n * (leviEmb k (stdBlocks d hd) t ^ j)⁻¹ ∈ U

variable (k) in

def C1 : Prop :=
  ∀ (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t → IsDominant k N J d hd t' →
    ∀ T T' : Module.End ℂ (fixed π (J)),
      IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T →
      IsHeckeOp π J (leviEmb k (stdBlocks d hd) t') T' →
      IsHeckeOp π J (leviEmb k (stdBlocks d hd) (t * t')) (T * T')

variable (k) in

def C2 : Prop :=
  ∀ (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t →
    ∀ T : Module.End ℂ (fixed π (J)), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T →
    ∀ v : fixed π (J),
      (Submodule.Quotient.mk ((T v : fixed π (J)) : V) : Jacquet π (unipRad k (stdBlocks d hd))) =
        ((deltaHalf k (Bl d) t : ℂˣ) : ℂ) •
          jac (stdBlocks d hd) π t (Submodule.Quotient.mk (v : V))

variable (k) in

def C3 : Prop :=
  ∀ (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π →
    (∀ v : fixed π (J),
      (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈
        fixed (jac (stdBlocks d hd) π) (KM k N J d hd)) ∧
    (∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π (J),
      (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w) ∧
    ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t →
    ∀ T : Module.End ℂ (fixed π (J)), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T →
    ∀ v : fixed π (J),
      (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0

variable (k) in

def C4 : Prop :=
  ∀ (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π →
    ∀ (l : ℕ) (hl : 0 < l) (t : Fin l → Levi k (Bl d)), (∀ i, IsDominant k N J d hd (t i)) →
    IsStrictlyDominant k N J d hd (List.ofFn t).prod →
    ∀ T : Fin l → Module.End ℂ (fixed π (J)),
      (∀ i, IsHeckeOp π J (leviEmb k (stdBlocks d hd) (t i)) (T i)) →
    ∀ J0 : Module.End ℂ (fixed (jac (stdBlocks d hd) π) (KM k N J d hd)),
      (∀ w, ((J0 w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)) : Jacquet π (unipRad k (stdBlocks d hd))) =
        jac (stdBlocks d hd) π (t ⟨0, hl⟩) w) →
    ∀ (A : Module.End ℂ (fixed π (J)))
      (AN : Module.End ℂ (fixed (jac (stdBlocks d hd) π) (KM k N J d hd))),
      (∀ (v : fixed π (J)) (w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)),
        (w : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (v : V) →
        ((AN w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)) : Jacquet π (unipRad k (stdBlocks d hd))) =
          Submodule.Quotient.mk ((A v : fixed π (J)) : V)) →
      (∀ i, A * T i = T (finRotate l i) * A) →
      LinearMap.trace ℂ _ (A * T ⟨0, hl⟩) =
        ((deltaHalf k (Bl d) (t ⟨0, hl⟩) : ℂˣ) : ℂ) * LinearMap.trace ℂ _ (AN * J0)

variable (k) in

def C5 : Prop :=
  ∀ (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π →
    ∀ θ : GL (Fin N) k ≃* GL (Fin N) k,
      (J).map θ.toMonoidHom = J →
      (unipRad k (stdBlocks d hd)).map θ.toMonoidHom = unipRad k (stdBlocks d hd) →
      (unipRadLower k (stdBlocks d hd)).map θ.toMonoidHom = unipRadLower k (stdBlocks d hd) →
      (leviEmb k (stdBlocks d hd)).range.map θ.toMonoidHom = (leviEmb k (stdBlocks d hd)).range →
    ∀ A : V →ₗ[ℂ] V, (∀ g, A ∘ₗ π g = π (θ g) ∘ₗ A) →
    ∃ (AK : Module.End ℂ (fixed π (J)))
      (AN : Module.End ℂ (fixed (jac (stdBlocks d hd) π) (KM k N J d hd))),
      (∀ v, ((AK v : fixed π (J)) : V) = A v) ∧
      (∀ (v : fixed π (J)) (w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)),
        (w : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (v : V) →
        ((AN w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)) : Jacquet π (unipRad k (stdBlocks d hd))) =
          Submodule.Quotient.mk (A v)) ∧
      ∀ (l : ℕ) (hl : 0 < l) (t : Fin l → Levi k (Bl d)),
        (∀ i, leviEmb k (stdBlocks d hd) (t (finRotate l i)) = θ (leviEmb k (stdBlocks d hd) (t i))) →
        IsDominant k N J d hd (t ⟨0, hl⟩) → IsStrictlyDominant k N J d hd (List.ofFn t).prod →
        ∀ T0 : Module.End ℂ (fixed π (J)),
          IsHeckeOp π J (leviEmb k (stdBlocks d hd) (t ⟨0, hl⟩)) T0 →
        ∀ J0 : Module.End ℂ (fixed (jac (stdBlocks d hd) π) (KM k N J d hd)),
          (∀ w, ((J0 w : fixed (jac (stdBlocks d hd) π) (KM k N J d hd)) :
              Jacquet π (unipRad k (stdBlocks d hd))) = jac (stdBlocks d hd) π (t ⟨0, hl⟩) w) →
          LinearMap.trace ℂ _ (AK * T0) =
            ((deltaHalf k (Bl d) (t ⟨0, hl⟩) : ℂˣ) : ℂ) * LinearMap.trace ℂ _ (AN * J0)

variable (k) in

def C0 : Prop :=
  ∀ (N m h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), 1 ≤ m →
    IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) ∧ IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) ∧
      HasIwahoriFact k N (Zls.Km k N m) d hd

variable (k) in

def CH : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ g : GL (Fin N) k, ∃ T : Module.End ℂ (fixed π J), IsHeckeOp π J g T

end PositivityTheory.Lbc

end
