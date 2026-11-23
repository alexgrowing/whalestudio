import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

noncomputable section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

structure Loc (X M : Type) [Group X] [Group M] where
  pr : X →* M
  loc : M →* X
  pr_loc : ∀ x, pr (loc x) = x
  comm : ∀ x g, pr g = 1 → loc x * g = g * loc x

def Loc.self (X : Type) [Group X] : Loc X X := ⟨MonoidHom.id X, MonoidHom.id X, fun _ => rfl, fun x g h => by
  have : g = 1 := h
  simp [this]⟩

variable {X M M' : Type} [Group X] [Group M] [Group M']

def Loc.Fact (L : Loc X M) (K : Subgroup X) (Kw : Subgroup M) : Prop := (∀ x ∈ Kw, L.loc x ∈ K) ∧ ∀ g ∈ K, L.pr g ∈ Kw

def Loc.Apart (L : Loc X M) (L' : Loc X M') : Prop := (∀ x, L.pr (L'.loc x) = 1) ∧ ∀ x, L'.pr (L.loc x) = 1

def tyFn (J : Subgroup M) (ψ : J →* ℂˣ) (g : M) : ℂ := if h : g ∈ J then (((ψ ⟨g, h⟩)⁻¹ : ℂˣ) : ℂ) else 0

structure TyLev (X M : Type) [Group X] [Group M] where
  L : Loc X M
  K : Subgroup X
  K₀ : Subgroup X
  J : Subgroup M
  ψ : J →* ℂˣ
  fact : L.Fact K J
  le : K₀ ≤ K
  ker : ∀ k ∈ K₀, ∀ h, ψ ⟨L.pr k, h⟩ = 1
  idx : K₀.relIndex K ≠ 0
  cms : IsCommensurated K₀

def TyLev.triv : TyLev Unit Unit where
  L := Loc.self Unit
  K := ⊤
  K₀ := ⊤
  J := ⊤
  ψ := 1
  fact := ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  le := le_rfl
  ker _ _ _ := rfl
  idx := by simp
  cms _ := by simp [Subgroup.relIndex_top_right, Subgroup.index_ne_zero_of_finite]

namespace TyLev

variable (T : TyLev X M)

def tf (h : X) (g : X) : ℂ := ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * tyFn T.J T.ψ (T.L.pr g) * dosetInd ℂ T.K h g

def admitted (f : X → ℂ) : Prop :=
  f ∈ Hecke ℂ T.K₀ ∧ (∀ g, f g ≠ 0 → T.L.pr g ∈ T.J) ∧ ∀ (j : T.J) g, f (g * T.L.loc j) = (((T.ψ j)⁻¹ : ℂˣ) : ℂ) * f g

def IsTy {V : Type} [AddCommGroup V] [Module ℂ V] (Φ : X → V) : Prop :=
  ∀ k (hk : k ∈ T.K) g, Φ (g * k) = ((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ : ℂˣ) : ℂ) • Φ g

def Cen (z : X) : Prop := (∀ g, z * g = g * z) ∧ T.L.pr z = 1

end TyLev

def wfn {J : Type} (K : Subgroup X) (F : J → X → ℂ) (w : List J) (f : X → ℂ) : X → ℂ := w.foldr (fun j acc => conv K (F j) acc) f

def tens {X₂ : Type} [Group X₂] (f : X → ℂ) (K₂ : Subgroup X₂) (h : X × X₂) : ℂ := f h.1 * Set.indicator (K₂ : Set X₂) 1 h.2

def hop {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (F : H → ℂ) : Module.End ℂ (forms ι K ξ) := if h : ∃ T, IsHecke ι K ξ F T then h.choose else 0

theorem heckeTrace_eq {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (K : Subgroup H)
    (ξ : Representation ℂ Γ V) (F : H → ℂ) : heckeTrace ι K ξ F = LinearMap.trace ℂ _ (hop ι K ξ F) := by
  unfold heckeTrace hop
  split_ifs <;> simp

def TfAdm : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h : X), T.L.pr h = 1 →
  T.admitted (T.tf h) ∧ (∀ k (hk : k ∈ T.K) g, T.tf h (k * g) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g ∧
    T.tf h (g * k) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g)

def ConvAdm : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (f f' : X → ℂ), T.admitted f → T.admitted f' → T.admitted (conv T.K₀ f f')

def ConvSupp : Prop := ∀ (X : Type) [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X), conv K f f' g ≠ 0 →
  ∃ x y, f x ≠ 0 ∧ f' y ≠ 0 ∧ g = x * y

def TfAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (z : X), T.Cen z → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ →
  ∀ g, hAct T.K₀ (T.tf (L'.loc t * z)) Φ g = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Φ (g * z * L'.loc x.out)

def TfCen : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (z : X), T.Cen z →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → ∀ g, hAct T.K₀ (T.tf z) Φ g = Φ (g * z)

def TfIdem : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h : X), T.L.pr h = 1 →
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g) → T.IsTy (hAct T.K₀ (T.tf h) Φ)) ∧
  conv T.K₀ (T.tf h) (T.tf 1) = T.tf h ∧ conv T.K₀ (T.tf 1) (T.tf h) = T.tf h

def TfMulCen : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (h z : X), T.L.pr h = 1 → T.Cen z →
  conv T.K₀ (T.tf z) (T.tf h) = T.tf (h * z) ∧ conv T.K₀ (T.tf h) (T.tf z) = T.tf (h * z)

def TfMulL : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (r : X), T.L.pr r = 1 → L'.pr r = 1 →
  conv T.K₀ (T.tf (L'.loc t)) (T.tf r) = T.tf (L'.loc t * r)

def TfMulR : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t : M') (r : X), T.L.pr r = 1 → L'.pr r = 1 →
  conv T.K₀ (T.tf r) (T.tf (L'.loc t)) = T.tf (L'.loc t * r)

def TfLoc : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ (t t' : M') (g : X),
  conv T.K₀ (T.tf (L'.loc t)) (T.tf (L'.loc t')) g =
    T.tf 1 (g * (L'.loc (L'.pr g))⁻¹) * conv Kw (dosetInd ℂ Kw t) (dosetInd ℂ Kw t') (L'.pr g)

def ConvRing : Prop := ∀ (X : Type) [Group X] (K : Subgroup X), IsCommensurated K → ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K,
  conv K f f' ∈ Hecke ℂ K ∧ ∀ f'' ∈ Hecke ℂ K, conv K (conv K f f') f'' = conv K f (conv K f' f'')

def TfComm : Prop := ∀ (X M M' M'' : Type) [Group X] [Group M] [Group M'] [Group M''] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ z z' : X, T.Cen z → T.Cen z' → ∀ t : M',
  (∀ (L'' : Loc X M'') (t' : M''), T.L.Apart L'' → L'.Apart L'' →
    conv T.K₀ (T.tf (L'.loc t * z)) (T.tf (L''.loc t' * z')) = conv T.K₀ (T.tf (L''.loc t' * z')) (T.tf (L'.loc t * z))) ∧
  ∀ t' : M', conv Kw (dosetInd ℂ Kw t) (dosetInd ℂ Kw t') = conv Kw (dosetInd ℂ Kw t') (dosetInd ℂ Kw t) →
    conv T.K₀ (T.tf (L'.loc t * z)) (T.tf (L'.loc t' * z')) = conv T.K₀ (T.tf (L'.loc t' * z')) (T.tf (L'.loc t * z))

def HopAct : Prop := ∀ (Γ X X₂ V : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V), IsCommensurated K → ∀ f ∈ Hecke ℂ K,
  ∀ (Φ : forms ι (K.prod K₂) ξ) (g : X) (g₂ : X₂),
    (hop ι (K.prod K₂) ξ (tens f K₂) Φ : X × X₂ → V) (g, g₂) = hAct K f (fun x => (Φ : X × X₂ → V) (x, g₂)) g

def HopConv : Prop := ∀ (Γ X X₂ V : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V), IsCommensurated K → ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K,
  hop ι (K.prod K₂) ξ (tens (conv K f f') K₂) = hop ι (K.prod K₂) ξ (tens f K₂) * hop ι (K.prod K₂) ξ (tens f' K₂)

def HopWord : Prop := ∀ (Γ X X₂ V J : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V), IsCommensurated K → ∀ F : J → X → ℂ, (∀ j, F j ∈ Hecke ℂ K) →
  ∀ f ∈ Hecke ℂ K, ∀ t : List J →₀ ℂ, FiniteDimensional ℂ (forms ι (K.prod K₂) ξ) →
  LinearMap.trace ℂ _ (CertificateRingHomMap.wop (fun j => hop ι (K.prod K₂) ξ (tens (F j) K₂)) t * hop ι (K.prod K₂) ξ (tens f K₂)) =
    t.sum fun w c => c * heckeTrace ι (K.prod K₂) ξ (tens (wfn K F w f) K₂)

def ExtP : Prop := ∀ (Γ X X₂ V : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V) (φ : X → V),
  (∀ γ, (ι γ).2 ∈ K₂ → ∀ g, φ ((ι γ).1 * g) = ξ γ (φ g)) → (∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∃ Φ : forms ι (K.prod K₂) ξ, (∀ g, (Φ : X × X₂ → V) (g, 1) = φ g) ∧
    ∀ g₂ : X₂, (∀ g, (Φ : X × X₂ → V) (g, g₂) = 0) ∨ ∃ γ, ∀ g, (Φ : X × X₂ → V) (g, g₂) = ξ γ (φ ((ι γ).1⁻¹ * g))

def ExtPEig : Prop := ∀ (Γ X X₂ V J : Type) [Group Γ] [Group X] [Group X₂] [AddCommGroup V] [Module ℂ V] (ι : Γ →* X × X₂)
  (K : Subgroup X) (K₂ : Subgroup X₂) (ξ : Representation ℂ Γ V), IsCommensurated K → ∀ φ : X → V, φ ≠ 0 →
  (∀ γ, (ι γ).2 ∈ K₂ → ∀ g, φ ((ι γ).1 * g) = ξ γ (φ g)) → (∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∀ (F : J → X → ℂ) (θ : J → ℂ), (∀ j, F j ∈ Hecke ℂ K) → (∀ j, hAct K (F j) φ = θ j • φ) →
  ∃ Φ : forms ι (K.prod K₂) ξ, Φ ≠ 0 ∧ ∀ j, hop ι (K.prod K₂) ξ (tens (F j) K₂) Φ = θ j • Φ

def FormsConj : Prop := ∀ (Γ Γ' H V J : Type) [Group Γ] [Group Γ'] [Group H] [AddCommGroup V] [Module ℂ V] (ι : Γ →* H) (ι' : Γ' →* H)
  (K : Subgroup H) (ξ : Representation ℂ Γ V) (ξ' : Representation ℂ Γ' V) (e : Γ' →* Γ) (h₀ : H) (y : V ≃ₗ[ℂ] V),
  (∀ γ, ι' γ = h₀ * ι (e γ) * h₀⁻¹) → (∀ γ v, ξ' γ (y v) = y (ξ (e γ) v)) →
  ∀ (F : J → H → ℂ) (θ : J → ℂ), (∀ j, ∃ T, IsHecke ι K ξ (F j) T) → (∀ j, ∃ T, IsHecke ι' K ξ' (F j) T) →
  (∀ j, Set.Finite {x : H ⧸ K | F j x.out ≠ 0}) →
  ∀ Φ : forms ι K ξ, Φ ≠ 0 → (∀ j, hop ι K ξ (F j) Φ = θ j • Φ) →
  ∃ Φ' : forms ι' K ξ', Φ' ≠ 0 ∧ ∀ j, hop ι' K ξ' (F j) Φ' = θ j • Φ'

def FormsFin : Prop := ∀ (Γ H V : Type) [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ι : Γ →* H)
  (K : Subgroup H) (ξ : Representation ℂ Γ V), Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)) →
  FiniteDimensional ℂ (forms ι K ξ)

def NZAbs : Prop := ∀ (Q : Type) [Fintype Q] (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)]
  [∀ q, FiniteDimensional ℂ (W q)] (J : Type) (T : ∀ q, J → Module.End ℂ (W q)) (θ : J → ℂ) (j₀ : J) (B : ∀ q, Module.End ℂ (W q)),
  (∀ q i j, Commute (T q i) (T q j)) → (∀ q j, Commute (B q) (T q j)) → θ j₀ = 1 → (∀ q, IsIdempotentElem (T q j₀)) →
  (∀ q x, B q (T q j₀ x) = 0 → T q j₀ x = 0) → (∃ q x, x ≠ 0 ∧ ∀ j, T q j x = θ j • x) →
  ∀ t : List J →₀ ℂ, (∀ q, CertificateRingHomMap.Cert (T q) θ t) → ∃ k, 1 ≤ k ∧ ∑ q, LinearMap.trace ℂ _ (CertificateRingHomMap.wop (T q) t * B q ^ k) ≠ 0

end UpperTheory.Gal.W2.Seed
