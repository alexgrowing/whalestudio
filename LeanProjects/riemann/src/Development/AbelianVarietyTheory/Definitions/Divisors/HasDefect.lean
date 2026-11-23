import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

abbrev Fld (Z : Scheme.{0}) : Type := ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}

def IsTr {S : Type} [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (v : TanM (𝟙 (Sp R)) G)
    (w : Sp (DualNumber S) ⟶ G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ G.hom) ⟶ G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ (tv v).left ∧ (g' * v').left = w

def IsInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) : Prop :=
  IsField ⊤ dd ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (w : Sp (DualNumber S) ⟶ G.left)
    (O : G.left.Opens) (f : Γ(G.left, O)), g ≫ G.hom = spMap φ → ⊤ ≤ g ⁻¹ᵁ O → IsTr G φ g v w →
      (valR w O f).snd = valR g O (dd O f)

def IsLift (D : R → R) (W : G.left.Opens) (d : Fld G.left) : Prop :=
  IsField W d ∧ ∀ O, O ≤ W → ∀ r, d O (constFn G.hom O r) = constFn G.hom O (D r)

variable {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R)

def dlg (δ : Fld G.left) (i i' : L.ι) (O : G.left.Opens) : Γ(G.left, O) :=
  δ O (pbT m (L.g i i').val O) * pbT m (L.g i i')⁻¹.val O

def KSRel (Θ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (J : Type) (W : J → G.left.Opens) (j : J → L.ι) (d : J → Fld G.left),
    ⨆ i, W i = ⊤ ∧ (∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)) ∧ (∀ i, IsLift G D (W i) (d i)) ∧
    ∀ i i' O, O ≤ W i ⊓ W i' → ∀ f, d i O f - d i' O f =
      ∑ a, ∑ b, constFn G.hom O (Θ a b) * dlg G m L (dd b) (j i) (j i') O * dd a O f

def op (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    (O : G.left.Opens) (f : Γ(G.left, O)) : Γ(G.left, O) :=
  2 * (k : Γ(G.left, O)) * d O f - ∑ a, ∑ b, constFn G.hom O (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, constFn G.hom O (u a) * dd a O f + (2 * (k : Γ(G.left, O)) ^ 2 * rsT p O + 2 * (k : Γ(G.left, O)) * rsT p' O) * f

structure Heat where

  Θ : Matrix (Fin n) (Fin n) R
  symm : Θᵀ = Θ

  u : Fin n → R

  J : Type

  W : J → G.left.Opens

  j : J → L.ι

  d : J → Fld G.left

  p : ∀ i, Γ(G.left, W i)

  p' : ∀ i, Γ(G.left, W i)
  cover : ⨆ i, W i = ⊤
  le : ∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)
  lift : ∀ i, IsLift G D (W i) (d i)
  glue : ∀ (k : ℕ) i i' O, O ≤ W i ⊓ W i' → ∀ f,
    op G dd Θ u (d i) (p i) (p' i) k O (pbT m (L.g (j i) (j i')).val O ^ k * f) =
      pbT m (L.g (j i) (j i')).val O ^ k * op G dd Θ u (d i') (p i') (p' i') k O f

abbrev SecM {Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ))

variable {G m L dd D}

def Heat.Acts (h : Heat G m L dd D) (k : ℕ) (τ τ' : SecM m L k) : Prop :=
  ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) =
    op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i))

end General

def ringOp {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω)
    (p p' : Ω) (k : ℕ) (f : Ω) : Ω :=
  2 * (k : Ω) * d f - ∑ a, ∑ b, Θ a b * dd a (dd b f) + 2 * ∑ a, u a * dd a f + (2 * (k : Ω) ^ 2 * p + 2 * (k : Ω) * p') * f

def epsHom {Ω : Type} [CommRing Ω] (δ : Derivation ℤ Ω Ω) : Ω →+* DualNumber Ω where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_zero' := by simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]

def IsValue {X Y : Scheme.{0}} {Ω : Type} [CommRing Ω] (m : Y ⟶ X) (L : LB X) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ m)) (k : ℕ) (σ : SecM m L k) (s : Ω) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z) (J), Good L z J →
    sval σ (r ≫ x) z J = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom s) * (val g r z J ^ k).val

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

def IsTerm (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good Q.P.L y J →
    sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def IsWt (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (a a' : Sp S ⟶ Y.H.left), a = x.left → a' = x'.left → ⊤ ≤ a ⁻¹ᵁ V → ⊤ ≤ a' ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
    (∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
    valR a' V f = c α * valR a V f

variable {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

def IsBasic : Prop :=
  ∀ i, (∃ V : Q.P.A.left.Opens, h.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h.p i) ∧ IsWt Y 0 _ (h.p' i) ∧
    ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
      IsWt Y α (Y.q.left ⁻¹ᵁ V) (h.d i _ f)

def TActs (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) : Prop :=
  ∃ τ τ', IsTerm Y k α σ τ ∧ IsTerm Y k α σ' τ' ∧ h.Acts k τ τ'

variable (Q) in

def ShiftEq (k : ℕ) (mu α : Q.X) (σ : Q.SecB k α) (σ₁ : Q.SecB k (α + k • mu)) (c : R) (σ₂ : Q.SecB k (α + k • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k)), u.IsGen →
    LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α) →
    ∀ z J, Good Q.P.L z J →
      sval σ₁ (DegPre.prB Q (FractionRing R)).left z J =
        (val u (𝟙 _) z J).val * sval σ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
          gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J

def HasDefect (c : ℕ → Q.X → Q.X → R) : Prop :=
  ∀ (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)), 1 ≤ k →
    ShiftEq Q k mu α σ σ₁ 0 σ₁ → TActs Y h k α σ σ' → TActs Y h k (α + k • mu) σ₁ σ₁' →
      ShiftEq Q k mu α σ' σ₁' (c k mu α) σ₁

end Raynaud

end GlobalTheory.Heat
