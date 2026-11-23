import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PairVEqZeroOfMemLieSpan
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAdaptedOfIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.GradedPieces GlobalTheory.TotalFrame

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

section Graded

variable {Z B : Mdl Y i₀}

def HasCoord (g : Z.X ⟶ B.X) (L : Lat B) {V : B.X.Opens} {n : ℕ} (m : Fin n → Γ(L.N.toMod, V)) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (c : ∀ σ, Fin (Dw.mult σ) → Fin n → k) : Prop :=
  ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V),
    LocM.IsTrans B.i Z.i τ mu ∧ ∀ σ i, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v),
      v ≫ B.tMap.φ = u σ i ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = c σ i l

variable (Z) in

structure LatChart (L : Lat B) : Type where

  g : Z.X ⟶ B.X

  isMap : IsMap Z B g

  U : Z.X.Opens

  aff : IsAffineOpen U

  V : B.X.Opens

  le : U ≤ g ⁻¹ᵁ V

  n : ℕ

  m : Fin n → Γ(L.N.toMod, V)

  frame : VB.IsFrame m

  c : ∀ σ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)

  ext : ∀ σ, ∃ (a : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, a (e i) l = c σ i l

  adapted : ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn →
    ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l)

variable (Z) in

def HasLatFlags (L : Lat B) : Prop :=
  (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) ∧ ∀ x : Z.X, ∃ q : LatChart Z L, x ∈ q.U

variable {L : Lat B}

namespace LatChart

def FrameAt (q : LatChart Z L) {k : Type} [Field k] (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ q.U ∧ Z.FlagAt x u ∧ HasCoord q.g L q.m x u fun σ i l => valR x q.U (q.c σ i l)

theorem exists_frameAt (q : LatChart Z L) {k : Type} [Field k] {x : Sp k ⟶ Z.X} (h : ⊤ ≤ x ⁻¹ᵁ q.U)
    (ho : Set.range x ⊆ Z.opn) : ∃ u, q.FrameAt x u :=
  (q.adapted k x h ho).imp fun _ hu => ⟨h, hu⟩

def IsTr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (a : Γ(Z.X, q.U ⊓ q'.U)) : Prop :=
  ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (u u' : Vecs Dw (Y Z.i).t k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    q.FrameAt x u → q'.FrameAt x u' → (∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) (d σ)) →
      valR x _ a = ∏ σ, ∏ i, d σ i ^ e σ i

open Classical in

def tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : Γ(Z.X, q.U ⊓ q'.U)ˣ :=
  if h : ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val then h.choose else 1

theorem isTr_tr {q q' : LatChart Z L} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}
    (h : ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val) : q.IsTr q' e (q.tr q' e).val := by
  rw [tr, dif_pos h]
  exact h.choose_spec

end LatChart

variable (Z L) in

def latLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : LB Z.X := ⟨LatChart Z L, LatChart.U, fun q q' => q.tr q' e⟩

variable (L) in

def Curve.degLat {k : Type} [Field k] (c : Curve k Z.X) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : ℤ :=
  c.degOf (latLB Z L e)

end Graded

section Descent

def Mdl.SecVal (Q : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {U : Q.X.Opens}
    (f : ∀ a, Γ(Q.X, U ⊓ (Q.U a).1)ˣ) {k : Type} [Field k] (x : Sp k ⟶ Q.X) (u : Vecs Dw (Y Q.i).t k) (r : k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ U ∧ ∃ (a : Fin Q.m) (φ : Γ(Q.X, (Q.U a).1) →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ Q.chart a = x ∧ (∀ σ, DiagAt (Y Q.i).t (x ≫ Q.π) ((Q.fr a).bc φ σ) (u σ) (d σ)) ∧
      r = valR x _ (f a).val * ∏ σ, ∏ i, d σ i ^ e σ i

def Mdl.IsAutLB (Q : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (N : LB Q.X)
    (f : ∀ i a, Γ(Q.X, N.U i ⊓ (Q.U a).1)ˣ) : Prop :=
  N.IsLB ∧ ∀ (i i' : N.ι) (k : Type) [Field k] (x : Sp k ⟶ Q.X) (u : Vecs Dw (Y Q.i).t k) (r r' : k), Q.FlagAt x u →
    Q.SecVal e (f i) x u r → Q.SecVal e (f i') x u r' → r' = valR x _ (N.g i i').val * r

def Mdl.cst (Z : Mdl Y i₀) (a : Z.i.c.V W) : Γ(Z.X, ⊤) := Z.s.appTop ((Scheme.ΓSpecIso (.of (Z.i.c.V W))).inv a)

instance isPrincipal_map_different {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) :
    ((differentIdeal ℤ (𝓞 E)).map (embV c W σ)).IsPrincipal :=
  IsBezout.isPrincipal_of_FG _ (Ideal.FG.map (IsNoetherian.noetherian _) _)

def diffGen {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : c.V W :=
  Submodule.IsPrincipal.generator ((differentIdeal ℤ (𝓞 E)).map (embV c W σ))

theorem span_diffGen {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) :
    Ideal.span {diffGen c W σ} = (differentIdeal ℤ (𝓞 E)).map (embV c W σ) := Ideal.span_singleton_generator _

def Descends {B : Mdl Y i₀} (Z : Mdl Y i₀) (L : Lat B) (l : Level H) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ)
    (b : (E →+* ℂ) → ℤ) : Prop :=
  HasLatFlags Z L ∧ ∃ (m : ℕ) (Q : Mdl Y i₀) (π : Z.X ⟶ Q.X) (N : LB Q.X) (f : ∀ i a, Γ(Q.X, N.U i ⊓ (Q.U a).1)ˣ),
    0 < m ∧ Q.i.l = l ∧ (∀ σ, Q.ty σ = Finset.range (Dw.mult σ + 1)) ∧ IsMap Z Q π ∧ IsFinite π ∧
    Q.IsAutLB (m • e) N f ∧
    ∀ (q : LatChart Z L) (i : N.ι), ∃ ε : Γ(Z.X, q.U ⊓ π ⁻¹ᵁ N.U i)ˣ,
      ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (τ : (Y Z.i).X ⟶ (Y Q.i).X)
        (mu : SABMap (Y Z.i).t (Y Q.i).t τ) (r : k), q.FrameAt x u → LocM.IsTrans Q.i Z.i τ mu →
        Q.SecVal (m • e) (f i) (x ≫ π) (fun σ a => u σ a ≫ mu.φ) r →
        r * (∏ σ, valR x ⊤ (Z.cst (diffGen Z.i.c W σ)) ^ b σ) ^ m = valR x _ ε.val

end Descent

end GlobalTheory.LocM
