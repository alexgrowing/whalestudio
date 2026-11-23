import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical

namespace GlobalTheory.LieFilt

section Matrices

variable {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}

def BlockUni {R : Type} [CommRing R] (N : Matrix κ κ R) : Prop :=
  ∀ z z', ¬ bl z < bl z' → N z z' = (1 : Matrix κ κ R) z z'

def minor {R : Type} [CommRing R] (w : κ ≃ Fin g) (k : ℕ) (P : Matrix (Fin g) κ R) : R :=
  ((P.submatrix w id).toSquareBlockProp fun z => bl z < k).det

def IntAdapted {K : Type} [NormedField K] (P : Matrix (Fin g) κ K) : Prop :=
  ∃ (N : Matrix κ κ K) (C' : Matrix κ (Fin g) K), BlockUni bl N ∧ (∀ b z, ‖(P * N) b z‖ ≤ 1) ∧ (∀ z b, ‖C' z b‖ ≤ 1) ∧
    P * N * C' = 1 ∧ C' * (P * N) = 1

def GrCond {K : Type} [NormedField K] (P : Matrix (Fin g) κ K) : Prop :=
  ∀ (k : ℕ) (a : κ → K), (∀ z, bl z ≠ k → a z = 0) →
    ((∀ z, ‖a z‖ ≤ 1) ↔ ∃ a' : κ → K, (∀ z, ¬ bl z < k → a' z = 0) ∧ ∀ b, ‖P.mulVec (a + a') b‖ ≤ 1)

end Matrices

section Sheaves

variable {X : Scheme.{0}} {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}

def LocAdapted (r : ι → ℕ) (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) (V : X.Opens) : Prop :=
  ∃ (f : ∀ a, Fin (r a) → Γ(E a, V)) (_ : ∀ a, VB.IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
    (hf' : ∀ a, VB.IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : VB.IsFrame c), ∀ a i,
    (∀ z : Σ a, Fin (r a), o a < o z.1 → (hc.basis le_rfl).repr ((T a).app V (f a i)) z = 0) ∧
      ∀ j, (hc.basis le_rfl).repr ((T a).app V (f a i)) ⟨a, j⟩ = ((hf' a).basis le_rfl).repr ((u a).app V (f a i)) j

def DualCharts {Y : Scheme.{0}} (ρ : X ⟶ Y) {F : Y.Modules} {g : ℕ} (ℓ : ∀ c : VB.Chart F g, Fin g → Γ(L, ρ ⁻¹ᵁ c.U))
    (hℓ : ∀ c, VB.IsFrame (ℓ c)) : Prop :=
  ∀ (c c' : VB.Chart F g) (b a : Fin g), trCo (hℓ c) (ℓ c') b a =
    ρ.appLE (c'.U ⊓ c.U) (ρ ⁻¹ᵁ c.U ⊓ ρ ⁻¹ᵁ c'.U) (fun _ hx => ⟨hx.2, hx.1⟩) (trCo c'.isFrame c.e a b)

end Sheaves

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsTanMat {K : Type} [CommRing K] (x : Sp K ⟶ Z.X) {g : ℕ} (ch : VB.Chart (omega Z.t.G) g) {κ : Type}
    (v : κ → (Sp (DualNumber K) ⟶ Z.t.G.left)) (P : Matrix (Fin g) κ K) : Prop :=
  ∀ (i : κ) (hv : IsTanAtG Z.t x (v i)) (hV : ⊤ ≤ x ⁻¹ᵁ ch.U) (b : Fin g), P b i = tanEv Z.t hv hV (ch.e b)

variable {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {M : X.Modules} {r g : ℕ} (t : FrAssign Z M r jB)
  (ch : VB.Chart (omega Z.t.G) g) {V : X.Opens} {f : Fin r → Γ(M, V)} (hf : VB.IsFrame f)

def GenCoord (A : Matrix (Fin g) (Fin r) Γ(W, jB ⁻¹ᵁ V)) : Prop :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V) (hx' : ⊤ ≤ x ⁻¹ᵁ (jB ⁻¹ᵁ V)),
    IsTanMat Z (x ≫ πB ≫ genι Z) ch (t V f hf K x hx) (A.map (TangentOrigin.evalPt x (jB ⁻¹ᵁ V) hx'))

def TanCoord (ρ : X ⟶ Z.X) {L : X.Modules} {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)}
    (hℓ : ∀ ch, VB.IsFrame (ℓ ch)) (T : M ⟶ L) : Prop :=
  ∀ (ch : VB.Chart (omega Z.t.G) g) (V : X.Opens) (hV : V ≤ ρ ⁻¹ᵁ ch.U), IsAffineOpen V →
    ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f), GenCoord Z jB πB t ch hf (Matrix.of fun b i => jB.app V (((hℓ ch).basis hV).repr (T.app V (f i)) b))

def MetDict {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {q : X ⟶ Sp (𝓞 F)} (ρ : X ⟶ Z.X) {L : X.Modules}
    {ℓ : ∀ ch : VB.Chart (omega Z.t.G) g, Fin g → Γ(L, ρ ⁻¹ᵁ ch.U)} (hℓ : ∀ ch, VB.IsFrame (ℓ ch))
    (G : ∀ σ' : c.F →+* ℂ, EigMet Z σ') (hL : VMetric q L g) : Prop :=
  ∀ (σ : F →+* ℂ) (z : CxPts q (σ.comp (algebraMap (𝓞 F) F))) (yc : CxPts (genStr Z) (σ.comp e.symm.toRingHom)),
    z.1 ≫ ρ = yc.1 ≫ genι Z → ∀ (ch : VB.Chart (omega Z.t.G) g), ⊤ ≤ (yc.1 ≫ genι Z) ⁻¹ᵁ ch.U →
    ∀ (u : EigFrame Z (σ.comp e.symm.toRingHom) (yc.1 ≫ genι Z)) (P : Matrix (Fin g) (Σ τ, Fin (Dw.mult τ)) ℂ),
      IsTanMat Z (yc.1 ≫ genι Z) ch (fun s : Σ τ, Fin (Dw.mult τ) => u.v s.1 s.2) P →
      (∀ τ i j, HermFrame.form ((hL.met _).G ⟨ρ ⁻¹ᵁ ch.U, ℓ ch, hℓ ch⟩ z) (fun b => P b ⟨τ, i⟩) (fun b => P b ⟨τ, j⟩) =
        (G _).gram yc u τ j i) ∧
      ∀ s s' : Σ τ, Fin (Dw.mult τ), s.1 ≠ s'.1 →
        HermFrame.form ((hL.met _).G ⟨ρ ⁻¹ᵁ ch.U, ℓ ch, hℓ ch⟩ z) (fun b => P b s) (fun b => P b s') = 0

end Free

end GlobalTheory.LieFilt

end
