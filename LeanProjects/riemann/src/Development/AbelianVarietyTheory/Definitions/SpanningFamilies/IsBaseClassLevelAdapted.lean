import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

structure UW {σ : c.F →+* ℂ} (U : Unf Xo c σ r) where
  g : ℕ
  e : Fin g ≃ Lt1 Dw
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ
  isom : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))
  pt : ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          ((U.un k x).u τ i)) ∧
        ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

theorem nonempty_uw {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (h : IsUnf U) : Nonempty (UW U) := by
  unfold Formalism.L2.PjFree.IsUnf at h
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hisom, hpt⟩ := h
  exact ⟨{ g := g, e := e, F := F, ik := ik, φ := φ, isom := hisom, pt := hpt }⟩

def UW.emb {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (W : UW U) (k : U.Comp) :
    (W.F.Di (W.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (W.φ k).toLinearMap

def UW.mark {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (W : UW U) (k : U.Comp) : Dw.La →ₗ[𝓞 E] (Fin r → E) :=
  W.emb k ∘ₗ W.F.t (W.ik k)

def unC {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) :
    @FrPt E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra := U.un k x

def mvMap (ga : GL (Fin r) E) (f : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Dw.La →ₗ[𝓞 E] (Fin r → E) :=
  (Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E) ∘ₗ f

def Jd (d : DeltaDat Xo c n) : Ideal (𝓞 E) := d.I.map (H.bar : 𝓞 E →+* 𝓞 E)

structure LevTie (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (ph : (Fin n → LaJ Xo c d) → c.F) {X : Data E r}
    (D : SW.Level X) (hn : r ≤ n) : Prop where
  m : D.𝔪 = Mfr d.l₂
  prod : D.𝔪 = Mfr l * Jd d
  cop : IsCoprime (Mfr l) (Jd d)
  w : D.w = (H.w0 : E)
  grp : ∀ k : GL (Fin r) (𝓞 E ⧸ D.𝔪), k ∈ D.J ↔ ∀ i j, ∃ a ∈ Mfr l,
    (k : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j - (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) i j =
      Ideal.Quotient.mk D.𝔪 a
  det : ∀ k : D.J, ((k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) : Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)).det = 1 → D.lam k = 1
  tie : ∀ L ∈ D.lats, ∀ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), (∀ a, δ a ∈ L) →
    L ≤ LinearMap.range δ ⊔ Jd d • L → ∃ t : ℂ, ‖t‖ = 1 ∧
      ∀ (xs : Fin n → Dw.La) (y : Matrix (Fin n) (Fin r) E),
        (∀ i : Fin r, Cong X (Jd d) (y (Fin.castLE hn i)) (δ (xs (Fin.castLE hn i))) ∧
          Cong X (Mfr l) (y (Fin.castLE hn i)) (D.β i)) →
        (∀ k : Fin n, r ≤ (k : ℕ) → Cong X (Mfr l) (y k) 0) →
        σ (ph fun b => Submodule.Quotient.mk (xs b)) = t * datF D (Mfr l) hn y

def IsBaseClassLevelAdapted (d : DeltaDat Xo c n) {X : Data E r} (D : SW.Level X) (hn : r ≤ n) (x0 : Fin n → Dw.La)
    (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  (∀ i : Fin r, Cong X (Mfr l) (d.pd • δ (x0 (Fin.castLE hn i))) (D.β i)) ∧
    ∀ k : Fin n, r ≤ (k : ℕ) → x0 k ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)

def NOK (Λ : Lt E n) (N M : ℕ) : Prop := (⟨Λ⟩ : GenLat E n).LevOK N M

end

end GlobalTheory.Dict
