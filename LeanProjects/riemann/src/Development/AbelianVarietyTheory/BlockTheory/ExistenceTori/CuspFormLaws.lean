import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ConjugateFieldNorm

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
open scoped TensorProduct

section Quot

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

@[reducible] def topU (A : Type) [CommRing A] [Algebra F A] [t : TopologicalSpace A] (V : HSpace E r) :
    TopologicalSpace (UA F A V) :=
  ⨅ (a : Fin r) (b : Fin r) (φ : E →ₗ[F] F),
    t.induced fun g => TensorProduct.rid F A (LinearMap.lTensor A φ (g.1.val a b))

@[reducible] def topG (V : HSpace E r) : TopologicalSpace (GA F V) :=
  (topU F (Ai F) V).induced Prod.fst ⊓ (topU F (Af F) V).induced Prod.snd

def ratG (V : HSpace E r) : Subgroup (GA F V) where
  carrier := {g | ∃ γ, IsRat F V γ g}
  one_mem' := ⟨1, by simp [IsRat, Matrix.map_one]⟩
  mul_mem' := by
    rintro g h ⟨γ, g1, g2⟩ ⟨δ, h1, h2⟩
    refine ⟨γ * δ, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.map_mul, ← g1, ← h1]; rfl
    · rw [Units.val_mul, Matrix.map_mul, ← g2, ← h2]; rfl
  inv_mem' := by
    rintro g ⟨γ, g1, g2⟩
    have e1 : g.1.1 = Matrix.GeneralLinearGroup.map (incl F (Ai F)) γ := Units.ext g1
    have e2 : g.2.1 = Matrix.GeneralLinearGroup.map (incl F (Af F)) γ := Units.ext g2
    refine ⟨γ⁻¹, ?_, ?_⟩
    · change (g.1.1⁻¹).val = _
      rw [e1, ← map_inv]; rfl
    · change (g.2.1⁻¹).val = _
      rw [e2, ← map_inv]; rfl

def AutQ (V : HSpace E r) : Type := Quotient (QuotientGroup.rightRel (ratG F V))

def autMk (V : HSpace E r) (g : GA F V) : AutQ F V := Quotient.mk _ g

instance (V : HSpace E r) : MeasurableSpace (AutQ F V) := (@borel _ (topG F V)).map (autMk F V)

def autRt (V : HSpace E r) (h : GA F V) : AutQ F V → AutQ F V :=
  Quotient.map' (· * h) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab

theorem autRt_mk (V : HSpace E r) (h g : GA F V) : autRt F V h (autMk F V g) = autMk F V (g * h) := rfl

def IsAutProb (V : HSpace E r) (ν : Measure (AutQ F V)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ h s, MeasurableSet s → ν (autRt F V h ⁻¹' s) = ν s

def FinVol (V : HSpace E r) : Prop := ∃ ν, IsAutProb F V ν

def onQ (V : HSpace E r) (φ : GA F V → ℂ) (q : AutQ F V) : ℂ := φ (Quotient.out q)

theorem onQ_mk (V : HSpace E r) (φ : GA F V → ℂ) (h : ∀ γ ∈ ratG F V, ∀ g, φ (γ * g) = φ g) (g : GA F V) :
    onQ F V φ (autMk F V g) = φ g := by
  have e : (QuotientGroup.rightRel (ratG F V)) g (Quotient.out (autMk F V g)) :=
    Quotient.exact (Quotient.out_eq (autMk F V g)).symm
  rw [QuotientGroup.rightRel_apply] at e
  rw [← h _ e g, inv_mul_cancel_right, onQ]

example : FinVol F (HSpace.std E 0) := by
  refine ⟨Measure.dirac (autMk F _ 1), inferInstanceAs (IsProbabilityMeasure (Measure.dirac _)), fun h s _ => ?_⟩
  have : autRt F (HSpace.std E 0) h = id := by
    funext q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    have e : g * h = g := Prod.ext (Subtype.ext (Units.ext (Subsingleton.elim _ _)))
      (Subtype.ext (Units.ext (Subsingleton.elim _ _)))
    exact congrArg (autMk F _) e
  rw [this, Set.preimage_id]

end Quot

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E] {R : Nums E} (Q : CorePar F R)

def ValueWD (j : R.J) : Prop :=
  EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z)

def UnifTest (j : R.J) (σ : Q.c.F →+* ℂ) : Prop :=
  ∀ k (x : ((Q.U j σ).X k).dom),
    FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) ((Q.U j σ).un k x)

def WeightField (j : R.J) : Prop :=
  ∀ a n, ∀ f ∈ sec (Q.Xo j) Q.c a n, ∀ (S : Type) [CommRing S] [Algebra Q.c.F S], IsField S →
    ∀ (t : Ix (Q.Dw j) → Sˣ) (y y' : FrPt (Q.Xo j) Q.c S), FrBor t y y' →
      evR (Q.Xo j) Q.c f y' = wchar (ex (Q.Dw j) a n) t * evR (Q.Xo j) Q.c f y

def DictUnif (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) : Prop :=
  (∀ g, (Q.dict j σ hσ g).2 ∈ ((Q.U j σ).X (Q.dict j σ hσ g).1).dom ∧
    ∀ τ i, ‖dmin ((Q.U j σ).X (Q.dict j σ hσ g).1).Gm (Q.dict j σ hσ g).2 τ i‖ = 1) ∧
  (∀ g g', (∃ γ ∈ ((Q.U j σ).X (Q.dict j σ hσ g).1).Γ,
      Q.dict j σ hσ g' = ⟨(Q.dict j σ hσ g).1, lact γ (Q.dict j σ hσ g).2⟩) ↔
    ∃ γ ∈ ratG F (Q.V j), ∃ k ∈ Q.Kf j, g' = γ * g * k) ∧
  ∀ k, ∀ x ∈ ((Q.U j σ).X k).dom, ∃ g, ∃ γ ∈ ((Q.U j σ).X k).Γ, ∃ b ∈ Bor ((Q.U j σ).X k).Ψ R.r,
    Q.dict j σ hσ g = ⟨k, rmul (lact γ x) b⟩

def FrameExt (j : R.J) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    letI := io.toAlgebra
    ∀ y : FrPt (Q.Xo j) Q.c T.Fr, ∃ (y' : IntFr (Q.Xo j) Q.c T io) (t : Ix (Q.Dw j) → T.Frˣ), FrBor t y y'.1

def PtOnComp (j : R.J) : Prop :=
  ∀ la, ∀ f ∈ sec (Q.Xo j) Q.c 0 0, f * f = f → f ≠ 0 → ∃ y : Q.Pt j la, Q.vAt_vw y f ≠ ⊤

def supLat (j : R.J) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Q.Cusp j a n) :=
  {f | ∀ la (y : Q.Pt j la), 0 ≤ Q.vAt_vw y f}

def autFn (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (f : Q.Rules j) : AutQ F (Q.V j) → ℂ :=
  onQ F (Q.V j) (Q.adelFn j σ hσ f)

def CuspSqInt (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (ν : Measure (AutQ F (Q.V j))) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ Q.Cusp j a n, MemLp (autFn Q j σ hσ f) 2 ν

def CuspFormL2NormZeroImpliesZero (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (ν : Measure (AutQ F (Q.V j))) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ Q.Cusp j a n, eLpNorm (autFn Q j σ hσ f) 2 ν = 0 → f = 0

def l2At (j : R.J) (ν : Measure (AutQ F (Q.V j))) (σ : Q.c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Q.Cusp j a n) : ENNReal :=
  ENNReal.ofReal (lieFac (Q.Dw j) Q.xiAbs a) *
    eLpNorm (autFn Q j (goodOf Q.c σ) (goodEmb_goodOf Q.c σ) f) 2 ν

def FormLawsAt (j : R.J) : Prop :=

  LevelByCongruence F (Q.V j) (R.g 0 * R.g 1) ∧

  ValueWD Q j ∧ WeightField Q j ∧

  (∀ σ (hσ : GoodEmb Q.c σ), UnifTest Q j σ ∧ DictUnif Q j σ hσ) ∧

  UnitIndep (Q.Xo j) Q.c ∧ IntFrNe (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) ∧ FrameExt Q j ∧ PtOnComp Q j ∧

  CuspFD (Q.Xo j) Q.c (Q.U j) ∧ SupDef (Q.Xo j) Q.c (Q.U j) ∧

  FinVol F (Q.V j) ∧
  ∀ ν, IsAutProb F (Q.V j) ν → ∀ σ (hσ : GoodEmb Q.c σ), CuspSqInt Q j σ hσ ν ∧ CuspFormL2NormZeroImpliesZero Q j σ hσ ν

def FormLaws : Prop := Q.Pins ∧ ∀ j, FormLawsAt Q j

def CuspLawsAt (j : R.J) : Prop :=
  FJ.CuNeF (Q.X0 j) (min (R.p j) (R.q j)) ∧ FJ.LatZ (Q.X0 j) (min (R.p j) (R.q j)) ∧
  FJ.OrbDom (Q.X0 j) (min (R.p j) (R.q j)) ∧ FJ.XcLatF (Q.X0 j) Q.frI (min (R.p j) (R.q j)) ∧
  FJ.ExpoMatch (Q.X0 j) Q.frI (min (R.p j) (R.q j)) (R.g 0 * R.g 1)

def CoreLaws : Prop :=
  FormLaws Q ∧ ∀ j, CuspMul (Q.Xo j) Q.c (Q.U j) ∧ CuspLawsAt Q j

variable {Q}

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies
