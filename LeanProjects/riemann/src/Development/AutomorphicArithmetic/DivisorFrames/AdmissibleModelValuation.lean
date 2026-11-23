import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
import Development.AutomorphicArithmetic.DivisorFrames.DominatingModelsSpherical
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem ext_uniq' {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O) [IsProper s] {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (x y : Sp ↥(Formalism.MainNotions.DIV.Cons.intO C) ⟶ X)
    (h : spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ y = spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ x) : y = x := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have : IsDominant (spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (Formalism.MainNotions.DIV.Cons.intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

private theorem ext_ex' {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O) [IsProper s] {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (a : O →+* ↥(Formalism.MainNotions.DIV.Cons.intO C)) (w : Sp C ⟶ X)
    (hs : w ≫ s = spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ spMap a) :
    ∃ z : Sp ↥(Formalism.MainNotions.DIV.Cons.intO C) ⟶ X, spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ z = w ∧ z ≫ s = spMap a := by
  have := GlobalTheory.LocM.Cht.isFractionRing_ball C
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) s).1
  let S : ValuativeCommSq s :=
    { R := ↥(Formalism.MainNotions.DIV.Cons.intO C)
      K := C
      i₁ := w
      i₂ := spMap a
      commSq := ⟨hs⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem UpperTheory.admissible_model_valuation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (O : Type) [CommRing O] (β : O →+* i₀.c.F) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β) (b₀ : O →+* i₀.c.V W), p.Prime → (p : ℂ) ∈ W.nonunits → (i₀.c.V W).subtype.comp b₀ = β → Dominates T (Y i₀) b₀ → ∀ (k : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Pad.Letter Dw), letterOf Dw st = some x → ∀ (M : LineModel Z k st x) (a : Fin Z.m) (i : Fin M.L.n) (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ), LocM.IsTrans i₀ Z.i τ mu → ∀ (C : Formalism.MainNotions.DIV.Cons.SCF p) (zO : Sp ↥(Formalism.MainNotions.DIV.Cons.intO ↥C.S) ⟶ Z.X) (φ : Γ(Z.X, (Z.U a).1) →+* ↥C.S) (y : Sp ↥C.S ⟶ (Xo i₀.l).XF i₀.c) (f : i₀.c.F →+* ↥C.S) (u G : Vecs Dw T.t ↥C.S) (cf : Fin (Dw.mult x.1) → ↥C.S), spMap φ ≫ Z.chart a = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO → ⊤ ≤ zO ⁻¹ᵁ M.L.U i → y ≫ (Y i₀).j = (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO) ≫ Z.π ≫ τ → y ≫ pullback.snd _ _ = spMap f → LocM.IsFrame T.t f (y ≫ T.j) u → LocM.IsFrame T.t f (y ≫ T.j) G → (∀ σ m, Transp T (Y i₀) y (u σ m) ((Z.fr a).bc φ σ m ≫ mu.φ)) → (∀ σ, Pull.Tri T.t (y ≫ T.j) (G σ) (u σ)) → IsCombAtG T.t (y ≫ T.j) (G x.1) cf (u x.1 x.2) → lnStep T.t (y ≫ T.j) G p k st = -Real.log ‖cf x.2‖ - Real.log ‖valF (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO) _ (M.r a i).val‖ := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ β T b₀ hp hW hb hD k st x hx M a i τ mu _ C zO φ y f u G cf h hi hy hf Fu FG hT
    hTri hc
  obtain ⟨P, hP⟩ := GlobalTheory.ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C zO (Pull.range_opn Z h)
  have N := M.norm ⟨C, P, zO, hP⟩ a i φ h hi
  have g₀ : LocM.Mdl.Pt.gen (Z := Z) ⟨C, P, zO, hP⟩ = spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO := rfl
  rw [g₀] at N
  have g₁ : (spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO) ≫ Z.π =
      spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ zO ≫ Z.π := Category.assoc _ _ _
  have g₂ : spMap (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype ≫ (zO ≫ Z.π) ≫ τ = y ≫ (Y i₀).j := by
    rw [hy]; simp only [Category.assoc]
  have F := Pull.chart_frame Z h
  rw [g₁] at N F
  have q₁ := Pull.lnStep_push (Dw := Dw) (p := p) mu k (zO ≫ Z.π) (Pull.ext_unique _ _) (fun σ j => (F.1 σ j).1) st
  rw [g₂] at q₁
  let alg : ↥(i₀.c.V W) →+* ↥(Formalism.MainNotions.DIV.Cons.intO ↥C.S) := (Spec.preimage (((zO ≫ Z.π) ≫ τ) ≫ (Y i₀).s)).hom
  have halg : spMap alg = ((zO ≫ Z.π) ≫ τ) ≫ (Y i₀).s := Spec.map_preimage _
  have compat : (Formalism.MainNotions.DIV.Cons.intO ↥C.S).subtype.comp alg = f.comp (i₀.c.V W).subtype := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    change spMap _ = spMap _
    rw [← ModelRelProbe.spMap_comp, ← ModelRelProbe.spMap_comp, halg, ← Category.assoc, g₂, Category.assoc,
      ModelRelProbe.j_over, ← Category.assoc, hf]
  let P₀ : PointsOfFlagModel.PtC (Y i₀) C := ⟨alg, f, compat, y, hf, (zO ≫ Z.π) ≫ τ, halg.symm, g₂⟩
  have q₂ := UpperTheory.dominating_models_spherical E H Dw i₀.l (Xo i₀.l) i₀.c O _ β _ T (Y i₀) b₀ hb hD p C P₀ u
    (fun σ m => (Z.fr a).bc φ σ m ≫ mu.φ)
    (fun σ m => GlobalTheory.LieMet.isTan_push mu _ ((Category.assoc _ _ _).trans g₂) (F.1 σ m).1) hT k st
  have pr : IsProper T.s := projProper _ _ _ T.proj
  obtain ⟨xO, hxO, -⟩ := ext_ex' T.s (alg.comp b₀) (y ≫ T.j) (by
    rw [Category.assoc, ModelRelProbe.j_over, ← Category.assoc, hf, ModelRelProbe.spMap_comp,
      ModelRelProbe.spMap_comp, ← RingHom.comp_assoc, compat, RingHom.comp_assoc, hb])
  rw [← hxO] at Fu FG hTri hc
  have q₃ := Pull.lnStep_tri HTBound.htBound hp C k xO (fun y hy => ext_uniq' T.s _ y hy) FG Fu hTri hx hc
  rw [hxO] at q₃
  have q₄ : lnStep T.t (y ≫ T.j) u p k st =
      lnStep (Dw := Dw) (Y i₀).t (y ≫ (Y i₀).j) (fun σ m => (Z.fr a).bc φ σ m ≫ mu.φ) p k st := q₂
  linarith
