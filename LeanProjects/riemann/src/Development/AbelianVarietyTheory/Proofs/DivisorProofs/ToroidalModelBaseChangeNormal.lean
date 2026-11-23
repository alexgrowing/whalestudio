import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat.CoordReg

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem lat_ind_empty {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ Z.X) :
    lat Z.t p x (ArIn.ind ∅ p) = latDR Z.t x := by
  rw [show ArIn.ind ∅ p = false by simp [ArIn.ind]]
  rfl

theorem inGr_of_mem {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X}
    {Λ : Set (Sp (DualNumber K) ⟶ Z.t.G.left)} {τ : E →+* ℂ} {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (hw : IsTanAtG Z.t x w) (h : w ∈ Λ) : InGr Z φ x Λ τ w := by
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, w, h, ?_⟩
  have hu : ∀ k : Fin 1, IsTanAtG Z.t x ((fun _ => w) k) := fun _ => hw
  have h1 := isCombAtG_single Z.t x hu 0
  have e1 : (Fin.cons w Fin.elim0 : Fin (0 + 1) → _) = fun _ : Fin 1 => w := by
    funext k
    obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
    rfl
  have e2 : (fun _ : Fin 1 => (1 : K)) = Pi.single 0 1 := by
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  rw [e1, e2]
  exact h1

theorem norm_le_one {C : Type} [NormedField C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ}
    {u u' : Fin r → (Sp (DualNumber C) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u')
    {Λ : Set (Sp (DualNumber C) ⟶ Z.t.G.left)} {δ : C} (hδ : ‖δ‖ = 1)
    (h : ∀ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u a w) ↔ InGr Z φ x Λ τ w))
    (h' : ∀ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u' a w) ↔ spMap (epsMul δ) ≫ w ∈ Λ))
    {i : Fin r} {a : Fin r → C} (ha : IsCombAtG Z.t x u a (u' i)) (b : Fin r) : ‖a b‖ ≤ 1 := by
  have h1 : spMap (epsMul δ) ≫ u' i ∈ Λ := by
    refine (h' _ (hu'.1 i)).1 ⟨Pi.single i 1, fun k => ?_, isCombAtG_single Z.t x (fun j => (hu'.1 j).1) i⟩
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have h2 := Trans.isEigTan_smul Z (hu'.1 i) δ
  obtain ⟨a', ha', hc⟩ := (h _ h2).2 (inGr_of_mem Z h2.1 h1)
  have h3 := (hu.2 _ h2).unique (comb_smul (fun j => (hu.1 j).1) ha δ) hc
  have h4 := ha' b
  rw [← congrFun h3 b, norm_mul, hδ, one_mul] at h4
  exact h4

theorem exists_generic {F : Type} [Field F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X) (πB : W ⟶ gen Z) {r : ℕ}
    {τ : E →+* ℂ} {U : X.Opens} {u u' : LocAssign Z r jB U}
    (hV : IsAffineOpen (jB ⁻¹ᵁ U)) (hu : IsLocFrame Z e jB πB r τ U u) (hu' : IsLocFrame Z e jB πB r τ U u') :
    ∃ T : Fin r → Fin r → Γ(W, jB ⁻¹ᵁ U),
      ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W) (hx : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U)
        (hxx : ⊤ ≤ x ⁻¹ᵁ (jB ⁻¹ᵁ U)) (i : Fin r),
        IsCombAtG Z.t (x ≫ πB ≫ genι Z) (u K x hx) (fun b => evalPt x _ hxx (T b i)) (u' K x hx i) := by
  let x₀ : Sp Γ(W, jB ⁻¹ᵁ U) ⟶ W := hV.fromSpec
  have h1 : ⊤ ≤ (x₀ ≫ jB) ⁻¹ᵁ U := hV.fromSpec_preimage_self.ge
  have hψ : x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
      spMap (Spec.preimage (x₀ ≫ πB ≫ genStr Z ≫ spMap e.toRingHom)).hom := (Spec.map_preimage _).symm
  choose a ha using fun i => ((hu.1 _ x₀ h1 _ hψ).2 _ ((hu'.1 _ x₀ h1 _ hψ).1 i)).exists
  refine ⟨fun b i => a i b, fun K _ x hx hxx i => ?_⟩
  have hx0 : x = spMap (evalPt x _ hxx) ≫ x₀ := eq_spec_fromSpec hV x hxx
  generalize evalPt x _ hxx = ψ at hx0 ⊢
  subst hx0
  have h3 := GlobalTheory.LatDRFree.comb_map Z.t ψ (ha i)
  rw [hu'.2 _ _ ψ x₀ h1 hx i, show u K (spMap ψ ≫ x₀) hx = _ from funext fun k => hu.2 _ _ ψ x₀ h1 hx k,
    Category.assoc]
  exact h3

theorem grLat_at {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {X W : Scheme.{0}} {jB : W ⟶ X}
    {πB : W ⟶ gen Z} {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {u : FrAssign Z M r jB}
    (h : IsGrLat Z e jB πB M r τ u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime)
    (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X)
    (h1 : xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)))
    (h2 : spMap ε.O.subtype ≫ xt = xg ≫ jB) (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f)
    (h3 : ⊤ ≤ xt ⁻¹ᵁ U) (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U) :
    haveI : Fact (resP v).Prime := ⟨hp⟩
    ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
          IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u U f hf _ xg hx i) a w) ↔
        InGr Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
          (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
          (latDR Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)) τ w) :=
  h v hp ε xg xt h1 h2 U f hf h3 hx

open Classical in

theorem lieLat_at {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {X W : Scheme.{0}} {jB : W ⟶ X}
    {πB : W ⟶ gen Z} {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {u : FrAssign Z M r jB} {kind : ℕ → Bool}
    (h : IsLieLat Z e jB πB M r τ kind (fun _ => True) u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime)
    (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X)
    (h1 : xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)))
    (h2 : spMap ε.O.subtype ≫ xt = xg ≫ jB) (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f)
    (h3 : ⊤ ≤ xt ⁻¹ᵁ U) (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U) :
    haveI : Fact (resP v).Prime := ⟨hp⟩
    ∃ δ : ℂ_[resP v],
      ‖δ‖ = (resP v : ℝ) ^ (-(if kind (resP v) = true ∧ τ (H.rt : E) = H.rt0 then vDiff E (resP v) else 0)) ∧
      ∀ w, IsEigTan Z (((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧
          IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
            (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ u U f hf _ xg hx i) a w) ↔
        spMap (epsMul δ) ≫ w ∈ lat Z.t (resP v) (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) (kind (resP v))) :=
  h v trivial hp ε xg xt h1 h2 U f hf h3 hx

end

theorem exists_isCoordMat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) →
    ∀ (M M' : X.Modules) (r : ℕ) (τ : E →+* ℂ) (t : FrAssign Z M r jB) (t' : FrAssign Z M' r jB),
    IsLieFrames Z e jB πB M r τ false t → IsLieFrames Z e jB πB M' r τ false t' →
    IsLieLat Z e jB πB M r τ (ArIn.ind ∅) (fun _ => True) t → GlobalTheory.TwoLat.IsGrLat Z e jB πB M' r τ t' →
    ∀ (V : X.Opens), IsAffineOpen V → ∀ (f : Fin r → Γ(M, V)) (hf : VB.IsFrame f) (f' : Fin r → Γ(M', V))
    (hf' : VB.IsFrame f'), ∃ A : Matrix (Fin r) (Fin r) Γ(X, V), GlobalTheory.TwoLat.IsCoordMat Z jB πB t t' hf hf' A := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hn pb M M' r τ t t' ht ht' hL hG V hV f hf f' hf'
  have hI := IntCritPf.intCrit F X W q _ jB d hq hn pb
  have hj : IsAffineHom jB := MorphismProperty.of_isPullback (P := @IsAffineHom) pb.flip inferInstance
  have hu : IsLocFrame Z e jB πB r τ V (fun K _ x hx => t' V f' hf' K x hx) :=
    ⟨ht'.1 V f' hf', ht'.2.2 V f' hf'⟩
  have hu' : IsLocFrame Z e jB πB r τ V (fun K _ x hx => t V f hf K x hx) :=
    ⟨ht.1 V f hf, ht.2.2 V f hf⟩
  obtain ⟨T, hT⟩ := exists_generic Z e jB πB (hV.preimage jB) hu hu'
  have key : ∀ b i, ∃ f₀ : Γ(X, V), jB.app V f₀ = T b i := fun b i => by
    refine hI _ hV _ fun v ε xg xt h1 h2 h3 hx => ?_
    obtain ⟨hp, hio, -⟩ := ioOf_spec F v ε
    haveI : Fact (resP v).Prime := ⟨hp⟩
    have hxU : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V := fun p hp => hx hp
    obtain ⟨δ, hδ, hd⟩ := lieLat_at Z hL v hp ε xg xt h1 h2 V f hf h3 hxU
    have hd' := grLat_at Z hG v hp ε xg xt h1 h2 V f' hf' h3 hxU
    have hk : ArIn.ind ∅ (resP v) = false := by simp [ArIn.ind]
    rw [lat_ind_empty] at hd
    have hδ1 : ‖δ‖ = 1 := by
      rw [hδ, if_neg (fun h => Bool.false_ne_true (hk.symm.trans h.1)), neg_zero, Real.rpow_zero]
    have h4 : (spMap (ioOf (resP v) ε) ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
        spMap ((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))) := by
      rw [Category.assoc, h1, sp_comp]
    have hy : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ V := fun p _ => hxU (Set.mem_univ _)
    have b1 := ht'.1 V f' hf' _ _ hy _ h4
    have b2 := ht.1 V f hf _ _ hy _ h4
    rw [show t' V f' hf' _ _ hy = _ from funext fun k => ht'.2.2 V f' hf' _ _ _ xg hxU hy k, Category.assoc] at b1
    rw [show t V f hf _ _ hy = _ from funext fun k => ht.2.2 V f hf _ _ _ xg hxU hy k, Category.assoc] at b2
    exact (hio _).1 (norm_le_one Z b1 b2 hδ1 hd' hd
      (GlobalTheory.LatDRFree.comb_map Z.t (ioOf (resP v) ε) (hT _ xg hxU hx i)) b)
  choose A hA using key
  refine ⟨Matrix.of A, fun K _ x hx i => ?_⟩
  have h := hT K x hx hx i
  simp only [← hA] at h
  simp only [Matrix.of_apply, Trans.evalPt_app]
  exact h

end GlobalTheory.TwoLat.CoordReg

end
