import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSectionLiftsLocallyStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

section Free

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem isComb_unique {X : Scheme.{0}} {t : SAB H X} {K : Type} [CommRing K] {x : Sp K ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {a : Fin m → K} {w w' : Sp (DualNumber K) ⟶ t.G.left}
    (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' := by
  obtain ⟨p, hp, hp'⟩ := h
  obtain ⟨q, hq, hq'⟩ := h'
  have e : p = q := by
    funext i
    exact Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  rw [← hp', ← hq', e]

theorem exists_coord_form {K : Type} [CommRing K] {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x)
    (τ : E →+* ℂ) {m : ℕ} {uu : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : ∀ b, IsEigTan Z χ x τ (uu b))
    (k : Fin (Dw.mult τ)) : ∃ d : Fin m → K, ∀ (a : Fin m → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left)
      (cf : Fin (Dw.mult τ) → K), IsCombAtG Z.t x uu a w → IsCombAtG Z.t x (g.v τ) cf w → cf k = ∑ b, a b * d b := by
  choose T hT using fun b => (g.basis τ _ (hu b).1 (hu b).2).exists
  refine ⟨fun b => T b k, fun a w cf h1 h2 => ?_⟩
  let U : Fin m → TanM x Z.t.G := fun b => tanOf (hu b).1
  have e1 : ∀ b, U b = ∑ j, T b j • g.vec τ j := fun b => (isComb_iff (g.vec τ) _ (U b)).1 (hT b)
  have h3 : IsCombAtG Z.t x uu a (tv (∑ b, a b • U b)).left := (isComb_iff U a _).2 rfl
  rw [isComb_unique h1 h3] at h2
  have e2 := (isComb_iff (g.vec τ) cf _).1 h2
  have e3 : ∑ j, cf j • g.vec τ j = ∑ j, (∑ b, a b * T b j) • g.vec τ j := by
    rw [← e2]
    simp only [e1, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  exact Fintype.linearIndependent_iffₛ.1 (g.linearIndependent_vec τ) _ _ e3 k

theorem genericPt_π_genStr {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) :
    genericPt C.Y ≫ C.π ≫ genStr Z = spMap (constF e C.Y) := by
  letI := (constF e C.Y).toAlgebra
  rw [← Category.assoc, ← C.y0_x, Category.assoc, genStr, Z.jQ_over]
  exact GlobalTheory.ShFam.ptF_snd _

end Free

theorem top_le_genPt {G Y : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y) {W : Y.Opens} (h : j (genericPoint G) ∈ W) :
    ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W := by
  intro p _
  have h1 : genPt G p ⤳ genericPoint G := by
    have : genPt G p ∈ Set.range (G.fromSpecStalk (genericPoint G)) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have h2 : genPt G p ∈ j ⁻¹ᵁ W := h1.mem_open (j ⁻¹ᵁ W).isOpen h
  simpa using h2

theorem exists_coordFunctional : ∀ (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)),
    ∀ ch ch' : (((fl₀ a).root i).pull j).ι, genericPoint G ∈ (((fl₀ a).root i).pull j).U ch ⊓ (((fl₀ a).root i).pull j).U ch' →
      ∃ (W : Y₀.Opens) (hW : W ≤ (ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) (hx : ⊤ ≤ (GlobalTheory.FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
        (lam : Γ((fl₀ a).F i.succ, W) → G.functionField),
        (∀ (s : Γ(Y₀, W)) (t : Γ((fl₀ a).F i.succ, W)), lam (s • t) = TangentOrigin.evalPt (GlobalTheory.FlagCov.genPt G ≫ j) W hx s * lam t) ∧
        (∃ t : Γ((fl₀ a).F i.succ, W), ((fl₀ a).π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0)) ∧
        (∀ t : Γ((fl₀ a).F i.succ, W), ((fl₀ a).π i).app W t = Twist.resM _ (hW.trans inf_le_left) ((ch PUnit.unit).e 0) →
          lam t = ((r a i ch)⁻¹ : G.functionFieldˣ)) ∧
        (∀ t : Γ((fl₀ a).F i.succ, W), ((fl₀ a).π i).app W t = Twist.resM _ (hW.trans inf_le_right) ((ch' PUnit.unit).e 0) →
          lam t = ((r a i ch')⁻¹ : G.functionFieldˣ)) := by
  intro D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ G _ j πG pb _ _ φ φs jG r hc a i
    ch ch' hη
  haveI := (h a).isVB.isQuasicoherent
  obtain ⟨hr, -⟩ := hL.2.2.2.2.2.2 a
  obtain ⟨V, f, hV, hf⟩ := (h a).isVB (π₀ (j (genericPoint G)))
  have m1 : j (genericPoint G) ∈ (ch PUnit.unit).U :=
    LB.wchart_le ((fl₀ a).root i) (fun _ : PUnit.{1} => j) ch PUnit.unit hη.1
  have m2 : j (genericPoint G) ∈ (ch' PUnit.unit).U :=
    LB.wchart_le ((fl₀ a).root i) (fun _ : PUnit.{1} => j) ch' PUnit.unit hη.2
  obtain ⟨W, hW, t₀, hηW, ht₀⟩ := GlobalTheory.T.graded_section_lifts_locally (fl₀ a) i (((ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) ⊓ π₀ ⁻¹ᵁ V)
    (Twist.resM _ (inf_le_left.trans inf_le_left) ((ch PUnit.unit).e 0)) (j (genericPoint G)) ⟨⟨m1, m2⟩, hV⟩
  have hWV : W ≤ π₀ ⁻¹ᵁ V := hW.trans inf_le_right
  have hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W := top_le_genPt j hηW
  have hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, hc.1]
    exact top_le_genPt _ (by simpa using hV)
  have hpt : genPt G ≫ jG ≫ πB = spMap φ ≫ genericPt (O.var c) ≫ (O.Φ.C c).π := by
    rw [hc.2.1, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (O.Φ.C c).π) φs
  obtain ⟨g, hg⟩ := (O.Φ.C c).f0.exists_isMap φ (φ' := φ.comp (constF O.κ.e (O.var c)))
    (x' := genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) rfl (by
      have := congrArg (· ≫ genι O.s.T.Z) hpt
      simpa only [Category.assoc] using this)
  have hu : IsEigBasis O.s.T.Z (φ.comp (constF O.κ.e (O.var c))) (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (embB D a)
      (u a V f hf G.functionField (genPt G ≫ jG) hxV) := by
    have := (hL.2.2.2.1 a).1 V f hf G.functionField (genPt G ≫ jG) hxV (φ.comp (algebraMap _ (O.var c).Fn)) (by
      have h1 := congrArg (· ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) hpt
      simp only [Category.assoc] at h1 ⊢
      rw [h1, ← Category.assoc (O.Φ.C c).π, ← Category.assoc (genericPt _), genericPt_π_genStr,
        ← Spec.map_comp, ← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
      simp [constF])
    rw [Category.assoc] at this
    exact this
  let aG : Γ((fl₀ a).F i.succ, W) → Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField := fun t b =>
    TangentOrigin.evalPt (genPt G ≫ j) W hx (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι i.succ).app W t) b)
  have key : ∃ d : Fin (rkB D.what₂.Tau O.N O.j a) → G.functionField,
      ∀ (c₁ : (((fl₀ a).root i).pull j).ι) (hW₁ : W ≤ (c₁ PUnit.unit).U) (t : Γ((fl₀ a).F i.succ, W)),
        ((fl₀ a).π i).app W t = Twist.resM _ hW₁ ((c₁ PUnit.unit).e 0) →
          ∑ b, aG t b * d b = ((r a i c₁)⁻¹ : G.functionFieldˣ) := by
    have H1 := fun c₁ hW₁ t ht => hc.2.2 a i hr c₁ V f hf W hW₁ hWV t ht hx hxV
    have hv := funext (hg (embB D a))
    obtain ⟨τ, _ | _⟩ := a
    · obtain ⟨d, hd, -⟩ := hu.2 _ ⟨g.tan _ (Fin.cast hr i.rev), g.eig _ (Fin.cast hr i.rev)⟩
      refine ⟨d, fun c₁ hW₁ t ht => (H1 c₁ hW₁ t ht (Fin.cast hr i.rev) d ?_).2 ?_⟩
      · rw [hg] at hd
        exact hd
      have := i.2
      simp only [Fin.val_cast, Fin.val_rev]
      omega
    · obtain ⟨d, hd⟩ := exists_coord_form g _ hu.1 (Fin.cast hr i)
      refine ⟨d, fun c₁ hW₁ t ht => ?_⟩
      obtain ⟨w, cf, h1, h2, h3, -⟩ := H1 c₁ hW₁ t ht
      rw [← h3]
      exact (hd _ w cf h1 (hv ▸ h2)).symm
  obtain ⟨d, hd⟩ := key
  refine ⟨W, hW.trans inf_le_left, hx, fun t => ∑ b, aG t b * d b, fun s t => ?_, ⟨t₀, ?_⟩,
    fun t ht => hd ch _ t ht, fun t ht => hd ch' _ t ht⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [aG]
    rw [Scheme.Modules.Hom.app_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  · rw [ht₀, Twist.resM_resM]

end GlobalTheory.FlagCov

end
