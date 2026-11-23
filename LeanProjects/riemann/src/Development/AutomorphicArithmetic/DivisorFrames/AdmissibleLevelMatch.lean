import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingFlag
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingMetric
import Development.AutomorphicArithmetic.DivisorFrames.GenericFibreOpenProjective
import Development.AutomorphicArithmetic.DivisorFrames.PointsGenericFibreComponents
import Development.AutomorphicArithmetic.DivisorFrames.EqGenericPointOfIntegralDim
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimComponent
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.ConsGeo

set_option backward.isDefEq.respectTransparency false

private theorem spC {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem factorRes (X : Scheme.{0}) {k : Type} [Field k] (w : Sp k ⟶ X) :
    ∃ ψ : X.residueField (w (closedPoint k)) →+* k, w = spMap ψ ≫ X.fromSpecResidueField _ :=
  ⟨(X.descResidueField (Scheme.stalkClosedPointTo w)).hom,
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X w).symm⟩

private theorem factorGen (X : Scheme.{0}) [IsIntegral X] {k : Type} [Field k] (w : Sp k ⟶ X)
    (h : w (closedPoint k) = genericPoint X) : ∃ θ : X.functionField →+* k, w = spMap θ ≫ gpt X := by
  obtain ⟨ψ, hψ⟩ := factorRes X w
  have key : ∀ x : X, x = genericPoint X → ∀ ψ : X.residueField x →+* k,
      ∃ θ : X.functionField →+* k, spMap ψ ≫ X.fromSpecResidueField x = spMap θ ≫ gpt X := by
    rintro _ rfl ψ
    refine ⟨ψ.comp (X.residue (genericPoint X)).hom, ?_⟩
    rw [spC, Category.assoc]
    rfl
  obtain ⟨θ, hθ⟩ := key _ h ψ
  exact ⟨θ, hψ.trans hθ⟩

private theorem ptComp {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (j : k →+* k') (w : Sp k ⟶ X) :
    (spMap j ≫ w) (closedPoint k') = w (closedPoint k) := by
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg w (Subsingleton.elim (α := PrimeSpectrum k) _ _))

private theorem gptPt (X : Scheme.{0}) [IsIntegral X] : gpt X (closedPoint X.functionField) = genericPoint X :=
  Scheme.fromSpecStalk_closedPoint

private theorem spInj {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B) (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem resSurj {X X' : Scheme.{0}} (g : X' ⟶ X) (x : X) (w' : Sp (X.residueField x) ⟶ X')
    (h : w' ≫ g = X.fromSpecResidueField x) (y : X') (ψ : X'.residueField y →+* X.residueField x)
    (hψ : w' = spMap ψ ≫ X'.fromSpecResidueField y) : Function.Surjective ψ := by
  have hx : g y = x := by
    have h1 := congrArg (fun m : Sp (X.residueField x) ⟶ X => m (closedPoint _)) h
    have h0 : w' (closedPoint _) = y := by
      rw [hψ]
      exact (ptComp ψ _).trans (Scheme.fromSpecResidueField_apply y _)
    exact (congrArg g h0.symm).trans (((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans
      (Scheme.fromSpecResidueField_apply x _))
  subst hx
  have h2 : spMap (ψ.comp (g.residueFieldMap y).hom) ≫ X.fromSpecResidueField (g y) =
      spMap (RingHom.id _) ≫ X.fromSpecResidueField (g y) := by
    rw [spC, Category.assoc]
    have := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y
    refine (congrArg (spMap ψ ≫ ·) this).trans ?_
    rw [← Category.assoc, ← hψ, h]
    simp [spMap]
  have h3 := spInj _ _ ((cancel_mono _).1 h2)
  exact fun a => ⟨_, DFunLike.congr_fun h3 a⟩

private theorem lft {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (h : f.Finite) :
    LocallyOfFiniteType (spMap f) := by
  have : IsFinite (spMap f) := (IsFinite.SpecMap_iff _).2 h
  infer_instance

private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] {e : F ≃+* i₀.c.F}
    {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U) (L : Lev Z T)
    [IsDiscreteValuationRing (Z.i.c.V W)]
    (hfull : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (hgen : Z.opn ⊆ (nmodel Z).gen) (d : ℕ)
    (hd : ∀ C, ((nmodel Z).comp C).relDim = d) (c : U.Comp) (hc : (Φ.C c).Y.dim = d)
    (K : Type) [Field K] (ι : (Φ.C c).Y.Fn →+* K) (w : Sp K ⟶ Z.X)
    (hw : Match L (Φ.C c) w (spMap ι ≫ genericPt (Φ.C c).Y)) :
    ∃ (C : (nmodel Z).Comp) (θ : ((nmodel Z).comp C).X.functionField →+* K),
      w = spMap θ ≫ gpt ((nmodel Z).comp C).X ≫ (nmodel Z).compι C := by
  have hx : w (closedPoint K) ∈ Z.opn := (UpperTheory.level_flag_compact_point L _ _ _ hw).1
  obtain ⟨ψ, hψ⟩ := factorRes Z.X w
  have hx' : Z.X.fromSpecResidueField (w (closedPoint K)) (closedPoint _) ∈ Z.opn :=
    (Scheme.fromSpecResidueField_apply (w (closedPoint K)) _).symm ▸ hx
  obtain ⟨c', q', hq'⟩ := UpperTheory.level_unfolding_flag Φ L (Z.X.fromSpecResidueField (w (closedPoint K))) hx'
  obtain ⟨-, -, ⟨f, hf1, hf2⟩, hbc⟩ := UpperTheory.level_flag_compact_point L _ _ _ hq'
  have h1 := hbc _ ψ
  rw [← hψ] at h1
  have h2 := UpperTheory.level_unfolding_metric Φ L hfull w _ _ _ _ h1 hw
  obtain ⟨rfl, h3⟩ := Sigma.mk.inj h2
  have h4 := eq_of_heq h3
  have h5 : q' (closedPoint _) = genericPoint (Φ.C c').Y.X := by
    refine (ptComp ψ q').symm.trans ?_
    rw [h4]
    exact (ptComp ι _).trans (gptPt _)
  obtain ⟨θ', hθ'⟩ := factorGen _ q' h5
  obtain ⟨C, w', hw'⟩ := (UpperTheory.points_generic_fibre_components _ (nmodel Z) _).2 (Z.X.fromSpecResidueField (w (closedPoint K))) (hgen hx')
  obtain ⟨hint, hopen, -, hproj, hdim, ε, hε⟩ := UpperTheory.generic_fibre_open_projective (Z.i.c.V W) Z.i.c.F ((nmodel Z).comp C)
  obtain ⟨ψ', hψ'⟩ := factorRes _ w'
  have hsurj := resSurj _ _ w' hw' _ ψ' hψ'
  haveI := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  haveI := lft ε.toRingHom (RingHom.Finite.of_surjective _ ε.surjective)
  haveI := lft e.toRingHom (RingHom.Finite.of_surjective _ e.surjective)
  haveI := lft (incl Z) (by
    haveI := Z.i.c.fin
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℚ _) ?_
    rw [Subsingleton.elim ((incl Z).comp (algebraMap ℚ _)) (algebraMap ℚ _)]
    exact RingHom.finite_algebraMap.2 inferInstance)
  have hE : w' ≫ ((nmodel Z).comp C).toBase.genFibreStr ≫ spMap ε.toRingHom = spMap f := by
    haveI := mono_spMap_subtype (Z.i.c.V W)
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← hf1, ← hw']
    simp only [Category.assoc]
    exact congrArg (w' ≫ ·) hε
  have h6 := UpperTheory.eq_genericPoint_of_integral_dim F _ (Φ.C c').Y.X
    (((nmodel Z).comp C).toBase.genFibreStr ≫ spMap ε.toRingHom ≫ spMap (incl Z) ≫ spMap e.toRingHom)
    (Φ.C c').Y.str d (by rw [hdim, hd]) (by rw [(Φ.C c').Y.topologicalKrullDim_eq, hc]) _ _ ψ' θ'
    (RingHom.isIntegral_of_surjective _ hsurj) (by
      rw [← Category.assoc, ← hψ', ← Category.assoc _ (gpt _), ← hθ', ← (Φ.C c').π_str, reassoc_of% hE,
        reassoc_of% hf2])
  have h7 : (spMap ψ ≫ w' ≫ ((nmodel Z).comp C).toBase.genFibreι) (closedPoint K) =
      genericPoint ((nmodel Z).comp C).X := by
    refine (ptComp ψ _).trans ((Scheme.Hom.comp_apply _ _ _).trans ?_)
    exact (congrArg _ h6).trans (genericPoint_eq_of_isOpenImmersion _)
  obtain ⟨θ, hθ⟩ := factorGen ((nmodel Z).comp C).X _ h7
  refine ⟨C, θ, ?_⟩
  rw [← Category.assoc, ← hθ, Category.assoc, Category.assoc, hw']
  exact hψ

set_option backward.isDefEq.respectTransparency true in
theorem UpperTheory.admissible_level_match :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), (∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) → ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)] (L : GlobalTheory.ConsGeo.Lev z.Z s.T.Z) (c : s.Comp) (K : Type) [Field K] (ι : (fl.C c).Y.Fn →+* K) (w : Sp K ⟶ z.Z.X), GlobalTheory.ConsGeo.Match L (fl.C c) w (spMap ι ≫ genericPt (fl.C c).Y) → ∃ (C : (nmodel z.Z).Comp) (θ : ((nmodel z.Z).comp C).X.functionField →+* K), w = spMap θ ≫ GlobalTheory.ConsGeo.gpt ((nmodel z.Z).comp C).X ≫ (nmodel z.Z).compι C := by
  intro D A N j S κ s fl hdim p hp W hW z _ L c K _ ι w hw
  have h1 : z.Z.opn ⊆ (nmodel z.Z).gen := opn_subset_gen hp hW
  have h2 : ∀ C, ((nmodel z.Z).comp C).relDim = Formalism.DegreeFormula.dimFl D.what₂.Tau N :=
    fun C => GlobalTheory.ShFam.Pad.RelDim.relDim_comp D A N j S κ p hp W hW z C
  have h3 := core (Z := z.Z) (T := s.T.Z) fl L z.full h1 _ h2 c (hdim c) K ι w hw
  exact h3
