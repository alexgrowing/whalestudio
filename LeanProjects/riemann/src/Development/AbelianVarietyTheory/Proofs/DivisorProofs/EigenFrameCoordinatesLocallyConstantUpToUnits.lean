import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FrameSpread

open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {F : EigFrame Z φ x}
    {F' : EigFrame Z φ' x'} {F'' : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''} (h1 : F.IsMap a F')
    (h2 : F.IsMap (b.comp a) F'') : F'.IsMap b F'' := fun τ i => by
  rw [h2 τ i, h1 τ i, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp]

end

theorem unitAt_det_co : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → f.IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK → f'.IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  haveI : IsIso (genι TF.Y) := GlobalTheory.VarFlag.isIso_genι
  let e : X₀ TF.Y Z ⟶ gen TF.Y := (barComp TF.Y Z).ι ≫ inv (genι TF.Y)
  have he : e ≫ genι TF.Y = (barComp TF.Y Z).ι := by simp [e]
  have hstrY : genStr TF.Y = genι TF.Y ≫ TF.Y.s := by
    have h0 : genι TF.Y ≫ TF.Y.s = genStr TF.Y ≫ spMap (RingHom.id c.F) := pullback.condition
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [h1, Category.comp_id] at h0
    exact h0.symm
  obtain ⟨U, hU, φU, F, hxU, hUstr, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y (e x)
  let ψ : ∀ p : X₀ TF.Y Z, e p ∈ U → (Γ(gen TF.Y, U) →+* (X₀ TF.Y Z).presheaf.stalk p) := fun p hp =>
    (e.stalkMap p).hom.comp ((gen TF.Y).presheaf.germ U (e p) hp).hom
  have hψ : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ e = spMap (ψ p hp) ≫ hU.fromSpec := by
    intro p hp
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hmono : ∀ {R : Type} [CommRing R] (a b : Γ(gen TF.Y, U) →+* R),
      spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec → a = b := fun a b h =>
    GlobalTheory.ShFam.EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 h)
  have hring : ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X₀ TF.Y Z) (ρ : c.F →+* R) (a : Γ(gen TF.Y, U) →+* R),
      q ≫ s₀ TF.Y Z = spMap ρ → q ≫ e = spMap a ≫ hU.fromSpec → ρ = a.comp φU := by
    intro R _ q ρ a h1 h2
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h1, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hUstr, ← Category.assoc (spMap a), ← h2, hstrY]
    simp only [Category.assoc]
    rw [← Category.assoc e, he]
  have hpt : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ (barComp TF.Y Z).ι = spMap (ψ p hp) ≫ hU.fromSpec ≫ genι TF.Y := by
    intro p hp
    rw [← he, ← Category.assoc, hψ p hp, Category.assoc]
  have hgen : ∀ p : X₀ TF.Y Z, (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk p :=
    fun p =>
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes (Set.mem_univ p))).symm
  obtain ⟨Fx, hFx⟩ := F.exists_isMap (ψ x hxU) (hring _ φ _ hφ (hψ x hxU)) (hpt x hxU)
  have hWx : ∀ τ, UnitAt x (algebraMap _ (X₀ TF.Y Z).functionField (Fx.co f τ).det) :=
    fun τ => ⟨_, EigFrame.isUnit_det_co Fx f τ, rfl⟩
  choose W hxW hW using fun τ => (hWx τ).exists_nhds
  refine ⟨⟨(e ⁻¹ᵁ U : Set (X₀ TF.Y Z)) ∩ ⋂ τ, (W τ : Set (X₀ TF.Y Z)),
    (e ⁻¹ᵁ U).isOpen.inter (isOpen_iInter_of_finite fun τ => (W τ).isOpen)⟩,
    ⟨hxU, Set.mem_iInter.2 hxW⟩, ?_⟩
  rintro y ⟨hyU, hyW⟩ φ' f' φK fK fK' hφ' hφK hfK hfK' τ
  rw [Set.mem_iInter] at hyW
  have hyU' : e y ∈ U := hyU
  obtain ⟨Fy, hFy⟩ := F.exists_isMap (ψ y hyU') (hring _ φ' _ hφ' (hψ y hyU')) (hpt y hyU')
  have hKp : ∀ p hp, spMap ((algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField).comp (ψ p hp)) ≫
      hU.fromSpec = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ e := by
    intro p hp
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField)
      (ψ p hp), Category.assoc, ← hψ, ← Category.assoc, ← hgen]
  have hK : (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU') =
      (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (ψ x hxU) :=
    hmono _ _ ((hKp y hyU').trans (hKp x hxU).symm)
  have hKpt := (hKp y hyU').symm
  obtain ⟨FK, hFK⟩ := F.exists_isMap
    ((algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU'))
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (hring _ φK _ hφK hKpt) (by rw [← he]; exact (reassoc_of% hKpt) (genι TF.Y))
  have hFyK : Fy.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFy hFK
  have hFxK : Fx.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFx (by rw [← hK]; exact hFK)
  have hy : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι := by
    rw [hgen y, Category.assoc]
  have hx : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι := by
    rw [hgen x, Category.assoc]
  have e1 := EigFrame.IsMap.co (τ := τ) hfK' hFyK hy
  have e2 := EigFrame.IsMap.co (τ := τ) hFxK hfK hx
  have dmap : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      (M.map g).det = g M.det := fun g _ M => (RingHom.map_det g M).symm
  rw [← EigFrame.co_mul fK' FK fK τ, Matrix.det_mul, e1, dmap]
  refine UnitAt.mul ⟨_, EigFrame.isUnit_det_co f' Fy τ, rfl⟩ ?_
  convert hW τ y (hyW τ) using 1
  erw [e2]
  exact dmap _ _

end GlobalTheory.FrameSpread
