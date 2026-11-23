import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AutomorphicArithmetic.DivisorFrames.ExistsStalkPointLift
import Development.AutomorphicArithmetic.DivisorFrames.TransitionLocalFrame
import Development.AutomorphicArithmetic.DivisorFrames.FrameModelsCompat
import Development.AutomorphicArithmetic.DivisorFrames.FlagStalkFrame
import Development.AutomorphicArithmetic.DivisorFrames.TangentModelsCompat
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem bc_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    (ρ : A →+* R) (χ : R →+* S) (u : Vecs Dw t A) : u.bc (χ.comp ρ) = (u.bc ρ).bc χ := by
  funext σ j
  rw [Vecs.bc, Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]

private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {l : Level H} {c : Coeff l} {R K k : Type} [CommRing R] [Field K]
    [Field k] {f : c.F →+* R} {x : Sp R ⟶ X} {G U : Vecs Dw t R} (hG : LocM.IsFrame t f x G)
    (hU : LocM.IsFrame t f x U) (ι : R →+* K) (hι : Function.Injective ι) (ev : R →+* k)
    (h : ∀ σ, Pull.Tri t (spMap ι ≫ x) (G.bc ι σ) (U.bc ι σ)) :
    (∀ σ, Pull.Tri t (spMap ev ≫ x) (G.bc ev σ) (U.bc ev σ)) ∧
      ∀ σ m, ∃ cf : Fin (Dw.mult σ) → R, IsCombAtG t x (G σ) cf (U σ m) ∧ ev (cf m) ≠ 0 := by
  have ex : ∀ σ m, ∃ cf : Fin (Dw.mult σ) → R, IsCombAtG t x (G σ) cf (U σ m) := fun σ m =>
    (hG.2 σ _ (hU.1 σ m).1 (hU.1 σ m).2).exists
  choose cf hcf using ex
  have tri : ∀ σ, Pull.Tri t (spMap ev ≫ x) (G.bc ev σ) (U.bc ev σ) := fun σ m => by
    obtain ⟨d, hd, hd'⟩ := h σ m
    have e : (fun i => ι (cf σ m i)) = d :=
      (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ι _ _ hG) σ).2 _ _ _
        (GlobalTheory.LatDRFree.comb_map t ι (hcf σ m)) hd'
    refine ⟨fun i => ev (cf σ m i), fun i hi => ?_, GlobalTheory.LatDRFree.comb_map t ev (hcf σ m)⟩
    have : cf σ m i = 0 := hι ((congrFun e i).trans ((hd i hi).trans (map_zero ι).symm))
    exact (congrArg ev this).trans (map_zero ev)
  refine ⟨tri, fun σ m => ⟨cf σ m, hcf σ m, ?_⟩⟩
  exact ((tri σ).diag (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hG) σ)
    (Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hU) σ) (GlobalTheory.LatDRFree.comb_map t ev (hcf σ m))).1

theorem UpperTheory.admissible_flag_valuation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : LocM.Mdl Y i₀) (O : Type) [CommRing O] (β : O →+* i₀.c.F) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* i₀.c.F) (Φ : FlagCpt T e) (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (b : 𝓞 F →+* O') (B : Vert.Model O') (μ : Match Φ.Y b B) (q : B.X ⟶ Z.X) (a : Fin Z.m) (τ : (Y Z.i).X ⟶ (Y i₀).X) (mu : SABMap (Y Z.i).t (Y i₀).t τ) (y : μ.U.toScheme ⟶ (Xo i₀.l).XF i₀.c) (ψ : Γ(Z.X, (Z.U a).1) →+* B.X.functionField) (f : i₀.c.F →+* B.X.functionField) (g : EigFrame T f ((μ.U.fromSpecStalkOfMem _ μ.mem ≫ μ.h) ≫ Φ.π ≫ genι T)) (x : Pad.Letter Dw) (c₀ : B.X.functionFieldˣ), μ.U ≤ q ⁻¹ᵁ (Z.U a).1 → LocM.IsTrans i₀ Z.i τ mu → y ≫ (Y i₀).j = μ.U.ι ≫ q ≫ Z.π ≫ τ → y ≫ T.jQ = μ.h ≫ Φ.π → spMap ψ ≫ Z.chart a = B.X.fromSpecStalk (genericPoint _) ≫ q → (∀ σ i, Transp T (Y i₀) (μ.U.fromSpecStalkOfMem _ μ.mem ≫ y) (g.v σ i) ((Z.fr a).bc ψ σ i ≫ mu.φ)) → (∀ y₀ : Φ.Y.X, (∀ σ, Pull.Tri (k := B.X.functionField) T.t ((μ.U.fromSpecStalkOfMem _ μ.mem ≫ μ.h) ≫ Φ.π ≫ genι T) (Vecs.bc (μ.φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField)) (GlobalTheory.LineNorm.fr Φ y₀).v σ) (g.v σ)) ∧ ∀ cf : Fin (Dw.mult x.1) → B.X.functionField, IsCombAtG T.t ((μ.U.fromSpecStalkOfMem _ μ.mem ≫ μ.h) ≫ Φ.π ≫ genι T) (Vecs.bc (μ.φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField)) (GlobalTheory.LineNorm.fr Φ y₀).v x.1) cf (g.v x.1 x.2) → cf x.2 * (c₀ : B.X.functionField) = μ.φ (GlobalTheory.LineNorm.dg Φ y₀ x.1 x.2 : Φ.Y.Fn)) → ∀ (k : Type) [Field k] (z : Sp k ⟶ μ.U.toScheme) (y₁ : Sp k ⟶ Φ.Y.X), z ≫ μ.h = y₁ → ∃ (s : B.X.functionField) (φ' : Γ(Z.X, (Z.U a).1) →+* k) (f' : i₀.c.F →+* k) (u : Vecs Dw T.t k) (cf : Fin (Dw.mult x.1) → k), UnitAt (below (z ≫ μ.U.ι)) s ∧ s * (c₀ : B.X.functionField) = μ.φ (GlobalTheory.LineNorm.dg Φ (below y₁) x.1 x.2 : Φ.Y.Fn) ∧ TrueGeo.valAt (z ≫ μ.U.ι) s = cf x.2 ∧ spMap φ' ≫ Z.chart a = (z ≫ μ.U.ι) ≫ q ∧ (z ≫ y) ≫ pullback.snd _ _ = spMap f' ∧ LocM.IsFrame T.t f' ((z ≫ y) ≫ T.j) u ∧ LocM.IsFrame T.t f' ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v) ∧ (∀ σ m, Transp T (Y i₀) (z ≫ y) (u σ m) ((Z.fr a).bc φ' σ m ≫ mu.φ)) ∧ (∀ σ, Pull.Tri T.t ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v σ) (u σ)) ∧ IsCombAtG T.t ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v x.1) cf (u x.1 x.2) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z O _ β T F _ _ e Φ O' _ _ _ b B μ q a τ mu y ψ f g x c₀ hU hT hy hyQ hψ hg hK k _ z y₁ hz
  obtain ⟨ζ, ρ, ζev, ζι, ζh, ιρ, evρ, -⟩ := UpperTheory.exists_stalk_point_lift F O' Φ.Y b B μ k z y₁ hz
  have hι : Function.Injective (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField) :=
    IsFractionRing.injective _ _
  have hval := TrueGeo.Base.valAt_stalk (z ≫ μ.U.ι)
  have hloc : ∀ r, (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom r ≠ 0 → IsUnit r := fun r hr =>
    isUnit_of_map_unit (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom r (isUnit_iff_ne_zero.2 hr)
  have hun : ∀ r, IsUnit r →
      UnitAt (below (z ≫ μ.U.ι)) (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField r) :=
    fun r hr => ⟨r, hr, rfl⟩
  generalize (algebraMap (B.X.presheaf.stalk (below (z ≫ μ.U.ι))) B.X.functionField) = ι at ζι ιρ hι hval hun
  generalize (Scheme.stalkClosedPointTo (z ≫ μ.U.ι)).hom = ev at ζev evρ hval hloc
  obtain ⟨φR, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 (ζ ≫ μ.U.ι ≫ q) fun r _ => hU (ζ r).2
  replace hφ : spMap φR ≫ Z.chart a = ζ ≫ μ.U.ι ≫ q := hφ
  obtain ⟨fR, hfR⟩ : ∃ fR : i₀.c.F →+* B.X.presheaf.stalk (below (z ≫ μ.U.ι)),
      (ζ ≫ y) ≫ pullback.snd _ _ = spMap fR :=
    ⟨(Spec.preimage ((ζ ≫ y) ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have F₂ := UpperTheory.transition_local_frame E H Dw Xo p W Y i₀ Z a τ mu hT _ φR (ζ ≫ y) fR
    (by rw [hφ, Category.assoc, hy]; simp only [Category.assoc]) hfR
  obtain ⟨uR, hu, tr⟩ := UpperTheory.frame_models_compat E H Dw _ _ _ _ _ _ _ T (Y i₀) _ (ζ ≫ y) fR _ F₂
  have hG := UpperTheory.flag_stalk_frame E H Dw _ _ _ O β T F e Φ (below y₁) _ ρ (ζ ≫ y) fR
    (by rw [Category.assoc, hyQ, ← Category.assoc, ζh, Category.assoc]) hfR
  have ιφ : ι.comp φR = ψ := by
    have : Mono (Z.chart a) := Pull.mono_fromSpec (Z.U a).2
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    rw [← cancel_mono (Z.chart a)]
    refine Eq.trans ?_ hψ.symm
    change spMap (ι.comp φR) ≫ _ = _
    rw [← ModelRelProbe.spMap_comp, Category.assoc, hφ, ← Category.assoc, ζι, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have trχ : ∀ (S : Type) [CommRing S] (χ : B.X.presheaf.stalk (below (z ≫ μ.U.ι)) →+* S) σ m,
      Transp T (Y i₀) ((spMap χ ≫ ζ) ≫ y) (uR.bc χ σ m) ((Z.fr a).bc (χ.comp φR) σ m ≫ mu.φ) := fun S _ χ σ m => by
    have := (UpperTheory.tangent_models_compat E H Dw _ _ _ _ _ _ _ T (Y i₀) _ _ _ _ (tr σ m)).2 S χ
    rw [bc_comp, Category.assoc]
    simpa only [Vecs.bc, Category.assoc] using this
  have ug : uR.bc ι = g.v := funext fun σ => funext fun m => by
    have := trχ _ ι σ m
    rw [ζι, ιφ] at this
    exact (UpperTheory.tangent_models_compat E H Dw _ _ _ _ _ _ _ T (Y i₀) _ _ _ _ (hg σ m)).1 _ this
  have px : (μ.U.fromSpecStalkOfMem _ μ.mem ≫ μ.h) ≫ Φ.π ≫ genι T = spMap ι ≫ (ζ ≫ y) ≫ T.j := by
    rw [← ζι, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    simp only [Category.assoc]
    rw [← Category.assoc y, hyQ, Category.assoc]
  have pk : spMap ev ≫ (ζ ≫ y) ≫ T.j = (z ≫ y) ≫ T.j := by
    simp only [← Category.assoc]
    rw [ζev]
  obtain ⟨K₁, K₂⟩ := hK (below y₁)
  rw [← ιρ, bc_comp, ← ug] at K₁ K₂
  erw [px] at K₁ K₂
  obtain ⟨tri, hc⟩ := core hG hu ι hι ev K₁
  obtain ⟨cf, c₁, c₂⟩ := hc x.1 x.2
  have hGk := GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hG
  have huk := GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ ev _ _ hu
  have ck : IsCombAtG T.t (spMap ev ≫ (ζ ≫ y) ≫ T.j) (Vecs.bc ev (Vecs.bc ρ (GlobalTheory.LineNorm.fr Φ (below y₁)).v) x.1)
      (fun i => ev (cf i)) (uR.bc ev x.1 x.2) := GlobalTheory.LatDRFree.comb_map T.t ev c₁
  rw [pk, ← bc_comp, evρ] at hGk tri ck
  rw [pk] at huk
  refine ⟨ι (cf x.2), ev.comp φR, ev.comp fR, uR.bc ev, fun i => ev (cf i), hun _ (hloc _ c₂),
    K₂ (fun i => ι (cf i)) (GlobalTheory.LatDRFree.comb_map T.t ι c₁), hval _, ?_, ?_, huk, hGk, fun σ m => ?_, tri, ck⟩
  · rw [← ModelRelProbe.spMap_comp, Category.assoc, hφ, ← Category.assoc, ζev, Category.assoc]
  · rw [← ModelRelProbe.spMap_comp, ← hfR]
    simp only [← Category.assoc]
    rw [ζev]
  · have := trχ _ ev σ m
    rwa [ζev] at this
