import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem mem_eigSp_iff_forall {R V O : Type} [CommRing R] [AddCommGroup V] [Module R V] [CommRing O]
    (ρ : O →+* Module.End R V) (τ : O →+* R) (u : V) :
    u ∈ eigSp ρ τ ↔ ∀ a, ρ a u = τ a • u := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem spMap_dualMap_id {A : Type} [CommRing A] : spMap (dualMap (RingHom.id A)) = 𝟙 _ := by
  have h : dualMap (RingHom.id A) = RingHom.id _ := RingHom.ext fun a => by
    show TrivSqZeroExt.inl (TrivSqZeroExt.fst a) + TrivSqZeroExt.inr (TrivSqZeroExt.snd a) = a
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem frame_of_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  classical
  intro E _ _ _ H D l Xo c U O _ β Y Z p κ σ r e hκ hs
  obtain ⟨F, _, _, ⟨MA⟩⟩ := lieModel_exists Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1)
  obtain ⟨ρA, hρA, -⟩ := lieModel_exists_unique_act Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) F MA (𝓞 E)
    Y.t.act.act Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  have hg : spMap (genMap (Z.ξ₀ ≫ Y.j) p) ≫ Y.X.fromSpecStalk p.1 = Z.ξ₀ ≫ Y.j := LieTangent.spec_genMap _ p
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) (Z.ξ₀ ≫ Y.j) (genMap (Z.ξ₀ ≫ Y.j) p) hg MA Z.M
  have h0 : IsEigFrame Y.t.act (Y.X.fromSpecStalk p.1) (((RingHom.id _).comp κ).comp (tauIn c σ)) e :=
    hs _ (RingHom.id _) _ (by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]; exact Category.id_comp _) e (fun i => by rw [spMap_dualMap_id, Category.id_comp])
  choose f hf using fun i => MA.onto (e i) (h0.1 i).1
  have hfe : (fun k => MA.pt (f k)) = e := funext hf
  have hfr := ((GlobalTheory.T.lie_model_eigenvectors_action Y.X (Y.X.presheaf.stalk p.1) Y.t.G (Y.X.fromSpecStalk p.1) F MA).2 (𝓞 E) Y.t.act ρA
    (((RingHom.id _).comp κ).comp (tauIn c σ)) hρA).2 r f
  rw [hfe] at hfr
  obtain ⟨-, hfs⟩ := hfr.1 h0
  have hb : ∀ i, (Z.M.pt (j (f i))).left = spMap (dualMap (genMap (Z.ξ₀ ≫ Y.j) p)) ≫ (e i).left :=
    fun i => by rw [hj, hf]
  have hext : ∀ i, Z.M.Extends p (j (f i)) (e i) := fun i => ⟨(h0.1 i).1, hb i⟩
  have h1 : IsEigFrame Y.t.act (Z.ξ₀ ≫ Y.j) (((genMap (Z.ξ₀ ≫ Y.j) p).comp κ).comp (tauIn c σ))
      (fun i => Z.M.pt (j (f i))) := hs _ _ _ hg _ hb
  rw [hκ] at h1
  obtain ⟨hbi, hbs⟩ := (((GlobalTheory.T.lie_model_eigenvectors_action Y.X Z.Ω Y.t.G (Z.ξ₀ ≫ Y.j) Z.V Z.M).2 (𝓞 E) Y.t.act Z.ρ
    (Z.inc.comp (tauIn c σ)) Z.act).2 r fun i => j (f i)).1 h1
  refine ⟨fun i => j (f i), hext, hbi, le_antisymm ?_ (Submodule.span_le.2 ?_)⟩
  · intro e' he'
    obtain ⟨hl, hE⟩ : e' ∈ Z.M.lat p ∧ e' ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)) := he'
    obtain ⟨v, hv⟩ := (Z.M.mem_lat_iff p e').1 hl
    obtain ⟨w, rfl⟩ := MA.onto v hv.1
    have hw : e' = j w := LieVB.pt_left_inj Z.M (hv.2.trans (hj w).symm)
    letI : Algebra c.F (Y.X.presheaf.stalk p.1) := κ.toAlgebra
    letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
    obtain ⟨ft, ⟨hft1, hft2⟩, -⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c (Y.X.presheaf.stalk p.1) F ρA w
    have hint : ∀ a y, Z.ρ a (j y) = j (ρA a y) := fun a y => LieVB.pt_left_inj Z.M (by
      have h2 := congrArg (fun q => q.left) (Z.act a (j y))
      have h3 := congrArg (fun q => q.left) (hρA a y)
      simp only [Over.comp_left] at h2 h3
      rw [h2, hj, hj, h3, Category.assoc])
    obtain ⟨_, -, huq⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c Z.Ω Z.V Z.ρ e'
    have e1 := huq (fun τ => j (ft τ)) ⟨fun τ a => by
      show Z.ρ a (j (ft τ)) = _
      rw [hint, hft1, j.map_smulₛₗ]
      show (genMap (Z.ξ₀ ≫ Y.j) p) (κ _) • _ = Z.inc _ • _
      rw [← hκ]; rfl, by rw [← map_sum, hft2, hw]⟩
    have e2 := huq (fun τ => if τ = σ then e' else 0) ⟨fun τ a => by
      by_cases h : τ = σ
      · subst h
        simp only [if_true]
        exact (mem_eigSp_iff_forall _ _ _).1 hE a
      · simp [h], by simp⟩
    have e3 : j (ft σ) = e' := by simpa using congrFun (e1.trans e2.symm) σ
    have hmem : ft σ ∈ eigSp ρA (((RingHom.id _).comp κ).comp (tauIn c σ)) :=
      (mem_eigSp_iff_forall _ _ _).2 fun a => hft1 σ a
    rw [← hfs] at hmem
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    rw [← e3, ← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [j.map_smulₛₗ]
    exact Submodule.smul_mem _ (⟨genMap (Z.ξ₀ ≫ Y.j) p (a i), _, rfl⟩ : regAt (Z.ξ₀ ≫ Y.j) p)
      (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨(Z.M.mem_lat_iff p _).2 ⟨_, hext i⟩, hbs ▸ Submodule.subset_span ⟨i, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LocFn
