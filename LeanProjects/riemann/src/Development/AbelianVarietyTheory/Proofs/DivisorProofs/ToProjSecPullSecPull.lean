import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackCompStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.Fib

theorem trait (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x₀ : M.S)
    (hx : M.π x₀ = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ :=
  GlobalTheory.T.exists_completeTrait_over_closedPoint_modification R hR M x₀ hx

theorem compositum (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X)
    (h : a (closedPoint K₁) = b (closedPoint K₂)) :
    ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b :=
  GlobalTheory.T.exists_common_field_of_fieldPoints_same_point X K₁ K₂ a b h

theorem baseChangeIso (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W']
    (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G ξ' β)
    (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W')
    (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y) (he' : IsMonHom e'.hom)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω')
    (i₂ : ResidueField W' →+* Ω') (hc : spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ')
    (hκ : io.comp κ = i₂.comp κ') :
    ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left),
      IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧
      e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') :=
  GlobalTheory.T.groupFibre_baseChange_common_field_iso S G W' G' ξ' β hβ k Y κ' e' he' Ω x κ Ω' io i₂ hc hκ

theorem toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ :=
  GlobalTheory.T.morphismToProjSpace_sectionPullback_comp R N X Y Z L s h g f hs₁ hs₂

theorem toProj_congr {R : Type} [CommRing R] {N : ℕ} {X Z : Scheme.{0}} {L : LB X} (s : Fin (N + 1) → L.Sec)
    {a b : Z ⟶ X} (hab : a = b) {f g : Z ⟶ Sp R} (hfg : f = g)
    (h₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) a) = ⊤) (h₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) b) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) a) h₁ = GlobalTheory.ProjSpace.toProj g (fun i => GlobalTheory.secPull (s i) b) h₂ := by
  subst hab; subst hfg; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem fib : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    (∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s) →
    ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ M.S) (κ : ResidueField R →+* Ω), x ≫ M.π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ (GlobalTheory.Mum.SecEmb.embH s).toScheme), IsMonHom e.hom ∧
      l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) ∧
      l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT hH Ω _ x κ hx
  have hcl : ∀ q : Sp Ω, M.π (x q) = closedPoint R := fun q => by
    rw [← Scheme.Hom.comp_apply, hx, Subsingleton.elim q (closedPoint Ω)]
    exact IsLocalRing.comap_closedPoint (κ.comp (residue R))
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξ0⟩ := trait R hR M _ (hcl (closedPoint Ω))
  obtain ⟨W', _, _, _, io', G', _, β, κ', e', hW', hio', hiof, hβ, hκ', he', hptw⟩ := hT W hW φ ξ hφi hφl hξ
  have hio0 : (spMap io') (closedPoint W') = closedPoint W := by
    letI := io'.toAlgebra
    have : Algebra.IsIntegral W W' := ⟨fun a => hiof.to_isIntegral a⟩
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal W')))
  have hres0 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  have hpt0 : (spMap (residue W') ≫ spMap io' ≫ ξ) (closedPoint (ResidueField W')) = x (closedPoint Ω) := by
    show ξ (spMap io' (spMap (residue W') (closedPoint _))) = _
    rw [hres0, hio0, hξ0]
  obtain ⟨Ω', _, io, i₂, hc⟩ := compositum M.S Ω (ResidueField W') x _ hpt0.symm
  have hκ : io.comp κ = i₂.comp κ' := by
    have e1 : spMap ((io.comp κ).comp (residue R)) = spMap ((i₂.comp κ').comp (residue R)) := by
      rw [RingHom.comp_assoc, spMap_comp', ← hx, RingHom.comp_assoc, hκ', spMap_comp', spMap_comp', spMap_comp',
        ← hξ, ← Category.assoc, hc]
      simp only [Category.assoc]
    have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    ext a
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact congrArg (fun f : R →+* Ω' => f r) e2
  obtain ⟨e, τ, he, hτ, heτ⟩ := baseChangeIso M.S G W' G' (spMap io' ≫ ξ) β hβ (ResidueField R) Y κ' e' he' Ω x κ
    Ω' io i₂ hc hκ
  have hrange : Set.range (pullback.fst G.hom (spMap io ≫ x)) ⊆ Set.range (GlobalTheory.Mum.SecEmb.embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hH
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hcl _
  let l := IsOpenImmersion.lift (GlobalTheory.Mum.SecEmb.embH s).ι (pullback.fst G.hom (spMap io ≫ x)) hrange
  have hl : l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Ω', inferInstance, io, e, l, he, hl, ?_⟩
  have : IsReduced ((Over.pullback (spMap (io.comp κ))).obj Y).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd Y.hom (spMap (io.comp κ)))
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsReduced ((Over.pullback (spMap io ≫ x)).obj G).left := isReduced_of_isOpenImmersion e.hom.left
  have hsep : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.hom_ext_of_geometricPoints_dense (PSpace.str R N) _ _ ?_ Set.univ dense_univ ?_
  · have a1 : GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s ≫ PSpace.str R N = (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π :=
      GlobalTheory.ProjSpace.toProj_str _ _ _
    have eo : e.hom.left ≫ pullback.snd Y.hom (spMap (io.comp κ)) = pullback.snd G.hom (spMap io ≫ x) := Over.w e.hom
    have a2 : (l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap io ≫ x ≫ M.π := by
      rw [Category.assoc, a1, reassoc_of% hl, pullback.condition_assoc, Category.assoc]
    have a3 : (e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap (io.comp κ) ≫ spMap (residue R) := by
      rw [Category.assoc, Category.assoc, hj, pullback.condition_assoc, reassoc_of% eo]
    rw [a2, a3, hx, spMap_comp', spMap_comp']
    simp only [Category.assoc]
  · intro K _ _ q _
    obtain ⟨⟨hs, hproj⟩, -⟩ := hptw K (q ≫ τ) (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')))
      (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) (by simp) (by simp)
    have e3 : q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') ≫ j =
        (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) ≫ j := by simp only [Category.assoc]
    rw [reassoc_of% heτ, e3, ← hproj]
    have hqb : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β := by
      rw [Category.assoc, hl, ← hτ]; simp only [Category.assoc]
    have hbase : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π =
        (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ G'.hom ≫ spMap (io'.comp φ) := by
      have hqb' : q ≫ l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β := by
        simp only [Category.assoc] at hqb; exact hqb
      rw [Category.assoc q l, reassoc_of% hqb', hβ.1.w_assoc, Category.assoc (spMap io'), hξ, spMap_comp']
      simp only [Category.assoc]
    have hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι)) = ⊤ := by
      rw [hqb]; exact hs
    rw [← Category.assoc]
    show (q ≫ l) ≫ GlobalTheory.ProjSpace.toProj ((GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π)
      (fun i => GlobalTheory.secPull (s i) (GlobalTheory.Mum.SecEmb.embH s).ι) (GlobalTheory.Mum.SecEmb.iSup_nonzeroLocus_embH s) = _
    rw [← GlobalTheory.ProjSpace.toProj_secPull]
    exact (toProj_secPull_secPull R N _ _ _ B s _ (q ≫ l) _ _ hs₂).trans (toProj_congr s hqb hbase _ _)

end GlobalTheory.Mum.SecEmb.Fib
