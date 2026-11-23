import Development.EtaleCohomology.EtaleSheaves.SteinPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

def ClosedAt {X T : Scheme.{0}} (c : X ⟶ T) (W : T.Opens) : Prop :=
  ∀ b : Γ(X, c ⁻¹ᵁ W), (c.app W).hom.IsIntegralElem b → ∃ a, c.app W a = b

theorem app_res_apply {X T : Scheme.{0}} (c : X ⟶ T) {W V : T.Opens} (h : W ⟶ V) (a : Γ(T, V)) :
    c.app W (T.presheaf.map h.op a) =
      X.presheaf.map (homOfLE (c.preimage_mono h.le)).op (c.app V a) := by
  rw [← CommRingCat.comp_apply, c.naturality, CommRingCat.comp_apply]; rfl

theorem integral_res {X T : Scheme.{0}} (c : X ⟶ T) {W V : T.Opens} (h : W ≤ V) (b : Γ(X, c ⁻¹ᵁ V))
    (hb : (c.app V).hom.IsIntegralElem b) :
    (c.app W).hom.IsIntegralElem (X.presheaf.map (homOfLE (c.preimage_mono h)).op b) := by
  obtain ⟨p, hm, hp⟩ := hb
  refine ⟨p.map (T.presheaf.map (homOfLE h).op).hom, hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have e : (c.app W).hom.comp (T.presheaf.map (homOfLE h).op).hom =
      (X.presheaf.map (homOfLE (c.preimage_mono h)).op).hom.comp (c.app V).hom := by
    ext a; exact app_res_apply c (homOfLE h) a
  rw [e, ← Polynomial.hom_eval₂, hp, map_zero]

theorem closedAt_of_local {X T : Scheme.{0}} (c : X ⟶ T) (hinj : ∀ W, Function.Injective (c.app W))
    (V : T.Opens) (hloc : ∀ x ∈ V, ∃ W, W ≤ V ∧ x ∈ W ∧ ClosedAt c W) : ClosedAt c V := by
  intro b hb
  choose W hWV hxW hW using fun x : V => hloc x.1 x.2
  choose a ha using fun x : V => hW x _ (integral_res c (hWV x) b hb)
  have hcomp : TopCat.Presheaf.IsCompatible T.sheaf.obj W a := by
    intro i j
    apply hinj
    have h1 := app_res_apply c (TopologicalSpace.Opens.infLELeft (W i) (W j)) (a i)
    have h2 := app_res_apply c (TopologicalSpace.Opens.infLERight (W i) (W j)) (a j)
    erw [h1, h2, ha, ha]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨s, hs, -⟩ := T.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩) a hcomp
  refine ⟨s, X.sheaf.eq_of_locally_eq' (fun i => c ⁻¹ᵁ W i) (c ⁻¹ᵁ V)
    (fun i => homOfLE (c.preimage_mono (hWV i))) ?_ _ _ fun i => ?_⟩
  · intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c z, hz⟩, hxW ⟨c z, hz⟩⟩
  · have h1 := app_res_apply c (homOfLE (hWV i)) s
    erw [hs i, ha i] at h1
    exact h1.symm

def NormClosed : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ V : g.normalization.Opens, IsAffineOpen V → ∀ b : Γ(Z, g.toNormalization ⁻¹ᵁ V),
    (g.toNormalization.app V).hom.IsIntegralElem b → ∃ a, g.toNormalization.app V a = b

def NormLocal : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ U : S.Opens, IsAffineOpen U → ∀ t : Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U),
    ClosedAt g.toNormalization (g.normalization.basicOpen t)

theorem NormClosed_of (hL : NormLocal) : NormClosed := by
  intro Z S g _ _ hZ V hV
  have : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
  refine closedAt_of_local _ (fun W => g.toNormalization.app_injective W) V fun x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.fromNormalization x)) isOpen_univ
  have hU' : IsAffineOpen (g.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  obtain ⟨f, f', e, hxf⟩ := exists_basicOpen_le_affine_inter hU' hV x ⟨hxU, hx⟩
  exact ⟨_, e ▸ g.normalization.basicOpen_le f', hxf, hL g hZ U hU f⟩

theorem RelNorm_of_closed (hN : NormClosed) : LateralTheory.E.SteinPf.RelNorm := by
  intro Z S g _ _ hZ
  haveI : IsIntegral Z := hZ.1
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance, inferInstance, inferInstance,
    g.toNormalization_fromNormalization, fun V hV hne => ⟨?_, ?_, hN g hZ.1 V hV⟩⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := g.toNormalization.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨z, hz⟩
  · haveI : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
    exact g.toNormalization.app_injective V

end LateralTheory.E.RelNormPf
