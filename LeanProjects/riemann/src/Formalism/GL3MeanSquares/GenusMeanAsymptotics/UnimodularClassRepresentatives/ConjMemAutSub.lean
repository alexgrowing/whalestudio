import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

theorem exists_reps {X : Type*} (r : X → X → Prop) (hr : Equivalence r) (A X₀ : Set X)
    (hfin : X₀.Finite) (hcov : ∀ x ∈ A, ∃ t ∈ X₀, r t x) :
    ∃ R : Finset X, (∀ t ∈ R, t ∈ X₀) ∧ ∀ x ∈ A, ∃! t, t ∈ R ∧ r t x := by
  classical
  let s : Setoid X := ⟨r, hr⟩
  let pick : Quotient s → X := fun c =>
    if H : ∃ t ∈ X₀, Quotient.mk s t = c then H.choose else Quotient.out c
  have hp1 : ∀ x ∈ X₀, pick (Quotient.mk s x) ∈ X₀ ∧
      Quotient.mk s (pick (Quotient.mk s x)) = Quotient.mk s x := by
    intro x hx
    have H : ∃ t ∈ X₀, Quotient.mk s t = Quotient.mk s x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos H]
    exact H.choose_spec
  refine ⟨hfin.toFinset.image (fun x => pick (Quotient.mk s x)), ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact (hp1 x (hfin.mem_toFinset.mp hx)).1
  · intro x hx
    obtain ⟨t₀, ht₀, h0⟩ := hcov x hx
    refine ⟨pick (Quotient.mk s t₀),
      ⟨Finset.mem_image.mpr ⟨t₀, hfin.mem_toFinset.mpr ht₀, rfl⟩, ?_⟩, ?_⟩
    · exact hr.trans (Quotient.exact (hp1 t₀ ht₀).2) h0
    · rintro t' ⟨ht', h1⟩
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp ht'
      have e1 := (hp1 x' (hfin.mem_toFinset.mp hx')).2
      have e2 : Quotient.mk s x' = Quotient.mk s t₀ := by
        rw [← e1]
        exact Quotient.sound (hr.trans h1 (hr.symm h0))
      rw [e2]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

@[reducible] def actV (S : VecSplit h h') : MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V) where
  smul g M := Formalism.HermitianLatticesTheory.gmap (extHom S g.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S 1) M = M
    rw [map_one]
    exact autSub_gmap_one M
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S (a.1 * b.1)) M = _
    rw [map_mul]
    exact autSub_gmap_mul _ _ _

@[reducible] def actV' (h' : V' →ₗ⋆[K] V' →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V') where
  smul g T := Formalism.HermitianLatticesTheory.gmap g.1 T
  one_smul T := autSub_gmap_one T
  mul_smul _ _ _ := autSub_gmap_mul _ _ _

theorem stab_actV (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    @MulAction.stabilizer _ _ _ (actV S) M = (autExt S M).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro e
    exact ⟨SplitBAux.extOf_mem_isom hs S g.2, e⟩
  · intro e
    exact e.2

theorem stab_actV' (T : Submodule (𝓞 K) V') :
    @MulAction.stabilizer _ _ _ (actV' h') T = (autSub h' T).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

theorem autSub_le_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) :
    autSub h A ≤ Formalism.HermitianLatticesTheory.isom h := fun _ hg => hg.1

theorem relIndex_stab (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    (@MulAction.stabilizer _ _ _ (actV S) M).relIndex
      (@MulAction.stabilizer _ _ _ (actV' h') (S.cut M)) = oM S M := by
  rw [stab_actV hs, stab_actV', Subgroup.relIndex_subgroupOf (autSub_le_isom h' _)]
  rfl

theorem extOf_res (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : SplitBAux.extOf S (SplitBAux.res S g hg hx) = g := by
  apply LinearEquiv.toLinearMap_injective
  apply SplitBAux.linearMap_ext S
  · change SplitBAux.extOf S _ S.x₀ = g S.x₀
    rw [SplitBAux.extOf_x₀, hx]
  · intro a
    change SplitBAux.extOf S _ (S.ι a) = g (S.ι a)
    rw [SplitBAux.extOf_ι, SplitBAux.res_spec]

theorem gmap_smul (g : V ≃ₗ[K] V) (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (I • A) = I • Formalism.HermitianLatticesTheory.gmap g A := Submodule.map_smul'' _ _ _

theorem conj_mem_autSub {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h A) : g * u * g⁻¹ ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, ← autSub_gmap_mul g⁻¹ g, inv_mul_cancel, autSub_gmap_one, hu.2]

theorem conj_mem_autSub' {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A)) : g⁻¹ * u * g ∈ autSub h A := by
  refine ⟨mul_mem (mul_mem (inv_mem hg) hu.1) hg, ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, hu.2, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_tube_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x y : V) :
    g y ∈ tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x ↔
      y ∈ tube (autSub h A) A 𝔭 J (g.symm x) := by
  constructor
  · rintro ⟨u, hu, hm⟩
    refine ⟨g⁻¹ * u * g, conj_mem_autSub' hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, map_sub, g.symm_apply_apply] at hm
    change y - g.symm (u (g (g.symm x))) ∈ _
    rwa [g.apply_symm_apply]
  · rintro ⟨u, hu, hm⟩
    refine ⟨g * u * g⁻¹, conj_mem_autSub hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
    change g.symm (g y - g (u (g.symm x))) ∈ _
    rwa [← map_sub, g.symm_apply_apply]

theorem image_tube {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    g '' tube (autSub h A) A 𝔭 J (g.symm x) =
      tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_tube_gmap hg A 𝔭 J x y).2 hy
  · intro hz
    refine ⟨g.symm z, (mem_tube_gmap hg A 𝔭 J x _).1 ?_, g.apply_symm_apply z⟩
    rwa [g.apply_symm_apply]

theorem cut_props (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      IsIntegralAt 𝔭 h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ∧
      fibLoc S L 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ≠ 0 := by
  rw [LocalizedFibreSets.gmap_locF] at hx ⊢
  rw [LocalizedFibreSets.cut_locF]
  refine ⟨LocalizedFibreSets.locF_idem _ _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF
    (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)), ?_⟩
  rw [UnimodularLocalization.fibLoc_locF]
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
  have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro e
    have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
    have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
    exact ht (e2 ▸ 𝔭.zero_mem)
  have hgood := BrB.good_cut (F := F) hK hF hs hd (BrB.scaleSplit S _ hc)
    (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi)
    (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
        rw [algebraMap_smul]; exact hx)
  have h1 := hgood.2 ⟨𝔭, h𝔭⟩
  rw [BrB.fibLoc_scale S L h𝔭.isPrime hg ht hc] at h1
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
