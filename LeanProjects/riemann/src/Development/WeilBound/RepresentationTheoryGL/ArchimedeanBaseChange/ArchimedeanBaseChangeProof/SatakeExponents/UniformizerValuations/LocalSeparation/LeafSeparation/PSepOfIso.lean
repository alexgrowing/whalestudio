import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.SepOfIso

noncomputable section

namespace PositivityTheory.Rg.BcB.F.RS.LeafModule

theorem core {G : Type} [Group G] {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (τ : Representation ℂ G W) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible)
    (hW : ∀ y : W, y ∈ ⨆ F : {F : U →ₗ[ℂ] W // ∀ g v, F (σ g v) = τ g (F v)}, LinearMap.range F.1)
    (x : W) (hx : x ≠ 0) : ∃ L : W →ₗ[ℂ] U, (∀ g y, L (τ g y) = σ g (L y)) ∧ L x ≠ 0 := by
  classical
  letI iW : Module (MonoidAlgebra ℂ G) W :=
    Module.compHom W (MonoidAlgebra.lift ℂ (Module.End ℂ W) G τ).toRingHom
  letI iU : Module (MonoidAlgebra ℂ G) U :=
    Module.compHom U (MonoidAlgebra.lift ℂ (Module.End ℂ U) G σ).toRingHom
  haveI tW : IsScalarTower ℂ (MonoidAlgebra ℂ G) W := ⟨fun c r w => by
    show (MonoidAlgebra.lift ℂ (Module.End ℂ W) G τ (c • r)) w = c • (MonoidAlgebra.lift ℂ (Module.End ℂ W) G τ r w)
    rw [map_smul]; rfl⟩
  haveI tU : IsScalarTower ℂ (MonoidAlgebra ℂ G) U := ⟨fun c r w => by
    show (MonoidAlgebra.lift ℂ (Module.End ℂ U) G σ (c • r)) w = c • (MonoidAlgebra.lift ℂ (Module.End ℂ U) G σ r w)
    rw [map_smul]; rfl⟩
  have gW : ∀ g (w : W), (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G) • w = τ g w := fun g w => by
    show (MonoidAlgebra.lift ℂ (Module.End ℂ W) G τ (MonoidAlgebra.single g 1)) w = _
    rw [MonoidAlgebra.lift_single, one_smul]
  have gU : ∀ g (u : U), (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G) • u = σ g u := fun g u => by
    show (MonoidAlgebra.lift ℂ (Module.End ℂ U) G σ (MonoidAlgebra.single g 1)) u = _
    rw [MonoidAlgebra.lift_single, one_smul]
  have lin : ∀ (F : U →ₗ[ℂ] W), (∀ g v, F (σ g v) = τ g (F v)) →
      ∀ (r : MonoidAlgebra ℂ G) (v : U), F (r • v) = r • F v := by
    intro F hF r v
    refine MonoidAlgebra.induction_linear r ?_ ?_ ?_
    · rw [zero_smul, zero_smul, map_zero]
    · intro a b ha hb
      rw [add_smul, map_add, ha, hb, add_smul]
    · intro g c
      show F ((MonoidAlgebra.lift ℂ (Module.End ℂ U) G σ (MonoidAlgebra.single g c)) v) =
        (MonoidAlgebra.lift ℂ (Module.End ℂ W) G τ (MonoidAlgebra.single g c)) (F v)
      rw [MonoidAlgebra.lift_single, MonoidAlgebra.lift_single, LinearMap.smul_apply, LinearMap.smul_apply,
        map_smul, hF]
  let FR : {F : U →ₗ[ℂ] W // ∀ g v, F (σ g v) = τ g (F v)} → (U →ₗ[MonoidAlgebra ℂ G] W) := fun F =>
    { toFun := F.1
      map_add' := F.1.map_add
      map_smul' := lin F.1 F.2 }
  obtain ⟨hnt, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ
  haveI sU : IsSimpleModule (MonoidAlgebra ℂ G) U := by
    haveI : Nontrivial (Submodule (MonoidAlgebra ℂ G) U) := (Submodule.nontrivial_iff _).2 hnt
    exact
      { eq_bot_or_eq_top := fun N => by
          have h := hirr (N.restrictScalars ℂ) (fun g v hv => by
            have : (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ G) • v ∈ N := N.smul_mem _ hv
            rwa [gU] at this)
          rcases h with h | h
          · exact Or.inl (by simpa using h)
          · exact Or.inr (by simpa using h) }
  have htop : (⨆ F, LinearMap.range (FR F)) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    refine Submodule.iSup_induction
      (fun F : {F : U →ₗ[ℂ] W // ∀ g v, F (σ g v) = τ g (F v)} => LinearMap.range F.1)
      (motive := fun y => y ∈ ⨆ F, LinearMap.range (FR F)) (hW y) ?_ ?_ ?_
    · intro F z hz
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hz
      exact Submodule.mem_iSup_of_mem F ⟨v, rfl⟩
    · exact zero_mem _
    · intro a b ha hb
      exact add_mem ha hb
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ G) W :=
    isSemisimpleModule_of_isSemisimpleModule_submodule' (fun F => IsSemisimpleModule.range (FR F)) htop
  obtain ⟨D, hD⟩ := exists_isCompl (Submodule.span (MonoidAlgebra ℂ G) {x})
  have hDt : D ≠ ⊤ := by
    intro h
    rw [h] at hD
    have h1 := hD.inf_eq_bot
    rw [inf_top_eq, Submodule.span_singleton_eq_bot] at h1
    exact hx h1
  obtain ⟨C, hC, hDC⟩ := (IsCoatomic.eq_top_or_exists_le_coatom D).resolve_left hDt
  have hxC : x ∉ C := by
    intro hxC
    apply hC.1
    rw [eq_top_iff, ← hD.sup_eq_top]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hxC) hDC
  obtain ⟨F, hF⟩ : ∃ F, ¬ LinearMap.range (FR F) ≤ C := by
    by_contra h
    push_neg at h
    apply hC.1
    rw [eq_top_iff, ← htop]
    exact iSup_le h
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) (W ⧸ C) := isSimpleModule_iff_isCoatom.2 hC
  have hφ : C.mkQ ∘ₗ FR F ≠ 0 := by
    intro h0
    apply hF
    intro z hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hz
    have h1 := LinearMap.congr_fun h0 v
    simpa [Submodule.Quotient.mk_eq_zero] using h1
  let e := LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hφ)
  let L0 : W →ₗ[MonoidAlgebra ℂ G] U := e.symm.toLinearMap ∘ₗ C.mkQ
  refine ⟨L0.restrictScalars ℂ, fun g y => ?_, ?_⟩
  · show L0 (τ g y) = σ g (L0 y)
    rw [← gW, ← gU, map_smul]
  · intro h0
    apply hxC
    have h1 : e.symm (C.mkQ x) = 0 := h0
    have h2 : C.mkQ x = 0 := by simpa using h1
    simpa [Submodule.Quotient.mk_eq_zero] using h2

end PositivityTheory.Rg.BcB.F.RS.LeafModule

namespace PositivityTheory.Rg.BcB.F.RS.Leaf

theorem sepOfIso_of : SepOfIso := by
  intro G V _ _ _ _ ρ S σ hS hsum
  classical
  let ρS : Representation ℂ G S :=
    { toFun := fun g => (ρ g).restrict (hS g)
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (by simp [Module.End.mul_apply]) }
  have hW : ∀ y : S, y ∈ ⨆ F : {F : σ.V →ₗ[ℂ] S // ∀ g v, F (σ.ρ g v) = ρS g (F v)}, LinearMap.range F.1 := by
    rintro ⟨y, hy⟩
    suffices key : ∃ hz : y ∈ S,
        (⟨y, hz⟩ : S) ∈ ⨆ F : {F : σ.V →ₗ[ℂ] S // ∀ g v, F (σ.ρ g v) = ρS g (F v)}, LinearMap.range F.1 by
      obtain ⟨_, h⟩ := key
      exact h
    refine Submodule.iSup_induction
      (fun f : {f : σ.V →ₗ[ℂ] V // (∀ v, f v ∈ S) ∧ ∀ g v, f (σ.ρ g v) = ρ g (f v)} => LinearMap.range f.1)
      (motive := fun z => ∃ hz : z ∈ S,
        (⟨z, hz⟩ : S) ∈ ⨆ F : {F : σ.V →ₗ[ℂ] S // ∀ g v, F (σ.ρ g v) = ρS g (F v)}, LinearMap.range F.1)
      (hsum hy) ?_ ?_ ?_
    · intro f z hz
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hz
      exact ⟨f.2.1 v, Submodule.mem_iSup_of_mem
        ⟨f.1.codRestrict S f.2.1, fun g v => Subtype.ext (f.2.2 g v)⟩ ⟨v, rfl⟩⟩
    · exact ⟨zero_mem S, zero_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨add_mem ha hb, add_mem ha' hb'⟩
  refine ⟨hS, {L : V →ₗ[ℂ] σ.V // ∀ g, ∀ x ∈ S, L (ρ g x) = σ.ρ g (L x)}, fun L => L.1,
    fun L g x hx _ => L.2 g x hx, fun x hx _ h0 => ?_⟩
  by_contra hx0
  obtain ⟨L, hL, hLx⟩ := LeafModule.core ρS σ.ρ σ.irred hW ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h))
  obtain ⟨M, hM⟩ := LinearMap.exists_extend L
  have e1 : ∀ y (hy : y ∈ S), M y = L ⟨y, hy⟩ := fun y hy => LinearMap.congr_fun hM ⟨y, hy⟩
  apply hLx
  rw [← e1 x hx]
  exact h0 ⟨M, fun g y hy => by rw [e1 _ (hS g y hy), e1 y hy]; exact hL g ⟨y, hy⟩⟩

end PositivityTheory.Rg.BcB.F.RS.Leaf
