import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd

set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

instance countable_prodSub {X Y : Type} [AddGroup X] [AddGroup Y] (Γ : AddSubgroup X) (Δ : AddSubgroup Y) [Countable Γ]
    [Countable Δ] : Countable ((Γ.prod Δ : AddSubgroup (X × Y))) := by
  refine Function.Injective.countable (f := fun g : (Γ.prod Δ : AddSubgroup (X × Y)) =>
    ((⟨(g : X × Y).1, (AddSubgroup.mem_prod.1 g.2).1⟩ : Γ), (⟨(g : X × Y).2, (AddSubgroup.mem_prod.1 g.2).2⟩ : Δ))) ?_
  intro g g' h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

instance mcv_sub {X : Type} [AddGroup X] [MeasurableSpace X] [MeasurableAdd X] (Γ : AddSubgroup X) :
    MeasurableConstVAdd Γ X := ⟨fun g => measurable_const_add (g : X)⟩

instance mv_sub {X : Type} [AddGroup X] [MeasurableSpace X] [MeasurableAdd X] (Γ : AddSubgroup X) :
    MeasurableVAdd Γ X where
  measurable_const_vadd g := measurable_const_add (g : X)
  measurable_vadd_const x := measurable_subtype_coe.add_const x

instance mAdd_prod {X Y : Type} [Add X] [Add Y] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableAdd X] [MeasurableAdd Y] :
    MeasurableAdd (X × Y) where
  measurable_const_add c := ((measurable_const_add c.1).comp measurable_fst).prodMk ((measurable_const_add c.2).comp measurable_snd)
  measurable_add_const c := ((measurable_add_const c.1).comp measurable_fst).prodMk ((measurable_add_const c.2).comp measurable_snd)

instance countable_botSub {X : Type} [AddGroup X] : Countable ((⊥ : AddSubgroup X)) := by
  infer_instance

section Chain

variable {U N Z N' : Type} [AddCommGroup U] [AddCommGroup N] [AddCommGroup Z] [AddCommGroup N']
  [MeasurableSpace U] [MeasurableSpace N] [MeasurableSpace Z] [MeasurableSpace N']
  [MeasurableAdd₂ U] [MeasurableAdd₂ N] [MeasurableAdd₂ Z] [MeasurableAdd₂ N'] [MeasurableNeg Z] [MeasurableSub₂ Z]

def phi (P : N ≃ᵐ (Z × N')) : (U × N) ≃ᵐ (N' × (U × Z)) :=
  ((MeasurableEquiv.refl U).prodCongr P).trans ((MeasurableEquiv.prodAssoc.symm).trans MeasurableEquiv.prodComm)

theorem phi_apply (P : N ≃ᵐ (Z × N')) (p : U × N) : phi P p = ((P p.2).2, (p.1, (P p.2).1)) := rfl

theorem phi_symm_apply (P : N ≃ᵐ (Z × N')) (w : N' × (U × Z)) : (phi P).symm w = (w.2.1, P.symm (w.2.2, w.1)) := rfl

def sh (τ : U × N' → Z) (hτ : Measurable τ) : (N' × (U × Z)) ≃ᵐ (N' × (U × Z)) where
  toFun w := (w.1, (w.2.1, w.2.2 + τ (w.2.1, w.1)))
  invFun w := (w.1, (w.2.1, w.2.2 - τ (w.2.1, w.1)))
  left_inv w := by simp
  right_inv w := by simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.add (hτ.comp (measurable_snd.fst.prodMk measurable_fst))))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.sub (hτ.comp (measurable_snd.fst.prodMk measurable_fst))))

theorem sh_apply {τ : U × N' → Z} (hτ : Measurable τ) (w : N' × (U × Z)) :
    sh τ hτ w = (w.1, (w.2.1, w.2.2 + τ (w.2.1, w.1))) := rfl

theorem sh_symm_apply {τ : U × N' → Z} (hτ : Measurable τ) (w : N' × (U × Z)) :
    (sh τ hτ).symm w = (w.1, (w.2.1, w.2.2 - τ (w.2.1, w.1))) := rfl

theorem sh_mp {τ : U × N' → Z} (hτ : Measurable τ) (l : Measure N') (νu : Measure U) (μZ : Measure Z) [SFinite l]
    [SFinite νu] [SFinite μZ] [μZ.IsAddRightInvariant] :
    MeasurePreserving (sh τ hτ) (l.prod (νu.prod μZ)) (l.prod (νu.prod μZ)) := by
  have h1 := (measurePreserving_prodAssoc l νu μZ).symm
  have h2 := shear_mp' (l.prod νu) μZ (fun p : N' × U => τ (p.2, p.1)) (hτ.comp (measurable_snd.prodMk measurable_fst))
  have h3 := measurePreserving_prodAssoc l νu μZ
  have e : (sh τ hτ : N' × (U × Z) → N' × (U × Z)) =
      (MeasurableEquiv.prodAssoc) ∘ (fun p : (N' × U) × Z => (p.1, p.2 + τ (p.1.2, p.1.1))) ∘
        (MeasurableEquiv.prodAssoc (α := N') (β := U) (γ := Z)).symm := by
    funext w; rfl
  rw [e]
  exact h3.comp (h2.comp h1)

end Chain

section Main

variable {U N Z N' : Type} [AddCommGroup U] [AddCommGroup N] [AddCommGroup Z] [AddCommGroup N']
  [MeasurableSpace U] [MeasurableSpace N] [MeasurableSpace Z] [MeasurableSpace N']
  [MeasurableAdd₂ U] [MeasurableAdd₂ N] [MeasurableAdd₂ Z] [MeasurableAdd₂ N'] [MeasurableNeg Z] [MeasurableSub₂ Z]
  {νu : Measure U} [SFinite νu] {lam : Measure N} [SFinite lam] [lam.IsAddLeftInvariant]
  {μZ : Measure Z} [SFinite μZ] [μZ.IsAddLeftInvariant] [μZ.IsAddRightInvariant] {lam' : Measure N'} [SFinite lam']
  {ΓN : AddSubgroup N} {ΓZ : AddSubgroup Z} {ΓN' : AddSubgroup N'} [Countable ΓN] [Countable ΓZ] [Countable ΓN']
  {P : N ≃ᵐ (Z × N')} {c : ℝ≥0∞} {𝓖 : Set N} {𝓩 : Set Z} {𝓖' : Set N'} {τ : U × N' → Z}

theorem phi_add (hPadd : ∀ a b, P (a + b) = P a + P b) (p q : U × N) :
    phi (U := U) P (p + q) = phi P p + phi P q := by
  show ((P (p.2 + q.2)).2, (p.1 + q.1, (P (p.2 + q.2)).1)) = _
  rw [hPadd]
  rfl

theorem phi_map (hPc : lam.map P = c • (μZ.prod lam')) :
    (νu.prod lam).map (phi P) = c • (lam'.prod (νu.prod μZ)) := by
  have hg : MeasurePreserving P lam (c • (μZ.prod lam')) := ⟨P.measurable, hPc⟩
  have h1 := (MeasurePreserving.id νu).prod hg
  rw [Measure.prod_smul_right] at h1
  have h2 := (measurePreserving_prodAssoc νu μZ lam').symm
  have h3 := Measure.measurePreserving_swap (μ := νu.prod μZ) (ν := lam')
  have h23 := h3.comp h2
  calc (νu.prod lam).map (phi P)
      = ((νu.prod lam).map (Prod.map id P)).map (Prod.swap ∘ (MeasurableEquiv.prodAssoc (α := U) (β := Z) (γ := N')).symm) := by
        rw [Measure.map_map h23.measurable h1.measurable]; rfl
    _ = (c • (νu.prod (μZ.prod lam'))).map (Prod.swap ∘ (MeasurableEquiv.prodAssoc (α := U) (β := Z) (γ := N')).symm) := by
        rw [h1.map_eq]
    _ = c • (lam'.prod (νu.prod μZ)) := by rw [Measure.map_smul, h23.map_eq]

theorem chainC (hPc : lam.map P = c • (μZ.prod lam')) (hPadd : ∀ a b, P (a + b) = P a + P b)
    (hΓ : ∀ β, β ∈ ΓN ↔ (P β).1 ∈ ΓZ ∧ (P β).2 ∈ ΓN')
    (h𝓖 : IsAddFundamentalDomain ΓN 𝓖 lam) (h𝓩 : IsAddFundamentalDomain ΓZ 𝓩 μZ)
    (h𝓖' : IsAddFundamentalDomain ΓN' 𝓖' lam') (hτ : Measurable τ) (f : U × N → ℂ) (H : N' × (U × Z) → ℂ)
    (hf : ∀ γ ∈ ΓN, ∀ u β, f (u, γ + β) = f (u, β))
    (hH : ∀ g ∈ ΓZ, ∀ w : N' × (U × Z), H (w.1, (w.2.1, g + w.2.2)) = H w)
    (hfH : ∀ u β, f (u, β) = H ((P β).2, (u, (P β).1 + τ (u, (P β).2)))) :
    ∫ p, f p ∂(νu.prod (lam.restrict 𝓖)) =
      c.toReal • ∫ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by
  set Φ := phi (U := U) P
  set S := sh τ hτ
  set m := lam'.prod (νu.prod μZ)
  set m' := (lam'.restrict 𝓖').prod (νu.prod μZ)
  set S3 : Set (N' × (U × Z)) := 𝓖' ×ˢ (Set.univ ×ˢ 𝓩)
  set S4 : Set (N' × (U × Z)) := Set.univ ×ˢ (Set.univ ×ˢ 𝓩)

  set Γ₀ : AddSubgroup (U × N) := (⊥ : AddSubgroup U).prod ΓN
  set Γt : AddSubgroup (N' × (U × Z)) := ΓN'.prod ((⊥ : AddSubgroup U).prod ΓZ)
  set Γ₂ : AddSubgroup (N' × (U × Z)) := (⊥ : AddSubgroup N').prod ((⊥ : AddSubgroup U).prod ΓZ)
  have : VAddInvariantMeasure Γ₀ (U × N) (νu.prod lam) :=
    vaddInv_bot_prod νu lam ΓN (fun y _ => measurePreserving_add_left lam y)
  have : VAddInvariantMeasure ((⊥ : AddSubgroup U).prod ΓZ) (U × Z) (νu.prod μZ) :=
    vaddInv_bot_prod νu μZ ΓZ (fun y _ => measurePreserving_add_left μZ y)
  have : VAddInvariantMeasure Γ₂ (N' × (U × Z)) m' :=
    vaddInv_bot_prod (lam'.restrict 𝓖') (νu.prod μZ) _ (fun y hy => mp_of_vaddInv _ _ y hy)

  have hT0 : IsAddFundamentalDomain Γ₀ (Set.univ ×ˢ 𝓖) (νu.prod lam) := fd_prod' (fd_bot_univ νu) h𝓖
  have hS3 : IsAddFundamentalDomain Γt S3 m := fd_prod' h𝓖' (fd_prod' (fd_bot_univ νu) h𝓩)
  have hmemt : ∀ g : Γt, (Φ.symm (g : N' × (U × Z))) ∈ Γ₀ := by
    intro g
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    rw [phi_symm_apply]
    refine AddSubgroup.mem_prod.2 ⟨hg2.1, (hΓ _).2 ?_⟩
    rw [MeasurableEquiv.apply_symm_apply]
    exact ⟨hg2.2, hg.1⟩
  have hT1 : IsAddFundamentalDomain Γ₀ (Φ ⁻¹' S3) (νu.prod lam) := by
    refine hS3.preimage_of_equiv (f := Φ) ⟨Φ.measurable, ?_⟩ (e := fun g => ⟨Φ.symm g, hmemt g⟩) ?_ ?_
    · rw [phi_map hPc]; exact Measure.smul_absolutelyContinuous
    · refine ⟨fun g g' h => Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
      refine ⟨⟨Φ g, ?_⟩, Subtype.ext (Φ.symm_apply_apply _)⟩
      have hg := AddSubgroup.mem_prod.1 g.2
      rw [phi_apply]
      have hP := (hΓ _).1 hg.2
      exact AddSubgroup.mem_prod.2 ⟨hP.2, AddSubgroup.mem_prod.2 ⟨hg.1, hP.1⟩⟩
    · intro g p
      show Φ (Φ.symm g + p) = g + Φ p
      rw [phi_add hPadd, MeasurableEquiv.apply_symm_apply]
  have hS4 : IsAddFundamentalDomain Γ₂ S4 m' := fd_prod' (fd_bot_univ _) (fd_prod' (fd_bot_univ νu) h𝓩)
  have hSmp : MeasurePreserving S m' m' := sh_mp hτ _ _ _
  have hS5 : IsAddFundamentalDomain Γ₂ (S.symm ⁻¹' S4) m' := by
    refine hS4.preimage_of_equiv (f := S.symm) hSmp.symm.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g w
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    show S.symm ((g : N' × (U × Z)) + w) = (g : N' × (U × Z)) + S.symm w
    rw [sh_symm_apply, sh_symm_apply]
    rw [AddSubgroup.mem_bot] at hg2 hg
    ext
    · rfl
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, hg.1, hg2.1, zero_add]; abel

  have eS3 : m.restrict S3 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m, S3, ← Measure.prod_restrict, Measure.restrict_univ]
  have eS4 : m'.restrict S4 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m', S4, ← Measure.prod_restrict, Measure.restrict_univ]
  have hpt : ∀ p, f p = H (S (Φ p)) := by
    rintro ⟨u, β⟩
    rw [hfH, phi_apply, sh_apply]
  calc ∫ p, f p ∂(νu.prod (lam.restrict 𝓖))
      = ∫ p in Set.univ ×ˢ 𝓖, f p ∂(νu.prod lam) := by rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫ p in Φ ⁻¹' S3, f p ∂(νu.prod lam) := by
        refine hT0.setIntegral_eq hT1 fun g p => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        rw [AddSubgroup.mem_bot] at hg
        obtain ⟨u, β⟩ := p
        show f ((g : U × N) + (u, β)) = f (u, β)
        have e : (g : U × N) + (u, β) = (u, (g : U × N).2 + β) := by ext <;> simp [hg.1]
        rw [e, hf _ hg.2]
    _ = ∫ p in Φ ⁻¹' S3, H (S (Φ p)) ∂(νu.prod lam) := by simp only [← hpt]
    _ = ∫ w in S3, H (S w) ∂((νu.prod lam).map Φ) := (Φ.measurableEmbedding.setIntegral_map (μ := νu.prod lam) (fun w => H (S w)) S3).symm
    _ = c.toReal • ∫ w in S3, H (S w) ∂m := by rw [phi_map hPc, Measure.restrict_smul, integral_smul_measure]
    _ = c.toReal • ∫ w in S4, H (S w) ∂m' := by rw [eS3, ← eS4]
    _ = c.toReal • ∫ w in S.symm ⁻¹' S4, H w ∂m' := by
        congr 1
        have e : S ⁻¹' (S.symm ⁻¹' S4) = S4 := by ext w; simp
        have h := hSmp.setIntegral_preimage_emb S.measurableEmbedding H (S.symm ⁻¹' S4)
        rw [e] at h
        exact h
    _ = c.toReal • ∫ w in S4, H w ∂m' := by
        congr 1
        refine hS5.setIntegral_eq hS4 fun g w => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        have hg2 := AddSubgroup.mem_prod.1 hg.2
        rw [AddSubgroup.mem_bot] at hg hg2
        show H ((g : N' × (U × Z)) + w) = H w
        have e : (g : N' × (U × Z)) + w = (w.1, (w.2.1, (g : N' × (U × Z)).2.2 + w.2.2)) := by
          ext <;> simp [hg.1, hg2.1]
        rw [e, hH _ hg2.2]
    _ = c.toReal • ∫ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by rw [eS4]

theorem chainE (hPc : lam.map P = c • (μZ.prod lam')) (hPadd : ∀ a b, P (a + b) = P a + P b)
    (hΓ : ∀ β, β ∈ ΓN ↔ (P β).1 ∈ ΓZ ∧ (P β).2 ∈ ΓN')
    (h𝓖 : IsAddFundamentalDomain ΓN 𝓖 lam) (h𝓩 : IsAddFundamentalDomain ΓZ 𝓩 μZ)
    (h𝓖' : IsAddFundamentalDomain ΓN' 𝓖' lam') (hτ : Measurable τ) (f : U × N → ℝ≥0∞) (H : N' × (U × Z) → ℝ≥0∞)
    (hf : ∀ γ ∈ ΓN, ∀ u β, f (u, γ + β) = f (u, β))
    (hH : ∀ g ∈ ΓZ, ∀ w : N' × (U × Z), H (w.1, (w.2.1, g + w.2.2)) = H w)
    (hfH : ∀ u β, f (u, β) = H ((P β).2, (u, (P β).1 + τ (u, (P β).2)))) :
    ∫⁻ p, f p ∂(νu.prod (lam.restrict 𝓖)) =
      c * ∫⁻ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by
  set Φ := phi (U := U) P
  set S := sh τ hτ
  set m := lam'.prod (νu.prod μZ)
  set m' := (lam'.restrict 𝓖').prod (νu.prod μZ)
  set S3 : Set (N' × (U × Z)) := 𝓖' ×ˢ (Set.univ ×ˢ 𝓩)
  set S4 : Set (N' × (U × Z)) := Set.univ ×ˢ (Set.univ ×ˢ 𝓩)

  set Γ₀ : AddSubgroup (U × N) := (⊥ : AddSubgroup U).prod ΓN
  set Γt : AddSubgroup (N' × (U × Z)) := ΓN'.prod ((⊥ : AddSubgroup U).prod ΓZ)
  set Γ₂ : AddSubgroup (N' × (U × Z)) := (⊥ : AddSubgroup N').prod ((⊥ : AddSubgroup U).prod ΓZ)
  have : VAddInvariantMeasure Γ₀ (U × N) (νu.prod lam) :=
    vaddInv_bot_prod νu lam ΓN (fun y _ => measurePreserving_add_left lam y)
  have : VAddInvariantMeasure ((⊥ : AddSubgroup U).prod ΓZ) (U × Z) (νu.prod μZ) :=
    vaddInv_bot_prod νu μZ ΓZ (fun y _ => measurePreserving_add_left μZ y)
  have : VAddInvariantMeasure Γ₂ (N' × (U × Z)) m' :=
    vaddInv_bot_prod (lam'.restrict 𝓖') (νu.prod μZ) _ (fun y hy => mp_of_vaddInv _ _ y hy)

  have hT0 : IsAddFundamentalDomain Γ₀ (Set.univ ×ˢ 𝓖) (νu.prod lam) := fd_prod' (fd_bot_univ νu) h𝓖
  have hS3 : IsAddFundamentalDomain Γt S3 m := fd_prod' h𝓖' (fd_prod' (fd_bot_univ νu) h𝓩)
  have hmemt : ∀ g : Γt, (Φ.symm (g : N' × (U × Z))) ∈ Γ₀ := by
    intro g
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    rw [phi_symm_apply]
    refine AddSubgroup.mem_prod.2 ⟨hg2.1, (hΓ _).2 ?_⟩
    rw [MeasurableEquiv.apply_symm_apply]
    exact ⟨hg2.2, hg.1⟩
  have hT1 : IsAddFundamentalDomain Γ₀ (Φ ⁻¹' S3) (νu.prod lam) := by
    refine hS3.preimage_of_equiv (f := Φ) ⟨Φ.measurable, ?_⟩ (e := fun g => ⟨Φ.symm g, hmemt g⟩) ?_ ?_
    · rw [phi_map hPc]; exact Measure.smul_absolutelyContinuous
    · refine ⟨fun g g' h => Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
      refine ⟨⟨Φ g, ?_⟩, Subtype.ext (Φ.symm_apply_apply _)⟩
      have hg := AddSubgroup.mem_prod.1 g.2
      rw [phi_apply]
      have hP := (hΓ _).1 hg.2
      exact AddSubgroup.mem_prod.2 ⟨hP.2, AddSubgroup.mem_prod.2 ⟨hg.1, hP.1⟩⟩
    · intro g p
      show Φ (Φ.symm g + p) = g + Φ p
      rw [phi_add hPadd, MeasurableEquiv.apply_symm_apply]
  have hS4 : IsAddFundamentalDomain Γ₂ S4 m' := fd_prod' (fd_bot_univ _) (fd_prod' (fd_bot_univ νu) h𝓩)
  have hSmp : MeasurePreserving S m' m' := sh_mp hτ _ _ _
  have hS5 : IsAddFundamentalDomain Γ₂ (S.symm ⁻¹' S4) m' := by
    refine hS4.preimage_of_equiv (f := S.symm) hSmp.symm.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro g w
    have hg := AddSubgroup.mem_prod.1 g.2
    have hg2 := AddSubgroup.mem_prod.1 hg.2
    show S.symm ((g : N' × (U × Z)) + w) = (g : N' × (U × Z)) + S.symm w
    rw [sh_symm_apply, sh_symm_apply]
    rw [AddSubgroup.mem_bot] at hg2 hg
    ext
    · rfl
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, hg.1, hg2.1, zero_add]; abel

  have eS3 : m.restrict S3 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m, S3, ← Measure.prod_restrict, Measure.restrict_univ]
  have eS4 : m'.restrict S4 = (lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩)) := by
    simp only [m', S4, ← Measure.prod_restrict, Measure.restrict_univ]
  have hpt : ∀ p, f p = H (S (Φ p)) := by
    rintro ⟨u, β⟩
    rw [hfH, phi_apply, sh_apply]
  calc ∫⁻ p, f p ∂(νu.prod (lam.restrict 𝓖))
      = ∫⁻ p in Set.univ ×ˢ 𝓖, f p ∂(νu.prod lam) := by rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫⁻ p in Φ ⁻¹' S3, f p ∂(νu.prod lam) := by
        refine hT0.setLIntegral_eq hT1 f fun g p => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        rw [AddSubgroup.mem_bot] at hg
        obtain ⟨u, β⟩ := p
        show f ((g : U × N) + (u, β)) = f (u, β)
        have e : (g : U × N) + (u, β) = (u, (g : U × N).2 + β) := by ext <;> simp [hg.1]
        rw [e, hf _ hg.2]
    _ = ∫⁻ p in Φ ⁻¹' S3, H (S (Φ p)) ∂(νu.prod lam) := by simp only [← hpt]
    _ = ∫⁻ w in S3, H (S w) ∂((νu.prod lam).map Φ) := by
        rw [Φ.measurableEmbedding.restrict_map, Φ.measurableEmbedding.lintegral_map]
    _ = c * ∫⁻ w in S3, H (S w) ∂m := by rw [phi_map hPc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = c * ∫⁻ w in S4, H (S w) ∂m' := by rw [eS3, ← eS4]
    _ = c * ∫⁻ w in S.symm ⁻¹' S4, H w ∂m' := by
        congr 1
        have e : S ⁻¹' (S.symm ⁻¹' S4) = S4 := by ext w; simp
        have h := hSmp.setLIntegral_comp_preimage_emb S.measurableEmbedding H (S.symm ⁻¹' S4)
        rw [e] at h
        exact h
    _ = c * ∫⁻ w in S4, H w ∂m' := by
        congr 1
        refine hS5.setLIntegral_eq hS4 H fun g w => ?_
        have hg := AddSubgroup.mem_prod.1 g.2
        have hg2 := AddSubgroup.mem_prod.1 hg.2
        rw [AddSubgroup.mem_bot] at hg hg2
        show H ((g : N' × (U × Z)) + w) = H w
        have e : (g : N' × (U × Z)) + w = (w.1, (w.2.1, (g : N' × (U × Z)).2.2 + w.2.2)) := by
          ext <;> simp [hg.1, hg2.1]
        rw [e, hH _ hg2.2]
    _ = c * ∫⁻ q, H q ∂((lam'.restrict 𝓖').prod (νu.prod (μZ.restrict 𝓩))) := by rw [eS4]

end Main

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
