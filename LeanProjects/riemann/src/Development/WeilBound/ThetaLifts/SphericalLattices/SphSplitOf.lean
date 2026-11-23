import Development.WeilBound.ThetaLifts.SphericalLattices.SplitLoc

noncomputable section

namespace PositivityTheory.Sph.SplitPl

open scoped Matrix Topology
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  GlobalTheory.SplitFlip PositivityTheory.KCo

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

theorem intInd_eq (v : Pl F) {a b : ℕ} : (SplitDict.intInd v : Matrix (Fin a) (Fin b) (Fv F v) → ℂ) =
    Set.indicator {Z : Matrix (Fin a) (Fin b) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) := by
  unfold SplitDict.intInd
  congr 1
  ext Z
  exact forall₂_congr fun i j => (GlobalTheory.WeylFour.IndOSelf.mem_int_iff _).symm

theorem irrAt_of (hS : SurjSt) (hI : IrrSt) {om : Rep σ X W} {v : Pl F}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ} (hnd : n ≤ d)
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (hα : USm α) (h1 : ν ≠ 1) : IrrAt om v := by
  rintro N ⟨hAN, hNS, hst⟩
  rcases hI _ n d ν α hnd hν hα (N.map ι) ((aug_le_map hb hD).trans (Submodule.map_mono hAN)) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ (hNS hψ)
      exact ⟨ψ₁, hst h hh ψ hψ ψ₁ h₁ ha, e⟩) with h | h
  · right
    refine le_antisymm hNS fun φ hφ => ?_
    obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hφ
    obtain ⟨χ, hχ, e⟩ := h _ hf
    have e' : χ = φ₀ := hb.2.1 (hNS hχ) h₀ e
    have := add_mem (hAN ha) (e' ▸ hχ)
    rwa [sub_add_cancel] at this
  · left
    refine le_antisymm (fun φ hφ => ?_) hAN
    obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 (hNS hφ)
    have hN0 : φ₀ ∈ N := by
      have := sub_mem hφ (hAN ha)
      rwa [sub_sub_cancel] at this
    have := add_mem ha (mem_augAt hb hD h₀ (h _ ⟨φ₀, hN0, rfl⟩ hf))
    rwa [sub_add_cancel] at this

theorem sphAt_of (hL : LatSt) {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {α : (Fv F v)ˣ →* ℂˣ}
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hs : M.vac v ∈ SB _) (hvac : ι (M.vac v) = SplitDict.intInd v)
    (hg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB 1 α g₀ 1))
    (hh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB 1 α 1 h₀)) :
    SphAt M ψ om v := by
  intro ω ρ L
  have rg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (g, 1) φ ∈ SB _ ∧ ι (ω (g, 1) φ) = omB 1 α g₀ 1 (ι φ) := fun g₀ => by
    obtain ⟨g, hg', r⟩ := hg g₀
    refine ⟨g, hg', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts g hg' 1 (one_mem_UAt W v) φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have rh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (1, h) φ ∈ SB _ ∧ ι (ω (1, h) φ) = omB 1 α 1 h₀ (ι φ) := fun h₀ => by
    obtain ⟨h, hh', r⟩ := hh h₀
    refine ⟨h, hh', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts 1 (one_mem_UAt X v) h hh' φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have liftR : ∀ f ∈ Submodule.span ℂ {f | ∃ h : GL (Fin d) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (Y * h.1)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h₀, rfl⟩ := hx
      obtain ⟨h, hh', r⟩ := rh h₀
      obtain ⟨hS, e⟩ := r _ hs
      have hc : (α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2) ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
      refine ⟨((α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2))⁻¹ • ω (1, h) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_right_action, intInd_eq]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add, e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  have liftL : ∀ f ∈ Submodule.span ℂ {f | ∃ g : GL (Fin n) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (g.1 * Y)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      obtain ⟨g, hg', r⟩ := rg (invT g₀)⁻¹
      obtain ⟨hS, e⟩ := r _ hs
      have hc : apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
      refine ⟨(apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2))⁻¹ • ω (g, 1) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_left_action, intInd_eq, invT_inv_val, Matrix.transpose_transpose]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add, e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  refine ⟨M.vac v, hs, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨m, g, hgK, hinv⟩ := avgL (hb.1 hφ)
    choose x hx hxr using fun i => rg (invT (g i))
    have hterm : ∀ i, ι (ω (x i, 1) φ) = fun Y => ι φ (((g i)⁻¹).val * Y) := fun i => by
      rw [(hxr i φ hφ).2, split_weil_rep_left_action, apow_KO (invT_mem_KO (hgK i))]
      funext Y
      rw [one_mul, invT_val, Matrix.transpose_transpose]
    set φ' := ∑ i, ω (x i, 1) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => (hxr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y) := by
      rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i) Y
    have hf : (fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftR _ (hL (Fv F v) n d _ hf fun h hh Y => hinv h hh Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    have haug : ((m + 1 : ℕ) : ℂ) • φ - φ' ∈ augAt om v := by
      have e : ((m + 1 : ℕ) : ℂ) • φ - φ' = ∑ i : Fin (m + 1), -(ω (x i, 1) φ - φ) := by
        rw [hφ', Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, neg_sub]
      rw [e]
      exact sum_mem fun i _ => neg_mem (PositivityTheory.Sph.IsLocRep.sub_mem_aug L (hx i) hφ)
    have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    refine Submodule.mem_sup.2 ⟨_, Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) haug, _,
      Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) (hz' ▸ hz), ?_⟩
    rw [← smul_add, sub_add_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · obtain ⟨m, h, hhK, hinv⟩ := avgR (hb.1 hφ)
    choose y hy hyr using fun i => rh (h i)
    have hterm : ∀ i, ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v),
        ι (((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) ψ') = fun Y => ι ψ' (Y * (h i).val) := fun i ψ' hψ' => by
      rw [map_smul, (hyr i ψ' hψ').2, split_weil_rep_right_action, apow_KO (hhK i)]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    have hfix : ∀ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) (M.vac v) = M.vac v := fun i =>
      hb.2.1 (Submodule.smul_mem _ _ (hyr i _ hs).1) hs (by
        rw [hterm i _ hs, hvac, intInd_eq]
        funext Y
        exact ind_mulKO Y (hhK i))
    set φ' := ∑ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => Submodule.smul_mem _ _ (hyr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (Y * (h i).val) := by
      rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i φ hφ) Y
    have hf : (fun Y => ∑ i, ι φ (Y * (h i).val)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftL _ (latT hL hf fun k hk Y => hinv k hk Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    obtain ⟨c, hc⟩ := PositivityTheory.Sph.IsLocRep.span_vac L hs hz
    rw [hz', hφ'] at hc
    exact ⟨m, y, fun i => ((α (gdet (h i)) : ℂ))⁻¹, c, fun i => ⟨hy i, hfix i⟩, hc⟩

theorem pair_case (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hL : LatSt) {B : Base F E} (hBg : B.IsGood σ)
    {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil B.ψ χX χW om) (hHX : IsHecke F E χX) (hHW : IsHecke F E χW)
    (hnd : n ≤ d) (v : Pl F) (t : E →ₐ[F] Fv F v) : SphAt M B.ψ om v ∨ IrrAt om v := by
  obtain ⟨⟨ι₀, hι₀⟩, s1, s2, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hBg ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  have hu := (section_statement F E σ hBg.cm v t).2
  by_cases h1 : chrW χW t = 1
  · left
    have := hX.lat
    have := hW.lat
    obtain ⟨b, hb⟩ := exists_isSplitBasis t X.L hBg.cm
    obtain ⟨c, hc⟩ := exists_isSplitBasis t W.L hBg.cm
    obtain ⟨δ, hδ⟩ := SplitDict.exists_cond hBg.std v
    obtain ⟨ι, hι, hv, hg, hh⟩ := SplitDict.model_Bar hBg hX hW (hM.vac v) hom hb hc hδ (b' := δ • b) rfl
    rw [h1] at hg hh
    refine sphAt_of (α := chrW χX t) hL hι.bij (hM.vac v).1 hv (fun g₀ => ?_) (fun h₀ => ?_)
    · obtain ⟨g, hg', e⟩ := s1 ((δ • b) * g₀ * (δ • b)⁻¹)
      refine ⟨g, hg', ?_⟩
      have := hg g hg'
      rwa [show SplitDict.inB t (δ • b) g = g₀ by
        rw [SplitDict.inB, show Matrix.GeneralLinearGroup.map (piW t) g.1 = (δ • b) * g₀ * (δ • b)⁻¹ from Units.ext e]
        group] at this
    · obtain ⟨h, hh', e⟩ := s2 (c * h₀ * c⁻¹)
      refine ⟨h, hh', ?_⟩
      have := hh h hh'
      rwa [show SplitDict.inB t c h = h₀ by
        rw [SplitDict.inB, show Matrix.GeneralLinearGroup.map (piW t) h.1 = c * h₀ * c⁻¹ from Units.ext e]
        group] at this
  · right
    refine irrAt_of surjectivity_statement (irrSt_of hB) hnd hι₀.bij ⟨fun g hg => ⟨_, (k ι₀ hι₀).1 g hg
      (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_, fun g hg => ⟨_, (k ι₀ hι₀).2 g hg
        (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_⟩ (hu χW hHW) (hu χX hHX) h1
    · obtain ⟨g, hg, e⟩ := s1 g₀
      exact ⟨g, hg, (k ι₀ hι₀).1 g hg g₀ e⟩
    · obtain ⟨g, hg, e⟩ := s2 g₀
      exact ⟨g, hg, (k ι₀ hι₀).2 g hg g₀ e⟩

end PositivityTheory.Sph.SplitPl

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem sphSplit_of (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hL : LatSt) : SphSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨t⟩
  exact ⟨SplitPl.pair_case hB hL hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hT.chars.heckeβ
      (PositivityTheory.KCo.isHecke_div hT.chars.heckeβ hT.chars.heckeα) (Nat.le_add_right a a') v t,
    SplitPl.pair_case hB hL hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hT.chars.heckeα
      (PositivityTheory.KCo.isHecke_div hT.chars.heckeα hT.chars.heckeβ) (Nat.le_add_left a' a) v t⟩

end PositivityTheory.Sph

end
