import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermXGen

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section iso2

variable {k r : ℕ}

lemma part_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h m : B.Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) (hX : ∀ a : Fin r, (h * m) *ᵥ bvec (eI k r a) = bvec (eI k r a))
    {w w' x x' : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (hw' : inWb k r w') (hx : x ∈ Xsp k r)
    (hx' : x' ∈ Xsp k r) (e : (h * m) *ᵥ (w + x) = w' + x') : h *ᵥ w = w' := by
  rw [mulVec_add, fix_X hX hx, ← mulVec_mulVec] at e
  have hmw := N_wb hm hw
  have e2 : m *ᵥ w = w + (m *ᵥ w - w) := by abel
  rw [e2, mulVec_add, uw_X hz hh hmw] at e
  have hd : h *ᵥ w - w' = x' - x - (m *ᵥ w - w) := by
    calc h *ᵥ w - w' = (h *ᵥ w + (m *ᵥ w - w) + x) - w' - (m *ᵥ w - w) - x := by abel
      _ = (w' + x') - w' - (m *ᵥ w - w) - x := by rw [e]
      _ = x' - x - (m *ᵥ w - w) := by abel
  have hX0 : h *ᵥ w - w' ∈ Xsp k r := by
    rw [hd]; exact Submodule.sub_mem _ (Submodule.sub_mem _ hx' hx) hmw
  have hW0 : inWb k r (h *ᵥ w - w') := by
    intro i hi; simp [uw_inWb hz hh hw i hi, hw' i hi]
  exact sub_eq_zero.1 (X_wb_zero hX0 hW0)

lemma fixes_e {s : B.Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hs : ∀ a, s *ᵥ fvec k r z a = fvec k r z a) :
    ∀ a : Fin r, s *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  intro a
  have := hs ⟨a.val, by omega⟩
  rwa [fvec_lt] at this

theorem isoCore : IsoCore := by
  intro k r z z' hk hr hz hz' D0 y hy α hα β hβ hν hν' hαβ
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have hyG := hy.1
  have hG := hy.2.1
  have hyu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hyG
  have hαu := Wz.unit α hα
  have hβu := Wz'.unit β hβ
  have hβν : β *ᵥ D0.nu' = D0.nu' := by
    conv_lhs => rw [← hν']
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hβu, one_mulVec]
  have hU0W : ∀ u ∈ D0.U0, inWb k r u := fun u hu => ((D0.isotropic_subspace_eq u).1 hu).1.1
  have hU0z : ∀ u ∈ D0.U0, herm (Hpk k r) u z = 0 := fun u hu => ((D0.isotropic_subspace_eq u).1 hu).1.2
  have hU0z' : ∀ u ∈ D0.U0, herm (Hpk k r) u z' = 0 := fun u hu => ((D0.isotropic_subspace_eq_primed u).1 hu).1.2
  have hβU : ∀ u ∈ D0.U0, β *ᵥ u ∈ D0.U0 := by
    intro u hu
    obtain ⟨⟨huW, huz'⟩, huν'⟩ := (D0.isotropic_subspace_eq_primed u).1 hu
    refine (D0.isotropic_subspace_eq_primed _).2 ⟨⟨uw_inWb hz'.1 hβ huW, ?_⟩, ?_⟩
    · conv_lhs => rw [← hβ.2.2]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huz'
    · conv_lhs => rw [← hβν]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huν'
  have hαU : ∀ u ∈ D0.U0, α *ᵥ u ∈ D0.U0 := by
    intro u hu
    obtain ⟨⟨huW, huz⟩, huν⟩ := (D0.isotropic_subspace_eq u).1 hu
    refine (D0.isotropic_subspace_eq _).2 ⟨⟨uw_inWb hz.1 hα huW, ?_⟩, ?_⟩
    · conv_lhs => rw [← hα.2.2]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]; exact huz
    · conv_lhs => rw [← hν]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]; exact huν

  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
    { carrier := D0.U0
      add_mem' := by
        intro a b (ha : a ∈ D0.U0) (hb : b ∈ D0.U0)
        show a + b ∈ D0.U0
        rw [D0.isotropic_subspace_eq] at ha hb ⊢
        refine ⟨⟨fun i hi => by simp [ha.1.1 i hi, hb.1.1 i hi], ?_⟩, ?_⟩
        · rw [hm_add_l, ha.1.2, hb.1.2, add_zero]
        · rw [hm_add_l, ha.2, hb.2, add_zero]
      zero_mem' := by
        show (0 : Fin (2 * r + k + 1) → ℂ) ∈ D0.U0
        rw [D0.isotropic_subspace_eq]
        exact ⟨⟨fun i _ => rfl, by simp [herm]⟩, by simp [herm]⟩
      smul_mem' := by
        intro c a (ha : a ∈ D0.U0)
        show c • a ∈ D0.U0
        rw [D0.isotropic_subspace_eq] at ha ⊢
        refine ⟨⟨fun i hi => by simp [ha.1.1 i hi], ?_⟩, ?_⟩
        · rw [hm_smul_l, ha.1.2, mul_zero]
        · rw [hm_smul_l, ha.2, mul_zero] }
  have hSmem : ∀ u, u ∈ S ↔ u ∈ D0.U0 := fun u => Iff.rfl
  let b := Module.finBasis ℂ S
  let bv : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ := fun i => (b i : Fin (2 * r + k + 1) → ℂ)
  have hbU : ∀ i, bv i ∈ D0.U0 := fun i => (b i).2
  have hbspan : ∀ u (hu : u ∈ D0.U0), u = ∑ i, (b.repr ⟨u, (hSmem u).2 hu⟩ i) • bv i := by
    intro u hu
    have := congrArg Subtype.val (b.sum_repr ⟨u, (hSmem u).2 hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm

  choose! Vf hVf V'f hV'f hq using hy.2.2.2.2
  let q : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u => u + Vf u
  have hqy : ∀ u ∈ D0.U0, y *ᵥ (u + V'f u) = q u := hq
  have hesI : ∀ a : Fin r, r + k < (esI k r a).val := fun a => by simp [esI]; omega
  have hq_f : ∀ u ∈ D0.U0, ∀ a, herm (Hpk k r) (q u) (fvec k r z a) = 0 := by
    intro u hu a
    show herm (Hpk k r) (u + Vf u) _ = 0
    rw [hm_add_l]
    unfold fvec
    split_ifs with ha
    · rw [herm_bvec_eI, herm_bvec_eI, hU0W u hu _ (Or.inr (hesI _)), X_hi (hVf u hu) _ (hesI _), add_zero]
    · rw [hU0z u hu, herm_X_wb (hVf u hu) hz.1, add_zero]
  have hq_yf : ∀ u ∈ D0.U0, ∀ c, herm (Hpk k r) (q u) (y *ᵥ fvec k r z' c) = 0 := by
    intro u hu c
    rw [← hqy u hu, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hyG, hm_add_l]
    unfold fvec
    split_ifs with hc
    · rw [herm_bvec_eI, herm_bvec_eI, hU0W u hu _ (Or.inr (hesI _)), X_hi (hV'f u hu) _ (hesI _), add_zero]
    · rw [hU0z' u hu, herm_X_wb (hV'f u hu) hz'.1, add_zero]
  have hq_gv : ∀ u ∈ D0.U0, ∀ i, herm (Hpk k r) (q u) (gramVec k r z z' y i) = 0 := by
    intro u hu i
    cases i with
    | inl a => exact hq_f u hu a
    | inr c => exact hq_yf u hu c
  have hgv_q : ∀ u ∈ D0.U0, ∀ i, herm (Hpk k r) (gramVec k r z z' y i) (q u) = 0 := by
    intro u hu i
    rw [hm_symm _ (Formalism.QuantumDeterminants.hpkFacts k r).1, hq_gv u hu i, star_zero]
  have hq_q : ∀ u ∈ D0.U0, ∀ u' ∈ D0.U0, herm (Hpk k r) (q u) (q u') = herm (Hpk k r) u u' := by
    intro u hu u' hu'
    show herm (Hpk k r) (u + Vf u) (u' + Vf u') = _
    rw [hm_add_l, hm_add_r, hm_add_r, herm_X_gen (hVf u hu) (wb_hi (hU0W u' hu')),
      herm_X_gen (hVf u hu) (X_hi (hVf u' hu')), herm_wb_X (hVf u' hu') (wb_hi (hU0W u hu))]
    ring

  have key0 : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → ∀ g : Fin (Module.finrank ℂ S) → ℂ,
      (∀ u ∈ D0.U0, herm (Hpk k r) (∑ i, g i • q (c i)) (q u) = 0) → g = 0 := by
    intro c hc hli g hg
    set u₀ := ∑ i, g i • c i with hu₀d
    have hu₀ : u₀ ∈ D0.U0 := (hSmem u₀).1 (S.sum_mem fun i _ => S.smul_mem (g i) ((hSmem _).2 (hc i)))
    have h0 : herm (Hpk k r) u₀ u₀ = 0 := by
      have := hg u₀ hu₀
      rw [hm_sum_l] at this
      rw [hu₀d, hm_sum_l, ← this]
      exact Finset.sum_congr rfl fun i _ => by rw [hq_q _ (hc i) _ hu₀]
    have hz0 : u₀ = 0 := by
      by_contra hne
      have := posV hz (hU0W u₀ hu₀) (hU0z u₀ hu₀) hne
      rw [h0] at this; simp at this
    funext i
    exact (Fintype.linearIndependent_iff.1 hli) g hz0 i
  have hlib : LinearIndependent ℂ bv := b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hlibβ : LinearIndependent ℂ (fun i => β *ᵥ bv i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : ∑ i, g i • bv i = 0 := by
      have h2 := congrArg (fun v => β⁻¹ *ᵥ v) hg
      simp only [mv_sum, mulVec_smul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hβu, one_mulVec, mulVec_zero] at h2
      exact h2
    exact (Fintype.linearIndependent_iff.1 hlib) g this
  have liq : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → LinearIndependent ℂ (fun i => q (c i)) := by
    intro c hc hli
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := key0 c hc hli g (fun u _ => by rw [hg]; simp [herm])
    intro i; rw [this]; rfl
  have hgvli := (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' y ⟨hk, hz, hz'⟩ ⟨hyG, hG⟩).1
  have famli : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → LinearIndependent ℂ (Sum.elim (gramVec k r z z' y) (fun i => q (c i))) := by
    intro c hc hli
    refine hgvli.sum_type (liq c hc hli) ?_
    rw [Submodule.disjoint_def]
    intro v hv1 hv2
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv2
    obtain ⟨g1, hg1⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv1
    have := key0 c hc hli g (fun u hu => by
      rw [← hg1, hm_sum_l]
      exact Finset.sum_eq_zero fun j _ => by rw [hgv_q u hu j, mul_zero])
    rw [this]; simp
  have hβbU : ∀ i, β *ᵥ bv i ∈ D0.U0 := fun i => hβU _ (hbU i)

  obtain ⟨s, hsG, hs⟩ := PI.UnitaryGroupMassFormula.DLm.Lifts.wittHpk k r
    (Sum.elim (gramVec k r z z' y) (fun i => q (β *ᵥ bv i)))
    (Sum.elim (gramVec k r z z' y) (fun i => q (bv i)))
    (famli _ hβbU hlibβ) (famli _ hbU hlib) (by
      intro i j
      cases i with
      | inl a =>
        cases j with
        | inl c => rfl
        | inr c => simp only [Sum.elim_inl, Sum.elim_inr]; rw [hgv_q _ (hβbU c), hgv_q _ (hbU c)]
      | inr a =>
        cases j with
        | inl c => simp only [Sum.elim_inl, Sum.elim_inr]; rw [hq_gv _ (hβbU a), hq_gv _ (hbU a)]
        | inr c =>
          simp only [Sum.elim_inr]
          rw [hq_q _ (hβbU a) _ (hβbU c), hq_q _ (hbU a) _ (hbU c), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1])
  have hsf : ∀ a, s *ᵥ fvec k r z a = fvec k r z a := fun a => hs (Sum.inl (Sum.inl a))
  have hsyf : ∀ c, s *ᵥ (y *ᵥ fvec k r z' c) = y *ᵥ fvec k r z' c := fun c => hs (Sum.inl (Sum.inr c))
  have hsq : ∀ i, s *ᵥ q (β *ᵥ bv i) = q (bv i) := fun i => hs (Sum.inr i)
  have hsu : IsUnit s.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hsG
  have hsS : s ∈ C2.CurvatureSupportSet k r z := by
    rw [← Formalism.FourierDecayAlt.P.fixed_frame_property k r z hz]; exact ⟨hsG, hsf⟩
  obtain ⟨h, hh, m, hm, hsd⟩ := parabolic_levi_unipotent_decomp hz hsS
  set s' := y⁻¹ * s⁻¹ * y with hs'd
  have hsinv : ∀ v, s *ᵥ v = v → s⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, one_mulVec]
  have hs'f : ∀ c, s' *ᵥ fvec k r z' c = fvec k r z' c := by
    intro c
    rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec, hsinv _ (hsyf c), mulVec_mulVec, Matrix.nonsing_inv_mul _ hyu,
      one_mulVec]
  have hs'G : s' ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hyG) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hsG)) hyG
  have hs'S : s' ∈ C2.CurvatureSupportSet k r z' := by
    rw [← Formalism.FourierDecayAlt.P.fixed_frame_property k r z' hz']; exact ⟨hs'G, hs'f⟩
  obtain ⟨h', hh', m', hm', hs'd2⟩ := parabolic_levi_unipotent_decomp hz' hs'S

  have hhβ : ∀ i, h *ᵥ (β *ᵥ bv i) = bv i := by
    intro i
    have e := hsq i
    rw [hsd] at e
    exact part_eq hz.1 hh hm.1 (by rw [← hsd]; exact fixes_e hsf) (hU0W _ (hβbU i)) (hU0W _ (hbU i))
      (hVf _ (hβbU i)) (hVf _ (hbU i)) e
  have hhβ' : ∀ u ∈ D0.U0, h *ᵥ (β *ᵥ u) = u := by
    intro u hu
    rw [hbspan u hu, mv_sum, mv_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mulVec_smul, mulVec_smul, hhβ i]
  have hβα : ∀ u ∈ D0.U0, β *ᵥ (α *ᵥ u) = u := by
    intro u hu
    have e := hαβ (α *ᵥ u) (hαU u hu)
    have inj : ∀ v v' : Fin (2 * r + k + 1) → ℂ, α *ᵥ v = α *ᵥ v' → v = v' := by
      intro v v' hvv
      have := congrArg (fun t => α⁻¹ *ᵥ t) hvv
      simpa [mulVec_mulVec, Matrix.nonsing_inv_mul _ hαu] using this
    exact inj _ _ e
  have hxs : s *ᵥ xcof k r z z' y = xcof k r z z' y := by
    unfold xcof; rw [mv_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mulVec_smul, hsyf c]
  have hhom : h *ᵥ omW k r z z' y = omW k r z z' y := by
    unfold omW
    calc h *ᵥ prW k r z (xcof k r z z' y) = h *ᵥ prW k r z (m *ᵥ xcof k r z z' y) := by
          rw [prW_N hm.1 (xcof_esI z z' y)]
      _ = prW k r z (h *ᵥ (m *ᵥ xcof k r z z' y)) := by rw [prW_UW hz hh]
      _ = prW k r z (s *ᵥ xcof k r z z' y) := by rw [hsd, mulVec_mulVec]
      _ = prW k r z (xcof k r z z' y) := by rw [hxs]
  have hα_eq : h = α := by
    refine uw_eq hz D0.nu_mem D0.nu_unit D0.isotropic_subspace_eq hh hα (fun u hu => ?_) ?_
    · conv_lhs => rw [← hβα u hu]
      rw [hhβ' _ (hαU u hu)]
    · rw [hν]
      obtain ⟨t, ht, hom⟩ := hy.2.2.1
      rw [hom, mulVec_smul] at hhom
      exact smul_right_injective _ (Complex.ofReal_ne_zero.2 ht.ne') hhom

  have hs'X : ∀ a : Fin r, (h' * m') *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    rw [← hs'd2]; exact fixes_e hs'f
  have hh'b : ∀ i, h' *ᵥ bv i = β *ᵥ bv i := by
    intro i
    have e : s' *ᵥ (bv i + V'f (bv i)) = β *ᵥ bv i + V'f (β *ᵥ bv i) := by
      rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec, hqy _ (hbU i)]
      have : s⁻¹ *ᵥ q (bv i) = q (β *ᵥ bv i) := by
        rw [← hsq i, mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, one_mulVec]
      rw [this, ← hqy _ (hβbU i), mulVec_mulVec, Matrix.nonsing_inv_mul _ hyu, one_mulVec]
    rw [hs'd2] at e
    exact part_eq hz'.1 hh' hm'.1 hs'X (hU0W _ (hbU i)) (hU0W _ (hβbU i)) (hV'f _ (hbU i)) (hV'f _ (hβbU i)) e
  have hh'U : ∀ u ∈ D0.U0, h' *ᵥ u = β *ᵥ u := by
    intro u hu
    rw [hbspan u hu, mv_sum, mv_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mulVec_smul, mulVec_smul, hh'b i]
  have hxs' : s' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y) = y⁻¹ *ᵥ xcofL k r z z' y := by
    have hfix : s⁻¹ *ᵥ xcofL k r z z' y = xcofL k r z z' y := by
      apply hsinv
      unfold xcofL; rw [mv_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [mulVec_smul, hsf a]
    rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec,
      show y *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y) = xcofL k r z z' y by
        rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, one_mulVec], hfix]
  have hhom' : h' *ᵥ omW' k r z z' y = omW' k r z z' y := by
    unfold omW'
    calc h' *ᵥ prW k r z' (y⁻¹ *ᵥ xcofL k r z z' y) = h' *ᵥ prW k r z' (m' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y)) := by
          rw [prW_N hm'.1 (ginv_xcofL_esI z z' hyG)]
      _ = prW k r z' (h' *ᵥ (m' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y))) := by rw [prW_UW hz' hh']
      _ = prW k r z' (s' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y)) := by rw [hs'd2, mulVec_mulVec]
      _ = prW k r z' (y⁻¹ *ᵥ xcofL k r z z' y) := by rw [hxs']
  have hβ_eq : h' = β := by
    refine uw_eq hz' D0.nu'_mem D0.nu'_unit D0.isotropic_subspace_eq_primed hh' hβ hh'U ?_
    rw [hβν]
    obtain ⟨t, ht, hom⟩ := hy.2.2.2.1
    rw [hom, mulVec_smul] at hhom'
    exact smul_right_injective _ (Complex.ofReal_ne_zero.2 ht.ne') hhom'

  have hmu := Gz.unit m hm
  have hsys : s * y * s' = y := by
    rw [hs'd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s y, Matrix.mul_nonsing_inv _ hyu,
      Matrix.mul_one, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mul]
  rw [hsd, hs'd2, hα_eq, hβ_eq] at hsys
  refine ⟨m⁻¹, Gz.inv_mem m hm, β * m' * β⁻¹, unipotent_normal_unitary hz' hβ hm', ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv m hmu]
  calc α * (m * y * (β * m' * β⁻¹)) * β = α * m * y * (β * m') := by
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hβu, Matrix.mul_one]
    _ = y := hsys

theorem gfStab : GfStab := gfStab_of_iso isoCore

end iso2

end PI.UnitaryGroupMassFormula.GsFr
