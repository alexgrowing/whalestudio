import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.T.LocStepPf

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

theorem continuous_pZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    Continuous (pZ Z : Matrix (Fin n) (Fin n) k → _) := by
  refine continuous_pi fun ij => ?_
  show Continuous fun x : Matrix (Fin n) (Fin n) k =>
    trace (((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k) * x ^ (ij.1 : ℕ))
  exact (continuous_const.matrix_mul (continuous_pow _)).matrix_trace

theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Bz Z) := by
  have : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a} := by
    ext x
    simp [Bz]
  rw [this]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pZ_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : pZ Z (g.val * x * g⁻¹.val) = pZ Z x := by
  funext ij
  simp only [pZ]
  have hb := hg _ ((Module.finBasis k Z) ij.2).2
  rw [Units.conj_pow]
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z) ij.2 : Matrix (Fin n) (Fin n) k)
  set y := x ^ (ij.1 : ℕ)
  calc (b * (g.val * y * g⁻¹.val)).trace = ((b * g.val) * y * g⁻¹.val).trace := by
        simp only [mul_assoc]
    _ = ((g.val * b) * y * g⁻¹.val).trace := by rw [hb]
    _ = (g⁻¹.val * (g.val * b * y)).trace := Matrix.trace_mul_comm _ _
    _ = (b * y).trace := by
        rw [← mul_assoc, ← mul_assoc]
        simp

private theorem mem_iff_lemma {X : Type} [TopologicalSpace X] (U : Set X) (F : X → ℂ) :
    F ∈ supportedIn U ↔ (IsLocallyConstant F ∧ HasCompactSupport F) ∧ Function.support F ⊆ U :=
  Iff.rfl

private theorem isLocallyConstant_indicator_one_of_isClopen {X : Type} [TopologicalSpace X] {s : Set X} (hs : IsClopen s) :
    IsLocallyConstant (s.indicator (1 : X → ℂ)) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ s
  · exact ⟨s, hs.isOpen, hx, fun y hy => by simp [Set.indicator_apply, hx, hy]⟩
  · refine ⟨sᶜ, hs.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    have hy' : y ∉ s := hy
    simp [Set.indicator_apply, hx, hy']

private theorem mul_indicator_mem_supportedIn_of_isClopen {X : Type} [TopologicalSpace X] {U s : Set X} (hs : IsClopen s)
    {F : X → ℂ} (hF : F ∈ supportedIn U) : F * s.indicator 1 ∈ supportedIn U := by
  rw [mem_iff_lemma] at hF ⊢
  obtain ⟨⟨hlc, hcs⟩, hsub⟩ := hF
  exact ⟨⟨hlc.mul (isLocallyConstant_indicator_one_of_isClopen hs), hcs.mul_right⟩, (Function.support_mul_subset_left _ _).trans hsub⟩

theorem local_descent_holds : LocStep (k := k) := by
  classical
  unfold LocStep Kills
  intro m Z hCR ξ hsupp hinv hfib f hf
  haveI : NonarchimedeanRing k := by
    convert! (ValuativeRel.nonarchimedeanRing k)
    exact Valuation.toTopologicalSpace_eq _
  have hbasis : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  obtain ⟨q, hq_def⟩ : ∃ q : Sp k m → (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      q = fun p => pZ Z p.1 := ⟨_, rfl⟩
  have hq : Continuous q := by rw [hq_def]; exact (continuous_pZ Z).comp continuous_fst
  obtain ⟨⟨hflc, hfcs⟩, hfsub⟩ := (mem_iff_lemma _ _).1 hf
  have hfS : f ∈ supportedIn (univ : Set (Sp k m)) :=
    (mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, subset_univ _⟩
  have hloc : ∀ y, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsOpen O ∧ y ∈ O ∧
      ∀ W, IsClopen W → W ⊆ O → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro y
    obtain ⟨A, hA⟩ : ∃ A : Set (Sp k m → ℂ), A = {F | (∃ g ∈ Gz Z, ∃ h ∈ supportedIn (univ : Set (Sp k m)),
        F = h - fun p => h (act g p)) ∨ (F ∈ supportedIn (univ : Set (Sp k m)) ∧
        ∀ p ∈ (Bz Z ∩ pZ Z ⁻¹' {y}) ×ˢ (univ : Set (Fin m → k)), F p = 0)} := ⟨_, rfl⟩
    have hfJ : f ∈ Submodule.span ℂ A := by
      rcases hfib y with ⟨c, hcZ, hc⟩ | hB
      · refine Submodule.subset_span ?_
        rw [hA, Set.mem_setOf_eq]
        refine Or.inr ⟨hfS, fun p hp => ?_⟩
        by_contra hne
        have hpU := hfsub (Function.mem_support.mpr hne)
        have hZN : p.1 ∈ ZN Z := by
          simp only [ZN, Set.mem_setOf_eq]
          exact ⟨c, hcZ, hc p.1 hp.1.1 hp.1.2⟩
        exact (show p.1 ∉ ZN Z from hpU.2) hZN
      · by_contra hnot
        obtain ⟨l, hlf, hlJ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
        have hz : ∀ F ∈ Submodule.span ℂ A, l F = 0 := by
          intro F hF
          have h1 := Submodule.mem_map_of_mem (f := l) hF
          rw [hlJ] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        apply hlf
        refine hB l ?_ ?_ f ((mem_iff_lemma _ _).2 ⟨⟨hflc, hfcs⟩, fun p hp => (hfsub hp).1⟩)
        · intro F hF hvan
          exact hz F (Submodule.subset_span (by rw [hA, Set.mem_setOf_eq]; exact Or.inr ⟨hF, hvan⟩))
        · intro g hg F hF
          have h1 := hz _ (Submodule.subset_span
            (by rw [hA, Set.mem_setOf_eq]; exact Or.inl ⟨g, hg, F, hF, rfl⟩))
          rw [map_sub, sub_eq_zero] at h1
          exact h1.symm
    have hP : ∀ F ∈ Submodule.span ℂ A, ∃ O : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
        IsOpen O ∧ y ∈ O ∧ ∀ W, IsClopen W → W ⊆ O → ξ (F * (q ⁻¹' W).indicator 1) = 0 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        rw [hA, Set.mem_setOf_eq] at hF
        rcases hF with ⟨g, hg, h, hh, rfl⟩ | ⟨hrS, hvan⟩
        · refine ⟨univ, isOpen_univ, mem_univ _, fun W hW _ => ?_⟩
          have hqa : ∀ p, q (act g p) = q p := by
            intro p; rw [hq_def]; exact pZ_conj Z hg p.1
          set φ : Sp k m → ℂ := (q ⁻¹' W).indicator 1 with hφ
          have hφa : ∀ p, φ (act g p) = φ p := by
            intro p; simp only [hφ, Set.indicator_apply, Set.mem_preimage, hqa, Pi.one_apply]
          have hsplit : (h - fun p => h (act g p)) * φ = h * φ - fun p => (h * φ) (act g p) := by
            funext p
            simp only [Pi.mul_apply, Pi.sub_apply, hφa]
            ring
          rw [hsplit, map_sub, hinv g hg _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hh), sub_self]
        · obtain ⟨⟨hrlc, hrcs⟩, -⟩ := (mem_iff_lemma _ _).1 hrS
          have hsuppc : IsClosed (Function.support F) := by
            have h1 := (hrlc.isOpen_fiber 0).isClosed_compl
            have h2 : Function.support F = {x | F x = 0}ᶜ := by ext x; simp
            rw [h2]; exact h1
          have hKc : IsCompact (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k)))) :=
            IsCompact.of_isClosed_subset hrcs (hsuppc.inter ((isClosed_Bz Z).prod isClosed_univ))
              (inter_subset_left.trans (subset_tsupport F))
          have hKq := (hKc.image hq).isClosed
          refine ⟨(q '' (Function.support F ∩ (Bz Z ×ˢ (univ : Set (Fin m → k)))))ᶜ,
            hKq.isOpen_compl, ?_, fun W hW hWO => ?_⟩
          · rintro ⟨p, ⟨hpF, hpB⟩, hpy⟩
            refine (Function.mem_support.mp hpF) (hvan p ⟨⟨hpB.1, ?_⟩, mem_univ _⟩)
            rw [Set.mem_preimage, Set.mem_singleton_iff, ← hpy, hq_def]
          · refine hsupp _ (mul_indicator_mem_supportedIn_of_isClopen (hW.preimage hq) hrS) (fun p hp => ?_)
            by_cases hpW : q p ∈ W
            · have h0 : F p = 0 := by
                by_contra hne
                exact hWO hpW ⟨p, ⟨hne, hp⟩, rfl⟩
              simp [h0]
            · simp [Set.indicator_apply, hpW]
      | zero => exact ⟨univ, isOpen_univ, mem_univ _, fun W _ _ => by simp⟩
      | add F F' _ _ hF hF' =>
        obtain ⟨O, hO, hyO, hOW⟩ := hF
        obtain ⟨O', hO', hyO', hOW'⟩ := hF'
        exact ⟨O ∩ O', hO.inter hO', ⟨hyO, hyO'⟩, fun W hW hWO => by
          rw [add_mul, map_add, hOW W hW (hWO.trans inter_subset_left),
            hOW' W hW (hWO.trans inter_subset_right), add_zero]⟩
      | smul a F _ hF =>
        obtain ⟨O, hO, hyO, hOW⟩ := hF
        exact ⟨O, hO, hyO, fun W hW hWO => by rw [smul_mul_assoc, map_smul, hOW W hW hWO, smul_zero]⟩
    exact hP f hfJ
  choose O hO hyO hOW using hloc
  have hV : ∀ y, ∃ V : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      IsClopen V ∧ y ∈ V ∧ V ⊆ O y := fun y => by
    obtain ⟨V, hVB, hyV, hVO⟩ := hbasis.exists_subset_of_mem_open (hyO y) (hO y)
    exact ⟨V, hVB, hyV, hVO⟩
  choose V hVc hyV hVO using hV
  have hunion : ∀ B1 B2 : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k), IsClopen B1 →
      (∀ W, IsClopen W → W ⊆ B1 → ξ (f * (q ⁻¹' W).indicator 1) = 0) →
      (∀ W, IsClopen W → W ⊆ B2 → ξ (f * (q ⁻¹' W).indicator 1) = 0) →
      ∀ W, IsClopen W → W ⊆ B1 ∪ B2 → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro B1 B2 hB1 hQ1 hQ2 W hW hWB
    have hsplit : f * (q ⁻¹' W).indicator 1 =
        f * (q ⁻¹' (W ∩ B1)).indicator 1 + f * (q ⁻¹' (W \ B1)).indicator 1 := by
      funext p
      by_cases h1 : q p ∈ W <;> by_cases h2 : q p ∈ B1 <;> simp [Set.indicator_apply, h1, h2]
    rw [hsplit, map_add, hQ1 _ (hW.inter hB1) inter_subset_right,
      hQ2 _ (hW.diff hB1) (fun z hz => (hWB hz.1).resolve_left hz.2), add_zero]
  have hfin : ∀ t : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k),
      IsClopen (⋃ i ∈ t, V i) ∧
      ∀ W, IsClopen W → W ⊆ ⋃ i ∈ t, V i → ξ (f * (q ⁻¹' W).indicator 1) = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have he : (⋃ i ∈ (∅ : Finset (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k)), V i) = ∅ := by
        ext z; simp
      rw [he]
      refine ⟨isClopen_empty, fun W _ hW => ?_⟩
      have hW0 : W = ∅ := Set.subset_empty_iff.mp hW
      subst hW0
      have h0 : f * (q ⁻¹' (∅ : Set (Fin (2 * m + 1) × Fin (Module.finrank k Z) → k))).indicator 1 = 0 := by
        funext p; simp
      rw [h0, map_zero]
    | insert a s _ ih =>
      rw [Finset.set_biUnion_insert]
      exact ⟨(hVc a).union ih.1, hunion _ _ (hVc a)
        (fun W hW hWV => hOW a W hW (hWV.trans (hVO a))) ih.2⟩
  obtain ⟨t, ht⟩ := (IsCompact.image hfcs hq).elim_finite_subcover V (fun y => (hVc y).isOpen)
    (fun z _ => mem_iUnion.2 ⟨z, hyV z⟩)
  obtain ⟨hc, hQt⟩ := hfin t
  have heq : f * (q ⁻¹' (⋃ i ∈ t, V i)).indicator 1 = f := by
    funext p
    by_cases hp : f p = 0
    · simp [hp]
    · have hmem : q p ∈ ⋃ i ∈ t, V i := ht ⟨p, subset_tsupport f (Function.mem_support.mpr hp), rfl⟩
      rw [Pi.mul_apply, Set.indicator_of_mem (show p ∈ q ⁻¹' (⋃ i ∈ t, V i) from hmem),
        Pi.one_apply, mul_one]
  rw [← heq]
  exact hQt _ hc subset_rfl

end PositivityTheory.RgUd.T.LocStepPf
