import Formalism.SharpRestriction.GrowthBounds.RootWeights.HomLatticeDividedPowerStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem equivariant_intertwines_monoid (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    {u : Module.End K V} (hu : u ∈ Umon E) : ∃ u' ∈ Umon E', ∀ y, T (u y) = u' (T y) :=  by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    exact ⟨E' a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun z => hT a b z⟩
  | one => exact ⟨1, one_mem _, fun z => rfl⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hy''⟩ := hy
    obtain ⟨z', hz', hz''⟩ := hz
    refine ⟨y' * z', mul_mem hy' hz', fun w => ?_⟩
    show T (y (z w)) = y' (z' (T w))
    rw [hy'', hz'']

theorem equivariant_image_highest_vector (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (h0 : T v ≠ 0) : IsHWV E' mu (T v) :=  by
  obtain ⟨hv0, hvw, hvh⟩ := hv
  refine ⟨h0, ?_, fun a b hab => ?_⟩
  · rw [mem_weightSp_iff_diagonal_apply] at hvw ⊢
    intro a
    rw [← hT, hvw a, map_smul]
  · rw [← hT, hvh a b hab, map_zero]

theorem equivariant_maps_isotypic (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    (mu : Fin n → ℤ) : ∀ x ∈ isoSub E mu, T x ∈ isoSub E' mu :=  by
  intro x hx
  have hle : isoSub E mu ≤ (isoSub E' mu).comap T := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    obtain ⟨u', hu', hT'⟩ := equivariant_intertwines_monoid E E' T hT hu
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [hT']
    by_cases h0 : T v = 0
    · rw [h0, map_zero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨u', hu', T v, equivariant_image_highest_vector E E' T hT mu v hv h0, rfl⟩
  exact hle hx

theorem highest_vector_mem_isotypic (E : GLOps n K V) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) : v ∈ isoSub E mu := by
  unfold isoSub
  exact Submodule.subset_span ⟨1, one_mem _, v, hv, rfl⟩

end

private theorem E_apply_mem_weightSp_add_rootW_of_isGLRep {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) (a b : Fin n) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSp_iff_diagonal_apply] at hx ⊢
  intro c
  have h1 := congrArg (fun F : Module.End K V => F x) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  rcases eq_or_ne c a with rfl | hca <;> rcases eq_or_ne c b with rfl | hcb
  · simp
  · simp [hcb, hcb.symm, add_smul]
    abel
  · simp [hca, add_smul]
    abel
  · simp [hca, hcb, hcb.symm]

private theorem E_apply_mem_isoSub_of_mem {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) : ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  intro x hx
  have hle : isoSub E mu ≤ (isoSub E mu).comap (E a b) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨E a b * u, mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, rfl⟩
  exact hle hx

theorem isotypic_submodules_span_top (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicSubmodulesSpanTop := by
  classical
  intro n K V _ _ _ _ _ E hE
  set S : Submodule K V := ⨆ mu, isoSub E mu with hSdef
  have hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => E a b x ∈ S) hx ?_ ?_ ?_
    · intro mu y hy
      exact (le_iSup (fun mu => isoSub E mu) mu) (E_apply_mem_isoSub_of_mem E mu a b y hy)
    · rw [map_zero]
      exact S.zero_mem
    · intro y z hy hz
      rw [map_add]
      exact S.add_mem hy hz
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE S hS
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨s, π, hπ, hπW, hbot, hπwt, hsum⟩ := weight_projections_exist E hE
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let T : Finset (Fin n → ℤ) := s.filter (fun mu => ∃ y ∈ W', y ≠ 0 ∧ y ∈ weightSp E mu)
    have hT : T.Nonempty := by
      by_contra hTe
      rw [Finset.not_nonempty_iff_eq_empty] at hTe
      apply hw0
      rw [← hsum w]
      apply Finset.sum_eq_zero
      intro mu hmu
      by_contra hne0
      have hmT : mu ∈ T := Finset.mem_filter.mpr
        ⟨hmu, π mu w, hπW mu W' (fun a y hy => hW' a a y hy) w hwW, hne0, hπwt mu w⟩
      rw [hTe] at hmT
      exact Finset.notMem_empty _ hmT
    obtain ⟨mu, hmuT, hmin⟩ := T.exists_min_image (fun nu => ∑ i : Fin n, (i.val : ℤ) * nu i) hT
    obtain ⟨hmus, v, hvW, hv0, hvw⟩ := Finset.mem_filter.mp hmuT
    have hhw : IsHWV E mu v := by
      refine ⟨hv0, hvw, fun a b hab => ?_⟩
      by_contra hne1
      have hmem : E a b v ∈ weightSp E (mu + rootW a b) := E_apply_mem_weightSp_add_rootW_of_isGLRep E hE mu v hvw a b
      have hs' : mu + rootW a b ∈ s := by
        by_contra hns
        rw [hbot _ hns] at hmem
        exact hne1 ((Submodule.mem_bot K).mp hmem)
      have hT' : mu + rootW a b ∈ T := Finset.mem_filter.mpr ⟨hs', E a b v, hW' a b v hvW, hne1, hmem⟩
      have hle := hmin _ hT'
      have hcalc : ∑ i : Fin n, (i.val : ℤ) * (mu + rootW a b) i =
          (∑ i : Fin n, (i.val : ℤ) * mu i) + ((a.val : ℤ) - b.val) := by
        simp [rootW, Pi.single_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hab' : (a.val : ℤ) < b.val := by exact_mod_cast hab
      rw [hcalc] at hle
      linarith
    have hvS : v ∈ S := (le_iSup (fun mu => isoSub E mu) mu) (highest_vector_mem_isotypic E mu v hhw)
    have hvI : v ∈ S ⊓ W' := ⟨hvS, hvW⟩
    rw [hc.inf_eq_bot] at hvI
    exact hv0 ((Submodule.mem_bot K).mp hvI)
  rw [← hc.sup_eq_top, hW'bot, sup_bot_eq]

private theorem E_apply_eq_zero_of_isHWV_zero {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (v : V) (hv : IsHWV E 0 v) (a b : Fin n) :
    E a b v = 0 := by
  obtain ⟨hv0, hvw, hvh⟩ := hv
  have hvw' : ∀ c, E c c v = 0 := fun c => by rw [(mem_weightSp_iff_diagonal_apply E 0 v).mp hvw c]; simp
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact hvh a b hab
  · exact hvw' a
  have hne : a ≠ b := ne_of_gt hab
  have r1 : ∀ y, E b a (E a b y) = E a b (E b a y) + (E b b y - E a a y) := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 b a a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at h1
    rw [← h1]
    abel
  have r2 : ∀ y, E b b (E a b y) = E a b (E b b y) - E a b y := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 b b a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, if_neg hne.symm, zero_sub,
      LinearMap.neg_apply] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    abel
  have r3 : ∀ y, E a a (E a b y) = E a b (E a a y) + E a b y := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 a a a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, if_neg hne.symm, sub_zero] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    abel
  have hpow : ∀ (k : ℕ) (y : V), (E a b ^ (k + 1)) y = E a b ((E a b ^ k) y) := fun k y => by
    rw [pow_succ']
    rfl
  have H : ∀ k : ℕ, E b b ((E a b ^ k) v) - E a a ((E a b ^ k) v) = (-(2 * (k : K))) • (E a b ^ k) v := by
    intro k
    induction k with
    | zero => simp [hvw']
    | succ k ih =>
      rw [hpow, r2, r3]
      have e1 : E a b (E b b ((E a b ^ k) v)) - E a b ((E a b ^ k) v) -
          (E a b (E a a ((E a b ^ k) v)) + E a b ((E a b ^ k) v)) =
          E a b (E b b ((E a b ^ k) v) - E a a ((E a b ^ k) v)) - (2 : K) • E a b ((E a b ^ k) v) := by
        rw [map_sub, two_smul]
        abel
      rw [e1, ih, map_smul, ← sub_smul]
      congr 1
      push_cast
      ring
  have Ek : ∀ k : ℕ, E b a ((E a b ^ (k + 1)) v) = (-(((k : K) + 1) * k)) • (E a b ^ k) v := by
    intro k
    induction k with
    | zero =>
      rw [hpow, r1]
      simp [hvh b a hab, hvw']
    | succ k ih =>
      rw [hpow (k + 1), r1, ih, H (k + 1), map_smul, ← hpow k, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hfv
  have hall : ∀ k, (E a b ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hv0
    | succ k ih =>
      intro h0
      cases k with
      | zero =>
        apply hfv
        simpa using h0
      | succ m =>
        have h1 := Ek (m + 1)
        rw [h0, map_zero] at h1
        have hc : (-((((m + 1 : ℕ) : K) + 1) * ((m + 1 : ℕ) : K))) ≠ 0 := by
          have h2 : ((m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have h3 : ((m + 1 : ℕ) : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
          exact neg_ne_zero.mpr (mul_ne_zero h3 h2)
        exact ih ((smul_eq_zero.mp h1.symm).resolve_left hc)
  have heig : ∀ k : ℕ, (E b b - E a a).HasEigenvector (-(2 * (k : K))) ((E a b ^ k) v) := by
    intro k
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, LinearMap.sub_apply]
    exact ⟨H k, hall k⟩
  have hinj : Function.Injective (fun k : ℕ => -(2 * (k : K))) := by
    intro k j hkj
    simpa using hkj
  have hli := Module.End.eigenvectors_linearIndependent' (E b b - E a a) (fun k : ℕ => -(2 * (k : K))) hinj
    (fun k => (E a b ^ k) v) heig
  have := hli.finite
  exact not_finite ℕ

theorem isotypic_zero_killed_by_operators {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V) (hE : IsGLRep E) (x : V) (hx : x ∈ isoSub E 0) (a b : Fin n) : E a b x = 0 :=  by
  have hle : isoSub E 0 ≤ LinearMap.ker (E a b) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    have hP : u v = v ∨ u v = 0 := by
      have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
      clear hu
      induction hu' using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨⟨c, d⟩, rfl⟩ := hy
        exact Or.inr (E_apply_eq_zero_of_isHWV_zero E hE v hv c d)
      | one => exact Or.inl rfl
      | mul y z _ _ hy hz =>
        rcases hz with hz | hz
        · show y (z v) = v ∨ y (z v) = 0
          rw [hz]
          exact hy
        · right
          show y (z v) = 0
          rw [hz, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hP with h | h <;> rw [h]
    · exact E_apply_eq_zero_of_isHWV_zero E hE v hv a b
    · exact map_zero _
  exact hle hx

theorem invariant_projection_exists (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionExists :=  by
  intro n K V _ _ _ _ _ E hE
  set Inv : Submodule K V := ⨅ a, ⨅ b, LinearMap.ker (E a b) with hInvdef
  have hInvmem : ∀ x, x ∈ Inv ↔ ∀ a b, E a b x = 0 := by
    intro x
    simp [Inv, Submodule.mem_iInf]
  have hInvS : ∀ a b, ∀ x ∈ Inv, E a b x ∈ Inv := by
    intro a b x hx
    rw [(hInvmem x).mp hx a b]
    exact Inv.zero_mem
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE Inv hInvS
  refine ⟨Inv.projection W' hc, ?_⟩
  have hPE : ∀ c d y, Inv.projection W' hc (E c d y) = 0 := by
    intro c d y
    have hy := Submodule.projection_add_projection_eq_self hc y
    rw [← hy, map_add, (hInvmem _).mp (Submodule.projection_apply_mem hc y) c d, zero_add]
    exact (Submodule.projection_apply_eq_zero_iff hc).mpr
      (hW' c d _ (Submodule.projection_apply_mem hc.symm y))
  unfold IsInvProj IsIsoProj
  refine ⟨fun x hx => ?_, fun mu hmu x hx => ?_⟩
  · exact Submodule.projection_apply_of_mem_left hc ((hInvmem x).mpr (fun a b => isotypic_zero_killed_by_operators E hE x hx a b))
  · have hle : isoSub E mu ≤ LinearMap.ker (Inv.projection W' hc) := by
      unfold isoSub
      rw [Submodule.span_le]
      rintro y ⟨u, hu, v, hv, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      have hQ : u = 1 ∨ ∀ z, Inv.projection W' hc (u z) = 0 := by
        have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
        clear hu
        induction hu' using Submonoid.closure_induction with
        | mem y hy =>
          obtain ⟨⟨c, d⟩, rfl⟩ := hy
          exact Or.inr (hPE c d)
        | one => exact Or.inl rfl
        | mul y z _ _ hy hz =>
          rcases hy with rfl | hy
          · rw [one_mul]
            exact hz
          · right
            intro w
            exact hy (z w)
      rcases hQ with rfl | hQ
      · obtain ⟨c, hc0⟩ : ∃ c, mu c ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hmu (funext hcon)
        have hvw := (mem_weightSp_iff_diagonal_apply E mu v).mp hv.2.1 c
        have hK : (mu c : K) ≠ 0 := Int.cast_ne_zero.mpr hc0
        have hv' : v = ((mu c : K))⁻¹ • E c c v := by
          rw [hvw, smul_smul, inv_mul_cancel₀ hK, one_smul]
        rw [Module.End.one_apply, hv', map_smul, hPE, smul_zero]
      · exact hQ v
    exact hle hx

theorem equivariant_commutes_isotypic (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : EquivariantCommutesInvariantProjection :=  by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE' T hT P P' hP hP' x
  have htop := isotypic_submodules_span_top D h2 n K V E hE
  have hx : x ∈ ⨆ mu, isoSub E mu := by
    rw [htop]
    trivial
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => T (P x) = P' (T x)) hx ?_ ?_ ?_
  · intro mu y hy
    by_cases hmu : mu = 0
    · subst hmu
      rw [hP.1 y hy, hP'.1 (T y) (equivariant_maps_isotypic E E' T hT 0 y hy)]
    · rw [hP.2 mu hmu y hy, map_zero, hP'.2 mu hmu (T y) (equivariant_maps_isotypic E E' T hT mu y hy)]
  · simp
  · intro y z hy hz
    simp only [map_add]
    rw [hy, hz]

theorem invariant_projection_range_trivial (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (P : Module.End K V)
    (hP : IsInvProj E P) (x : V) : P x ∈ isoSub E 0 :=  by
  have htop := isotypic_submodules_span_top D h2 n K V E hE
  have hx : x ∈ ⨆ mu, isoSub E mu := by
    rw [htop]
    trivial
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => P x ∈ isoSub E 0) hx ?_ ?_ ?_
  · intro mu y hy
    by_cases hmu : mu = 0
    · subst hmu
      rw [hP.1 y hy]
      exact hy
    · rw [hP.2 mu hmu y hy]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem invariant_projection_kills_operators (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : OperatorsKillInvariantProjection := by
  intro n K V _ _ _ _ _ E hE P hP x a b
  exact isotypic_zero_killed_by_operators E hE _ (invariant_projection_range_trivial D h2 E hE P hP x) a b

end Formalism.MainNotions.G.GLWeightTheory
