import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

private theorem sum_matrix_single_diag_one_eq_one {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] :
    ∑ i : n, Matrix.single i i (1 : F) = 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
    have he : (Finset.univ.filter fun w : n => w = u ∧ w = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨rfl, rfl⟩
      exact h rfl
    rw [he]
    simp

private theorem intertwiner_of_ker {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (ht : ∀ B : Matrix (d t) (d t) F, ∃ x ∈ S, x t = B)
    (hk : ∀ x ∈ S, x t = 0 → x s = 0) :
    ∃ V : Matrix (d s) (d t) F, V ≠ 0 ∧ ∀ x ∈ S, x s * V = V * x t := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x t = y t → x s = y s := by
    intro x hx y hy h
    have := hk (x - y) (S.sub_mem hx hy) (by rw [Pi.sub_apply, h, sub_self])
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨i0⟩ := (inferInstance : Nonempty (d t))
  choose xx hxS hxt using fun j => ht (Matrix.single j i0 (1 : F))
  choose z hzS hzt using fun j => ht (Matrix.single i0 j (1 : F))
  have hne : xx i0 s ≠ 0 := by
    intro h0
    have hx0 : ∀ j, xx j s = 0 := by
      intro j
      have := key (xx j * xx i0) (S.mul_mem (hxS j) (hxS i0)) (xx j) (hxS j)
        (by rw [Pi.mul_apply, hxt, hxt, Matrix.single_mul_single_same, one_mul])
      rw [← this, Pi.mul_apply, h0, mul_zero]
    have h1 := key (∑ j, xx j * z j) (Subalgebra.sum_mem _ fun j _ => S.mul_mem (hxS j) (hzS j)) 1 S.one_mem
      (by
        rw [Finset.sum_apply]
        simp only [Pi.mul_apply, hxt, hzt, Matrix.single_mul_single_same, one_mul, Pi.one_apply]
        exact sum_matrix_single_diag_one_eq_one)
    rw [Finset.sum_apply] at h1
    simp only [Pi.mul_apply, hx0, zero_mul, Finset.sum_const_zero, Pi.one_apply] at h1
    exact zero_ne_one h1
  obtain ⟨a, b, hab⟩ : ∃ a b, xx i0 s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨Matrix.of fun u j => xx j s u b, ?_, ?_⟩
  · intro hV
    apply hab
    have := congrFun (congrFun hV a) i0
    simpa using this
  · intro x hx
    ext u k
    have e := key (x * xx k) (S.mul_mem hx (hxS k)) (∑ j, x t j k • xx j)
      (Subalgebra.sum_mem _ fun j _ => S.smul_mem (hxS j) _) (by
        rw [Pi.mul_apply, hxt, Finset.sum_apply]
        simp only [Pi.smul_apply, hxt]
        ext p q
        by_cases hq : i0 = q <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, hq])
    have e2 := congrFun (congrFun e u) b
    simp only [Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [e2]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem separate {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (hs : ∀ B : Matrix (d s) (d s) F, ∃ x ∈ S, x s = B)
    (hk : ∃ x ∈ S, x t = 0 ∧ x s ≠ 0) : ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
  obtain ⟨x, hxS, hxt, hxs⟩ := hk
  obtain ⟨a, b, hab⟩ : ∃ a b, x s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxs (Matrix.ext h)
  choose p hpS hps using fun i => hs (Matrix.single i a (x s a b)⁻¹)
  choose q hqS hqs using fun i => hs (Matrix.single b i (1 : F))
  refine ⟨∑ i, p i * x * q i, ?_, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun i _ => S.mul_mem (S.mul_mem (hpS i) hxS) (hqS i)
  · rw [Finset.sum_apply]
    simp [Pi.mul_apply, hxt]
  · rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hps, hqs, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    ext u v
    by_cases h : u = v
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
      have he : (Finset.univ.filter fun w : d s => w = u ∧ w = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨rfl, rfl⟩
        exact h rfl
      rw [he]
      simp

theorem UpperTheory.V.AlgebraTools.density_prod :
    ∀ {F Γ : Type} [Field F] [Monoid Γ] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (ρ : ∀ s, Γ →* Matrix (d s) (d s) F), (∀ s, Submodule.span F (Set.range (ρ s)) = ⊤) → (∀ s t, s ≠ t → ∀ V : Matrix (d s) (d t) F, (∀ g, ρ s g * V = V * ρ t g) → V = 0) → Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) = ⊤ := by
  intro F Γ _ _ σ _ _ d _ _ _ ρ hspan hint
  let φ : Γ →* ((s : σ) → Matrix (d s) (d s) F) :=
    { toFun := fun g s => ρ s g
      map_one' := funext fun s => map_one (ρ s)
      map_mul' := fun g h => funext fun s => map_mul (ρ s) g h }
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra F ((s : σ) → Matrix (d s) (d s) F),
      S = Algebra.adjoin F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) := ⟨_, rfl⟩
  have hmem : ∀ g, (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F) ∈ S := by
    intro g
    rw [hSdef]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  have hsurj : ∀ s (B : Matrix (d s) (d s) F), ∃ x ∈ S, x s = B := by
    intro s B
    have hB : B ∈ Submodule.span F (Set.range (ρ s)) := by
      rw [hspan s]
      exact Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact ⟨_, hmem g, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, h1, e1⟩ := hy
      obtain ⟨x2, h2, e2⟩ := hz
      exact ⟨x1 + x2, S.add_mem h1 h2, by rw [Pi.add_apply, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, h1, e1⟩ := hy
      exact ⟨c • x1, S.smul_mem h1 c, by rw [Pi.smul_apply, e1]⟩
  have hsep : ∀ s t, s ≠ t → ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
    intro s t hst
    apply separate d S s t (hsurj s)
    by_contra hno
    push_neg at hno
    obtain ⟨V, hV0, hV⟩ := intertwiner_of_ker d S s t (hsurj t) hno
    exact hV0 (hint s t hst V fun g => hV _ (hmem g))
  have he : ∀ s, ∃ e ∈ S, e s = 1 ∧ ∀ t, t ≠ s → e t = 0 := by
    intro s
    have hT : ∀ T : Finset σ, s ∉ T → ∃ e ∈ S, e s = 1 ∧ ∀ t ∈ T, e t = 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, S.one_mem, rfl, by simp⟩
      | @insert t T htT ih =>
        intro hs
        rw [Finset.mem_insert, not_or] at hs
        obtain ⟨e, heS, hes, het⟩ := ih hs.2
        obtain ⟨y, hyS, hyt, hys⟩ := hsep s t hs.1
        refine ⟨e * y, S.mul_mem heS hyS, by rw [Pi.mul_apply, hes, hys, one_mul], ?_⟩
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [Pi.mul_apply, hyt, mul_zero]
        · rw [Pi.mul_apply, het u hu, zero_mul]
    obtain ⟨e, heS, hes, het⟩ := hT (Finset.univ.erase s) (by simp)
    exact ⟨e, heS, hes, fun t ht => het t (by simp [ht])⟩
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    choose e heS hes het using he
    choose zz hzS hzs using fun s => hsurj s (Y s)
    have hY : Y = ∑ s, zz s * e s := by
      funext u
      rw [Finset.sum_apply, Finset.sum_eq_single u]
      · rw [Pi.mul_apply, hzs, hes, mul_one]
      · intro b _ hb
        rw [Pi.mul_apply, het b u hb.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ u) h
    rw [hY]
    exact Subalgebra.sum_mem _ fun s _ => S.mul_mem (hzS s) (heS s)
  have h2 : Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) =
      Subalgebra.toSubmodule S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hmem g
    · rw [hSdef, Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      have hx' : x ∈ MonoidHom.mrange φ :=
        (Submonoid.closure_le.mpr (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_mrange.mpr ⟨g, rfl⟩)) hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hx'
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [h2, htop]
  simp
