import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem im_form {K : Type} [Field K] {τ : K} (x y : Etau K τ) :
    (x * star y).im = x.im * y.re - x.re * y.im := by
  simp; ring

private theorem smul_im' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).im = algebraMap O K r * x.im := by
  rw [QuadraticAlgebra.im_smul, Algebra.smul_def]

private theorem smul_re' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).re = algebraMap O K r * x.re := by
  rw [QuadraticAlgebra.re_smul, Algebra.smul_def]

private theorem fix_lat {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {τ t : K} {S : Set (Etau K τ)} (h : IsFixP O τ t S) : IsLat O τ S := by
  classical
  obtain ⟨s, hs⟩ := h.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.image (fun x : Etau K τ => t * x.im) ∪ s.image (fun x : Etau K τ => t * x.re))
  set B : K := algebraMap O K (b : O) with hBdef
  have hB : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have key : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)),
      t * x.im * B ∈ (algebraMap O K).range ∧ t * x.re * B ∈ (algebraMap O K).range := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r1, hr1⟩ := hb (t * x.im) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      obtain ⟨r2, hr2⟩ := hb (t * x.re) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
      refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩⟩
      · rw [hr1, Algebra.smul_def, hBdef]
        ring
      · rw [hr2, Algebra.smul_def, hBdef]
        ring
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · have e := add_mem hx.1 hy.1
        convert e using 1
        simp only [QuadraticAlgebra.im_add]
        ring
      · have e := add_mem hx.2 hy.2
        convert e using 1
        simp only [QuadraticAlgebra.re_add]
        ring
    | smul r x _ hx =>
      rw [smul_im', smul_re']
      refine ⟨?_, ?_⟩
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.1
        convert e using 1
        ring
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.2
        convert e using 1
        ring
  have m1 : B • (1 : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (1 : Etau K τ))).im = x.im * B := by
      rw [im_form]
      simp
    rw [e, ← mul_assoc]
    exact (key x hx).1
  have m2 : B • (ω : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (ω : Etau K τ))).im = -(x.re * B) := by
      rw [im_form]
      simp
    rw [e, mul_neg, ← mul_assoc]
    exact neg_mem (key x hx).2
  refine ⟨h.fg, ?_⟩
  rw [eq_top_iff]
  intro y _
  have e : y = (y.re / B) • (B • (1 : Etau K τ)) + (y.im / B) • (B • (ω : Etau K τ)) := by
    ext <;> simp <;> field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span m1))
    (Submodule.smul_mem _ _ (Submodule.subset_span m2))

private theorem dual_pair {O K : Type} [CommRing O] [Field K] [Algebra O K]
    {τ : K} (u v : Etau K τ) (hd : u.im * v.re - u.re * v.im ≠ 0) (y : Etau K τ) :
    y ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)) ↔
      ∀ x ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)),
        (u.im * v.re - u.re * v.im)⁻¹ * (x * star y).im ∈ (algebraMap O K).range := by
  constructor
  · intro hy x hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.1 hy
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hx
    refine ⟨p * s - q * r, ?_⟩
    rw [im_form]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, smul_im', smul_re',
      map_sub, map_mul]
    field_simp
    ring
  · intro H
    obtain ⟨β, hβ⟩ := H u (Submodule.subset_span (by simp))
    obtain ⟨α, hα⟩ := H v (Submodule.subset_span (by simp))
    rw [im_form] at hα hβ
    refine Submodule.mem_span_pair.2 ⟨-α, β, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, smul_re', map_neg, hα, hβ]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, smul_im', map_neg, hα, hβ]
      field_simp
      ring

theorem UpperTheory.isLattice_iff_fixedPoint_quadraticTorus :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ S : Set (Etau K τ), (∀ t : K, IsFixP O τ t S → IsLat O τ S) ∧ (IsLat O τ S → (∀ y ∈ S, ω * y ∈ S) → ∃ t : K, t ≠ 0 ∧ IsFixP O τ t S) := by
  intro O K _ _ _ _ _ Δ τ hL hτ S
  haveI := hL.frac
  refine ⟨fun t h => fix_lat h, fun hS hst => ?_⟩
  obtain ⟨y, x, hx, -, -, e⟩ := latCls O K Δ τ hL hτ S hS
  have e' : S = (Submodule.span O {(y : Etau K τ), (y : Etau K τ) * x} : Submodule O (Etau K τ)) := by
    rw [e]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨p, q, rfl⟩, rfl⟩
      exact ⟨p, q, by simp [mul_add]⟩
    · rintro ⟨p, q, rfl⟩
      exact ⟨_, ⟨p, q, rfl⟩, by simp [mul_add]⟩
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := (isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  have hd : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im ≠ 0 := by
    have : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im =
        -(QuadraticAlgebra.norm (y : Etau K τ) * x.im) := by
      simp [norm_def]; ring
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero hn hx)
  refine ⟨_, inv_ne_zero hd, hS.fg, fun w => ?_, hst⟩
  rw [e']
  exact dual_pair _ _ hd w
