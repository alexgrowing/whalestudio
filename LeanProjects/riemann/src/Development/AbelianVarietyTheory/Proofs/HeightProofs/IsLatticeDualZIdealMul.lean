import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CuspFormNormData

open NumberField Matrix Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

namespace GlobalTheory.CuspCharLattice

section General

variable {K : Type} [Field K] [NumberField K]

theorem exists_smul_mem {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {M : Submodule (𝓞 K) W}
    {x : W} (hx : x ∈ Submodule.span K (M : Set W)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨⟨e, he⟩, b, hb⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) a
    refine ⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero he), ?_⟩
    have hb' : algebraMap (𝓞 K) K b = e • a := hb
    have : (d * e) • a • x = b • d • x := by
      rw [mul_smul, ← smul_assoc e a x, ← hb', algebraMap_smul, smul_comm]
    rw [this]
    exact M.smul_mem _ hx

theorem exists_den {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ M, ∀ i, d • x i ∈ (1 : Submodule (𝓞 K) K) := by
  classical
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y h =>
    exact Submodule.mem_one.2 (hy _ (Finset.mem_image.2 ⟨(y, i), by simpa using h, rfl⟩))
  | zero => simp
  | add y z _ _ hy hz => rw [Pi.add_apply, smul_add]; exact add_mem hy hz
  | smul a y _ hy => rw [Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy

end General

variable {R : Ranks} {H : Host R} {n : ℕ}

theorem isLattice_dualZ (Y : Submodule (𝓞 H.E) (V H n))
    (h1 : ∀ i, ∃ c : H.E, c ≠ 0 ∧ (Pi.single i c : V H n) ∈ Y)
    (h2 : ∃ d : 𝓞 H.E, d ≠ 0 ∧ ∀ x ∈ Y, ∀ i, d • x i ∈ (1 : Submodule (𝓞 H.E) H.E)) :
    Submodule.IsLattice H.E (dualZ Y) := by
  classical
  refine ⟨?_, ?_⟩
  · choose c hc hcY using h1
    let J : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E := fun i =>
      FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton _ (c i))
    have hfg : (Submodule.pi Set.univ fun i => (J i : Submodule (𝓞 H.E) H.E)).FG :=
      Submodule.fg_pi fun i => FractionalIdeal.fg_of_isNoetherianRing le_rfl (J i)
    refine Submodule.FG.of_le hfg fun y hy i _ => ?_
    change y i ∈ J i
    rw [FractionalIdeal.mem_dual (FractionalIdeal.spanSingleton_ne_zero_iff.2 (hc i))]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    obtain ⟨z, hz⟩ := hy _ (Y.smul_mem o (hcY i))
    refine ⟨z, ?_⟩
    rw [← Pi.single_smul, dotProduct_single] at hz
    rw [Algebra.traceForm_apply, hz]
    simp
  · obtain ⟨d, hd, h⟩ := h2
    have hd' : algebraMap (𝓞 H.E) H.E d ≠ 0 := by simpa using hd
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hm : (Pi.single i (algebraMap (𝓞 H.E) H.E d) : V H n) ∈ dualZ Y := by
      intro y hy
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h y hy i)
      rw [single_dotProduct, ← Algebra.smul_def, ← hb]
      have hi : IsIntegral ℤ (Algebra.trace ℚ H.E (algebraMap (𝓞 H.E) H.E b)) :=
        Algebra.isIntegral_trace b.2
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
      exact ⟨z, by rw [← hz]; simp⟩
    have : (Pi.single i (x i) : V H n) = (x i / algebraMap (𝓞 H.E) H.E d) •
        (Pi.single i (algebraMap (𝓞 H.E) H.E d) : V H n) := by
      rw [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ hd']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem isLattice_dualZ_idealMul (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) (h𝔞 : 𝔞 ≠ 0)
    (N : Submodule (𝓞 H.E) (V H n)) (hN : N.FG)
    (hs : ∀ v : V H n, ∃ d : 𝓞 H.E, d ≠ 0 ∧ d • v ∈ N) :
    Submodule.IsLattice H.E (dualZ (idealMul 𝔞 N)) := by
  classical
  refine isLattice_dualZ _ (fun i => ?_) ?_
  · obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔞, a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h𝔞 (FractionalIdeal.eq_zero_iff.2 hc)
    obtain ⟨d, hd, hv⟩ := hs (Pi.single i 1)
    have hd' : algebraMap (𝓞 H.E) H.E d ≠ 0 := by simpa using hd
    refine ⟨a * algebraMap (𝓞 H.E) H.E d, mul_ne_zero ha0 hd',
      Submodule.subset_span ⟨a, ha, _, hv, ?_⟩⟩
    rw [← Pi.single_smul, ← Pi.single_smul, Algebra.smul_def d, mul_one, smul_eq_mul]
  · obtain ⟨d, hd, h⟩ := exists_den hN
    obtain ⟨e, he, hA⟩ := 𝔞.isFractional
    refine ⟨e * d, mul_ne_zero (nonZeroDivisors.ne_zero he) hd, fun x hx i => ?_⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hy
      obtain ⟨b, hb⟩ := hA a ha
      obtain ⟨b', hb'⟩ := Submodule.mem_one.1 (h v hv i)
      refine Submodule.mem_one.2 ⟨b * b', ?_⟩
      rw [map_mul, hb, hb', Pi.smul_apply, smul_eq_mul, smul_mul_smul_comm]
    | zero => simp
    | add y z _ _ hy hz => rw [Pi.add_apply, smul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy

theorem host_AA_ne_zero (H : Host R) : H.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact H.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := H.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem isLattice_X : ∀ (D : Formalism.BasicNotions.D7) (j : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants.Lift D.R) (c : GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree.CuspGeom D j),
    Submodule.IsLattice D.host.E c.X := by
  intro D j c
  letI := D.host.cmStar
  have hl := c.lat_lat
  refine isLattice_dualZ_idealMul _ (host_AA_ne_zero D.host) c.N ?_ fun v => ?_
  · refine Submodule.fg_of_fg_map_injective (c.frame.restrictScalars (𝓞 D.host.E)) c.frame_inj ?_
    exact Submodule.FG.of_le hl.fg (Submodule.map_comap_le _ _)
  · obtain ⟨d, hd, h⟩ := exists_smul_mem (M := c.lat) (x := c.frame v) (by rw [hl.span_eq_top]; trivial)
    refine ⟨d, hd, ?_⟩
    change (c.frame.restrictScalars (𝓞 D.host.E)) (d • v) ∈ c.lat
    rw [map_smul]
    exact h

end GlobalTheory.CuspCharLattice
