import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem locConst_of_factor {X Y Z : Type} [TopologicalSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (h : X → Z) (H : ∀ x y, f x = f y → h x = h y) : IsLocallyConstant h := by
  intro s
  have e : h ⁻¹' s = f ⁻¹' (f '' (h ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      show h x ∈ s
      rw [← H y x hyx]
      exact hy
  rw [e]
  exact hf _

private theorem algebraMap_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : algebraMap C (lauSub P) c ∈ vertex h ^ N := by
  have hle : Ideal.map (algebraMap C (lauSub P)) (maximalIdeal C) ≤ vertex h := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, mem_vertex]
    refine ⟨c, hc, ?_⟩
    show _ = (AddMonoidAlgebra.single 0 (algebraMap C K c)).coeff 0
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hm := Ideal.mem_map_of_mem (algebraMap C (lauSub P)) hc
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle N hm

private theorem single_mem_vertex_pow {C K : Type} [CommRing C] [CommRing K] [Algebra C K] [IsLocalRing C]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (d : ℤ) (M : Submodule C K)
    (hM : M ≤ P d) {x : K} (hx : x ∈ maximalIdeal C ^ N • M) :
    ∃ p ∈ vertex h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d x := by
  refine Submodule.smul_induction_on
    (p := fun y => ∃ p ∈ vertex h ^ N, (p : lauSub P).1 = AddMonoidAlgebra.single d y) hx ?_ ?_
  · intro c hc m hm
    refine ⟨algebraMap C (lauSub P) c * ⟨AddMonoidAlgebra.single d m, single_mem_lauSub P (hM hm)⟩,
      Ideal.mul_mem_right _ _ (algebraMap_mem_vertex_pow h N hc), ?_⟩
    rw [Subalgebra.coe_mul]
    show AddMonoidAlgebra.single 0 (algebraMap C K c) * AddMonoidAlgebra.single d m = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, Algebra.smul_def]
  · rintro x y ⟨p, hp, hpx⟩ ⟨q, hq, hqy⟩
    exact ⟨p + q, add_mem hp hq, by rw [Subalgebra.coe_add, hpx, hqy, AddMonoidAlgebra.single_add]⟩

theorem UpperTheory.V.Fr.alg_cont :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → ∀ (h : HasVertex (ρ.part C)) (ρD : NRep F n (lauSub (ρ.part C))), (∀ g i j, (ρD.r g i j).1 = AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j)) → (∀ v i g, (ρD.ψ v i g : lauSub (ρ.part C)).1 = AddMonoidAlgebra.single 0 (ρ.ψ v i g : K)) → ρD.Cont (vertex h) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hc h ρD hr hψ
  refine ⟨fun i j N => ?_, fun v i N => ?_⟩
  · refine locConst_of_factor (hc.cont i j N) _ fun g g' hgg => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hgg
    have hS : Submodule.span C (Set.range fun g => ρ.r g i j) ≤ ρ.part C (w n i - w n j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g0, rfl⟩
      exact NRep.r_mem_part C ρ g0 i j
    obtain ⟨p, hp, hpe⟩ := single_mem_vertex_pow h N (w n i - w n j) _ hS hgg
    rw [Ideal.Quotient.eq]
    have e : ρD.r g i j - ρD.r g' i j = p := by
      apply Subtype.ext
      rw [hpe, AddSubgroupClass.coe_sub, hr, hr, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hp
  · obtain ⟨χ, hχ, hχe⟩ := hc.psi
    refine locConst_of_factor ((hχ v i).1 N) _ fun g g' hgg => ?_
    rw [Ideal.Quotient.eq] at hgg ⊢
    have hm := algebraMap_mem_vertex_pow h N hgg
    have e : (↑(ρD.ψ v i g) : lauSub (ρ.part C)) - ↑(ρD.ψ v i g') =
        algebraMap C (lauSub (ρ.part C)) (χ v i g - χ v i g') := by
      apply Subtype.ext
      rw [AddSubgroupClass.coe_sub, hψ, hψ]
      show _ = AddMonoidAlgebra.single 0 (algebraMap C K (χ v i g - χ v i g'))
      rw [map_sub, hχe, hχe, AddMonoidAlgebra.single_sub]
    rw [e]
    exact hm
