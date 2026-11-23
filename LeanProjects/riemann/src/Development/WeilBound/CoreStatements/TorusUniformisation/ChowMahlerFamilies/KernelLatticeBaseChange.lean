import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.KernelLatticeBaseChange

section Span

variable {o C : Type} [CommRing o] [Field C] [Algebra o C] {RC : Subalgebra o C}
  {A B : Type} [AddCommGroup A] [Module C A] [AddCommGroup B] [Module C B]

theorem mem_span {S : Set A} {e : A} (he : e ∈ S) : e ∈ spanOver RC S :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, e, he, (one_smul _ _).symm⟩

theorem smul_mem {S : Set A} {a : C} (ha : a ∈ RC) {x : A} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, RC.mul_mem ha hc, e, he, (mul_smul _ _ _).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem map_mem (T : A →ₗ[C] B) {S : Set A} {S' : Set B} (h : ∀ e ∈ S, T e ∈ spanOver RC S')
    {x : A} (hx : x ∈ spanOver RC S) : T x ∈ spanOver RC S' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    rw [map_smul]
    exact smul_mem hc (h e he)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

end Span

theorem exists_section {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {V Z : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Z] [Module Ω Z]
    (Δ : AddSubgroup (V × Z)) (M : AddSubgroup V) (U : Submodule Ω V) (N : ℕ)
    (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) (hM : LocFree R N M) (hU : Summand M U)
    (hs : ∀ g ∈ M, g ∈ U → ∃ m, (g, m) ∈ Δ) :
    ∃ σ : V →ₗ[Ω] Z, ∀ v ∈ M, v ∈ U → (v, σ v) ∈ Δ := by
  let L : Submodule R V := { M with smul_mem' := fun a e he => hM.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L) (r := N) hM
  obtain ⟨ρ, h1, h2, h3⟩ := hU
  have hz : ∀ i, ∃ z : Z, (ρ (v i : V), z) ∈ Δ := fun i => hs _ (h3 _ (v i).2) (h1 _)
  choose z hz using hz
  refine ⟨∑ i, (φ i).smulRight (z i), fun e he heU => ?_⟩
  have h4 := congrArg ρ (hv e)
  rw [h2 e heU, map_sum] at h4
  simp only [map_smul] at h4
  have : (e, (∑ i, (φ i).smulRight (z i)) e) = ∑ i, φ i e • (ρ (v i : V), z i) := by
    ext
    · simp [Prod.fst_sum, h4]
    · simp [Prod.snd_sum]
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => hΔ _ (hφ i e he) _ (hz i)

section BC

variable {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C]

theorem bc_apply {ι : Type} (x : ι → Ω) (j : ι) : bcMap Ω C ι x j = algebraMap Ω C (x j) := rfl

theorem exists_lift {ι κ : Type} [Fintype ι] (T : (ι → Ω) →ₗ[Ω] (κ → Ω)) :
    ∃ S : (ι → C) →ₗ[C] (κ → C), ∀ v, S (bcMap Ω C ι v) = bcMap Ω C κ (T v) := by
  classical
  refine ⟨Fintype.linearCombination C fun x => bcMap Ω C κ (T (Pi.single x 1)), fun v => ?_⟩
  conv_rhs => rw [pi_eq_sum_univ' v]
  rw [Fintype.linearCombination_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, map_smul, bc_apply, algebraMap_smul]

theorem key {o : Type} [CommRing o] [Algebra o C] (RC : Subalgebra o C) {ι κ : Type} [Fintype ι]
    (Δ : AddSubgroup ((ι → Ω) × (κ → Ω))) (M : AddSubgroup (ι → Ω)) (U : Submodule Ω (ι → Ω))
    (hU : Summand M U) (σ : (ι → Ω) →ₗ[Ω] (κ → Ω)) (hσ : ∀ v ∈ M, v ∈ U → (v, σ v) ∈ Δ)
    (hσ' : ∀ x ∈ Δ, x.1 ∈ M ∧ (x.1, σ x.1) ∈ Δ) {x : (ι → C) × (κ → C)}
    (hx : x ∈ spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) '' Δ))
    (hxU : x.1 ∈ Submodule.span C (bcMap Ω C ι '' U)) :
    x ∈ spanOver RC (Prod.map (bcMap Ω C ι) (bcMap Ω C κ) '' {y | y ∈ Δ ∧ y.1 ∈ U}) := by
  obtain ⟨ρ, h1, h2, h3⟩ := hU
  obtain ⟨ρc, hρc⟩ := exists_lift (C := C) ρ
  obtain ⟨σc, hσc⟩ := exists_lift (C := C) σ
  have a2 : ∀ y ∈ Submodule.span C (bcMap Ω C ι '' U), ρc y = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [hρc, h2 u hu]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  let T : ((ι → C) × (κ → C)) →ₗ[C] ((ι → C) × (κ → C)) :=
    LinearMap.prod (ρc ∘ₗ LinearMap.fst C _ _)
      (LinearMap.snd C _ _ - σc ∘ₗ LinearMap.fst C _ _ + σc ∘ₗ ρc ∘ₗ LinearMap.fst C _ _)
  have hT : ∀ y, T y = (ρc y.1, y.2 - σc y.1 + σc (ρc y.1)) := fun y => rfl
  have hTx : T x = x := by
    rw [hT, a2 _ hxU, sub_add_cancel]
  rw [← hTx]
  refine map_mem T ?_ hx
  rintro _ ⟨⟨g, m⟩, hgm, rfl⟩
  obtain ⟨hg, hg'⟩ := hσ' _ hgm
  refine mem_span ⟨(ρ g, m - σ g + σ (ρ g)), ⟨?_, h1 g⟩, ?_⟩
  · have := Δ.add_mem (Δ.sub_mem hgm hg') (hσ _ (h3 g hg) (h1 g))
    simpa using this
  · rw [hT]
    simp only [Prod.map, hρc, hσc, map_add, map_sub]

variable {F : Type} [Zero F] {n : ℕ}

theorem mem_van {i : ℕ} {g : (Fin n → F) → Ω} :
    g ∈ vanSub Ω F n i ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → g x = 0 :=
  Iff.rfl

theorem mem_char {χ : F → Ω} {i : Fin n} {g : (Fin n → F) → Ω} :
    g ∈ charSub χ i ↔ ∃ c : Ω, c • (fun x : Fin n → F => χ (x i)) - g ∈ vanSub Ω F n ((i : ℕ) + 1) := by
  rw [charSub, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    exact ⟨c, by simpa using hu⟩
  · rintro ⟨c, hc⟩
    exact ⟨_, Submodule.neg_mem _ hc, _,
      Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _), by simp⟩

theorem van_le [Fintype F] (i : ℕ) :
    vanSub C F n i ≤ Submodule.span C (bcMap Ω C _ '' vanSub Ω F n i) := by
  classical
  intro g hg
  rw [pi_eq_sum_univ' g]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0
  · rw [mem_van.1 hg x hx, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single x 1, mem_van.2 fun y hy => ?_, ?_⟩)
    · rw [Pi.single_eq_of_ne]
      rintro rfl
      exact hx hy
    · funext y
      rw [bc_apply]
      by_cases h : y = x
      · subst h; simp
      · simp [h]

theorem char_le [Fintype F] (χ : F → Ω) (i : Fin n) :
    charSub (fun a => algebraMap Ω C (χ a)) i ≤ Submodule.span C (bcMap Ω C _ '' charSub χ i) := by
  refine sup_le ((van_le (Ω := Ω) _).trans (Submodule.span_mono (Set.image_mono ?_))) ?_
  · exact fun g hg => Submodule.mem_sup_left hg
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨_, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩

theorem bc_van {i : ℕ} {g : (Fin n → F) → Ω} (hg : g ∈ vanSub Ω F n i) :
    bcMap Ω C _ g ∈ vanSub C F n i :=
  mem_van.2 fun x hx => by rw [bc_apply, mem_van.1 hg x hx, map_zero]

theorem bc_char {χ : F → Ω} {i : Fin n} {g : (Fin n → F) → Ω} (hg : g ∈ charSub χ i) :
    bcMap Ω C _ g ∈ charSub (fun a => algebraMap Ω C (χ a)) i := by
  obtain ⟨c, hc⟩ := mem_char.1 hg
  refine mem_char.2 ⟨algebraMap Ω C c, mem_van.2 fun x hx => ?_⟩
  have := congrArg (algebraMap Ω C) (mem_van.1 hc x hx)
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_zero] at this
  exact this

variable {Sg : Type} {r s : Sg → ℕ}

theorem mem_kk (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (i : ℕ) (m : Fin (r τ) → Ω) :
    m ∈ D.kk τ i ↔ ∃ g, (g, m) ∈ D.Th τ ∧ g ∈ vanSub Ω F n i := by
  constructor
  · rintro ⟨⟨g, m⟩, ⟨h1, h2, -⟩, rfl⟩
    exact ⟨g, h1, h2⟩
  · rintro ⟨g, h1, h2⟩
    exact ⟨(g, m), ⟨h1, h2, trivial⟩, rfl⟩

theorem mem_step [One F] (D : LieLatticeData Ω F n Sg r s) (τ : Sg) {χ : F → Ω} (h1 : χ 1 = 1) (i : Fin n)
    (c : Ω) (m : Fin (r τ) → Ω) :
    (c, m) ∈ D.stepGraph τ χ i ↔
      ∃ g, (g, m) ∈ D.Th τ ∧ g ∈ charSub χ i ∧ g (Pi.single i 1) = c := by
  have he : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → (Pi.single i 1 : Fin n → F) j = 0 := by
    intro j hj
    rw [Pi.single_eq_of_ne]
    rintro rfl
    omega
  have hev : ∀ (d : Ω) (g : (Fin n → F) → Ω),
      d • (fun x : Fin n → F => χ (x i)) - g ∈ vanSub Ω F n ((i : ℕ) + 1) → g (Pi.single i 1) = d := by
    intro d g h
    have := mem_van.1 h _ he
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, h1, smul_eq_mul, mul_one] at this
    exact (sub_eq_zero.1 this).symm
  have h0 : (c, m) ∈ D.stepGraph τ χ i ↔ (c • (fun x : Fin n → F => χ (x i)), m) ∈
      D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := Iff.rfl
  rw [h0, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, hy, ⟨u, z⟩, ⟨hu, hz⟩, h⟩
    have hz' : z = 0 := hz
    subst hz'
    simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq] at h
    obtain ⟨h, rfl⟩ := h
    have hv : c • (fun x : Fin n → F => χ (x i)) - g ∈ vanSub Ω F n ((i : ℕ) + 1) := by
      rw [← h, add_sub_cancel_left]
      exact hu
    exact ⟨g, hy, mem_char.2 ⟨c, hv⟩, hev _ _ hv⟩
  · rintro ⟨g, hy, hg, hc⟩
    obtain ⟨d, hd⟩ := mem_char.1 hg
    obtain rfl : d = c := (hev _ _ hd).symm.trans hc
    exact ⟨(g, m), hy, (_, 0), ⟨hd, AddSubgroup.zero_mem _⟩, by simp⟩

end BC

end PositivityTheory.Xgn.KernelLatticeBaseChange

open PositivityTheory.Xgn.KernelLatticeBaseChange in
theorem PositivityTheory.Xgn.kernel_lattice_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG C _ _ _ _ RC _ τ
  obtain ⟨-, -, -, -, hχ⟩ := hχ
  obtain ⟨hχ0, hχ1, -⟩ := hχ τ
  have hth := (hB.th τ).1
  have hv0 : ∀ g : (Fin n → F) → Ω, g ∈ vanSub Ω F n 0 ↔ g 0 = 0 := fun g =>
    ⟨fun h => mem_van.1 h 0 fun _ _ => rfl, fun h => mem_van.2 fun x hx => by
      rw [show x = 0 from funext fun j => hx j (Nat.zero_le _)]
      exact h⟩
  obtain ⟨σ, hσ⟩ := exists_section R (D.Th τ) D.M (vanSub Ω F n 0) _
    (fun a ha => (hB.stable τ a ha).2.2) hB.freeM (hG.van 0)
    (fun g hg hg' => (hth g).2 ⟨hg, (hv0 g).1 hg'⟩)
  have hσ' : ∀ x ∈ D.Th τ, x.1 ∈ D.M ∧ (x.1, σ x.1) ∈ D.Th τ := fun x hx => by
    obtain ⟨h1, h2⟩ := (hth x.1).1 ⟨x.2, hx⟩
    exact ⟨h1, hσ _ h1 ((hv0 _).2 h2)⟩
  have hχ1' : algebraMap Ω C (χ τ 1) = 1 := by rw [hχ1, map_one]
  refine ⟨fun i => le_antisymm ?_ ?_, fun i => le_antisymm ?_ ?_⟩
  · intro m hm
    obtain ⟨g, h1, h2⟩ := (mem_kk _ _ _ _).1 hm
    have h3 := key RC (D.Th τ) D.M (vanSub Ω F n i) (hG.van i) σ
      (fun v hv hv' => hσ v hv ((hv0 v).2 (mem_van.1 hv' 0 fun _ _ => rfl))) hσ' h1 (van_le i h2)
    refine map_mem (LinearMap.snd C _ _) ?_ h3
    rintro _ ⟨⟨g', m'⟩, ⟨h4, h5⟩, rfl⟩
    exact mem_span ⟨m', (mem_kk _ _ _ _).2 ⟨g', h4, h5⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨m, hm, rfl⟩, rfl⟩
    obtain ⟨g, h1, h2⟩ := (mem_kk _ _ _ _).1 hm
    exact (mem_kk _ _ _ _).2 ⟨a • bcMap Ω C _ g,
      AddSubgroup.subset_closure ⟨a, ha, _, ⟨(g, m), h1, rfl⟩, rfl⟩,
      Submodule.smul_mem _ _ (bc_van h2)⟩
  · rintro ⟨c, m⟩ hm
    obtain ⟨g, h1, h2, rfl⟩ :=
      (mem_step (D.bc RC) τ (χ := fun a => algebraMap Ω C (χ τ a)) hχ1' i c m).1 hm
    have hc0 : ∀ v ∈ charSub (χ τ) i, v 0 = 0 := fun v hv => by
      obtain ⟨d, hd⟩ := mem_char.1 hv
      simpa [hχ0] using mem_van.1 hd 0 fun _ _ => rfl
    have h3 := key RC (D.Th τ) D.M (charSub (χ τ) i) (hG.char τ i) σ
      (fun v hv hv' => hσ v hv ((hv0 v).2 (hc0 v hv'))) hσ' h1 (char_le _ i h2)
    refine map_mem ((LinearMap.proj (R := C) (φ := fun _ : Fin n → F => C) (Pi.single i 1)).prodMap
      LinearMap.id) ?_ h3
    rintro _ ⟨⟨g', m'⟩, ⟨h4, h5⟩, rfl⟩
    exact mem_span ⟨(g' (Pi.single i 1), m'), (mem_step D τ hχ1 i _ _).2 ⟨g', h4, h5, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨⟨c, m⟩, hm, rfl⟩, rfl⟩
    obtain ⟨g, h1, h2, rfl⟩ := (mem_step D τ hχ1 i c m).1 hm
    exact (mem_step (D.bc RC) τ (χ := fun a => algebraMap Ω C (χ τ a)) hχ1' i _ _).2
      ⟨a • bcMap Ω C _ g, AddSubgroup.subset_closure ⟨a, ha, _, ⟨(g, m), h1, rfl⟩, rfl⟩,
        Submodule.smul_mem _ _ (bc_char h2), rfl⟩
