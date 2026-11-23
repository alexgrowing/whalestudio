import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirStep

section Abstract

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

theorem twKer_twAct_eq_map (ρ : Representation ℂ G V) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N₁), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N₁, θ₁ ⟨_, h⟩ = θ₁ n)
    (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
    (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
    (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
    (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
    twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ ∧
      twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨a, x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨h, hθ⟩ := h2 a
      refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
      rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rfl
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    obtain ⟨u₁, a, hu⟩ := h3 u
    obtain ⟨hu₁, e1⟩ := h1 u₁
    obtain ⟨ha, e2⟩ := h2 a
    have hθ : θ u = θ₁ u₁ * θ₂ a := by
      have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
      rw [this, map_mul, e1, e2]
    have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
        (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
          ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
      rw [hθ, hu, map_mul, Module.End.mul_apply, Units.val_mul, smul_sub, mul_smul]
      abel
    have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
      Submodule.subset_span ⟨u₁, _, rfl⟩
    show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂
    rw [hdec, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
    rfl
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    obtain ⟨h, hθ⟩ := h1 u
    exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩

theorem twJacquet_twAct_equiv (ρ : Representation ℂ G V) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N₁), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N₁, θ₁ ⟨_, h⟩ = θ₁ n)
    (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
    (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
    (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
    (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
    Nonempty (TwJacquet (twAct ρ N₁ θ₁ s hs) N₂ θ₂ ≃ₗ[ℂ] TwJacquet ρ N θ) := by
  obtain ⟨e, hle⟩ := twKer_twAct_eq_map ρ N₁ θ₁ s hs N₂ θ₂ N θ h1 h2 h3
  exact ⟨(Submodule.quotEquivOfEq _ _ e).trans (Submodule.quotientQuotientEquivQuotient _ _ hle)⟩

end Abstract

section Concrete

variable {k : Type} [Field k]

theorem mem_colFix_iff {N n : ℕ} (g : GL (Fin N) k) :
    g ∈ colFix k N n ↔ ∀ i j : Fin N, (j : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  show (∀ j : Fin N, (j : ℕ) < n → _ = _) ↔ _
  constructor
  · intro h i j hj
    have := congrFun (h j hj) i
    rw [mulVec_single_one] at this
    simpa [one_apply, Pi.single_apply, Matrix.col_apply] using this
  · intro h j hj
    rw [mulVec_single_one]
    funext i
    simpa [one_apply, Pi.single_apply, Matrix.col_apply] using h i j hj

theorem glEmbMat_castSucc_castSucc (N : ℕ) (A : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    glEmbMat k N A (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [glEmbMat]

theorem glEmbMat_castSucc_last (N : ℕ) (A : Matrix (Fin N) (Fin N) k) (i : Fin N) :
    glEmbMat k N A (Fin.castSucc i) (Fin.last N) = 0 := by
  simp [glEmbMat]

theorem glEmbMat_last_castSucc (N : ℕ) (A : Matrix (Fin N) (Fin N) k) (j : Fin N) :
    glEmbMat k N A (Fin.last N) (Fin.castSucc j) = 0 := by
  simp [glEmbMat]

theorem glEmbMat_last_last (N : ℕ) (A : Matrix (Fin N) (Fin N) k) :
    glEmbMat k N A (Fin.last N) (Fin.last N) = 1 := by
  simp [glEmbMat]

end Concrete

section ConcreteChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derCharM_apply (ψ : AddChar k Circle) (m n : ℕ) (x : derUnipM k m n) :
    derCharM k ψ m n x = Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
      (fun p : Fin (m + 1) × Fin (m + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
        ((x : Mir k m) : GL (Fin (m + 1)) k).val p.1 p.2)) := rfl

end ConcreteChar

section H1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colFix_anti {N a b : ℕ} (hab : b ≤ a) : colFix k N a ≤ colFix k N b :=
  fun _ hg i hi => hg i (lt_of_lt_of_le hi hab)

theorem MirUin_step (ψ : AddChar k Circle) {m n : ℕ} (hnm : n ≤ m) (u : MirUin k (m + 1)) :
    ∃ h : (u : Mir k (m + 1)) ∈ derUnipM k (m + 1) n, derCharM k ψ (m + 1) n ⟨u, h⟩ = mirChar k ψ m u := by
  have hu := (GlobalTheory.CompanionTheory.BZMir.mem_MirUin_iff_mem_derUnipM k (m + 1) (u : Mir k (m + 1))).1 u.2
  rw [derUnipM, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf] at hu
  refine ⟨Subgroup.mem_subgroupOf.2 ⟨hu.1, colFix_anti (by omega) hu.2⟩, ?_⟩
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) ∈ MirU k (m + 1))
  rw [mirChar_eq k ψ m u w hw.symm, derCharM_apply]
  congr 2
  have hw' : ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k) = unip k (m + 1) w := hw.symm
  rw [hw']
  rw [Finset.sum_eq_single (Fin.castSucc (Fin.last m), Fin.last (m + 1))]
  · exact unip_apply_castSucc_last k (m + 1) w (Fin.last m)
  · intro p hp hne
    have hc := (Finset.mem_filter.1 hp).2.1
    have h12 : p.1 ≠ p.2 := fun e => by rw [e] at hc; omega
    have h2 : p.2 ≠ Fin.last (m + 1) := fun e => hne (Prod.ext (Fin.ext (by
      rw [e] at hc; simp at hc ⊢; omega)) e)
    simp [unip, colMat, one_apply, h12, h2]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp, by simpa using hnm⟩) h

end H1

section H2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem levi_step (ψ : AddChar k Circle) {m n : ℕ} (hnm : n ≤ m) (a : derUnipM k m n) :
    ∃ h : ((levi k (m + 1)).comp (Mir k m).subtype) (a : Mir k m) ∈ derUnipM k (m + 1) n,
      derCharM k ψ (m + 1) n ⟨_, h⟩ = derCharM k ψ m n a := by
  have ha := Subgroup.mem_subgroupOf.1 a.2
  rw [derUnip, Subgroup.mem_inf] at ha
  obtain ⟨hB, hC⟩ := ha
  rw [mem_unipB] at hB
  rw [mem_colFix_iff] at hC
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) k := ((a : Mir k m) : GL (Fin (m + 1)) k).val with hA
  have hval : ((((levi k (m + 1)).comp (Mir k m).subtype) (a : Mir k m) : Mir k (m + 1)) : GL (Fin (m + 2)) k).val =
      glEmbMat k (m + 1) A := rfl
  refine ⟨Subgroup.mem_subgroupOf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (mem_colFix_iff _).2 ?_⟩, ?_⟩
  · rw [hval]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hji (lt_irrefl _)
      | cast j => exact glEmbMat_last_castSucc (m + 1) A j
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact glEmbMat_castSucc_last (m + 1) A i
      | cast j =>
        rw [glEmbMat_castSucc_castSucc]
        exact hB.1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
  · rw [hval]
    induction i using Fin.lastCases with
    | last => exact glEmbMat_last_last (m + 1) A
    | cast i => rw [glEmbMat_castSucc_castSucc]; exact hB.2 i
  · intro i j hj
    rw [hval]
    induction j using Fin.lastCases with
    | last => simp at hj; omega
    | cast j =>
      induction i using Fin.lastCases with
      | last => rw [glEmbMat_last_castSucc]; simp [one_apply, (Fin.castSucc_ne_last j).symm]
      | cast i =>
        rw [glEmbMat_castSucc_castSucc, hC i j (by simpa using hj)]
        simp [one_apply]
  · rw [derCharM_apply, derCharM_apply]
    congr 2
    rw [hval]
    symm
    have e1 : ∑ q ∈ Finset.univ.filter
        (fun p : Fin (m + 1) × Fin (m + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), A q.1 q.2 =
        ∑ q ∈ Finset.univ.filter
        (fun p : Fin (m + 1) × Fin (m + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)),
          glEmbMat k (m + 1) A (Function.Embedding.prodMap Fin.castSuccEmb Fin.castSuccEmb q).1
            (Function.Embedding.prodMap Fin.castSuccEmb Fin.castSuccEmb q).2 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [glEmbMat_castSucc_castSucc]
    rw [e1, ← Finset.sum_map _ _ (fun p : Fin (m + 2) × Fin (m + 2) => glEmbMat k (m + 1) A p.1 p.2)]
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hp
      simpa using hq
    · rintro ⟨i, j⟩ hp hnot
      have hc := (Finset.mem_filter.1 hp).2
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp at hc
        | cast j => have := j.isLt; simp at hc; omega
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact glEmbMat_castSucc_last (m + 1) A i
        | cast j =>
          exact absurd (Finset.mem_map.2 ⟨(i, j), by simpa using hc, rfl⟩) hnot

end H2

section H3

variable {k : Type} [Field k]

theorem derUnipM_decomp {m n : ℕ} (hnm : n ≤ m) (u : derUnipM k (m + 1) n) :
    ∃ u₁ : MirUin k (m + 1), ∃ a : derUnipM k m n,
      (u : Mir k (m + 1)) = u₁ * ((levi k (m + 1)).comp (Mir k m).subtype) (a : Mir k m) := by
  have hu := Subgroup.mem_subgroupOf.1 u.2
  rw [derUnip, Subgroup.mem_inf] at hu
  obtain ⟨hB, hC⟩ := hu
  rw [mem_unipB] at hB
  rw [mem_colFix_iff] at hC
  have hM := (mem_Mir_iff k _).1 (u : Mir k (m + 1)).2
  set X : Matrix (Fin (m + 2)) (Fin (m + 2)) k := ((u : Mir k (m + 1)) : GL (Fin (m + 2)) k).val with hX
  have hXl : ∀ j, X (Fin.last (m + 1)) j = if j = Fin.last (m + 1) then 1 else 0 := by
    intro j
    have := congrFun hM j
    simp only [eLast, Pi.single_apply] at this
    exact this
  let a₀ : GL (Fin (m + 1)) k := mirabolicProjection k (m + 1) (u : Mir k (m + 1))
  have hval : (a₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = blockMat k (m + 1) X := rfl
  have ha₀M : a₀ ∈ Mir k m := by
    rw [mem_Mir_iff, hval]
    funext j
    simp only [blockMat, eLast, Pi.single_apply]
    by_cases hj : j = Fin.last m
    · subst hj
      rw [if_pos rfl]
      exact hB.2 _
    · rw [if_neg hj]
      exact hB.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 (Fin.lt_last_iff_ne_last.2 hj))
  have ha₀D : a₀ ∈ derUnip k (m + 1) n := by
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, (mem_colFix_iff _).2 fun i j hj => ?_⟩
    · rw [hval]; exact hB.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hji)
    · rw [hval]; exact hB.2 _
    · rw [hval]
      show X (Fin.castSucc i) (Fin.castSucc j) = _
      rw [hC _ _ (by simpa using hj)]
      simp [one_apply]
  let c : Multiplicative (Fin (m + 1) → k) := Multiplicative.ofAdd fun i => X (Fin.castSucc i) (Fin.last (m + 1))
  refine ⟨⟨⟨unip k (m + 1) c, MirU_le_Mir k (m + 1) ⟨c, rfl⟩⟩, Subgroup.mem_subgroupOf.2 ⟨c, rfl⟩⟩,
    ⟨⟨a₀, ha₀M⟩, Subgroup.mem_subgroupOf.2 ha₀D⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show X = (1 + colMat k (m + 1) c.toAdd) * glEmbMat k (m + 1) (blockMat k (m + 1) X)
  rw [add_mul, one_mul]
  ext i j
  rw [Matrix.add_apply, mul_apply, Fin.sum_univ_castSucc]
  simp only [colMat, Fin.castSucc_ne_last, if_false, zero_mul, Finset.sum_const_zero, zero_add, if_true]
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => simp [glEmbMat, hXl]
    | cast i => simp [glEmbMat, c]
  | cast j =>
    induction i using Fin.lastCases with
    | last => simp [glEmbMat, hXl, Fin.castSucc_ne_last]
    | cast i => simp [glEmbMat, blockMat]

end H3

theorem phiMinus_twJacquet_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V),
    Nonempty (TwJacquet (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n) ≃ₗ[ℂ]
      TwJacquet τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)) := by
  intro k _ _ _ _ ψ m n hnm V _ _ τ
  exact twJacquet_twAct_equiv τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m) (derUnipM k m n)
    (derCharM k ψ m n) (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n) (MirUin_step ψ hnm) (levi_step ψ hnm)
    (derUnipM_decomp hnm)

end GlobalTheory.CompanionTheory.BZMirStep
