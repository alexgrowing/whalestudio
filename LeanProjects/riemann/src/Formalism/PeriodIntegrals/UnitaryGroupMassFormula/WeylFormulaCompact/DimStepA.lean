import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep

noncomputable section

namespace PI.WeylForKWork.DimensionInduction

open scoped InnerProductSpace
open Module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}

def Stab (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop := ∀ i, ∀ v ∈ W, ρ i v ∈ W

def Irr (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop :=
  ∀ W' : Submodule ℂ H, W' ≤ W → Stab ρ W' → W' = ⊥ ∨ W' = W

structure Good (ρ : ι → H →L[ℂ] H) : Prop where
  isom : ∀ i v, ‖ρ i v‖ = ‖v‖
  inv : ∀ i, ∃ j, ∀ v, ρ i (ρ j v) = v
  mul : ∀ i i', ∃ k, ∀ v, ρ i (ρ i' v) = ρ k v
  one : ∃ i, ∀ v, ρ i v = v

def Comm (ρ : ι → H →L[ℂ] H) (c : H →ₗ[ℂ] H) : Prop := ∀ i v, c (ρ i v) = ρ i (c v)

def commSub (ρ : ι → H →L[ℂ] H) : Submodule ℂ (H →ₗ[ℂ] H) where
  carrier := {c | Comm ρ c}
  add_mem' := by
    intro c d hc hd
    have hc : Comm ρ c := hc
    have hd : Comm ρ d := hd
    show Comm ρ (c + d)
    intro i v
    simp only [LinearMap.add_apply, map_add, hc i v, hd i v]
  zero_mem' := by
    show Comm ρ 0
    intro i v
    simp
  smul_mem' := by
    intro a c hc
    have hc : Comm ρ c := hc
    show Comm ρ (a • c)
    intro i v
    simp only [LinearMap.smul_apply, map_smul, hc i v]

def slice (ρ : ι → H →L[ℂ] H) (x₀ : H) : Submodule ℂ H where
  carrier := {v | ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ = v}
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, (commSub ρ).add_mem hc hd, rfl⟩
  zero_mem' := ⟨0, (commSub ρ).zero_mem, rfl⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, (commSub ρ).smul_mem a hc, rfl⟩

variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

lemma Good.inner (hρ : Good ρ) (i : ι) (x y : H) : ⟪ρ i x, ρ i y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ i : H →ₗ[ℂ] H), hρ.isom i⟩
  exact L.inner_map_map x y

lemma stab_orth (hρ : Good ρ) {W : Submodule ℂ H} (hW : Stab ρ W) : Stab ρ Wᗮ := by
  intro i v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro w hw
  obtain ⟨j, hj⟩ := hρ.inv i
  rw [← hj w, hρ.inner i]
  exact hv _ (hW j w hw)

lemma stab_inf {W W' : Submodule ℂ H} (h : Stab ρ W) (h' : Stab ρ W') : Stab ρ (W ⊓ W') := by
  intro i v hv
  exact ⟨h i v hv.1, h' i v hv.2⟩

lemma proj_comm (hρ : Good ρ) {W : Submodule ℂ H} [FiniteDimensional ℂ W] (hW : Stab ρ W) :
    Comm ρ (W.starProjection : H →ₗ[ℂ] H) := by
  intro i v
  have hWo := stab_orth hρ hW
  show W.starProjection (ρ i v) = ρ i (W.starProjection v)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hW i _ (W.orthogonalProjection v).2
  · intro w hw
    rw [← map_sub]
    exact (Submodule.mem_orthogonal' W _).1 (hWo i _ (W.sub_starProjection_mem_orthogonal v)) w hw

lemma comm_comp {c d : H →ₗ[ℂ] H} (hc : Comm ρ c) (hd : Comm ρ d) : Comm ρ (c ∘ₗ d) := by
  intro i v
  show c (d (ρ i v)) = ρ i (c (d v))
  rw [hd i v, hc i (d v)]

lemma kill {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hXs : Stab ρ X) (hXi : Irr ρ X)
    {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0) (hk : c x₁ = 0) : ∀ x ∈ X, c x = 0 := by
  have hst : Stab ρ (LinearMap.ker c ⊓ X) := by
    intro i v hv
    refine ⟨?_, hXs i v hv.2⟩
    show c (ρ i v) = 0
    rw [hc i v, LinearMap.mem_ker.1 hv.1, map_zero]
  rcases hXi _ inf_le_right hst with h | h
  · exfalso
    have hm : x₁ ∈ LinearMap.ker c ⊓ X := ⟨LinearMap.mem_ker.2 hk, hx₁⟩
    rw [h] at hm
    exact h0 ((Submodule.mem_bot ℂ).1 hm)
  · intro x hx
    rw [← h] at hx
    exact LinearMap.mem_ker.1 hx.1

lemma into (hρ : Good ρ) {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : Stab ρ W) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0)
    (hin : c x₁ ∈ W) : ∀ x ∈ X, c x ∈ W := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hd : Comm ρ (c - P ∘ₗ c) :=
    (commSub ρ).sub_mem hc (comm_comp (proj_comm hρ hW) hc)
  have h1 : (c - P ∘ₗ c) x₁ = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 hin, sub_self]
  intro x hx
  have h2 := kill hd hXs hXi hx₁ h0 h1 x hx
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
    sub_eq_zero] at h2
  rw [h2]
  exact (W.orthogonalProjection (c x)).2

lemma stab_map {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hX : Stab ρ X) :
    Stab ρ (X.map c) := by
  rintro i _ ⟨x, hx, rfl⟩
  exact ⟨ρ i x, hX i x hx, hc i x⟩

lemma stab_iSup {ν : Sort*} {F : ν → Submodule ℂ H} (hF : ∀ k, Stab ρ (F k)) :
    Stab ρ (⨆ k, F k) := by
  intro i v hv
  have hle : (⨆ k, F k) ≤ (⨆ k, F k).comap (ρ i : H →ₗ[ℂ] H) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (hF k i x hx)
  exact hle hv

theorem exists_hit (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X W : Submodule ℂ H} (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0)
    [FiniteDimensional ℂ W] (hWS : W ≤ S) (hW0 : W ≠ ⊥) (hWs : Stab ρ W) :
    ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ ∈ W ∧ c x₀ ≠ 0 := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : Comm ρ P := proj_comm hρ hWs
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  by_contra hne
  push_neg at hne
  have hzero : ∀ j, ∀ x ∈ X, P (ρ' j x) = 0 := by
    intro j
    have hcj : Comm ρ (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) := comm_comp hPc (hρ'c j)
    have hk : (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) x₀ = 0 := by
      refine hne _ hcj ?_
      simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
      exact (W.orthogonalProjection _).2
    exact kill hcj hXs hXi hx₀ h0 hk
  set T : Submodule ℂ H := ⨆ j, X.map (ρ' j : H →ₗ[ℂ] H) with hT
  have hTρ : Stab ρ T := stab_iSup fun j => stab_map (hρ'c j) hXs
  have hTρ' : Stab ρ' T := by
    intro j' v hv
    have hle : T ≤ T.comap (ρ' j' : H →ₗ[ℂ] H) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hρ'.mul j' j
      show ρ' j' (ρ' j x) ∈ T
      rw [hk x]
      exact Submodule.mem_iSup_of_mem k ⟨x, hx, rfl⟩
    exact hle hv
  have hTS : T ≤ S := by
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hSρ' j x (hXS hx)
  have hx₀T : x₀ ∈ T := by
    obtain ⟨o, ho⟩ := hρ'.one
    have hm : ρ' o x₀ ∈ T := Submodule.mem_iSup_of_mem o ⟨x₀, hx₀, rfl⟩
    rwa [ho] at hm
  rcases hSirr T hTS hTρ hTρ' with h | h
  · rw [h] at hx₀T
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀T)
  · have hle : T ≤ LinearMap.ker P := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.2 (hzero j x hx)
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have hwT : w ∈ T := by
      rw [h]
      exact hWS hw
    have h1 : P w = 0 := LinearMap.mem_ker.1 (hle hwT)
    have h2 : P w = w := by
      simp only [hP, ContinuousLinearMap.coe_coe]
      exact Submodule.starProjection_eq_self_iff.2 hw
    refine (Submodule.mem_bot ℂ).2 ?_
    rw [← h2]
    exact h1

theorem schur2 (hρ : Good ρ) {X W : Submodule ℂ H} [FiniteDimensional ℂ X] [FiniteDimensional ℂ W]
    (hXs : Stab ρ X) (hXi : Irr ρ X) (hWs : Stab ρ W) (hWi : Irr ρ W) {x₀ : H} (hx₀ : x₀ ∈ X)
    (h0 : x₀ ≠ 0) {c c' : H →ₗ[ℂ] H} (hc : Comm ρ c) (hc' : Comm ρ c') (hcW : c x₀ ∈ W)
    (hc0 : c x₀ ≠ 0) (hc'W : c' x₀ ∈ W) :
    finrank ℂ X = finrank ℂ W ∧ ∃ μ : ℂ, c' x₀ = μ • c x₀ := by
  have hAW : ∀ x : X, c x ∈ W := fun x => into hρ hc hWs hXs hXi hx₀ h0 hcW x x.2
  have hBW : ∀ x : X, c' x ∈ W := fun x => into hρ hc' hWs hXs hXi hx₀ h0 hc'W x x.2
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hmapW : X.map c = W := by
    rcases hWi _ (by rintro _ ⟨x, hx, rfl⟩; exact hAW ⟨x, hx⟩) (stab_map hc hXs) with h | h
    · exfalso
      have hm : c x₀ ∈ X.map c := ⟨x₀, hx₀, rfl⟩
      rw [h] at hm
      exact hc0 ((Submodule.mem_bot ℂ).1 hm)
    · exact h
  have hrank : finrank ℂ X = finrank ℂ W := by
    rw [← hmapW, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  refine ⟨hrank, ?_⟩
  let A : X →ₗ[ℂ] W := (c.domRestrict X).codRestrict W hAW
  let B : X →ₗ[ℂ] W := (c'.domRestrict X).codRestrict W hBW
  have hAinj : Function.Injective A := fun a b hab => hinj (congrArg Subtype.val hab)
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hAinj
  let e : X ≃ₗ[ℂ] W := LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩
  let T : Module.End ℂ X := e.symm.toLinearMap ∘ₗ B
  haveI : Nontrivial X := ⟨⟨⟨x₀, hx₀⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hBv : B v = μ • A v :=
    calc B v = e (T v) := (e.apply_symm_apply (B v)).symm
      _ = e (μ • v) := by rw [hTv]
      _ = μ • e v := map_smul e μ v
      _ = μ • A v := rfl
  have hcv : c' v = μ • c v := congrArg Subtype.val hBv
  have hd : Comm ρ (c' - μ • c) := (commSub ρ).sub_mem hc' ((commSub ρ).smul_mem μ hc)
  have hdv : (c' - μ • c) v = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hcv, sub_self]
  have hv0 : (v : H) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hfin := kill hd hXs hXi v.2 hv0 hdv x₀ hx₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hfin
  exact ⟨μ, hfin⟩

end PI.WeylForKWork.DimensionInduction
