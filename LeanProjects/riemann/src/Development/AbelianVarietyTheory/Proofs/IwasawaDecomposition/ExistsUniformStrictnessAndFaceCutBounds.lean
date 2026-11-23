import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormFromFinsupp
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan.StrictData

section Gen

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {φ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem toReal_add (β β' : LinearMap.BilinForm ℤ X) : toReal (β + β') = toReal β + toReal β' :=
  LinearMap.ext₂ fun a b => by simp [toReal]

theorem toReal_nsmul (k : ℕ) (β : LinearMap.BilinForm ℤ X) : toReal (k • β) = (k : ℝ) • toReal β :=
  LinearMap.ext₂ fun a b => by simp [toReal]

theorem toReal_mem_psdCone {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    toReal β ∈ psdCone bar X := by
  have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
    (fun i y => by fin_cases i; simpa using hp y) (fun i => by fin_cases i; simp)
  simpa using this

theorem evalZ_eq (β : LinearMap.BilinForm ℤ X) : φ.evalZ β = evalR φ (toReal β) := rfl

theorem evalZ_nsmul (hP : IsPolyFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) (k : ℕ) : φ.evalZ (k • β) = k * φ.evalZ β := by
  rw [evalZ_eq, evalZ_eq, toReal_nsmul]
  exact hP.homog _ (toReal_mem_psdCone hβ hp) _ (Nat.cast_nonneg k)

theorem evalZ_add_ge (hP : IsPolyFanOn bar φ X) {β β' : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) (hβ' : β' ∈ balForms bar X) (hp' : ∀ y, 0 ≤ β' y y) :
    φ.evalZ β + φ.evalZ β' ≤ φ.evalZ (β + β') := by
  rw [evalZ_eq, evalZ_eq, evalZ_eq, toReal_add]
  exact hP.superadd _ (toReal_mem_psdCone hβ hp) _ (toReal_mem_psdCone hβ' hp')

theorem evalZ_zero (hP : IsPolyFanOn bar φ X) : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  have := evalZ_nsmul hP (zero_mem (balForms bar X)) (fun y => by simp) 0
  simpa using this

theorem evalZ_nonneg (hP : IsPolyFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ y, 0 ≤ β y y) : 0 ≤ φ.evalZ β := by
  by_cases h0 : β = 0
  · subst h0; rw [evalZ_zero hP]
  · exact (hP.pos β hβ hp h0).le

def ratCone {m : ℕ} (u : Fin m → LinearMap.BilinForm ℤ X) : AddSubmonoid (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∃ k : ℕ, 0 < k ∧ k • β ∈ AddSubmonoid.closure (Set.range u)}
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨k', hk', hb⟩
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact AddSubmonoid.nsmul_mem _ ha _
    · rw [mul_smul]; exact AddSubmonoid.nsmul_mem _ hb _
  zero_mem' := ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩

theorem mem_ratCone {m : ℕ} {u : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} :
    β ∈ ratCone u ↔ ∃ k : ℕ, 0 < k ∧ k • β ∈ AddSubmonoid.closure (Set.range u) := Iff.rfl

theorem ratCone_le {m n : ℕ} {u : Fin m → LinearMap.BilinForm ℤ X} {v : Fin n → LinearMap.BilinForm ℤ X}
    (h : ∀ j, u j ∈ ratCone v) : ratCone u ≤ ratCone v := by
  intro β hβ
  obtain ⟨k, hk, hβ⟩ := mem_ratCone.1 hβ
  have hc : AddSubmonoid.closure (Set.range u) ≤ ratCone v :=
    AddSubmonoid.closure_le.2 (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨k', hk', h'⟩ := mem_ratCone.1 (hc hβ)
  exact mem_ratCone.2 ⟨k' * k, Nat.mul_pos hk' hk, by rwa [mul_smul]⟩

theorem mem_ratCone_of_eq_sum {m : ℕ} {u : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    (hk : 0 < k) (c : Fin m → ℕ) (h : k • β = ∑ i, c i • u i) : β ∈ ratCone u :=
  mem_ratCone.2 ⟨k, hk, by
    rw [h]; exact AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_range_self i)) _⟩

theorem le_of_mem_closure (hP : IsPolyFanOn bar φ X) {m N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} (hu : StrictWith bar φ N ℓ u) (hub : ∀ j, u j ∈ balForms bar X)
    (hup : ∀ j y, 0 ≤ u j y y) {x : LinearMap.BilinForm ℤ X} (hx : x ∈ AddSubmonoid.closure (Set.range u)) :
    x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (ℓ x : ℝ) ≤ N * φ.evalZ x := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨hub j, hup j, (hu.1 j).le⟩
  | zero => exact ⟨zero_mem _, fun y => by simp, by simp [evalZ_zero hP]⟩
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, fun z => ?_, ?_⟩
    · simp only [LinearMap.add_apply]; exact add_nonneg (hx.2.1 z) (hy.2.1 z)
    · have h1 := evalZ_add_ge hP hx.1 hx.2.1 hy.1 hy.2.1
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) N)
      rw [mul_add] at h2
      rw [map_add, Int.cast_add]
      linarith [hx.2.2, hy.2.2]

theorem strictWith_of_ratCone (hP : IsPolyFanOn bar φ X) {m n N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} {v : Fin n → LinearMap.BilinForm ℤ X} (hu : StrictWith bar φ N ℓ u)
    (hub : ∀ j, u j ∈ balForms bar X) (hup : ∀ j y, 0 ≤ u j y y) (hvb : ∀ i, v i ∈ balForms bar X)
    (hvp : ∀ i y, 0 ≤ v i y y) (hvu : ∀ i, v i ∈ ratCone u) (huv : ∀ j, u j ∈ ratCone v) :
    StrictWith bar φ N ℓ v := by
  refine ⟨fun i => ?_, hu.2.1, fun β hβ hp he => ?_⟩
  · obtain ⟨k, hk, hkv⟩ := mem_ratCone.1 (hvu i)
    have h1 := (le_of_mem_closure hP hu hub hup hkv).2.2
    rw [map_nsmul, evalZ_nsmul hP (hvb i) (hvp i)] at h1
    have h2 := hu.2.1 (v i) (hvb i) (hvp i)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h1' : (k : ℝ) * ℓ (v i) ≤ k * (N * φ.evalZ (v i)) := by
      have : ((k • ℓ (v i) : ℤ) : ℝ) = (k : ℝ) * ℓ (v i) := by push_cast [nsmul_eq_mul]; ring
      rw [this] at h1; linarith
    have h3 : (ℓ (v i) : ℝ) ≤ N * φ.evalZ (v i) := le_of_mul_le_mul_left h1' hk'
    exact le_antisymm h3 h2
  · obtain ⟨k, c, hk, hkc⟩ := hu.2.2 β hβ hp he
    obtain ⟨k', hk', hmem⟩ := mem_ratCone.1 (ratCone_le huv (mem_ratCone_of_eq_sum hk c hkc))
    obtain ⟨c', hc'⟩ := AddSubmonoid.mem_closure_range_iff_of_fintype.1 hmem
    exact ⟨k', c', hk', hc'⟩

end Gen

theorem pull_pull_symm {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] (e : X ≃ₗ[O] X)
    (β : LinearMap.BilinForm ℤ X) : pull e.toLinearMap (pull e.symm.toLinearMap β) = β :=
  LinearMap.ext₂ fun a b => by simp [pull]

section Mod

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {φ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem perModule_bound (hP : IsPolyFanOn bar φ X) : ∃ N₀ : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X),
    IsCell bar φ δ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith bar φ N ℓ δ := by
  classical
  obtain ⟨S, hS, hcov⟩ := hP.finite
  let uT : (T : Finset (LinearMap.BilinForm ℤ X)) → Fin T.card → LinearMap.BilinForm ℤ X :=
    fun T i => (T.equivFin.symm i : LinearMap.BilinForm ℤ X)
  let D : Finset (LinearMap.BilinForm ℤ X) → ℕ := fun T =>
    if h : ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ StrictWith bar φ N ℓ (uT T) then h.choose else 0
  refine ⟨hS.toFinset.powerset.sup D, fun m δ hδ => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X m δ (fun _ => 1) hδ.mem hδ.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell bar φ γ' := CellClass.isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  choose k a hk hka using fun i => GlobalTheory.T.cell_generators_smul_mem_other_cellCone bar φ δ γ' c hδ hγ' hc hsum' i
  let J := Finset.univ.filter fun j => ∃ i, 0 < a i j
  let T := J.image γ
  have hTS : T ∈ hS.toFinset.powerset := by
    rw [Finset.mem_powerset]
    intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    exact hS.mem_toFinset.2 (hγS j)
  let w : Fin T.card → LinearMap.BilinForm ℤ X := fun t => pull e.symm.toLinearMap (uT T t)
  have hwj : ∀ t, ∃ j, (∃ i, 0 < a i j) ∧ w t = γ' j := by
    intro t
    obtain ⟨j, hj, hjt⟩ := Finset.mem_image.1 (T.equivFin.symm t).2
    refine ⟨j, (Finset.mem_filter.1 hj).2, ?_⟩
    show pull _ ((T.equivFin.symm t : LinearMap.BilinForm ℤ X)) = pull _ (γ j)
    rw [hjt]
  have hδw : ∀ i, δ i ∈ ratCone w := by
    intro i
    refine mem_ratCone.2 ⟨k i, hk i, ?_⟩
    rw [hka i]
    refine AddSubmonoid.sum_mem _ fun j _ => ?_
    by_cases hj : 0 < a i j
    · refine AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure ?_) _
      have hmem : γ j ∈ T := Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hj⟩, rfl⟩
      refine ⟨T.equivFin ⟨γ j, hmem⟩, ?_⟩
      simp [w, uT, γ']
    · rw [Nat.eq_zero_of_not_pos hj, zero_smul]; exact zero_mem _
  have hwδ : ∀ t, w t ∈ ratCone δ := by
    intro t
    obtain ⟨j, ⟨i, hij⟩, hj⟩ := hwj t
    obtain ⟨k', b, hk', hb⟩ := GlobalTheory.T.cell_generator_mem_cone_of_smul_combination bar φ δ γ' i (k i) (a i) hδ hγ' (hk i) (hka i) j hij
    rw [hj]
    exact mem_ratCone_of_eq_sum hk' b hb
  have hwb : ∀ t, w t ∈ balForms bar X := fun t => by
    obtain ⟨j, -, hj⟩ := hwj t; rw [hj]; exact hγ'.mem j
  have hwp : ∀ t y, 0 ≤ w t y y := fun t y => by
    obtain ⟨j, -, hj⟩ := hwj t; rw [hj]; exact hγ'.nonneg j y
  obtain ⟨N, ℓ, hN, hℓ⟩ := isStrict_iff.1 hδ.strict
  have hw : StrictWith bar φ N ℓ w := strictWith_of_ratCone hP hℓ hδ.mem hδ.nonneg hwb hwp hwδ hδw
  have hex : ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ StrictWith bar φ N ℓ (uT T) :=
    ⟨N, _, hN, StrictWith.of_pull e.symm.surjective hw⟩
  have hD : D T = hex.choose := dif_pos hex
  obtain ⟨ℓT, hNT, hT⟩ := hex.choose_spec
  have hT' : StrictWith bar φ hex.choose ℓT (fun t => pull e.toLinearMap (w t)) := by
    have : (fun t => pull e.toLinearMap (w t)) = uT T := funext fun t => pull_pull_symm e _
    rw [this]; exact hT
  have hTw := StrictWith.of_pull e.surjective hT'
  refine ⟨hex.choose, _, hNT, ?_, strictWith_of_ratCone hP hTw hwb hwp hδ.mem hδ.nonneg hδw hwδ⟩
  rw [← hD]
  exact Finset.le_sup hTS

end Mod

theorem uniform_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E))
    (hψ : IsPolyFan H.bar q ψ) : ∃ N₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
      [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell H.bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith H.bar ψ N ℓ γ := by
  classical
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField E q
  have key : ∀ k, letI := (hR k).1; ∃ N₀ : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)),
      IsCell H.bar ψ δ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ (R k) →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧
        StrictWith H.bar ψ N ℓ δ := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule_bound (hψ (R k) (hR k).2.2)
  choose N₀ hN₀ using key
  refine ⟨Finset.univ.sup N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ :=
    hN₀ k m (fun i => pull f.symm.toLinearMap (γ i)) (CellClass.isCell_pull_equiv hγ f.symm)
  exact ⟨N, _, hN, hNle.trans (Finset.le_sup (Finset.mem_univ k)), StrictWith.of_pull f.symm.surjective hℓ⟩

section Face

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {φ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem apply_eq_sum_of_inRCone [Module.Finite ℤ X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hβc : toReal β = ∑ i, c i • toReal (γ i))
    (g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : ((g β : ℤ) : ℝ) = ∑ i, c i * g (γ i) := by
  obtain ⟨w, rfl⟩ := exists_linW_eq X g
  rw [← evalW_toReal, hβc, evalW_sum]

theorem faceCut_data (hP : IsPolyFanOn bar φ X) [Module.Finite ℤ X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hγ : IsCell bar φ γ) {N NF : ℕ} (hN : 0 < N) {ℓ ℓF : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hℓ : StrictWith bar φ N ℓ γ) {s : Fin m' ↪ Fin m} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hh : IsFaceCut γ s h)
    (hF : StrictWith bar φ NF ℓF fun j => γ (s j)) :
    IsFaceCut γ s ((N : ℤ) • ℓF - (NF : ℤ) • ℓ) ∧ (∀ β, InRCone γ β → 0 < h β → 0 < ((N : ℤ) • ℓF - (NF : ℤ) • ℓ) β) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(((N : ℤ) • ℓF - (NF : ℤ) • ℓ) β) ≤ (NF : ℤ) * ℓ β := by
  set h' := (N : ℤ) • ℓF - (NF : ℤ) • ℓ with hh'
  have happ : ∀ β, h' β = N * ℓF β - NF * ℓ β := fun β => by simp [h']
  have hreal : ∀ j, ((h' (γ j) : ℤ) : ℝ) = N * ((ℓF (γ j) : ℝ) - NF * φ.evalZ (γ j)) := fun j => by
    rw [happ]; push_cast; rw [hℓ.1 j]; ring
  have hnn : ∀ j, 0 ≤ h' (γ j) := fun j => by
    have h1 := hF.2.1 (γ j) (hγ.mem j) (hγ.nonneg j)
    have : (0 : ℝ) ≤ h' (γ j) := by rw [hreal]; exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    exact_mod_cast this
  have hzero : ∀ j, h' (γ j) = 0 ↔ j ∈ Set.range s := by
    intro j
    constructor
    · intro h0
      have h0' : ((h' (γ j) : ℤ) : ℝ) = 0 := by rw [h0]; simp
      rw [hreal] at h0'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have he : (NF : ℝ) * φ.evalZ (γ j) = ℓF (γ j) := by
        rcases mul_eq_zero.1 h0' with hz | hz
        · exact absurd hz hN'
        · linarith
      obtain ⟨k, c, hk, hkc⟩ := hF.2.2 (γ j) (hγ.mem j) (hγ.nonneg j) he
      have hk0 : h (k • γ j) = 0 := by
        rw [hkc, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_nsmul, (hh.2 (s i)).2 ⟨i, rfl⟩, smul_zero]
      rw [map_nsmul] at hk0
      exact (hh.2 j).1 ((smul_eq_zero.1 hk0).resolve_left hk.ne')
    · rintro ⟨i, rfl⟩
      have h1 := hF.1 i
      have : ((h' (γ (s i)) : ℤ) : ℝ) = 0 := by rw [hreal, ← h1]; ring
      exact_mod_cast this
  refine ⟨⟨hnn, hzero⟩, fun β hβ hpos => ?_, fun β hβ hp => ?_⟩
  · obtain ⟨c, hc, hβc⟩ := hβ
    have hsum : (0 : ℝ) < ∑ i, c i * h (γ i) := by
      rw [← apply_eq_sum_of_inRCone hβc h]; exact_mod_cast hpos
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < c i * h (γ i) := by
      by_contra hcon
      push_neg at hcon
      exact absurd hsum (not_lt.2 (Finset.sum_nonpos hcon))
    have hci : 0 < c i := by
      rcases (hc i).lt_or_eq with hz | hz
      · exact hz
      · rw [← hz, zero_mul] at hi; exact absurd hi (lt_irrefl 0)
    have hhi : h (γ i) ≠ 0 := fun h0 => by rw [h0] at hi; simp at hi
    have h'i : 0 < h' (γ i) := lt_of_le_of_ne (hnn i) (fun e => hhi ((hh.2 i).2 ((hzero i).1 e.symm)))
    have : (0 : ℝ) < h' β := by
      rw [apply_eq_sum_of_inRCone hβc h']
      have hterm : ∀ j ∈ Finset.univ, 0 ≤ c j * (h' (γ j) : ℝ) := fun j _ =>
        mul_nonneg (hc j) (by exact_mod_cast hnn j)
      calc (0 : ℝ) < c i * h' (γ i) := mul_pos hci (by exact_mod_cast h'i)
        _ ≤ ∑ j, c j * (h' (γ j) : ℝ) := Finset.single_le_sum hterm (Finset.mem_univ i)
    exact_mod_cast this
  · have h1 := hF.2.1 β hβ hp
    have h2 := evalZ_nonneg hP hβ hp
    have h3 : (0 : ℝ) ≤ ℓF β := le_trans (mul_nonneg (Nat.cast_nonneg _) h2) h1
    have h4 : (0 : ℤ) ≤ ℓF β := by exact_mod_cast h3
    have h5 := mul_nonneg (Int.natCast_nonneg N) h4
    rw [happ]
    linarith

end Face

theorem exists_strict_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith H.bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  intro E _ _ _ H q ψ hDom hψ
  obtain ⟨N₀, hN₀⟩ := uniform_bound E H q ψ hψ
  refine ⟨N₀, N₀, fun X _ _ _ _ hX m γ hγ => ?_⟩
  obtain ⟨N, ℓ, hN, hNle, hℓ⟩ := hN₀ X hX m γ hγ
  refine ⟨N, ℓ, hN, hNle, hℓ, fun m' s h hh => ?_⟩
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hF := isCell_face_of_isFaceCut E H q ψ hψ X hX (hDom X) m γ hγ m' s h hh
  obtain ⟨NF, ℓF, -, hNFle, hℓF⟩ := hN₀ X hX m' _ hF
  obtain ⟨h1, h2, h3⟩ := faceCut_data (hψ X hX) hγ hN hℓ hh hℓF
  refine ⟨_, h1, h2, fun β hβ hp => (h3 β hβ hp).trans ?_⟩
  have hℓβ : (0 : ℤ) ≤ ℓ β := by
    have := le_trans (mul_nonneg (Nat.cast_nonneg _) (evalZ_nonneg (hψ X hX) hβ hp)) (hℓ.2.1 β hβ hp)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNFle) hℓβ

end GlobalTheory.PolFan.StrictData
