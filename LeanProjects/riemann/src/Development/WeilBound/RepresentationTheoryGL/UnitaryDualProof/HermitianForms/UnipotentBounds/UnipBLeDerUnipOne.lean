import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.StepForm

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.Asm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem blkAt_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    (blkAt k n N h g).val i j =
      if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then g.val ⟨i, hi⟩ ⟨j, hj⟩ else 0)
      else if i = j then 1 else 0 := by
  have key : ∀ x : Fin N, (finSumFinEquiv.symm (Fin.cast (Nat.add_sub_cancel' h).symm x) : Fin n ⊕ Fin (N - n)) =
      if hx : (x : ℕ) < n then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x - n, by omega⟩ := by
    intro x
    split_ifs with hx
    · have : Fin.cast (Nat.add_sub_cancel' h).symm x = Fin.castAdd (N - n) ⟨x, hx⟩ := Fin.ext rfl
      rw [this, finSumFinEquiv_symm_apply_castAdd]
    · have : Fin.cast (Nat.add_sub_cancel' h).symm x = Fin.natAdd n ⟨x - n, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, finSumFinEquiv_symm_apply_natAdd]
  simp only [blkAt, glCongr, blkGL, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
  simp [blkHom, reindex_apply]
  rw [key i, key j]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n <;> simp [hi, hj]
  · by_cases hj : (j : ℕ) < n
    · have : i ≠ j := fun e => hi (e ▸ hj)
      simp [hi, hj, this]
    · have e : ((⟨i - n, by omega⟩ : Fin (N - n)) = ⟨j - n, by omega⟩) ↔ i = j := by
        rw [Fin.ext_iff, Fin.ext_iff]; simp only; omega
      simp only [hi, hj, dite_false, fromBlocks_apply₂₂, one_apply, e]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem scalAt_eq (m N : ℕ) (h : m ≤ N) (z : kˣ) : scalAt k m N h z = aDiag k N m z := by
  ext i j
  rw [scalAt, blkAt_apply]
  show _ = diagonal (fun i : Fin N => if (i : ℕ) < m then (z : k) else 1) i j
  rw [diagonal_apply]
  by_cases hi : (i : ℕ) < m
  · by_cases hj : (j : ℕ) < m
    · simp only [hi, hj, dite_true, if_true, Units.coe_map]
      show (algebraMap k (Matrix (Fin m) (Fin m) k) (z : k)) ⟨i, hi⟩ ⟨j, hj⟩ = _
      rw [algebraMap_matrix_apply]
      simp [Fin.ext_iff]
    · have : i ≠ j := fun e => hj (e ▸ hi)
      simp [hi, hj, this]
  · by_cases hj : (j : ℕ) < m
    · have : i ≠ j := fun e => hi (e ▸ hj)
      simp [hi, this]
    · by_cases e : i = j
      · subst e; simp [hi]
      · simp [hi, e]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem blkAt_comm_aDiag (n m N : ℕ) (hn : n ≤ m) (h : n ≤ N) (g : GL (Fin n) k) (z : kˣ) :
    blkAt k n N h g * aDiag k N m z = aDiag k N m z * blkAt k n N h g := by
  ext i j
  show ((blkAt k n N h g).val * diagonal fun i : Fin N => if (i : ℕ) < m then (z : k) else 1) i j =
    (diagonal (fun i : Fin N => if (i : ℕ) < m then (z : k) else 1) * (blkAt k n N h g).val) i j
  rw [mul_diagonal, diagonal_mul, blkAt_apply]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · simp [hi, hj, show (i : ℕ) < m by omega, show (j : ℕ) < m by omega, mul_comm]
    · simp [hi, hj]
  · by_cases e : i = j
    · subst e; simp [hi, mul_comm]
    · simp [hi, e]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem continuous_blkAt [IsTopologicalRing k] (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    refine Continuous.units_map _ ?_
    show Continuous fun A : Matrix (Fin n) (Fin n) k => reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 1)
    fun_prop
  have h2 : Continuous (glCongr k (Nat.add_sub_cancel' h)) := by
    refine Continuous.units_map _ ?_
    show Continuous fun A : Matrix (Fin (n + (N - n))) (Fin (n + (N - n))) k =>
      reindex (finCongr (Nat.add_sub_cancel' h)) (finCongr (Nat.add_sub_cancel' h)) A
    fun_prop
  exact h2.comp h1

def stab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by show ρ 1 v = v; rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem twKer_mono {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {H K : Subgroup G} (hHK : H ≤ K) (χH : H →* ℂˣ) (χK : K →* ℂˣ)
    (hχ : ∀ h : H, χH h = χK (Subgroup.inclusion hHK h)) : twKer ρ H χH ≤ twKer ρ K χK := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  exact Submodule.subset_span ⟨Subgroup.inclusion hHK n, v, by rw [hχ]; rfl⟩

theorem twKer_eq_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) (hH : ∀ n : H, (n : G) = 1) : twKer ρ H χ = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro w ⟨n, v, rfl⟩
  have : n = 1 := Subtype.ext (hH n)
  subst this
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem colFix_apply {N n : ℕ} {g : GL (Fin N) k} (hg : g ∈ colFix k N n) (r c : Fin N) (hc : (c : ℕ) < n) :
    g.val r c = (1 : Matrix (Fin N) (Fin N) k) r c := by
  have := congrFun (hg c hc) r
  rw [mulVec_single_one] at this
  simp only [col_apply, Pi.single_apply] at this
  rw [one_apply, this]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem derUnip_eq_one {N n : ℕ} (h : N ≤ n) (u : derUnip k N n) : (u : GL (Fin N) k) = 1 := by
  ext r c
  exact colFix_apply (u.2.2) r c (by omega)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unipB_le_derUnip_one (N : ℕ) : unipB k (Fin N) ≤ derUnip k N 1 := by
  intro g hg
  refine ⟨hg, fun c hc => ?_⟩
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hg
  have hc0 : (c : ℕ) = 0 := by omega
  rw [mulVec_single_one]
  funext r
  simp only [Pi.single_apply]
  by_cases e : r = c
  · subst e; simp [h2]
  · rw [if_neg e]
    exact h1 r c (Fin.lt_def.2 (by have := Fin.val_ne_of_ne e; omega))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem lvlChar_eq (ψ : AddChar k Circle) (N n : ℕ) (u : derUnip k N n) :
    lvlChar k ψ N n u = whitChar ψ N (Subgroup.inclusion (derUnip_le_unipB k N n) u) := by
  simp only [lvlChar, whitCharFrom, whitChar, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 2
  refine Finset.sum_subset (fun p hp => ?_) (fun p hp hp' => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hp hp'
    have hlt := hp' hp
    show (u : GL (Fin N) k).val p.1 p.2 = 0
    rw [colFix_apply u.2.2 p.1 p.2 (by omega), one_apply_ne]
    intro e; rw [e] at hp; omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem twKer_lvl_le {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (ψ : AddChar k Circle) (n : ℕ) :
    twKer π (derUnip k N n) (lvlChar k ψ N n) ≤ twKer π (unipB k (Fin N)) (whitChar ψ N) :=
  twKer_mono π (derUnip_le_unipB k N n) _ _ (lvlChar_eq ψ N n)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem twKer_whit_le {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (ψ : AddChar k Circle) :
    twKer π (unipB k (Fin N)) (whitChar ψ N) ≤ twKer π (derUnip k N 1) (lvlChar k ψ N 1) := by
  refine twKer_mono π (unipB_le_derUnip_one N) _ _ (fun u => ?_)
  rw [lvlChar_eq]
  rfl

theorem nabs_nonneg (z : kˣ) : 0 ≤ nabs k z := NNReal.coe_nonneg _

section Desc

variable (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin N) k) V)

def Lvl (m : ℕ) (hm : m + 1 ≤ N) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  IsPsd B ∧ Kills ψ π (m + 1) B ∧ MirEq π m hm ((N : ℝ) - m - 1) B ∧
    (∀ v, B v v = 0 → v ∈ twKer π (unipB k (Fin N)) (whitChar ψ N)) ∧
    ∀ m₂ : ℕ, m + 1 ≤ m₂ → m₂ < N → ∀ z : kˣ, nabs k z < 1 → ∀ v,
      Summable fun i : ℕ => (nabs k z ^ (i * m₂ * (N - m₂ - 1)))⁻¹ *
        (B (π (aDiag k N m₂ (z ^ i)) v) (π (aDiag k N m₂ (z ^ i)) v)).re

theorem lvl_top (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hh : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) (hi : ∀ g v w, B (π g v) (π g w) = B v w)
    (m : ℕ) (hm : m + 1 ≤ N) (hmN : m + 1 = N) : Lvl ψ π m hm B := by
  refine ⟨⟨hh, fun v => ?_⟩, ?_, ?_, ?_, ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  · intro v hv w
    rw [twKer_eq_bot π _ _ (derUnip_eq_one (by omega))] at hv
    rw [(Submodule.mem_bot ℂ).1 hv]
    simp
  · intro p _ v w
    rw [hi]
    have : ((N : ℝ) - m - 1) = 0 := by rw [← hmN]; push_cast; ring
    rw [this, Real.rpow_zero]
    simp
  · intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact zero_mem _
    · have := hp v hv0
      rw [hv] at this
      simp at this
  · intro m₂ h1 h2
    omega

variable (hψc : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψc hψ1

theorem lvl_step (hS : StepForm k) (hsm : IsSmooth π) (m : ℕ) (hm : m + 2 ≤ N) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : Lvl ψ π (m + 1) hm B) : ∃ B', Lvl ψ π m (by omega) B' := by
  obtain ⟨hpsd, hK, hM, hrad, hsum⟩ := hB
  obtain ⟨B', hpsd', hK', hrad', hM', hdom, hsum'⟩ := hS ψ hψc hψ1 m N hm V π hsm _ B hpsd hK hM
  refine ⟨B', hpsd', hK', ?_, ?_, ?_⟩
  · have e : ((N : ℝ) - ((m + 1 : ℕ) : ℝ) - 1) + 1 = (N : ℝ) - m - 1 := by push_cast; ring
    rw [e] at hM'
    exact hM'
  · intro v hv
    refine (sup_le (twKer_lvl_le π ψ (m + 1)) ?_) (hrad' v hv)
    intro u hu
    exact hrad u (by rw [LinearMap.mem_ker.1 hu]; rfl)
  · intro m₂ h1 h2 z hz v
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · refine (hsum' z hz v).congr (fun i => ?_)
      rw [scalAt_eq]
      congr 1
      have e : ((i * (m + 1) * (N - (m + 1) - 1) : ℕ) : ℝ) =
          (i : ℝ) * ((m : ℝ) + 1) * ((N : ℝ) - ((m + 1 : ℕ) : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.sub_sub, Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [Real.rpow_neg (nabs_nonneg z), ← e, Real.rpow_natCast]
    · have hs := hsum m₂ hlt h2 z hz v
      let K : Subgroup (GL (Fin (m + 1)) k) := (stab π v).comap (blkAt k (m + 1) N (by omega))
      have hKo : IsOpen (K : Set (GL (Fin (m + 1)) k)) :=
        (hsm v).preimage (continuous_blkAt (m + 1) N (by omega))
      obtain ⟨C, hC⟩ := hdom K hKo
      refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hs.mul_left (max C 0))
      · exact mul_nonneg (inv_nonneg.2 (pow_nonneg (nabs_nonneg z) _)) (hpsd'.2 _)
      · have hfix : ∀ g ∈ K, π (blkAt k (m + 1) N (by omega) g) (π (aDiag k N m₂ (z ^ i)) v) =
            π (aDiag k N m₂ (z ^ i)) v := by
          intro g hg
          have hg' : π (blkAt k (m + 1) N (by omega) g) v = v := hg
          rw [← Module.End.mul_apply, ← map_mul, blkAt_comm_aDiag (m + 1) m₂ N (by omega), map_mul,
            Module.End.mul_apply, hg']
        have h3 := hC _ hfix
        have hw : 0 ≤ (nabs k z ^ (i * m₂ * (N - m₂ - 1)))⁻¹ := inv_nonneg.2 (pow_nonneg (nabs_nonneg z) _)
        have hb := hpsd.2 (π (aDiag k N m₂ (z ^ i)) v)
        calc _ ≤ (nabs k z ^ (i * m₂ * (N - m₂ - 1)))⁻¹ * (C * (B (π (aDiag k N m₂ (z ^ i)) v)
                (π (aDiag k N m₂ (z ^ i)) v)).re) := mul_le_mul_of_nonneg_left h3 hw
          _ ≤ (nabs k z ^ (i * m₂ * (N - m₂ - 1)))⁻¹ * (max C 0 * (B (π (aDiag k N m₂ (z ^ i)) v)
                (π (aDiag k N m₂ (z ^ i)) v)).re) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hb) hw
          _ = _ := by ring

theorem lvl_all (hS : StepForm k) (hsm : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hh : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re)
    (hi : ∀ g v w, B (π g v) (π g w) = B v w) :
    ∀ d m (hm : m + 1 ≤ N), m + 1 + d = N → ∃ B', Lvl ψ π m hm B' := by
  intro d
  induction d with
  | zero => exact fun m hm hd => ⟨B, lvl_top ψ π B hh hp hi m hm (by omega)⟩
  | succ d ih =>
    intro m hm hd
    obtain ⟨B₁, hB₁⟩ := ih (m + 1) (by omega) (by omega)
    exact lvl_step ψ π hψc hψ1 hS hsm m (by omega) B₁ hB₁

end Desc

variable (k) in

theorem asmForm : AsmForm k := by
  intro hS ψ hψc hψ1 N V _ _ π hsm hU
  obtain ⟨B, hh, hp, hi⟩ := hU
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨B, hh, fun v => ?_, fun v => ?_, fun m h1 h2 => by omega⟩
    · by_cases hv : v = 0
      · simp [hv]
      · exact (hp v hv).le
    · rw [twKer_eq_bot π _ _ (fun u => Units.ext (Subsingleton.elim _ _)), Submodule.mem_bot]
      constructor
      · intro h
        by_contra hv
        have := hp v hv
        rw [h] at this
        simp at this
      · rintro rfl
        simp
  · obtain ⟨Q, hpsd, hK, -, hrad, hsum⟩ := lvl_all ψ π hψc hψ1 hS hsm B hh hp hi (N - 1) 0 (by omega) (by omega)
    exact ⟨Q, hpsd.1, hpsd.2, fun v => ⟨hrad v, fun hv => hK v (twKer_whit_le π ψ hv) v⟩,
      fun m h1 h2 z hz v => hsum m (by omega) h2 z hz v⟩

end PositivityTheory.RgUd.Form.Asm
