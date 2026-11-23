import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsVBallSubset
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsIsUnitAddMul
import Development.WeilBound.ThetaLifts.SphericalLattices.LattEq

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

section Int

variable {k : Type} [Field k] [ValuativeRel k]

theorem intM_zero {m p : Type} : IntM (0 : Matrix m p k) := fun _ _ => zero_mem _

theorem IntM.add {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z + Z') :=
  fun i j => add_mem (h i j) (h' i j)

theorem IntM.sub {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z - Z') :=
  fun i j => sub_mem (h i j) (h' i j)

theorem IntM.neg {m p : Type} {Z : Matrix m p k} (h : IntM Z) : IntM (-Z) := fun i j => neg_mem (h i j)

theorem IntM.smul {m p : Type} {c : k} (hc : c ∈ 𝒪[k]) {Z : Matrix m p k} (h : IntM Z) : IntM (c • Z) :=
  fun i j => mul_mem hc (h i j)

theorem intM_map {m p : Type} (A : Matrix m p 𝒪[k]) : IntM (A.map (algebraMap 𝒪[k] k)) := fun i j => (A i j).2

theorem IntM.mul {m p q : Type} [Fintype p] {P : Matrix m p k} {Q : Matrix p q k} (hP : IntM P) (hQ : IntM Q) :
    IntM (P * Q) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hP i l) (hQ l j)

variable {n d : ℕ}

theorem below_refl (t : k) (Y : Matrix (Fin n) (Fin d) k) : Below t Y Y :=
  ⟨1, 0, intM_zero, by simp [Matrix.map_one]⟩

theorem below_trans {t : k} {Y₁ Y₂ Y₃ : Matrix (Fin n) (Fin d) k} (h₁ : Below t Y₁ Y₂) (h₂ : Below t Y₂ Y₃) :
    Below t Y₁ Y₃ := by
  obtain ⟨A, Z, hZ, rfl⟩ := h₁
  obtain ⟨B, Z', hZ', rfl⟩ := h₂
  refine ⟨A * B, A.map (algebraMap 𝒪[k] k) * Z' + Z, (intM_map A).mul hZ' |>.add hZ, ?_⟩
  rw [Matrix.map_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add, add_assoc]

theorem below_int {t : k} (ht : t ∈ 𝒪[k]) {Y Y₀ : Matrix (Fin n) (Fin d) k} (h : Below t Y Y₀) (h₀ : IntM (t • Y₀)) :
    IntM (t • Y) := by
  obtain ⟨A, Z, hZ, rfl⟩ := h
  have : t • (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) = A.map (algebraMap 𝒪[k] k) * (t • Y₀) + t • (t • Z) := by
    rw [smul_add, Matrix.mul_smul]
  rw [this]
  exact ((intM_map A).mul h₀).add ((hZ.smul ht).smul ht)

theorem below_iff_rows (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Below t Y Y₀ ↔ ∀ i, Y i ∈ latt t Y₀ := by
  constructor
  · rintro ⟨A, Z, hZ, rfl⟩ i
    have e : (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) i =
        ∑ l, A i l • Y₀ l + ∑ j, (⟨Z i j, hZ i j⟩ : 𝒪[k]) • (t • (Pi.single j 1 : Fin d → k)) := by
      funext j'
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
      exact Finset.sum_congr rfl fun _ _ => rfl
    rw [e]
    refine add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨l, rfl⟩)))
      (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  · intro h
    have hr : Set.range Y₀ ∪ Set.range (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) =
        Set.range (Sum.elim Y₀ fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) := (Set.Sum.elim_range _ _).symm
    have h' : ∀ i, ∃ c : Fin n ⊕ Fin d → 𝒪[k],
        ∑ x, c x • Sum.elim Y₀ (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) x = Y i := by
      intro i
      have := h i
      rw [latt, hr] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using h'
    refine ⟨Matrix.of fun i l => c i (Sum.inl l), Matrix.of fun i j => (c i (Sum.inr j) : k),
      fun i j => (c i (Sum.inr j)).2, ?_⟩
    ext i j
    have := congrFun (hc i) j
    rw [Fintype.sum_sum_type] at this
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← this]
    congr 1
    show ∑ x, (c i (Sum.inr x) : k) * (t • (Pi.single x 1 : Fin d → k)) j = _
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp [mul_comm]

end Int

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem below_iff {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ Y, Below t Y Y₀ ↔ IntM (Y * h.1) := by
  obtain ⟨h, hh⟩ := latt_eq ht Y₀
  refine ⟨h, fun Y => ?_⟩
  rw [below_iff_rows]
  simp only [hh, IntM]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

def bsetoid (t : k) : Setoid (Matrix (Fin n) (Fin d) k) where
  r Y Y' := Below t Y Y' ∧ Below t Y' Y
  iseqv := ⟨fun Y => ⟨below_refl t Y, below_refl t Y⟩, fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨below_trans h.1 h'.1, below_trans h'.2 h.2⟩⟩

theorem mk_eq_iff {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} :
    Quotient.mk (bsetoid t) Y = Quotient.mk (bsetoid t) Y' ↔ Below t Y Y' ∧ Below t Y' Y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem out_rel {t : k} (Y : Matrix (Fin n) (Fin d) k) :
    Below t (Quotient.mk (bsetoid t) Y).out Y ∧ Below t Y (Quotient.mk (bsetoid t) Y).out :=
  mk_eq_iff.1 (Quotient.out_eq _)

def gens (k : Type) [Field k] [ValuativeRel k] (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k → ℂ) :=
  {f | ∃ h : GL (Fin d) k, f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]}
    (fun _ => (1 : ℂ)) (Y * h.1)}

theorem latSt : LatSt := by
  intro k _ _ _ _ n d Φ hΦ hK
  classical
  obtain ⟨h1, h2⟩ := hΦ
  obtain ⟨t, ht0, htO, hsupp, hinv⟩ := sb_bound h1 h2
  obtain ⟨S, hS⟩ := finite_cover (m := Fin n) (p := Fin d) t ht0

  have key : ∀ Y Y', Below t Y Y' → Below t Y' Y → Φ Y = Φ Y' := by
    intro Y Y' a b
    obtain ⟨U, hU, Z, hZ, rfl⟩ := orbit a b
    rw [hinv _ _ hZ]
    have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
    have := hK (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit) ⟨hu.unit, rfl⟩ Y'
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        U.map (algebraMap 𝒪[k] k) := rfl
    rw [← e]
    exact this
  set s := bsetoid (n := n) (d := d) t with hs
  set T : Finset (Quotient s) := (S.filter fun y => IntM (t • y)).image (Quotient.mk s) with hT
  have memT : ∀ Y, IntM (t • Y) → Quotient.mk s Y ∈ T := by
    intro Y hY
    obtain ⟨y, hy, Z, hZ, rfl⟩ := hS Y hY
    have hy' : IntM (t • y) := by
      have e : t • y = t • (y + t • Z) - t • (t • Z) := by rw [smul_add]; abel
      rw [e]; exact hY.sub ((hZ.smul htO).smul htO)
    refine Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hy'⟩, mk_eq_iff.2 ⟨?_, ?_⟩⟩
    · exact ⟨1, -Z, hZ.neg, by simp [Matrix.map_one]⟩
    · exact ⟨1, Z, hZ, by simp [Matrix.map_one]⟩
  have outT : ∀ c ∈ T, IntM (t • c.out) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact below_int htO (out_rel y).1 (Finset.mem_filter.1 hy).2
  let e : Quotient s → Matrix (Fin n) (Fin d) k → ℂ := fun c Y => if Quotient.mk s Y = c then 1 else 0
  let F : Quotient s → Finset (Quotient s) := fun c => T.filter fun c' => Below t c'.out c.out ∧ c' ≠ c
  have hi : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) ∈ Submodule.span ℂ (gens k n d) := by
    intro c _
    obtain ⟨h, hh⟩ := below_iff ht0 c.out
    refine Submodule.subset_span ⟨h, funext fun Y => ?_⟩
    by_cases hY : Below t Y c.out
    · rw [if_pos hY, Set.indicator_of_mem ((hh Y).1 hY)]
    · rw [if_neg hY, Set.indicator_of_notMem (fun h' => hY ((hh Y).2 h'))]
  have hdec : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) = e c + ∑ c' ∈ F c, e c' := by
    intro c hc
    funext Y
    simp only [Pi.add_apply, Finset.sum_apply]
    by_cases hB : Below t Y c.out
    · rw [if_pos hB]
      have hq : Quotient.mk s Y ∈ T := memT Y (below_int htO hB (outT c hc))
      by_cases hqc : Quotient.mk s Y = c
      · have h0 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
          simp only [e]
          rw [if_neg]
          intro h
          exact (Finset.mem_filter.1 hc').2.2 (h.symm.trans hqc)
        rw [h0, add_zero]
        simp only [e]
        rw [if_pos hqc]
      · have h0 : ∑ c' ∈ F c, e c' Y = 1 := by
          simp only [e]
          rw [Finset.sum_ite_eq, if_pos]
          exact Finset.mem_filter.2 ⟨hq, below_trans (out_rel Y).1 hB, hqc⟩
        rw [h0]
        simp only [e]
        rw [if_neg hqc, zero_add]
    · rw [if_neg hB]
      have h1 : e c Y = 0 := by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        rw [← h]
        exact (out_rel Y).2
      have h2 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        have h3 := (Finset.mem_filter.1 hc').2.1
        rw [← h] at h3
        exact below_trans (out_rel Y).2 h3
      rw [h1, h2, add_zero]
  have he : ∀ m, ∀ c ∈ T, (F c).card = m → e c ∈ Submodule.span ℂ (gens k n d) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc hm
      have hsum : ∑ c' ∈ F c, e c' ∈ Submodule.span ℂ (gens k n d) := by
        refine Submodule.sum_mem _ fun c' hc' => ?_
        have hc'T := (Finset.mem_filter.1 hc').1
        refine ih (F c').card ?_ c' hc'T rfl
        rw [← hm]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨c', hc', fun h => (Finset.mem_filter.1 h).2.2 rfl⟩
        · intro c'' hc''
          obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hc''
          obtain ⟨-, h4, h5⟩ := Finset.mem_filter.1 hc'
          refine Finset.mem_filter.2 ⟨h1, below_trans h2 h4, fun h => h5 ?_⟩
          rw [← Quotient.out_eq c', ← Quotient.out_eq c]
          refine mk_eq_iff.2 ⟨h4, ?_⟩
          rw [← h]
          exact h2
      have := Submodule.sub_mem _ (hi c hc) hsum
      rw [hdec c hc, add_sub_cancel_right] at this
      exact this
  have hΦ : Φ = ∑ c ∈ T, Φ c.out • e c := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, e, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hY : IntM (t • Y)
    · rw [if_pos (memT Y hY)]
      exact key _ _ (out_rel Y).2 (out_rel Y).1
    · rw [if_neg]
      · by_contra h
        exact hY (hsupp Y h)
      · intro hq
        exact hY (below_int htO (out_rel Y).2 (outT _ hq))
  rw [hΦ]
  exact Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (he _ c hc rfl)

end PositivityTheory.Sph

end
