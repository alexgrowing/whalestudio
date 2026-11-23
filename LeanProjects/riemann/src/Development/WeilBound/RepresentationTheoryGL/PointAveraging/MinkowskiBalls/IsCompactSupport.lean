import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

noncomputable section

namespace PositivityTheory.Rg.Ming.BallA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem isOpen_cb (a : k) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen {y : k | valuation k (y - a) ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
  have hz' : valuation k (z - y) ≤ γ := le_of_lt hz
  have e : z - a = (z - y) + (y - a) := by ring
  show valuation k (z - a) ≤ γ
  rw [e]
  exact Valuation.map_add_le _ hz' hy

theorem isCompact_cb (a : k) (γ : ValueGroupWithZero k) :
    IsCompact {y : k | valuation k (y - a) ≤ γ} := by
  have h := (IsNonarchimedeanLocalField.isCompact_closedBall k γ).image (continuous_add_const a)
  convert h using 1
  ext y
  constructor
  · intro hy
    exact ⟨y - a, hy, sub_add_cancel y a⟩
  · rintro ⟨x, hx, rfl⟩
    show valuation k (x + a - a) ≤ γ
    rw [add_sub_cancel_right]
    exact hx

theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  exact ⟨fun h i _ l _ => h i l, fun h i l => h i trivial l trivial⟩

theorem mem_ballM_self (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem ballM_mono {c c' : kˣ} (h : valuation k (c : k) ≤ valuation k (c' : k)) (x : Matrix (Fin n) (Fin r) k) :
    ballM c x ⊆ ballM c' x := fun _ hy i l => (hy i l).trans h

theorem ballM_eq_of_mem {c : kˣ} {x x₀ : Matrix (Fin n) (Fin r) k} (hx : x ∈ ballM c x₀) :
    ballM c x = ballM c x₀ := by
  ext y
  constructor
  · intro hy i l
    have e : y i l - x₀ i l = (y i l - x i l) + (x i l - x₀ i l) := by ring
    rw [e]
    exact Valuation.map_add_le _ (hy i l) (hx i l)
  · intro hy i l
    have e : y i l - x i l = (y i l - x₀ i l) - (x i l - x₀ i l) := by ring
    rw [e]
    exact Valuation.map_sub_le _ (hy i l) (hx i l)

theorem mem_symm {c : kˣ} {x x₀ : Matrix (Fin n) (Fin r) k} (hx : x ∈ ballM c x₀) : x₀ ∈ ballM c x := by
  rw [ballM_eq_of_mem hx]; exact mem_ballM_self c x₀

theorem isOpen_ballM (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) : IsOpen (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_set_pi Set.finite_univ
    (fun l _ => isOpen_cb _ (by simp)))

theorem isCompact_ballM (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) : IsCompact (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact isCompact_univ_pi (fun i => isCompact_univ_pi (fun l => isCompact_cb _ _))

theorem disj {c : kˣ} {x x₀ : Matrix (Fin n) (Fin r) k} (hx : x ∉ ballM c x₀) :
    ∀ y ∈ ballM c x, y ∉ ballM c x₀ := by
  intro y hy hy0
  apply hx
  rw [← ballM_eq_of_mem hy0, ballM_eq_of_mem hy]
  exact mem_ballM_self c x

theorem isClosed_ballM (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) : IsClosed (ballM c x₀) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨ballM c x, fun y hy => disj hx y hy, isOpen_ballM c x, mem_ballM_self c x⟩

theorem indicator_mem_SB (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀).indicator (fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ ballM c x₀
    · refine ⟨ballM c x₀, isOpen_ballM c x₀, hx, fun x' hx' => ?_⟩
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
    · refine ⟨ballM c x, isOpen_ballM c x, mem_ballM_self c x, fun x' hx' => ?_⟩
      rw [Set.indicator_of_notMem (disj hx x' hx'), Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' (isCompact_ballM c x₀) (isClosed_ballM c x₀)
      (fun x hx => Set.indicator_of_notMem hx _)

theorem KO_entry {N : ℕ} {h : GL (Fin N) k} (hh : h ∈ KO k (Fin N)) (i j : Fin N) :
    valuation k (h.val i j) ≤ 1 := by
  obtain ⟨H, rfl⟩ := hh
  exact (H.val i j).2

theorem left_le {m p q : ℕ} (h : Matrix (Fin m) (Fin p) k) (y : Matrix (Fin p) (Fin q) k)
    {γ : ValueGroupWithZero k} (hh : ∀ i j, valuation k (h i j) ≤ 1) (hy : ∀ i j, valuation k (y i j) ≤ γ) :
    ∀ i j, valuation k ((h * y) i j) ≤ γ := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  calc _ ≤ 1 * γ := mul_le_mul' (hh i l) (hy l j)
    _ = γ := one_mul γ

theorem right_le {m p q : ℕ} (y : Matrix (Fin m) (Fin p) k) (g : Matrix (Fin p) (Fin q) k)
    {γ : ValueGroupWithZero k} (hy : ∀ i j, valuation k (y i j) ≤ γ) (hg : ∀ i j, valuation k (g i j) ≤ 1) :
    ∀ i j, valuation k ((y * g) i j) ≤ γ := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  calc _ ≤ γ * 1 := mul_le_mul' (hy i l) (hg l j)
    _ = γ := mul_one γ

theorem KO_fwd {c : kˣ} {h : GL (Fin n) k} (hh : h ∈ KO k (Fin n)) {g : GL (Fin r) k} (hg : g ∈ KO k (Fin r))
    {x x₀ : Matrix (Fin n) (Fin r) k} (hx : x ∈ ballM c x₀) :
    h.val * x * g.val ∈ ballM c (h.val * x₀ * g.val) := by
  intro i l
  have e : h.val * x * g.val - h.val * x₀ * g.val = h.val * (x - x₀) * g.val := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [← Matrix.sub_apply, e]
  exact right_le _ _ (left_le _ _ (KO_entry hh) (fun i l => by rw [Matrix.sub_apply]; exact hx i l))
    (KO_entry hg) i l

theorem KO_inv {c : kˣ} {h : GL (Fin n) k} (hh : h ∈ KO k (Fin n)) {g : GL (Fin r) k} (hg : g ∈ KO k (Fin r))
    {x x₀ : Matrix (Fin n) (Fin r) k} :
    h.val * x * g.val ∈ ballM c (h.val * x₀ * g.val) ↔ x ∈ ballM c x₀ := by
  refine ⟨fun hx => ?_, KO_fwd hh hg⟩
  have := KO_fwd (inv_mem hh) (inv_mem hg) hx
  have e : ∀ y : Matrix (Fin n) (Fin r) k, (h⁻¹).val * (h.val * y * g.val) * (g⁻¹).val = y := by
    intro y
    simp [Matrix.mul_assoc]
  rwa [e, e] at this

theorem exists_small (a : k) {t : Set k} (ht : t ∈ nhds a) :
    ∃ c : kˣ, valuation k (c : k) < 1 ∧ {y : k | valuation k (y - a) ≤ valuation k (c : k)} ⊆ t := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff').mp ht
  obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  rcases lt_or_ge (γ : ValueGroupWithZero k) 1 with h1 | h1
  · obtain ⟨ρ, hρ⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      exact γ.ne_zero (by simpa using hρ.symm)
    have hv0 : valuation k ρ ≠ 0 := by simpa using hρ0
    have hlt : valuation k ρ * valuation k ρ < valuation k ρ := by
      rw [hρ] at hv0 ⊢
      simpa [hv0] using h1
    refine ⟨Units.mk0 (ρ ^ 2) (pow_ne_zero 2 hρ0), ?_, fun y hy => hγ ?_⟩
    · simp only [Units.val_mk0, pow_two, map_mul]
      exact hlt.trans (hρ ▸ h1)
    · simp only [Set.mem_ofPred_eq, Units.val_mk0, pow_two, map_mul] at hy ⊢
      rw [← hρ]
      exact hy.trans_lt hlt
  · refine ⟨Units.mk0 r' hr', hr1, fun y hy => hγ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    exact hy.trans_lt (hr1.trans_le h1)

theorem prod_le {ι : Type*} (s : Finset ι) (f : ι → kˣ) (hf : ∀ j, valuation k (f j : k) ≤ 1) {i : ι}
    (hi : i ∈ s) : valuation k ((∏ j ∈ s, f j : kˣ) : k) ≤ valuation k (f i : k) := by
  classical
  rw [Units.coe_prod, map_prod, ← Finset.mul_prod_erase s _ hi]
  exact mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hf j)

theorem nhds_entry (x₀ : Matrix (Fin n) (Fin r) k) {U : Set (Matrix (Fin n) (Fin r) k)} (hU : U ∈ nhds x₀) :
    ∃ t : Fin n → Fin r → Set k, (∀ i l, t i l ∈ nhds (x₀ i l)) ∧
      ∀ x : Matrix (Fin n) (Fin r) k, (∀ i l, x i l ∈ t i l) → x ∈ U := by
  have h1 : U ∈ Filter.pi (fun i => nhds (x₀ i)) := (nhds_pi (a := (x₀ : Fin n → Fin r → k))).ge hU
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.mp h1
  have h2 : ∀ i, ∃ s : Fin r → Set k, (∀ l, s l ∈ nhds (x₀ i l)) ∧
      ∀ y : Fin r → k, (∀ l, y l ∈ s l) → y ∈ t i := by
    intro i
    have h3 : t i ∈ Filter.pi (fun l => nhds (x₀ i l)) := (nhds_pi (a := x₀ i)).ge (ht i)
    obtain ⟨J, -, s, hs, hsub'⟩ := Filter.mem_pi.mp h3
    exact ⟨s, hs, fun y hy => hsub' (fun l _ => hy l)⟩
  choose s hs hsub2 using h2
  exact ⟨s, hs, fun x hx => hsub (fun i _ => hsub2 i (x i) (hx i))⟩

theorem nhds_ball (x₀ : Matrix (Fin n) (Fin r) k) {U : Set (Matrix (Fin n) (Fin r) k)} (hU : U ∈ nhds x₀) :
    ∃ c : kˣ, valuation k (c : k) < 1 ∧ ballM c x₀ ⊆ U := by
  obtain ⟨t, ht, hsub⟩ := nhds_entry x₀ hU
  have h2 : ∀ p : Fin n × Fin r, ∃ c : kˣ, valuation k (c : k) < 1 ∧
      {y : k | valuation k (y - x₀ p.1 p.2) ≤ valuation k (c : k)} ⊆ t p.1 p.2 :=
    fun p => exists_small _ (ht p.1 p.2)
  choose cc hcc1 hcc2 using h2
  obtain ⟨c₁, hc₁, -⟩ := exists_small (0 : k) (Filter.univ_mem (f := nhds (0 : k)))
  refine ⟨c₁ * ∏ p, cc p, ?_, fun x hx => hsub x fun i l => hcc2 (i, l)
    (show valuation k (x i l - x₀ i l) ≤ valuation k (cc (i, l) : k) from ?_)⟩
  · rw [Units.val_mul, map_mul]
    exact (mul_le_of_le_one_right' (by
      rw [Units.coe_prod, map_prod]; exact Finset.prod_le_one' fun j _ => (hcc1 j).le)).trans_lt hc₁
  · refine (hx i l).trans ?_
    rw [Units.val_mul, map_mul]
    exact (mul_le_of_le_one_left' hc₁.le).trans (prod_le _ _ (fun j => (hcc1 j).le) (Finset.mem_univ _))

variable {M : Type} [TopologicalSpace M]

theorem isCompact_support {f : M → ℂ} (hf : f ∈ SB M) : IsCompact (Function.support f) := by
  have hcl : IsClosed (Function.support f) := by
    have e : Function.support f = {x | f x = 0}ᶜ := by ext; simp
    rw [e]
    exact (hf.1.isOpen_fiber 0).isClosed_compl
  exact hf.2.isCompact.of_isClosed_subset hcl (subset_tsupport f)

theorem uniform (Ψ : SB (Matrix (Fin n) (Fin r) k)) :
    ∃ c₀ : kˣ, ∀ c : kˣ, valuation k (c : k) ≤ valuation k (c₀ : k) →
      ∀ y, Ψ.1 y ≠ 0 → ∀ z ∈ ballM c y, Ψ.1 z = Ψ.1 y := by
  have hK := isCompact_support Ψ.2
  have h1 : ∀ y : Matrix (Fin n) (Fin r) k, ∃ c : kˣ, valuation k (c : k) < 1 ∧
      ballM c y ⊆ {z | Ψ.1 z = Ψ.1 y} :=
    fun y => nhds_ball y ((Ψ.2.1.isOpen_fiber (Ψ.1 y)).mem_nhds rfl)
  choose cy hcy1 hcy2 using h1
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun y => ballM (cy y) y) (fun y => isOpen_ballM _ _)
    (fun z _ => Set.mem_iUnion.2 ⟨z, mem_ballM_self _ z⟩)
  refine ⟨∏ y ∈ T, cy y, fun c hc y hy z hz => ?_⟩
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.1 (hT hy)
  have hle : valuation k (c : k) ≤ valuation k (cy w : k) :=
    hc.trans (prod_le _ _ (fun j => (hcy1 j).le) hw)
  have hzw : z ∈ ballM (cy w) w := by
    rw [← ballM_eq_of_mem hyw]; exact ballM_mono hle y hz
  have e1 : Ψ.1 z = Ψ.1 w := hcy2 w hzw
  have e2 : Ψ.1 y = Ψ.1 w := hcy2 w hyw
  rw [e1, e2]

def rep (c : kˣ) (y : Matrix (Fin n) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  Classical.epsilon (fun z => z ∈ ballM c y)

theorem rep_mem (c : kˣ) (y : Matrix (Fin n) (Fin r) k) : rep c y ∈ ballM c y :=
  Classical.epsilon_spec (p := fun z => z ∈ ballM c y) ⟨y, mem_ballM_self c y⟩

theorem rep_eq {c : kˣ} {y y' : Matrix (Fin n) (Fin r) k} (h : y' ∈ ballM c y) : rep c y' = rep c y := by
  unfold rep
  rw [ballM_eq_of_mem h]

theorem decomp (Ψ : SB (Matrix (Fin n) (Fin r) k)) :
    ∃ c₀ : kˣ, ∀ c : kˣ, valuation k (c : k) ≤ valuation k (c₀ : k) →
      ∃ S : Finset (Matrix (Fin n) (Fin r) k), (∀ x ∈ S, ∀ y ∈ ballM c x, Ψ.1 y = Ψ.1 x ∧ Ψ.1 x ≠ 0) ∧
        Ψ.1 = ∑ x ∈ S, Ψ.1 x • (ballM c x).indicator (fun _ => (1 : ℂ)) := by
  classical
  obtain ⟨c₀, hc₀⟩ := uniform Ψ
  refine ⟨c₀, fun c hc => ?_⟩
  have D := hc₀ c hc
  have hK := isCompact_support Ψ.2
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun y => ballM c y) (fun y => isOpen_ballM _ _)
    (fun z _ => Set.mem_iUnion.2 ⟨z, mem_ballM_self _ z⟩)

  have hS : ∀ x ∈ (T.filter fun y => Ψ.1 y ≠ 0).image (rep c), Ψ.1 x ≠ 0 ∧ rep c x = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    have hy0 := (Finset.mem_filter.1 hy).2
    exact ⟨by rw [D y hy0 _ (rep_mem c y)]; exact hy0, rep_eq (rep_mem c y)⟩
  refine ⟨(T.filter fun y => Ψ.1 y ≠ 0).image (rep c), fun x hx y hy => ?_, ?_⟩
  · exact ⟨D x (hS x hx).1 y hy, (hS x hx).1⟩
  · funext z
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : Ψ.1 z = 0
    · rw [hz]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      have hzx : z ∉ ballM c x := fun hzx => (hS x hx).1 (by rw [← D x (hS x hx).1 z hzx]; exact hz)
      rw [Set.indicator_of_notMem hzx, mul_zero]
    · obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.1 (hT hz)
      have hy0 : Ψ.1 y ≠ 0 := by rw [D z hz y (mem_symm hzy)]; exact hz
      have hmem : rep c y ∈ (T.filter fun y => Ψ.1 y ≠ 0).image (rep c) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hyT, hy0⟩)
      have hz' : z ∈ ballM c (rep c y) := by rw [ballM_eq_of_mem (rep_mem c y)]; exact hzy
      rw [Finset.sum_eq_single (rep c y)]
      · rw [Set.indicator_of_mem hz', mul_one]
        exact D _ (hS _ hmem).1 z hz'
      · intro s hs hne
        have hzs : z ∉ ballM c s := by
          intro hzs
          apply hne
          rw [← (hS s hs).2, ← rep_eq hzs, rep_eq hzy]
        rw [Set.indicator_of_notMem hzs, mul_zero]
      · intro h; exact absurd hmem h

end PositivityTheory.Rg.Ming.BallA

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.BallA in
theorem ball : BallSt := by
  intro k _ _ _ _ n r
  exact ⟨fun c x₀ => ⟨isOpen_ballM c x₀, isCompact_ballM c x₀, indicator_mem_SB c x₀,
    fun x hx => ballM_eq_of_mem hx, fun h hh g hg x => KO_inv hh hg⟩,
    fun x₀ U hU => nhds_ball x₀ hU, fun Ψ => decomp Ψ⟩

end PositivityTheory.Rg.Ming

end
