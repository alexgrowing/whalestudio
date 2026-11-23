import Formalism.MahlerMeasure.StatementT

namespace Formalism.GM

open Module

theorem badCrit_dvd_pow_of_norm {p : ℕ} [Fact p.Prime] {a : ℤ_[p]} {E : ℕ}
    (h : (p : ℝ) ^ (-(E : ℤ)) ≤ ‖a‖) : a ∣ (p : ℤ_[p]) ^ E := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (not_le.2 (by positivity))
  rw [PadicInt.norm_eq_zpow_neg_valuation ha, zpow_le_zpow_iff_right₀ hp, neg_le_neg_iff] at h
  have hv : a.valuation ≤ E := by exact_mod_cast h
  have hsp := PadicInt.unitCoeff_spec ha
  set u := PadicInt.unitCoeff ha
  have hu : (u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by simp
  refine ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (E - a.valuation), ?_⟩
  calc (p : ℤ_[p]) ^ E = (p : ℤ_[p]) ^ a.valuation * (p : ℤ_[p]) ^ (E - a.valuation) := by
        rw [← pow_add, Nat.add_sub_cancel' hv]
    _ = ((u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) *
          (p : ℤ_[p]) ^ a.valuation * (p : ℤ_[p]) ^ (E - a.valuation) := by rw [hu, one_mul]
    _ = ((u : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation) *
          (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (E - a.valuation)) := by ring
    _ = _ := by rw [← hsp]

theorem badCrit_core {p : ℕ} [Fact p.Prime] {m : ℕ} (E : ℕ) (N : Submodule ℤ_[p] (Fin m → ℤ_[p]))
    (h : ∀ l : (Fin m → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p], (∃ z, l z = 1) →
      ∃ v ∈ N, (p : ℝ) ^ (-(E : ℤ)) ≤ ‖l v‖) :
    ∀ z, (p : ℤ_[p]) ^ E • z ∈ N := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨n, S⟩ := N.smithNormalForm (Pi.basisFun ℤ_[p] (Fin m))
  have hr : ∀ j, j ∈ Set.range S.f := by
    intro j
    by_contra hj
    obtain ⟨v, hv, hn⟩ := h (S.bM.coord j) ⟨S.bM j, by simp⟩
    have h0 : S.bM.coord j v = 0 := S.le_ker_coord_of_notMem_range hj hv
    rw [h0, norm_zero] at hn
    exact absurd hn (not_le.2 (zpow_pos hp0 _))
  have hd : ∀ i, S.a i ∣ (p : ℤ_[p]) ^ E := by
    intro i
    obtain ⟨v, hv, hn⟩ := h (S.bM.coord (S.f i)) ⟨S.bM (S.f i), by simp⟩
    have hc : S.bM.coord (S.f i) v = S.a i * S.bN.coord i ⟨v, hv⟩ := by
      show S.bM.repr ((⟨v, hv⟩ : N) : Fin m → ℤ_[p]) (S.f i) = S.a i * S.bN.repr ⟨v, hv⟩ i
      rw [S.repr_apply_embedding_eq_repr_smul]
      exact congrArg (· i) (S.bN.repr.map_smul (S.a i) ⟨v, hv⟩)
    apply badCrit_dvd_pow_of_norm
    calc _ ≤ _ := hn
      _ = ‖S.a i‖ * ‖S.bN.coord i ⟨v, hv⟩‖ := by rw [hc, norm_mul]
      _ ≤ ‖S.a i‖ * 1 := by gcongr; exact PadicInt.norm_le_one _
      _ = _ := mul_one _
  have hb : ∀ j, (p : ℤ_[p]) ^ E • S.bM j ∈ N := by
    intro j
    obtain ⟨i, rfl⟩ := hr j
    obtain ⟨t, ht⟩ := hd i
    rw [ht, mul_comm, mul_smul, ← S.snf i]
    exact N.smul_mem t (S.bN i).2
  intro z
  rw [← S.bM.sum_repr z, Finset.smul_sum]
  refine N.sum_mem fun j _ => ?_
  rw [smul_comm]
  exact N.smul_mem _ (hb j)

section
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]

theorem badCrit_smul_eq (c : ℤ_[p]) (x : Vs) : c • x = (c : ℚ_[p]) • x := by
  rw [← algebraMap_smul ℚ_[p] c x, PadicInt.algebraMap_apply]

theorem badCrit_be_smul_left (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (c : ℤ_[p]) (x y : Vs) :
    be (c • x) y = (c : ℚ_[p]) * be x y := by
  rw [badCrit_smul_eq, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem badCrit_be_smul_right (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (c : ℤ_[p]) (x y : Vs) :
    be x (c • y) = (c : ℚ_[p]) * be x y := by
  rw [badCrit_smul_eq, map_smul, smul_eq_mul]

theorem badCrit_torsionFree : Module.IsTorsionFree ℤ_[p] Vs :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    rw [badCrit_smul_eq, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (PadicInt.ext (h.trans PadicInt.coe_zero.symm))
    · exact Or.inr h

theorem badCrit_goodCount_bdd (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] :
    BddAbove {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℤ_[p] L, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hli : LinearIndependent ℤ_[p] (fun i => (⟨x i, hx i⟩ : L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun v : L => be (v : Vs) (y i)) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.sum_apply,
      Submodule.coe_zero, map_zero, LinearMap.zero_apply] at h1
    simp only [badCrit_be_smul_left, hxy, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have hp : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    exact PadicInt.ext (((mul_eq_zero.1 h1).resolve_right hp).trans PadicInt.coe_zero.symm)
  simpa using hli.fintype_card_le_finrank

end

section
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]

theorem badCrit_pairs (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] (hle : L₁ ≤ L)
    (hprim : ∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) :
    ∃ x y : Fin (Module.finrank ℤ_[p] L₁) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  classical
  have := badCrit_torsionFree (p := p) (Vs := Vs)
  have : Module.Finite ℤ_[p] L₁ :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  set m := Module.finrank ℤ_[p] L₁
  let u := Module.finBasis ℤ_[p] L₁
  let bL := Module.finBasis ℤ_[p] L
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set C : ℝ := ∑ a, ∑ b, ‖be (u a) (bL b)‖
  have hC : ∀ w ∈ L, ∀ a, ‖be (u a) w‖ ≤ C := by
    intro w hw a
    have hw' : w = ∑ b, (bL.repr ⟨w, hw⟩ b) • (bL b : Vs) := by
      have := congrArg Subtype.val (bL.sum_repr ⟨w, hw⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hw', map_sum]
    calc ‖∑ b, be (u a) ((bL.repr ⟨w, hw⟩ b) • (bL b : Vs))‖
        ≤ ∑ b, ‖be (u a) ((bL.repr ⟨w, hw⟩ b) • (bL b : Vs))‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖be (u a) (bL b)‖ := by
          gcongr with b
          rw [badCrit_be_smul_right, norm_mul, ← PadicInt.norm_def]
          exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)
      _ ≤ C := Finset.single_le_sum (f := fun a => ∑ b, ‖be (u a) (bL b)‖)
          (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ a)
  obtain ⟨E, hE⟩ := pow_unbounded_of_one_lt (C * (p : ℝ) ^ D) hp1
  have hCE : C ≤ (p : ℝ) ^ ((E : ℤ) - D) := by
    rw [zpow_sub₀ hp0.ne', zpow_natCast, le_div_iff₀ (zpow_pos hp0 _)]
    exact hE.le
  have hnp : ∀ z : ℤ, ‖(p : ℚ_[p]) ^ z‖ = (p : ℝ) ^ (-z) := by
    intro z
    exact Padic.norm_p_zpow z
  have hint : ∀ w ∈ L, ∀ a, ‖(p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w‖ ≤ 1 := by
    intro w hw a
    rw [norm_mul, hnp]
    calc (p : ℝ) ^ (-((E : ℤ) - D)) * ‖be (u a) w‖
        ≤ (p : ℝ) ^ (-((E : ℤ) - D)) * (p : ℝ) ^ ((E : ℤ) - D) := by
          gcongr; exact (hC w hw a).trans hCE
      _ = 1 := by rw [← zpow_add₀ hp0.ne']; simp
  let g : L → Fin m → ℤ_[p] := fun w a => ⟨(p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w, hint w.1 w.2 a⟩
  have hg : ∀ w a, ((g w a : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w :=
    fun _ _ => rfl
  let G : L →ₗ[ℤ_[p]] (Fin m → ℤ_[p]) :=
    { toFun := g
      map_add' := fun w w' => by
        funext a; apply PadicInt.ext
        rw [Pi.add_apply, PadicInt.coe_add, hg, hg, hg, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun c w => by
        funext a; apply PadicInt.ext
        rw [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, PadicInt.coe_mul, hg, hg,
          Submodule.coe_smul, badCrit_be_smul_right]
        ring }
  have hG : ∀ w a, ((G w a : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be (u a) w :=
    fun _ _ => rfl
  have hcore := badCrit_core E (LinearMap.range G) (by
    rintro l ⟨z0, hz0⟩
    set c : Fin m → ℤ_[p] := fun a => l (fun j => if a = j then 1 else 0)
    have hl : ∀ z, l z = ∑ a, z a * c a := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ l z]; rfl
    set uu : L₁ := u.equivFun.symm c
    have huu : (uu : Vs) = ∑ a, c a • (u a : Vs) := by
      show ((u.equivFun.symm c : L₁) : Vs) = _
      rw [Basis.equivFun_symm_apply, Submodule.coe_sum]
      rfl
    have hprim' : ∀ (b : ℤ_[p]) (x : Vs), x ∈ L₁ → (uu : Vs) = b • x → IsUnit b := by
      intro b x hx hbx
      have h1 : uu = b • (⟨x, hx⟩ : L₁) := Subtype.ext hbx
      have h2 : c = b • u.equivFun ⟨x, hx⟩ := by
        rw [← u.equivFun.apply_symm_apply c]
        change u.equivFun uu = _
        rw [h1, map_smul]
      apply IsUnit.of_mul_eq_one (∑ a, z0 a * u.equivFun ⟨x, hx⟩ a)
      rw [← hz0, hl, h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    obtain ⟨u', hu', hn⟩ := hprim uu uu.2 hprim'
    refine ⟨G ⟨u', hu'⟩, LinearMap.mem_range_self _ _, ?_⟩
    have hq : ((l (G ⟨u', hu'⟩) : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ ((E : ℤ) - D) * be uu u' := by
      rw [hl, PadicInt.coe_sum, huu, map_sum, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PadicInt.coe_mul, hG, badCrit_be_smul_left]; ring
    rw [PadicInt.norm_def, hq, norm_mul, hnp]
    calc (p : ℝ) ^ (-(E : ℤ)) = (p : ℝ) ^ (-((E : ℤ) - D)) * (p : ℝ) ^ (-D) := by
          rw [← zpow_add₀ hp0.ne']; ring_nf
      _ ≤ _ := by gcongr)
  have hw : ∀ j : Fin m, ∃ w : L, G w = (p : ℤ_[p]) ^ E • Pi.single j 1 :=
    fun j => LinearMap.mem_range.1 (hcore (Pi.single j 1))
  choose w hw using hw
  refine ⟨fun i => (u i : Vs), fun j => (w j : Vs), fun i => hle (u i).2, fun j => (w j).2, ?_⟩
  intro i j
  have h1 := congrArg (fun z => ((z i : ℤ_[p]) : ℚ_[p])) (hw j)
  simp only [hG] at h1
  have h2 : ((((p : ℤ_[p]) ^ E • (Pi.single j 1 : Fin m → ℤ_[p])) i : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ ((E : ℤ) - D) * (if i = j then (p : ℚ_[p]) ^ D else 0) := by
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, ← zpow_add₀ hpq]; push_cast; simp
    · simp
  rw [h2] at h1
  exact mul_left_cancel₀ (zpow_ne_zero _ hpq) h1

end

theorem bad_criterion_holds : M.BadCrit := by
  intro p _ Vs _ _ _ _ be L L₁ D hfin hle _hsat hprim
  obtain ⟨x, y, hx, hy, hxy⟩ := badCrit_pairs be L L₁ D hle hprim
  have hg : Module.finrank ℤ_[p] L₁ ≤ M.goodCount p (fun x y => be x y) L D :=
    le_csSup (badCrit_goodCount_bdd be L D) ⟨x, y, hx, hy, hxy⟩
  unfold M.bad
  omega

end Formalism.GM
