import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

section SlopeTestRemainingChoices

private theorem jq_gen {T W J : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [AddCommGroup J] [Module ℂ J]
    (θ : T →* (Module.End ℂ W)ˣ) (σ : Representation ℂ T J) (δ : T →* ℂˣ) (q : W →ₗ[ℂ] J) :
    ∃ S : Subgroup T, ∀ t, t ∈ S ↔ ∀ v, q ((θ t : Module.End ℂ W) v) = (((δ t)⁻¹ : ℂˣ) : ℂ) • σ t (q v) := by
  refine ⟨{ carrier := {t | ∀ v, q ((θ t : Module.End ℂ W) v) = (((δ t)⁻¹ : ℂˣ) : ℂ) • σ t (q v)}
            one_mem' := ?one, mul_mem' := ?mul, inv_mem' := ?inv }, fun t => Iff.rfl⟩
  case one =>
    intro v
    simp
  case mul =>
    intro a b ha hb v
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have e1 : ((θ (a * b) : Module.End ℂ W) v) = (θ a : Module.End ℂ W) ((θ b : Module.End ℂ W) v) := by
      rw [map_mul, Units.val_mul, Module.End.mul_apply]
    rw [e1, ha, hb, map_smul, smul_smul, map_mul, map_mul, Module.End.mul_apply, mul_inv, Units.val_mul, mul_comm]
  case inv =>
    intro a ha v
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h := ha ((θ a⁻¹ : Module.End ℂ W) v)
    have e1 : (θ a : Module.End ℂ W) ((θ a⁻¹ : Module.End ℂ W) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Module.End.one_apply]
    rw [e1] at h
    have h2 := congrArg (fun w => (((δ a : ℂˣ) : ℂ)) • σ a⁻¹ w) h
    rw [map_smul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply] at h2
    rw [← h2, map_inv δ a, inv_inv]

private theorem jq_sum {n : ℕ} (a : Fin n → ℤ) (ha : Antitone a) :
    ((∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat : ℕ) : ℤ) =
      ∑ i, a i * modExp (fun _ : Fin n => Unit) i := by
  have hnn : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      ((a p.1 - a p.2).toNat : ℤ) = a p.1 - a p.2 := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (ha hp.2.le))
  push_cast
  rw [Finset.sum_congr rfl hnn, Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmGL.modExp, Fintype.card_unit, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_filter]
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter]
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem jq_delta {x : kˣ} (hx : IsUnif x) (a : Fin n → ℤ) :
    (deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => x ^ a i) : ℂ) *
      (deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => x ^ a i) : ℂ) *
      (resCard k : ℂ) ^ (∑ i, a i * modExp (fun _ : Fin n => Unit) i) = 1 := by
  rw [val_deltaHalf, ← Complex.ofReal_mul, Real.mul_self_sqrt (modulus_pos k _).le]
  unfold modulus
  have hdet : ∀ i, GeneralLinearGroup.det ((leviTorus k (Fin n) fun i => x ^ a i) i) = x ^ a i := by
    intro i
    simp [leviTorus]
  simp only [hdet]
  have hn : ∀ z : ℤ, nabs k (x ^ z) = (nabs k x) ^ z := by
    intro z
    simp [GlobalTheory.SplitWeil.nabs, map_zpow, NNReal.coe_zpow]
  obtain ⟨p, hp, hpx⟩ := hx
  have hnx : nabs k x = ((resCard k : ℝ))⁻¹ := GlobalTheory.SplitWeil.nabs_uniformiser hp hpx.symm
  have hq : (0 : ℝ) < resCard k := by
    rw [← inv_pos, ← hnx]
    exact nabs_pos' k x
  have key : ∀ (s : Finset (Fin n)) (f : Fin n → ℤ), ∏ i ∈ s, (resCard k : ℝ) ^ f i = (resCard k : ℝ) ^ ∑ i ∈ s, f i := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hq.ne']
  simp only [hn, hnx, _root_.inv_zpow', ← _root_.zpow_mul]
  rw [key, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, ← Complex.ofReal_mul, ← zpow_add₀ hq.ne']
  simp [neg_mul, Finset.sum_neg_distrib]

private theorem jq_card {G : Type} [Group G] (I : Subgroup G) (d : G) (h : FinOrb I I d) (s : Finset G)
    (hs : ∀ v : fixd (Representation.trivial ℤ G ℤ) I,
      (hk (Representation.trivial ℤ G ℤ) I d v : ℤ) = ∑ u ∈ s, Representation.trivial ℤ G ℤ (u * d) v) :
    s.card = (MulAction.orbit I (d : G ⧸ I)).ncard := by
  have hfin : (MulAction.orbit I (d : G ⧸ I)).Finite := h
  haveI : Finite (MulAction.orbit I (d : G ⧸ I)) := hfin.to_subtype
  letI : Fintype (MulAction.orbit I (d : G ⧸ I)) := Fintype.ofFinite _
  have hv : (1 : ℤ) ∈ fixd (Representation.trivial ℤ G ℤ) I := fun u _ => rfl
  have h1 := hs ⟨1, hv⟩
  have e := (hkApply ℤ G ℤ (Representation.trivial ℤ G ℤ) I I d h).1 ⟨1, hv⟩
  have e2 : (hk (Representation.trivial ℤ G ℤ) I d ⟨1, hv⟩ : ℤ) = (hk2 (Representation.trivial ℤ G ℤ) I I d ⟨1, hv⟩ : ℤ) := rfl
  rw [e2, e] at h1
  simp only [UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Representation.trivial_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
  have h2 : (Fintype.card (MulAction.orbit I (d : G ⧸ I)) : ℤ) = (s.card : ℤ) := h1
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact_mod_cast h2.symm

private theorem jq_dom (C : Subgroup 𝓀[k]ˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (t : Fin n → kˣ) (ht : Dom t) (v : fixd π (iwC k n C)) :
    (Submodule.Quotient.mk (hk π (iwC k n C) (diagT k (Fin n) t) v : V) : Jacquet π (unipB k (Fin n))) =
      ((MulAction.orbit (iwC k n C) ((diagT k (Fin n) t : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard : ℂ) •
        jacBU π t (Submodule.Quotient.mk (v : V)) := by
  obtain ⟨s, hsU, -, hsum⟩ := domSum k n t ht
  have hfin : FinOrb (iwC k n C) (iwC k n C) (diagT k (Fin n) t) := (heckePairIwC k n C).1 _
  have hcard := jq_card (iwC k n C) (diagT k (Fin n) t) hfin s
    (fun v => hsum C ℤ ℤ (Representation.trivial ℤ (GL (Fin n) k) ℤ) v)
  have hu : ∀ u ∈ s, (Submodule.Quotient.mk (π (u * diagT k (Fin n) t) (v : V)) : Jacquet π (unipB k (Fin n))) =
      Submodule.Quotient.mk (π (diagT k (Fin n) t) (v : V)) := by
    intro u hu
    rw [Submodule.Quotient.eq, map_mul, Module.End.mul_apply]
    apply Submodule.subset_span
    refine ⟨⟨u, (Subgroup.mem_inf.mp (hsU u hu)).1⟩, π (diagT k (Fin n) t) (v : V), ?_⟩
    simp
  rw [hsum C ℂ V π v, ← hcard, jacBU_mk, ← Submodule.mkQ_apply, map_sum]
  simp only [Submodule.mkQ_apply]
  rw [Finset.sum_congr rfl hu, Finset.sum_const, Nat.cast_smul_eq_nsmul]

private theorem unif_lt {x : kˣ} (hx : IsUnif x) : valuation k (x : k) < 1 := by
  obtain ⟨p, hp, hpx⟩ := hx
  rw [← hpx]
  exact (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hp

private theorem unif_dec {x : kˣ} (hx : IsUnif x) (y : kˣ) :
    ∃ a : ℤ, valuation k (y : k) = valuation k (x : k) ^ a := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hO := Valuation.integer.integers (valuation k)
  have hint : ∀ z : 𝒪[k], z ≠ 0 → ∃ m : ℕ, valuation k (algebraMap 𝒪[k] k z) = valuation k (x : k) ^ m := by
    intro z hz
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hp
    refine ⟨m, ?_⟩
    rw [map_mul, map_pow, map_mul, map_pow, hO.valuation_unit, one_mul, hpx]
  rcases le_total (valuation k (y : k)) 1 with h | h
  · have hy : (y : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).mpr h
    obtain ⟨m, hm⟩ := hint ⟨y, hy⟩ (fun h0 => y.ne_zero (congrArg Subtype.val h0))
    have hm' : valuation k (y : k) = valuation k (x : k) ^ m := hm
    exact ⟨m, by rw [zpow_natCast]; exact hm'⟩
  · have h' : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ h
    have hy : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).mpr h'
    obtain ⟨m, hm⟩ := hint ⟨_, hy⟩ (fun h0 => (y⁻¹).ne_zero (congrArg Subtype.val h0))
    refine ⟨-(m : ℤ), ?_⟩
    have hm' : valuation k ((y⁻¹ : kˣ) : k) = valuation k (x : k) ^ m := hm
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hm'
    rw [_root_.zpow_neg, zpow_natCast, ← hm', inv_inv]

private theorem dom_zpow {x : kˣ} (hx : IsUnif x) {a : Fin n → ℤ} (ha : Antitone a) : Dom fun i => x ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 (unif_lt hx)).2 (ha hij)

private theorem unit_norm (C : Subgroup 𝓀[k]ˣ) (u : Fin n → kˣ) (hu : ∀ i, valuation k (u i : k) = 1) :
    diagT k (Fin n) u ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  obtain ⟨_, htop, hconj, hunit⟩ := memIwC k n C
  have hI : diagT k (Fin n) u ∈ iwahori k (Fin n) := by
    rw [← htop]
    unfold UpperTheory.V.AlgebraTools.iwC
    apply Subgroup.mem_sup_right
    exact Subgroup.mem_map_of_mem _ ((Subgroup.mem_pi _).mpr (fun i _ => (hunit (u i)).mpr (hu i)))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj _ hI _ hh
  · intro hh
    have h2 := hconj _ (inv_mem hI) _ hh
    simpa [mul_assoc] using h2

private theorem anti_diff (a : Fin n → ℤ) : ∃ b : Fin n → ℤ, Antitone b ∧ Antitone (a + b) := by
  set M : ℤ := ∑ k, |a k| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hle : ∀ i, |a i| ≤ M := fun i =>
    Finset.single_le_sum (f := fun k => |a k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨fun i => -(2 * M * ((i : ℕ) : ℤ)), ?_, ?_⟩
  · intro i j hij
    have h1 : (i : ℕ) ≤ (j : ℕ) := hij
    have h2 : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast h1
    dsimp only
    nlinarith
  · intro i j hij
    simp only [Pi.add_apply]
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · have h1 : (i : ℕ) < (j : ℕ) := h
      have h2 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by omega
      have hi := abs_le.mp (hle i)
      have hj := abs_le.mp (hle j)
      nlinarith [hi.1, hi.2, hj.1, hj.2]

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.jqTheta :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), ∀ θ : (Fin n → kˣ) →* (Module.End ℂ (fixd π (iwC k n C)))ˣ, (∀ t, Dom t → (θ t : Module.End ℂ (fixd π (iwC k n C))) = hk π (iwC k n C) (diagT k (Fin n) t)) → ∀ (t : Fin n → kˣ) (v : fixd π (iwC k n C)), (Submodule.Quotient.mk ((θ t : Module.End ℂ (fixd π (iwC k n C))) v : V) : Jacquet π (unipB k (Fin n))) = (((((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t)⁻¹ : ℂˣ) : ℂ) • jacB π t (Submodule.Quotient.mk (v : V) : Jacquet π (unipB k (Fin n))) := by
  intro k _ _ _ _ n C V _ _ π θ hθ t v
  let q : fixd π (iwC k n C) →ₗ[ℂ] Jacquet π (unipB k (Fin n)) :=
    (Submodule.mkQ _).comp (Submodule.subtype _)
  have hq : ∀ w, q w = Submodule.Quotient.mk (w : V) := fun w => rfl
  obtain ⟨S, hS⟩ := jq_gen θ (jacB π) ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) q
  suffices hall : ∀ t, t ∈ S from (hS t).mp (hall t) v
  obtain ⟨x, hx⟩ := exists_isUnif (k := k)
  have hA : ∀ a : Fin n → ℤ, Antitone a → (fun i => x ^ a i) ∈ S := by
    intro a ha
    rw [hS]
    intro w
    have hdom := dom_zpow hx ha
    rw [hθ _ hdom, hq, hq, jq_dom C π _ hdom w, UnramFixed.jacB_apply, smul_smul]
    congr 1
    have hc : (MulAction.orbit (iwC k n C)
        ((diagT k (Fin n) (fun i => x ^ a i) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard =
        resCard k ^ ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (a p.1 - a p.2).toNat :=
      domCard k n C x hx a ha
    rw [hc, Nat.cast_pow, ← zpow_natCast, jq_sum a ha, Units.val_inv_eq_inv_val, ← mul_inv]
    apply eq_inv_of_mul_eq_one_left
    rw [mul_comm]
    exact jq_delta hx a
  have hB : ∀ u : Fin n → kˣ, (∀ i, valuation k (u i : k) = 1) → u ∈ S := by
    intro u hu
    rw [hS]
    intro w
    have hdom : Dom u := fun i j _ => by rw [hu i, hu j]
    rw [hθ _ hdom, hq, hq, jq_dom C π _ hdom w, UnramFixed.jacB_apply, smul_smul]
    congr 1
    have hδ1 : ((deltaHalf k fun _ : Fin n => Unit) (leviTorus k (Fin n) u) : ℂ) = 1 := by
      rw [val_deltaHalf]
      unfold modulus
      have hdet : ∀ i, GeneralLinearGroup.det ((leviTorus k (Fin n) u) i) = u i := by
        intro i
        simp [leviTorus]
      have hn : ∀ i, nabs k (u i) = 1 := fun i => nabs_eq_one k (hu i)
      simp [hdet, hn]
    have horb : (MulAction.orbit (iwC k n C)
        ((diagT k (Fin n) u : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = 1 := by
      have hN := unit_norm C u hu
      rw [Set.ncard_eq_one]
      refine ⟨((diagT k (Fin n) u : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C), ?_⟩
      ext y
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨g, rfl⟩
        show (((g : GL (Fin n) k) * diagT k (Fin n) u : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = _
        rw [QuotientGroup.eq]
        exact (Subgroup.mem_normalizer_iff.mp hN _).mpr (by simpa [mul_assoc] using g.2)
      · rintro rfl
        exact MulAction.mem_orbit_self _
    rw [horb, Units.val_inv_eq_inv_val]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hδ1]
    simp
  intro t
  choose c hc using fun i => unif_dec hx (t i)
  obtain ⟨b, hb, hcb⟩ := anti_diff c
  have hx0 : valuation k (x : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  let u : Fin n → kˣ := fun i => t i * x ^ (-c i)
  have hu : ∀ i, valuation k (u i : k) = 1 := by
    intro i
    simp only [u, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hc i]
    rw [← zpow_add₀ hx0, add_neg_cancel, zpow_zero]
  have ht : t = (fun i => x ^ (c + b) i) * (fun i => x ^ b i)⁻¹ * u := by
    funext i
    simp only [u, Pi.mul_apply, Pi.inv_apply, Pi.add_apply, _root_.zpow_add, _root_.zpow_neg]
    rw [mul_inv_cancel_right, mul_comm (t i), mul_inv_cancel_left]
  rw [ht]
  exact S.mul_mem (S.mul_mem (hA _ hcb) (S.inv_mem (hA _ hb))) (hB u hu)
