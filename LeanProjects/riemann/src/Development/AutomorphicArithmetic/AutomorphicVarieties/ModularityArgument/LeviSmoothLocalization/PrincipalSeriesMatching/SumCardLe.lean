import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchAd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import GroundTheory.GlobalFields.TateThesis.LocalConductor

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private theorem sum_card_le {α ι : Type*} [Fintype ι] (Q : ι → α → Prop) (hQ : ∀ c c' y, Q c y → Q c' y → c = c')
    (s : Multiset α) : ∑ c, (s.filter (Q c)).card ≤ (s.filter fun y => ∃ c, Q c y).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib]
    refine add_le_add ?_ ih
    by_cases h : ∃ c, Q c y
    · obtain ⟨c, hc⟩ := h
      rw [if_pos ⟨c, hc⟩, Finset.sum_eq_single c (fun b _ hb => by rw [if_neg fun h => hb (hQ _ _ _ h hc)]; rfl) (by simp),
        if_pos hc]
    · rw [if_neg h, Finset.sum_eq_zero fun b _ => by rw [if_neg fun h' => h ⟨b, h'⟩]; rfl]
      exact Nat.zero_le _

private theorem comb {W : Type} [Fintype W] {α : W → Type 1} (r : Setoid (Fin 3)) (s : ∀ w, Multiset (α w))
    (Q : ∀ w, Fin 3 → α w → Prop) (f : W → ℕ) (hf : ∀ w, 0 < f w) (hs : ∀ w, (s w).card ≤ 3)
    (hQ : ∀ w i i' y, Q w i y → Q w i' y → r i i')
    (h : ∀ i, (Finset.univ.filter fun i' => r i' i).card * ∑ w, f w = ∑ w, f w * ((s w).filter (Q w i)).card) :
    ∀ w, ∀ y ∈ s w, ∃ i, Q w i y := by
  have h3 : ∑ c : Quotient r, (Finset.univ.filter fun i' => r i' c.out).card = 3 := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := Quotient.mk r) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine (Finset.sum_congr rfl fun c _ => congrArg _ (Finset.filter_congr fun i _ => ?_)).trans this.symm
    exact Quotient.mk_eq_iff_out.symm
  have hle : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ ((s w).filter fun y => ∃ c : Quotient r, Q w c.out y).card :=
    fun w => sum_card_le (fun c : Quotient r => Q w c.out)
      (fun c c' y h h' => by rw [← c.out_eq, ← c'.out_eq]; exact Quotient.sound (hQ w _ _ y h h')) (s w)
  have hle3 : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ 3 := fun w =>
    (hle w).trans ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hs w))
  have heq : ∑ w, f w * ∑ c : Quotient r, ((s w).filter (Q w c.out)).card = ∑ w, f w * 3 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_congr rfl fun (c : Quotient r) _ => h c.out, ← Finset.sum_mul, h3, ← Finset.sum_mul,
      mul_comm]
  intro w y hy
  have h1 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left (f w) (hle3 w)).1 heq w (Finset.mem_univ w)
  have h2 := Nat.eq_of_mul_eq_mul_left (hf w) h1
  have h4 := Multiset.eq_of_le_of_card_le (Multiset.filter_le (fun y => ∃ c : Quotient r, Q w c.out y) (s w))
    ((hs w).trans (h2.symm.le.trans (hle w)))
  obtain ⟨c, hc⟩ := Multiset.filter_eq_self.1 h4 y hy
  exact ⟨_, hc⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem un_div {a b c : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) (h : c = a * b⁻¹) : IsUnram c := fun x hx => by
  simp [h, ha x hx, hb x hx]

private theorem lin_ne (ξ : kˣ →* ℂˣ) : lin ξ ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  unfold lin at this
  split_ifs at this <;> simp at this

private theorem lin_deg (ξ : kˣ →* ℂˣ) : (lin ξ).natDegree = if IsUnram ξ then 1 else 0 := by
  unfold lin
  split_ifs
  · rw [natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X _ (Units.ne_zero _)]
    simp
  · simp

private theorem lin_root {ξ : kˣ →* ℂˣ} {x : ℂ} (h : (lin ξ).eval x = 0) :
    IsUnram ξ ∧ ((ξ (unif k) : ℂˣ) : ℂ) * x = 1 := by
  unfold lin at h
  split_ifs at h with hu
  · refine ⟨hu, ?_⟩
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X] at h
    exact (sub_eq_zero.1 h).symm
  · simp at h

end Loc

private theorem core {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 ℚ)}
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ →* ℂˣ) (ha : ∀ i, IsSmoothChar (a i)) (e : ℕ → (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (he : ∀ j ∈ Finset.range 2, ∀ w : PlacesOver K v, (e j).comp (nm w) = 1)
    (hc : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → ∀ w : PlacesOver K v, IsUnram (θ.comp (nm w)) →
      ((Finset.range 2).filter fun j => IsUnram (θ * e j)).card = ∑ w' : PlacesOver K v, fdeg w')
    (s : ∀ w : PlacesOver K v, Multiset (IrrGL (w.1.adicCompletion K))) (hs : ∀ w, (s w).card ≤ 3)
    (hm : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ →
      ∏ j ∈ Finset.range 2, ∏ i, lin (a i * θ * e j) = ∏ w, (pol (s w) (θ.comp (nm w))).comp (X ^ fdeg w))
    (w : PlacesOver K v) : ∀ y ∈ s w, ∃ i hζ, y = IrrGL.ofChar ((a i).comp (nm w)) hζ := by
  have hf : ∀ w : PlacesOver K v, 0 < fdeg w := fun w => (normVal ℚ K v w 1).2.2.1
  have hup : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, ∀ j ∈ Finset.range 2, ∀ w : PlacesOver K v,
      (θ * e j).comp (nm w) = θ.comp (nm w) := fun θ j hj w => by
    rw [MonoidHom.mul_comp, he j hj w, mul_one]
  have hup' : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, ∀ j ∈ Finset.range 2, IsUnram (θ * e j) → ∀ w : PlacesOver K v,
      IsUnram (θ.comp (nm w)) := fun θ j hj h w => hup θ j hj w ▸ ((normVal ℚ K v w _).1 h).1
  have hind : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → ∀ w : PlacesOver K v, IsUnram (θ.comp (nm w)) →
      ∀ w' : PlacesOver K v, IsUnram (θ.comp (nm w')) := fun θ hθ w h => by
    have h1 : 0 < ((Finset.range 2).filter fun j => IsUnram (θ * e j)).card := by
      rw [hc θ hθ w h]
      exact Finset.sum_pos (fun w _ => hf w) ⟨w, Finset.mem_univ _⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h1
    exact hup' θ j (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2
  let r : Setoid (Fin 3) := ⟨fun i i' => IsUnram ((a i * (a i')⁻¹).comp (nm w)),
    ⟨fun i x _ => by simp, fun {i i'} h x hx => by
      have := h x hx
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this ⊢
      exact this.symm, fun {i i' i''} h h' x hx => by
      have h1 := h x hx
      have h2 := h' x hx
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at h1 h2 ⊢
      exact h1.trans h2⟩⟩
  have key := comb r s (fun w i y => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * ((a i)⁻¹).comp (nm w))) fdeg hf hs
    (by
      rintro w' i i' y ⟨ξ, hξ, rfl, hu⟩ ⟨ξ', hξ', h', hu'⟩
      obtain rfl := (polFacts _).2.2.1 _ _ _ _ h'
      refine hind _ ((ha i).mul (ha i').inv) w' (un_div hu' hu ?_) w
      ext1 x
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_comm (ξ x), mul_comm (ξ x), mul_comm ((a i) _)]
      group)
    (by
      intro i
      have h1 := congrArg natDegree (hm _ (ha i).inv)
      rw [Finset.prod_comm, natDegree_prod _ _ fun i' _ => Finset.prod_ne_zero_iff.2 fun j _ => lin_ne _,
        natDegree_prod _ _ fun w' _ h0 => by
          have := congrArg (eval 0) h0
          rw [eval_comp, eval_pow, eval_X, zero_pow (hf w').ne', ((polFacts _).2.2.2 _ _).1] at this
          simp at this] at h1
      rw [Finset.card_filter, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i' _ => ?_) (h1.trans (Finset.sum_congr rfl fun w' _ => ?_))
      · rw [natDegree_prod _ _ fun j _ => lin_ne _, Finset.sum_congr rfl fun j _ => lin_deg _, ← Finset.card_filter]
        split_ifs with hr
        · rw [one_mul, hc _ ((ha i').mul (ha i).inv) w hr]
        · rw [zero_mul, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          exact fun j hj hu => hr (hup' _ j hj hu w)
      · rw [natDegree_comp, natDegree_X_pow, ((polFacts _).2.2.2 _ _).2.1, mul_comm]
        rfl)
  intro y hy
  obtain ⟨i, ζ, hζ, rfl, hu⟩ := key w y hy
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
    ((((ζ * ((a i)⁻¹).comp (nm w)) (unif _) : ℂˣ) : ℂ)⁻¹) (hf w)
  have h0 : (∏ w, (pol (s w) (((a i)⁻¹).comp (nm w))).comp (X ^ fdeg w)).eval x = 0 := by
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
    rw [eval_comp, eval_pow, eval_X, hx]
    exact (((polFacts _).2.2.2 _ _).2.2.1 _).2 ⟨ζ, ⟨hζ, hy⟩, hu, mul_inv_cancel₀ (Units.ne_zero _)⟩
  rw [← hm _ (ha i).inv, eval_prod] at h0
  obtain ⟨j, hj, h0⟩ := Finset.prod_eq_zero_iff.1 h0
  rw [eval_prod] at h0
  obtain ⟨i', -, h0⟩ := Finset.prod_eq_zero_iff.1 h0
  obtain ⟨h1, h2⟩ := lin_root h0
  have h3 := ((normVal ℚ K v w _).1 h1).2
  have h4 : ((a i' * (a i)⁻¹).comp (nm w)) (unif _) = (ζ * ((a i)⁻¹).comp (nm w)) (unif _) := by
    rw [← hup _ j hj w, MonoidHom.comp_apply, h3]
    refine Units.ext ?_
    have h5 := congrArg (· ^ fdeg w) h2
    simp only [mul_pow, one_pow, hx] at h5
    rw [Units.val_pow_eq_pow_val]
    exact (mul_inv_eq_one₀ (Units.ne_zero _)).1 h5
  have h6 : ζ = (a i').comp (nm w) := by
    refine (polFacts _).2.1 _ _ (un_div hu (hup' _ j hj h1 w) ?_) ?_
    · ext1 x
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      group
    · simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply] at h4 ⊢
      exact (mul_right_cancel h4).symm
  subst h6
  exact ⟨i', hζ, rfl⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adK :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdK := by
  intro K _ _ _ hK D hD P hP v w
  obtain ⟨η, hη⟩ := matchAd K hK D hD P hP
  obtain ⟨h1, h2, h3⟩ := hη v
  have hν : IsSmoothChar (D.ν v) :=
    GroundTheory.Global.isOpen_ker_of_continuous v GroundTheory.Global.Complex.units_noSmallSubgroups _ (D.unit v).1
  have sf := fun w : PlacesOver K v => suppFacts K 3 (by norm_num) P w.1
  choose s hs using fun w => (sf w).1
  have key := core ![D.ν v, 1, (D.ν v)⁻¹] (fun i => by fin_cases i; exacts [hν, isSmoothChar_one, hν.inv])
    (fun j => (η ^ j).loc v)
    (fun j hj w => by
      have := Finset.mem_range.1 hj
      interval_cases j
      · rw [pow_zero]; rfl
      · rw [pow_one]; exact h1 w)
    h2 s
    (fun w => by
      obtain ⟨-, h4, h5⟩ := (sf w).2.2.1 _ (hs w)
      have := Multiset.card_nsmul_le_sum (s := (s w).map Sigma.fst) (a := 1) fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
        exact h5 y hy
      simpa [h4] using this)
    (fun θ hθ => by
      rw [← h3 s hs θ hθ]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Fin.prod_univ_three, Matrix.cons_val, one_mul, mul_assoc]) w
  have hch : ∀ t, SuppAt P w.1 t → ∀ ζ ∈ chars t,
      ζ = (D.ν v).comp (nm w) ∨ ζ = 1 ∨ ζ = ((D.ν v).comp (nm w))⁻¹ := by
    rintro t ht ζ ⟨hζ, hm⟩
    obtain rfl := (sf w).2.1 _ _ ht (hs w)
    obtain ⟨i, hi, e⟩ := key _ hm
    obtain rfl := (polFacts _).2.2.1 _ _ _ _ e
    fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  refine ⟨⟨((sf w).2.2.1 _ (hs w)).1.2 fun y hy => ?_, fun t ht ζ hζ => ?_⟩, hch⟩
  · obtain ⟨i, hi, rfl⟩ := key y hy
    rfl
  · have hn : ‖((ζ (unif (w.1.adicCompletion K)) : ℂˣ) : ℂ)‖ = 1 := by
      rcases hch t ht ζ hζ with rfl | rfl | rfl
      · exact (D.unit v).2 _
      · simp
      · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
        exact (D.unit v).2 _
    have hq : (1 : ℝ) < Ideal.absNorm w.1.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.1
    rw [hn]
    exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num), Real.one_lt_rpow hq (by norm_num)⟩
