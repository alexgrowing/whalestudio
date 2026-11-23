import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_fin {G K : Type} [Group G] [Field K] [CharZero K] (θ : G →* Kˣ) (z : G → K)
    (hz : ∀ g h, z (g * h) = z g + θ g * z h) (H N : Subgroup G) [N.FiniteIndex] (h0 : ∀ g ∈ H, g ∈ N → z g = 0) :
    ∃ m, ∀ g ∈ H, z g = θ g * m - m := by
  have z1 : z 1 = 0 := by simpa using hz 1 1
  have key : ∀ g ∈ H, θ g = 1 → z g = 0 := by
    intro g hg h1
    have hp : ∀ n : ℕ, z (g ^ n) = n * z g := by
      intro n
      induction n with
      | zero => simp [z1]
      | succ n ih => rw [pow_succ', hz, ih, h1]; push_cast; ring
    obtain ⟨n, hn, -, hN⟩ := N.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero g
    have := h0 _ (H.pow_mem hg n) hN
    rw [hp] at this
    exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  by_cases h1 : ∀ g ∈ H, θ g = 1
  · exact ⟨0, fun g hg => by simp [key g hg (h1 g hg)]⟩
  · push Not at h1
    obtain ⟨a, ha, h1⟩ := h1
    have hne : (θ a : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => h1 (Units.ext h)
    refine ⟨z a / (θ a - 1), fun g hg => ?_⟩
    have hc : θ (g * a * (a * g)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (θ g), mul_inv_cancel]
    have e := hz (g * a * (a * g)⁻¹) (a * g)
    rw [inv_mul_cancel_right, hc, key _ (H.mul_mem (H.mul_mem hg ha) (H.inv_mem (H.mul_mem ha hg))) hc, hz, hz] at e
    push_cast at e
    field_simp
    linear_combination -e

private theorem cob_conj {G K : Type} [Group G] [Field K] (θ : G →* Kˣ) (z : G → K)
    (hz : ∀ g h, z (g * h) = z g + θ g * z h) (H H' : Subgroup G) (u : G) (hu : ∀ x ∈ H, u⁻¹ * x * u ∈ H')
    (h : ∃ m, ∀ g ∈ H', z g = θ g * m - m) : ∃ m, ∀ g ∈ H, z g = θ g * m - m := by
  obtain ⟨m, hm⟩ := h
  refine ⟨θ u * m - z u, fun x hx => ?_⟩
  have e := hz u (u⁻¹ * x * u)
  have e2 : θ (u⁻¹ * x * u) = θ x := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  rw [hm _ (hu x hx), e2, ← mul_assoc, mul_inv_cancel_left, hz] at e
  linear_combination e

private theorem cover (R : Fin 4 → Fin 4 → Prop) (tr : ∀ a b c, R a b → R b c → R a c)
    (as : ∀ a b, a ≠ b → R a b → ¬ R b a) (m : Fin 4 → Fin 4)
    (h : ∀ i j, i ≠ j → R i j → (∀ k, k ≠ i → k ≠ j → R i k → ¬ R k j) → m i < m j) :
    ∀ i j, i ≠ j → R i j → m i < m j := by
  classical
  suffices H : ∀ n i j, (Finset.univ.filter fun k => k ≠ i ∧ k ≠ j ∧ R i k ∧ R k j).card = n → i ≠ j → R i j → m i < m j from
    fun i j => H _ i j rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hn hij hR
    by_cases hk : ∀ k, k ≠ i → k ≠ j → R i k → ¬ R k j
    · exact h i j hij hR hk
    · push Not at hk
      obtain ⟨k, ki, kj, r1, r2⟩ := hk
      refine (ih _ ?_ i k rfl ki.symm r1).trans (ih _ ?_ k j rfl kj r2)
      · rw [← hn]
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun hs => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          refine ⟨ha.1, ?_, ha.2.2.1, tr _ _ _ ha.2.2.2 r2⟩
          rintro rfl
          exact as _ _ kj r2 ha.2.2.2
        · have := @hs k (by simp [ki, kj, r1, r2])
          simp at this
      · rw [← hn]
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun hs => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          refine ⟨?_, ha.2.1, tr _ _ _ r1 ha.2.2.1, ha.2.2.2⟩
          rintro rfl
          exact as _ _ ki ha.2.2.1 r1
        · have := @hs k (by simp [ki, kj, r1, r2])
          simp at this

private def pat (K : Type) [Field K] (R : Fin 4 → Fin 4 → Prop) (rf : ∀ a, R a a) (tr : ∀ a b c, R a b → R b c → R a c) :
    Subalgebra K (M4 K) where
  carrier := {X | ∀ a b, X a b ≠ 0 → R a b}
  mul_mem' {X Y} hX hY a b h := by
    rw [Matrix.mul_apply] at h
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact tr _ _ _ (hX _ _ (left_ne_zero_of_mul hk)) (hY _ _ (right_ne_zero_of_mul hk))
  add_mem' {X Y} hX hY a b h := by
    by_cases h1 : X a b = 0
    · exact hY a b (by simpa [h1] using h)
    · exact hX a b h1
  algebraMap_mem' x a b h := by
    by_cases h1 : a = b
    · exact h1 ▸ rf a
    · exact absurd (by simp [Matrix.algebraMap_matrix_apply, h1]) h

section
variable {K : Type} [Field K] {R : Fin 4 → Fin 4 → Prop} {rf : ∀ a, R a a} {tr : ∀ a b c, R a b → R b c → R a c}

private theorem pat_diag (as : ∀ a b, a ≠ b → R a b → ¬ R b a) {X Y : M4 K} (hX : X ∈ pat K R rf tr) (hY : Y ∈ pat K R rf tr)
    (i : Fin 4) : (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    by_contra h
    exact as _ _ hk (hY _ _ (right_ne_zero_of_mul h)) (hX _ _ (left_ne_zero_of_mul h))
  · simp

private theorem pat_off {X Y : M4 K} (hX : X ∈ pat K R rf tr) (hY : Y ∈ pat K R rf tr) {i j : Fin 4} (hij : i ≠ j)
    (hk : ∀ k, k ≠ i → k ≠ j → R i k → ¬ R k j) : (X * Y) i j = X i i * Y i j + X i j * Y j j := by
  rw [Matrix.mul_apply, ← Finset.sum_pair (f := fun k => X i k * Y k j) hij]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk' => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  by_contra h
  exact hk k hk'.1 hk'.2 (hX _ _ (left_ne_zero_of_mul h)) (hY _ _ (right_ne_zero_of_mul h))

private theorem pat_aeval (as : ∀ a b, a ≠ b → R a b → ¬ R b a) {X : M4 K} (hX : X ∈ pat K R rf tr) (p : Polynomial K) :
    Polynomial.aeval X p ∈ pat K R rf tr ∧ ∀ i, (Polynomial.aeval X p) i i = p.eval (X i i) := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨by rw [Polynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ _, fun i => by simp [Matrix.algebraMap_matrix_apply]⟩
  | add p q hp hq => exact ⟨by rw [map_add]; exact add_mem hp.1 hq.1, fun i => by simp [hp.2, hq.2]⟩
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    exact ⟨mul_mem h.1 hX, fun i => by rw [pat_diag as h.1 hX, h.2, Polynomial.eval_mul_X]⟩

private theorem pat_prj (as : ∀ a b, a ≠ b → R a b → ¬ R b a) {X : M4 K} (hX : X ∈ pat K R rf tr) (c : Fin 4 → K)
    (hc : Function.Injective c) (m : Fin 4 → Fin 4) (hm : ∀ i, X i i = c (m i)) (a : Fin 4) :
    prj c X a ∈ pat K R rf tr ∧ ∀ i, (prj c X a i i = 0 ↔ m i ≠ a) := by
  refine ⟨(pat_aeval as hX _).1, fun i => ?_⟩
  rw [prj, (pat_aeval as hX _).2, hm, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, hc.eq_iff]

private theorem pat_split (as : ∀ a b, a ≠ b → R a b → ¬ R b a) {H : Type} [Group H] (r : H →* M4 K)
    (hr : ∀ g, r g ∈ pat K R rf tr) {I : Subgroup H} {ps : Fin 4 → H → K} {s : H} (ho : Ord I ps s r)
    (hc : Function.Injective fun a => ps a s) (m : Fin 4 → Fin 4) (hm : ∀ i, r s i i = ps (m i) s) {i j : Fin 4} (hij : i ≠ j)
    (hk : ∀ k, k ≠ i → k ≠ j → R i k → ¬ R k j) (hlt : m j < m i) : ∃ a, ∀ g, r g i j = a * (r g i i - r g j j) := by
  obtain ⟨hP, hP'⟩ := pat_prj as (hr s) _ hc m hm (m i)
  obtain ⟨hQ, hQ'⟩ := pat_prj as (hr s) _ hc m hm (m j)
  have st := fun g => ho.stable g _ _ hlt
  generalize prj (fun a => ps a s) (r s) (m i) = P at *
  generalize prj (fun a => ps a s) (r s) (m j) = Q at *
  have p1 : P i i ≠ 0 := fun h => (hP' i).1 h rfl
  have p2 : P j j = 0 := (hP' j).2 hlt.ne
  have q1 : Q j j ≠ 0 := fun h => (hQ' j).1 h rfl
  have q2 : Q i i = 0 := (hQ' i).2 hlt.ne'
  have e : ∀ g, P i i * r g i i * Q i j + (P i i * r g i j + P i j * r g j j) * Q j j = 0 := fun g => by
    have := congrFun (congrFun (st g) i) j
    rwa [pat_off (mul_mem hP (hr g)) hQ hij hk, pat_off hP (hr g) hij hk, pat_diag as hP (hr g)] at this
  have e1 := e 1
  simp only [map_one, Matrix.one_apply_eq, Matrix.one_apply_ne hij] at e1
  refine ⟨P i j / P i i, fun g => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff p1]
  apply mul_right_cancel₀ q1
  linear_combination e g - r g i i * e1

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.diagonal_character_order_lt_of_stable_flag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoV Ω l → ∀ r, D.EPt r → DiagType r → ∀ m : Fin 4 → Fin 4, Function.Injective m → (∀ i, ∀ s ∈ D.Ip l, r s i i = ((D.ps (m i) s : c.O) : PadicAlgCl l)) → ∀ i j, i ≠ j → Ge r i j → m i < m j := by
  intro Ω _ _ _ l hl c D hD hSo r hr hdt m hm hI
  obtain ⟨hmult, hunr, -, heq, heqP, hE, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, grefl, gtr, -⟩ := geAlg _ r _ hmult hE
  obtain ⟨fSb, -, -, -, -, -, hinj, -, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hcont, -⟩ := eptInt D hD r hr
  obtain ⟨κ, m', hκ, -, hI', hδ⟩ := diagChar D hD r hr hdt
  have hs0 : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  obtain rfl : m' = m := funext fun i => hinj (Subtype.ext ((hI' i _ hs0).symm.trans (hI i _ hs0)))
  refine cover (Ge r) gtr hdt m' fun i j hij hge hk => ?_
  by_contra hlt
  have hlt : m' j < m' i := lt_of_le_of_ne (not_lt.1 hlt) fun h => hij (hm h).symm
  have hp : ∀ g, r g ∈ pat _ (Ge r) grefl gtr := fun g a b h => ⟨g, h⟩
  have hκ0 : ∀ i g, r g i i ≠ 0 := fun i g => hκ i g ▸ (κ i g).ne_zero
  let θ : G ℚ Ω →* (PadicAlgCl l)ˣ := κ i / κ j
  have hθ : ∀ g, (θ g : PadicAlgCl l) = r g i i / r g j j := fun g => by
    simp [θ, hκ]
  let z : G ℚ Ω → PadicAlgCl l := fun g => r g i j / r g j j
  have hz : ∀ g h, z (g * h) = z g + θ g * z h := fun g h => by
    simp only [z]
    rw [hθ, map_mul, pat_off (hp g) (hp h) hij hk, pat_diag hdt (hp g) (hp h)]
    have := hκ0 j g
    have := hκ0 j h
    field_simp
    ring
  have hz1 : ∀ g, r g = 1 → z g = 0 := fun g h => by
    simp only [z, h, Matrix.one_apply_ne hij, zero_div]
  have hent : ∀ i j, Continuous fun g => r g i j := fun i j => (continuous_apply_apply i j).comp hcont
  obtain ⟨-, -, hconj⟩ := Chr.placesQ Ω
  have hL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ m, ∀ g ∈ Dec (F := ℚ) A, z g = θ g * m - m := by
    intro A hA
    obtain ⟨u, hu, -⟩ := hconj l A (D.pl l) hl.out hA (hD.pl_over l hl.out)
    refine cob_conj θ z hz _ _ u hu ?_
    obtain ⟨a, ha⟩ := pat_split hdt (r.comp (D.Gp l).subtype) (fun g => hp g) heq.2
      (fun a b h => hinj (Subtype.ext h)) m' (fun i => hI i _ hs0) hij hk hlt
    refine ⟨a, fun g hg => ?_⟩
    have e : r g i j = a * (r g i i - r g j j) := ha ⟨g, hg⟩
    simp only [z]
    rw [hθ, e]
    have := hκ0 j g
    field_simp
  have hU : ∀ A : ValuationSubring Ω, ∃ m, ∀ g ∈ Ine (F := ℚ) A, z g = θ g * m - m := by
    intro A
    by_cases hA : Raw.Away D.T A
    · haveI := D.rbar.ker.quotient_finite_of_isOpen fo
      haveI : D.rbar.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact cob_fin θ z hz _ D.rbar.ker fun g hg h1 => hz1 g (hunr A hA g hg h1)
    · simp only [Raw.Away, not_forall, not_not] at hA
      obtain ⟨p, hpT, hA⟩ := hA
      rcases Finset.mem_insert.1 hpT with rfl | hpb
      · obtain ⟨a, ha⟩ := hL A hA
        exact ⟨a, fun g hg => ha g hg.1⟩
      · have hpp := (fSb p hpb).1
        obtain ⟨u, -, hu⟩ := hconj p A (D.pl p) hpp hA (hD.pl_over p hpp)
        refine cob_conj θ z hz _ _ u hu ?_
        haveI := D.ψ.ker.quotient_finite_of_isOpen hD.psi_open
        haveI : D.ψ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
        exact cob_fin θ z hz _ D.ψ.ker fun g hg h1 => hz1 g ((heqP p hpb).2 ⟨g, hg.1⟩ ⟨hg, h1⟩)
  have hw : ∀ a b : Fin 4, a < b → D.wts4 b < D.wts4 a := by
    have := hD.two_le
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Raw.wts4] at h ⊢ <;> omega
  obtain ⟨δ, hδo, hδ1⟩ := hδ i
  obtain ⟨δ', hδo', hδ1'⟩ := hδ j
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (hw _ _ hlt)
  obtain ⟨a, ha⟩ := hSo (δ' / δ) (Subgroup.isOpen_mono (H₁ := δ.ker ⊓ δ'.ker) (fun g hg => by
      have h1 : δ g = 1 := hg.1
      have h2 : δ' g = 1 := hg.2
      simp [h1, h2]) (hδo.inter hδo')) (n + 1) (by omega) (fun g => θ g) (fun g => by
      have h0 := hκ0 j g
      rw [hθ]
      rw [hδ1', hn] at h0 ⊢
      rw [hδ1]
      have h1 := (δ g).ne_zero
      simp only [MonoidHom.div_apply, Units.val_div_eq_div_val]
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_eq_one_iff_eq (mul_ne_zero h0 h1)]
      ring) z ((hent i j).div (hent j j) (hκ0 j)) hz hU hL
  have hs : ∀ X ∈ Submodule.span (PadicAlgCl l) (Set.range r), X i j = a * (X i i - X j j) := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e := ha g
      simp only [z] at e
      have := hκ0 j g
      rw [hθ, div_eq_iff this] at e
      rw [e]
      field_simp
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, hx, hy]; ring
    | smul b x _ hx => simp only [Matrix.smul_apply, hx, smul_eq_mul]; ring
  have a0 : a = 0 := by
    have := hs _ (hE i)
    simpa [Matrix.single_apply, hij] using this.symm
  obtain ⟨g, hg⟩ := hge
  exact hg (by rw [hs _ (Submodule.subset_span ⟨g, rfl⟩), a0, zero_mul])
