import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneCntO
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FiltCount

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
private theorem filt_ht {Z Y ι : Type} [AddCommGroup Z] [AddCommGroup Y] [Fintype ι] (ht : ι → ℕ) (f : ι → Z →+ Y)
    (P : ι → Set Y) (h0 : ∀ z, (∀ i, f i z = 0) → z = 0) (hP : ∀ i, (P i).Finite)
    (hf : ∀ i z, (∀ j, ht j < ht i → f j z = 0) → f i z ∈ P i) : Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  let e₀ := (Fintype.equivFin ι).symm
  let e := (Tuple.sort (ht ∘ e₀)).trans e₀
  have hm : Monotone (ht ∘ e) := Tuple.monotone_sort (ht ∘ e₀)
  rw [← e.prod_comp]
  refine filtCount Z Y _ (fun i => f (e i)) (fun i => P (e i)) (fun z hz => h0 z fun i => ?_) (fun i => hP _)
    fun i z hz => hf _ z fun j hj => ?_
  · obtain ⟨i, rfl⟩ := e.surjective i
    exact hz i
  · obtain ⟨j, rfl⟩ := e.surjective j
    exact hz j (hm.reflect_lt hj)

private theorem conj_entry {R : Type} [CommRing R] {n : ℕ} (T B T' : Matrix (Fin n) (Fin n) R)
    (hT : ∀ i j, j < i → T i j = 0) (hT' : ∀ i j, j < i → T' i j = 0) (i j : Fin n)
    (hB : ∀ p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → B p q = 0) : (T * B * T') i j = T i i * B i j * T' j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro p _ hp
    by_cases c : p < i
    · rw [hT i p c, zero_mul]
    · rw [hB p j (not_lt.1 c) le_rfl (.inl hp), mul_zero]
  · simp
  · intro q _ hq
    by_cases c : j < q
    · rw [hT' q j c, mul_zero]
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases c' : p < i
      · rw [hT i p c', zero_mul]
      · rw [hB p q (not_lt.1 c') (not_lt.1 c) (.inr hq), mul_zero]
  · simp

private theorem adic_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f f' : D → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => f g * f' g := fun N => by
  simp only [map_mul]
  exact (h N).mul (h' N)

private theorem adic_sum {D R ι : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} (s : Finset ι) {f : ι → D → R}
    (h : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := fun N => by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsLocallyConstant.of_constant _ fun _ _ => rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, map_add]
    exact (h i N).add ih

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (y : Pt G0.frame O n) (v : L.Vl)

private theorem psi_cont (i : Fin n) : AdicCont (maximalIdeal O) fun g : L.Gv v => (y.ψ v i g : O) := by
  have e : (fun g : L.Gv v => (y.ψ v i g : O)) = fun g => ∑ q, (∑ p, (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i p *
      mat y.ρ (G0.φ v g) p q) * (y.w v : Matrix (Fin n) (Fin n) O) q i := funext fun g => ((y.tri v g).2 i).symm
  rw [e]
  exact adic_sum _ fun q => adic_mul (adic_sum _ fun p => adic_mul (fun N => IsLocallyConstant.const _)
    fun N => (y.cont p q N).comp_continuous (G0.φ_cont v)) fun N => IsLocallyConstant.const _

private noncomputable def cj (m : ℕ) (Z : Mm O n m) : Mm O n m :=
  red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * red m (y.w v : Matrix (Fin n) (Fin n) O)

private theorem i2 (m : ℕ) :
    red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [← red_mul, Units.mul_inv, red_one]

private theorem cj_rho (m : ℕ) (g : L.Gv v) : (∀ i j, j < i → cj y v m (y.ρ0 m (G0.φ v g)) i j = 0) ∧
    ∀ i, cj y v m (y.ρ0 m (G0.φ v g)) i i = algebraMap O (Om O m) (y.ψ v i g : O) := by
  have e : cj y v m (y.ρ0 m (G0.φ v g)) =
      red m (((y.w v)⁻¹ * y.ρ (G0.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    rw [Units.val_mul, Units.val_mul, red_mul, red_mul]; rfl
  rw [e]
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (congrArg (Ideal.Quotient.mk _) ((y.tri v g).1 i j h)).trans (map_zero _)
  · exact congrArg (Ideal.Quotient.mk _) ((y.tri v g).2 i)

private noncomputable def crd (m : ℕ) (i j : Fin n) : Zbor y m v →+ (L.Gv v → Om O m) :=
  AddMonoidHom.mk' (fun β g => cj y v m (β.1 g) i j) fun β β' => funext fun g => by
    simp only [cj, AddSubgroup.coe_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

private theorem crd_coc (m : ℕ) (i j : Fin n) (β : Zbor y m v)
    (hB : ∀ g p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → cj y v m (β.1 g) p q = 0) :
    IsLocallyConstant (crd y v m i j β) ∧ ∀ g h, crd y v m i j β (g * h) =
      crd y v m i j β g + ((y.ψ v i g : O) * (y.ψ v j g⁻¹ : O)) • crd y v m i j β h := by
  refine ⟨β.2.1.comp fun Z : Mm O n m => cj y v m Z i j, fun g h => ?_⟩
  have e : cj y v m (β.1 (g * h)) = cj y v m (β.1 g) +
      cj y v m (y.ρ0 m (G0.φ v g)) * cj y v m (β.1 h) * cj y v m (y.ρ0 m (G0.φ v g⁻¹)) := by
    have i3 : ∀ M : Mm O n m, red m (y.w v : Matrix (Fin n) (Fin n) O) *
        (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * M) = M := fun M => by
      rw [← mul_assoc, i2, one_mul]
    rw [β.2.2.1 g h, map_inv]
    simp only [cj, mul_add, add_mul, mul_assoc, i3]
  change cj y v m (β.1 (g * h)) i j = cj y v m (β.1 g) i j + _ • cj y v m (β.1 h) i j
  rw [e, Matrix.add_apply, conj_entry _ _ _ (cj_rho y v m g).1 (cj_rho y v m g⁻¹).1 i j (hB h), (cj_rho y v m g).2,
    (cj_rho y v m g⁻¹).2, Algebra.smul_def, map_mul]
  ring

end

theorem UpperTheory.V.Th.locVO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (v : L.Vl) (d : ℕ), LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) d → (∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → ∃ C : ℕ, ∀ m, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ (m * ((n + n.choose 2) * (1 + d)) + C) := by
  intro l _ L G0 O _ _ _ _ _ n y v d hL hε
  let P : ∀ m, {p : Fin n × Fin n // p.1 ≤ p.2} → Set (L.Gv v → Om O m) := fun m t =>
    {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ((y.ψ v t.1.1 g : O) * (y.ψ v t.1.2 g⁻¹ : O)) • z h}
  have hP : ∀ t, ∃ C : ℕ, ∀ m, (P m t).Finite ∧ (P m t).ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
    rintro ⟨⟨i, j⟩, hij⟩
    let χ : L.Gv v →* Oˣ := y.ψ v i * (y.ψ v j)⁻¹
    have e : ∀ g, ((χ g : Oˣ) : O) = (y.ψ v i g : O) * (y.ψ v j g⁻¹ : O) := fun g => by
      show ((y.ψ v i g * (y.ψ v j g)⁻¹ : Oˣ) : O) = _
      rw [map_inv, Units.val_mul]
    have h := oneCntO l O (L.Gv v) _ d χ hL ?_ ?_
    · simpa only [e] using h
    · simp only [e]
      exact adic_mul (psi_cont y v i) fun N => (psi_cont y v j N).comp_continuous continuous_inv
    · rcases hij.lt_or_eq with hlt | heq
      · by_contra c
        push Not at c
        refine y.N1 v i j hlt (MonoidHom.ext fun g => ?_)
        have c' : y.ψ v i g * (y.ψ v j g)⁻¹ = G0.frame.eps O O (G0.φ v g) := Units.ext (c g)
        show y.ψ v i g = y.ψ v j g * G0.frame.eps O O (G0.φ v g)
        rw [← c', mul_comm, inv_mul_cancel_right]
      · obtain ⟨g, hg⟩ := hε
        refine ⟨g, fun c => hg ?_⟩
        have hij' : i = j := heq
        subst hij'
        have c1 : χ g = 1 := mul_inv_cancel (y.ψ v i g)
        rw [c1] at c
        exact c.symm
  choose C hC using hP
  refine ⟨∑ t, C t, fun m => ?_⟩
  refine And.imp_right (fun h2 => ?_) <| filt_ht (fun t : {p : Fin n × Fin n // p.1 ≤ p.2} => (t.1.2 : ℕ) - t.1.1)
    (fun t => crd y v m t.1.1 t.1.2) (P m) (fun β h => ?_) (fun t => (hC t m).1) fun t β h => ?_
  · refine h2.trans ((Finset.prod_le_prod' fun t _ => (hC t m).2).trans (le_of_eq ?_))
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_le', smul_eq_mul]
    congr 1
    ring
  · refine Subtype.ext (funext fun g => ?_)
    have e0 : cj y v m (β.1 g) = 0 := Matrix.ext fun p q => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · exact congrFun (h ⟨(p, q), not_lt.1 c⟩) g
    have e1 := congrArg (fun M => red m (y.w v : Matrix (Fin n) (Fin n) O) * M *
      red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) e0
    simp only [cj, ← mul_assoc, i2, one_mul, mul_zero, zero_mul] at e1
    rwa [mul_assoc, i2, mul_one] at e1
  · exact crd_coc y v m t.1.1 t.1.2 β fun g p q c1 c2 c3 => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · refine congrFun (h ⟨(p, q), not_lt.1 c⟩ ?_) g
        simp only [Fin.le_def, Fin.lt_def, ne_eq, Fin.ext_iff] at c c1 c2 c3 ⊢
        omega
