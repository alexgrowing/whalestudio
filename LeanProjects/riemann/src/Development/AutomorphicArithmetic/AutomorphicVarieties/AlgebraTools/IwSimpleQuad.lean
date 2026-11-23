import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem quadAbs {A G M ι : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (s : G) (hs : s * s = 1) (x : ι → G)
    (hx : ∀ c, x c ∈ I) (hT : ∀ v : fixd ρ I, (hk ρ I s v : M) = ∑ c, ρ (x c * s) v) (o : ι) (ho : x o = 1)
    (y d : ι → G) (hy : ∀ c ≠ o, y c ∈ I) (hc : ∀ c ≠ o, ∀ c', x c' * y c = y c * x c')
    (hd : ∀ c ≠ o, d c ∈ Subgroup.normalizer (I : Set G))
    (h : ∀ c ≠ o, s * x c * s = y c * s * d c * y c) :
    hk ρ I s * hk ρ I s = (Fintype.card ι : A) • 1 + ∑ c ∈ Finset.univ.erase o, hk ρ I s * hk ρ I (d c) := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have fx : ∀ (w : fixd ρ I), ∀ g ∈ I, ρ g w = w := fun w => w.2
  have key : ∀ c ≠ o, ∑ c', ρ (x c' * s) (ρ (x c * s) v) = (hk ρ I s (hk ρ I (d c) v) : M) := by
    intro c hco
    rw [← fx (hk ρ I s _) _ (hy c hco), hT, map_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [(hkNorm A G M ρ I (d c) hI (hd c hco)).1]
    conv_rhs => rw [← fx v _ (hy c hco)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    calc x c' * s * (x c * s) = x c' * (s * x c * s) := by group
      _ = (x c' * y c) * s * d c * y c := by rw [h c hco]; group
      _ = _ := by rw [hc c hco]; group
  have k0 : ∑ c', ρ (x c' * s) (ρ (x o * s) v) = (Fintype.card ι : A) • (v : M) := by
    have : ∀ c', ρ (x c' * s) (ρ (x o * s) v) = v := fun c' => by
      rw [← Module.End.mul_apply, ← map_mul, ho, one_mul, mul_assoc, hs, mul_one, fx v _ (hx c')]
    simp only [this]
    simp [Nat.cast_smul_eq_nsmul]
  rw [Module.End.mul_apply, hT, hT]
  simp only [map_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ o), k0]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Module.End.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c hc' => key c (Finset.ne_of_mem_erase hc')

private theorem matId {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Rˣ) :
    (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) * (1 + single i j (a : R)) * (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) =
      (1 + single i j ((a⁻¹ : Rˣ) : R)) * (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) *
      (diagT R (Fin n) (fun l => if l = i then a else if l = j then -a⁻¹ else 1) : Matrix (Fin n) (Fin n) R) *
      (1 + single i j ((a⁻¹ : Rˣ) : R)) := by
  have hP : (pm R n (Equiv.swap i j) : Matrix (Fin n) (Fin n) R) =
      1 - single i i 1 - single j j 1 + single i j 1 + single j i 1 := by
    ext p q
    rw [pm_apply]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply, Equiv.swap_apply_def]
    by_cases h1 : p = i <;> by_cases h2 : p = j <;> by_cases h3 : q = i <;> by_cases h4 : q = j <;>
      simp_all [eq_comm]
  have hD : (diagT R (Fin n) (fun l => if l = i then a else if l = j then -a⁻¹ else 1) : Matrix (Fin n) (Fin n) R) =
      1 - single i i 1 - single j j 1 + single i i (a : R) - single j j ((a⁻¹ : Rˣ) : R) := by
    ext p q
    rw [val_diagT]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, single_apply, diagonal_apply]
    by_cases h1 : p = i <;> by_cases h2 : p = j <;> by_cases h3 : q = i <;> by_cases h4 : q = j <;>
      simp_all [eq_comm]
  rw [hP, hD]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm, zero_mul, mul_zero,
    Units.inv_mul, Units.mul_inv]
  abel

private theorem swapDiag {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (t : Fin n → Rˣ) :
    pm R n w * diagT R (Fin n) (t ∘ w) = diagT R (Fin n) t * pm R n w := by
  ext p q
  rw [Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul, pm_apply]
  split_ifs with h
  · simp [h]
  · simp

private theorem diagNorm {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) {t : Fin n → kˣ} (ht : t ∈ torusO k (Fin n)) :
    diagT k (Fin n) t ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  have h := diagT_mem_iwahori ht
  have N := (memIwC k n C).2.2.1
  refine Subgroup.mem_normalizer_iff.2 fun b => ⟨N _ h b, fun hb => ?_⟩
  have := N _ (inv_mem h) _ hb
  simpa [mul_assoc] using this

theorem UpperTheory.V.AlgebraTools.simpleQuad :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (i j : Fin n), (j : ℕ) = i + 1 → (IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n (Equiv.swap i j)))) ∧ (C = ⊤ → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) = ((resCard k : A) - 1) • hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) + (resCard k : A) • 1) := by
  intro k _ _ _ _ n C A M _ _ _ ρ i j hj
  classical
  have hij : i ≠ j := fun h => by rw [h] at hj; omega
  have hI := (heckePairIwC k n C).1
  have hU : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hq : resCard k = Fintype.card 𝓀[k] := Nat.card_eq_fintype_card
  obtain ⟨r0, hr0⟩ := (IsLocalRing.residue_surjective (R := 𝒪[k])).hasRightInverse
  have hup : ∀ (b : 𝒪[k]) c, IsLocalRing.residue 𝒪[k] (Function.update r0 (IsLocalRing.residue 𝒪[k] b) b c) = c := by
    intro b c
    by_cases h : c = IsLocalRing.residue 𝒪[k] b
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr0 c
  obtain ⟨x, hx1, hx2, hx3, -⟩ := simpleOrbit k n C i j hj _ (hup 0)
  set r := Function.update r0 (IsLocalRing.residue 𝒪[k] 0) 0 with hr
  set s := pm k n (Equiv.swap i j) with hs
  have hss : s * s = 1 := by rw [hs, ← map_mul, Equiv.swap_mul_self, map_one]
  have hx0 : x 0 = 1 := by
    ext1
    rw [hx1]
    have : r 0 = 0 := by rw [hr, ← map_zero (IsLocalRing.residue 𝒪[k])]; simp
    simp [this]
  have hT : ∀ v : fixd ρ (iwC k n C), (hk ρ (iwC k n C) s v : M) = ∑ c, ρ (x c * s) v := by
    intro v
    have horb : ∀ c, ((x c * s : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ∈
        MulAction.orbit (iwC k n C) (s : GL (Fin n) k ⧸ iwC k n C) := fun c => ⟨⟨x c, hU (hx2 c)⟩, rfl⟩
    have hinj : Function.Injective fun c => x c * s := fun c c' h =>
      ((hx3 _).1 (horb c)).unique rfl (congrArg _ h.symm)
    have := (hkApply A _ M ρ _ _ s (hI s)).2.1 (Finset.univ.image fun c => x c * s) (fun y hy => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact horb c) (fun q hq => by
      obtain ⟨c, hc, hu⟩ := (hx3 q).1 hq
      refine ⟨x c * s, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ c), hc⟩, ?_⟩
      rintro y ⟨hy, hy'⟩
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hy
      rw [hu c' hy']) v
    rw [Finset.sum_image fun c _ c' _ h => hinj h] at this
    exact this
  have hex : ∀ c : 𝓀[k], ∃ (y : GL (Fin n) k) (t : Fin n → kˣ), t ∈ torusO k (Fin n) ∧ (c ≠ 0 → y ∈ iwC k n C ∧
      (∀ c', x c' * y = y * x c') ∧ s * x c * s = y * s * diagT k (Fin n) t * y) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨1, 1, one_mem _, fun h => absurd hc h⟩
    obtain ⟨u, hu⟩ : IsUnit (r c) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hup 0]; exact hc
    obtain ⟨z, hz1, hz2, -⟩ := simpleOrbit k n C i j hj _ (hup ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]))
    let a : kˣ := Units.map (algebraMap 𝒪[k] k).toMonoidHom u
    have ha : valuation k (a : k) = 1 := (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have hz := hz1 (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]))
    rw [Function.update_self] at hz
    have hz' : (z (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : Matrix (Fin n) (Fin n) k) =
      1 + single i j ((a⁻¹ : kˣ) : k) := hz
    have hxc : (x c : Matrix (Fin n) (Fin n) k) = 1 + single i j (a : k) := by rw [hx1, ← hu]; rfl
    refine ⟨z (IsLocalRing.residue 𝒪[k] ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])),
      fun l => if l = i then a else if l = j then -a⁻¹ else 1, fun l => ?_, fun _ => ⟨hU (hz2 _), fun c' => ?_, ?_⟩⟩
    · dsimp only
      split_ifs <;> simp [ha]
    · ext1
      rw [Units.val_mul, Units.val_mul, hz', hx1]
      simp only [mul_add, add_mul, mul_one, one_mul, single_mul_single_of_ne _ _ _ _ hij.symm]
      abel
    · ext1
      simp only [Units.val_mul, hz', hxc]
      exact matId i j hij a
  choose y t ht hy using hex
  have Q := quadAbs ρ _ hI s hss x (fun c => hU (hx2 c)) hT 0 hx0 y (fun c => diagT k (Fin n) (t c))
    (fun c h => (hy c h).1) (fun c h => (hy c h).2.1) (fun c _ => diagNorm C (ht c)) (fun c h => (hy c h).2.2)
  rw [← hq] at Q
  refine ⟨fun hu => ?_, fun hC => ?_⟩
  · obtain ⟨q, hq'⟩ := hu
    have hsw : ∀ c, hk ρ (iwC k n C) s * hk ρ (iwC k n C) (diagT k (Fin n) (t c)) =
        hk ρ (iwC k n C) (diagT k (Fin n) (t c ∘ Equiv.swap i j)) * hk ρ (iwC k n C) s := by
      intro c
      have h' : t c ∘ Equiv.swap i j ∈ torusO k (Fin n) := fun l => ht c _
      rw [← ((hkNorm A _ M ρ _ _ hI (diagNorm C (ht c))).2.2.2 s).2,
        ← ((hkNorm A _ M ρ _ _ hI (diagNorm C h')).2.2.2 s).1, hs, ← swapDiag]
      congr 3
      ext l
      simp
    have h1 : hk ρ (iwC k n C) s * (((q⁻¹ : Aˣ) : A) • (hk ρ (iwC k n C) s -
        ∑ c ∈ Finset.univ.erase 0, hk ρ (iwC k n C) (diagT k (Fin n) (t c)))) = 1 := by
      rw [mul_smul_comm, mul_sub, Finset.mul_sum, Q, add_sub_cancel_right, smul_smul, ← hq', Units.inv_mul, one_smul]
    have h2 : (((q⁻¹ : Aˣ) : A) • (hk ρ (iwC k n C) s -
        ∑ c ∈ Finset.univ.erase 0, hk ρ (iwC k n C) (diagT k (Fin n) (t c ∘ Equiv.swap i j)))) * hk ρ (iwC k n C) s = 1 := by
      rw [smul_mul_assoc, sub_mul, Finset.sum_mul, Q]
      simp only [hsw]
      rw [add_sub_cancel_right, smul_smul, ← hq', Units.inv_mul, one_smul]
    refine ⟨⟨_, _, h1, ?_⟩, rfl⟩
    rw [← left_inv_eq_right_inv h2 h1]
    exact h2
  · have h1 : ∀ c, hk ρ (iwC k n C) (diagT k (Fin n) (t c)) = 1 := fun c => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [(hkNorm A _ M ρ _ _ hI (diagNorm C (ht c))).1]
      refine v.2 _ ?_
      rw [hC, (memIwC k n ⊤).2.1]
      exact diagT_mem_iwahori (ht c)
    rw [Q, add_comm]
    simp only [h1, mul_one, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_sub Fintype.card_pos, hq, Nat.cast_one]
