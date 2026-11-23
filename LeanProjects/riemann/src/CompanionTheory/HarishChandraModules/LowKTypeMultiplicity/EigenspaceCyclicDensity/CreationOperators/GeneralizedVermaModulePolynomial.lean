import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordMonomial

open Finset MvPolynomial
open scoped TensorProduct

noncomputable section

namespace CompanionTheory.D.LK

open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)

theorem deg_pderiv {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical
  rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega

theorem pderiv_deg_zero {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]

theorem deg_X_mul {σ : Type} (j : σ) (f : MvPolynomial σ ℂ) : (X j * f).totalDegree ≤ f.totalDegree + 1 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)

theorem deg_X_pderiv {σ : Type} (j i : σ) (f : MvPolynomial σ ℂ) : (X j * pderiv i f).totalDegree ≤ f.totalDegree := by
  cases h : f.totalDegree with
  | zero => simp [pderiv_deg_zero i f h.le]
  | succ k => exact (deg_X_mul _ _).trans (Nat.succ_le_succ (deg_pderiv i f k h.le))

theorem generalized_verma_module_polynomial : Verma2 := by
  intro n ε
  let u : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) - dd ε a c
  let v : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) + dd ε a c
  have hδ : ∀ (a c : Fin n) (T : Module.End ℂ (MvPolynomial (NC ε) ℂ)),
      Commute (if a = c then 1 else 0) T := by
    intro a c T
    split_ifs <;> simp
  refine ⟨fun c d => ∑ i : NC ε, yy i * (u i.1.1 c * v d i.1.2), ?_, ?_, ?_, ?_⟩
  · intro c d e f
    refine glRel_abstract yy u v ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d e f
    · intro i j
      refine LinearMap.ext fun f => ?_
      simp [yy, mul_left_comm]
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.sub_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).add_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a c j
      rw [← dd_yy]
      simp only [u, sub_mul, mul_sub, (hδ a c (yy j)).eq]
      abel
    · intro a c j
      rw [← dd_yy]
      simp only [v, add_mul, mul_add, (hδ a c (yy j)).eq]
      abel
    · intro d e
      have h0 : ¬(ε d = true ∧ ε e = false) → dd ε d e = 0 := fun h => dif_neg h
      simp only [u, v]
      generalize dd ε d e = T at *
      by_cases hde : d = e
      · subst hde
        cases h : ε d <;> simp_all
      · cases h : ε d <;> cases h' : ε e <;> simp_all
  · intro i f
    have hu : ∀ j : NC ε, u j.1.1 i.1.1 = if j.1.1 = i.1.1 then 1 else 0 := by
      intro j
      simp [u, dd, i.2.1]
    have hv : ∀ j : NC ε, v i.1.2 j.1.2 = if i.1.2 = j.1.2 then 1 else 0 := by
      intro j
      simp [v, dd, i.2.2]
    simp only [hu, hv]
    rw [Finset.sum_eq_single i]
    · simp [yy]
    · intro j _ hj
      split_ifs with h1 h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hj
      all_goals simp
    · simp
  · intro a b f
    simp [yy, LinearMap.sum_apply, map_sum]

  · intro c d f h
    have hd : ∀ (i : NC ε) (a b : Fin n), (X i * dd ε a b f).totalDegree ≤ f.totalDegree := fun i a b => by
      unfold dd
      split_ifs
      · exact deg_X_pderiv _ _ f
      · simp
    rw [LinearMap.sum_apply]
    refine totalDegree_finsetSum_le fun i _ => ?_
    have i1 := i.2.1
    have i2 := i.2.2
    cases hc : ε c
    · have e1 : i.1.1 ≠ c := fun e => by rw [e, hc] at i1; exact Bool.noConfusion i1
      have e2 : dd ε d i.1.2 = 0 := dif_neg (by simp [← h, hc])
      simp only [u, v, if_neg e1, e2, yy, Module.End.mul_apply, add_zero, zero_sub, LinearMap.neg_apply,
        LinearMap.mulLeft_apply]
      split_ifs
      · rw [mul_neg, totalDegree_neg]; exact hd _ _ _
      · simp
    · have e1 : d ≠ i.1.2 := fun e => by rw [← e, ← h, hc] at i2; exact Bool.noConfusion i2
      have e2 : dd ε i.1.1 c = 0 := dif_neg (by simp [hc])
      simp only [u, v, if_neg e1, e2, yy, Module.End.mul_apply, zero_add, sub_zero, LinearMap.mulLeft_apply]
      split_ifs
      · exact hd _ _ _
      · simp

theorem kRel_tens {n : ℕ} {ε : Fin n → Bool} {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
    {E : Fin n → Fin n → Module.End ℂ V} {M : Fin n → Fin n → Module.End ℂ Z} (hE : KRel ε E) (hM : GlRel M) :
    KRel ε fun a b => ((E a b).rTensor Z + (M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] Z)) := by
  intro a b c d h1 h2
  apply TensorProduct.ext'
  intro v z
  have e1 := LinearMap.congr_fun (hE a b c d h1 h2) v
  have e2 := LinearMap.congr_fun (hM a b c d) z
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at e1 e2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, sub_eq_iff_eq_add.1 e2, TensorProduct.add_tmul,
    TensorProduct.tmul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  split_ifs <;> simp <;> abel

theorem free_module_induction : FreeStep := by
  rintro n m ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩
  classical
  let ε : Fin n → Bool := fun c => decide ((c : ℕ) ≤ m)
  obtain ⟨M', hM', hX, hc, hdeg⟩ := generalized_verma_module_polynomial n ε
  let P := MvPolynomial (NC ε) ℂ
  let cc : P →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ)
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  let y : Pos n → Module.End ℂ P := fun i =>
    if h : ε i.1.1 = true ∧ ε i.1.2 = false then yy (⟨i.1, h⟩ : NC ε) else 0
  let S : ℕ → Set (Z ⊗[ℂ] P) := fun k =>
    {t | ∃ k₁ z f, z ∈ Fil k₁ ∧ k₁ + f.totalDegree ≤ k ∧ t = z ⊗ₜ f}
  have hin : ∀ {k k₁ : ℕ} {z : Z} {f : P}, z ∈ Fil k₁ → k₁ + f.totalDegree ≤ k →
      z ⊗ₜ[ℂ] f ∈ Submodule.span ℂ (S k) := fun hz hf => Submodule.subset_span ⟨_, _, _, hz, hf, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (Z ⊗[ℂ] P)) (k : ℕ) (Q : Submodule ℂ (Z ⊗[ℂ] P)),
      (∀ k₁ z f, z ∈ Fil k₁ → k₁ + f.totalDegree ≤ k → T (z ⊗ₜ f) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨k₁, z, f, hz, hf, rfl⟩
    exact h k₁ z f hz hf
  have hy : ∀ i f, (y i f).totalDegree ≤ f.totalDegree + 1 := fun i f => by
    simp only [y]
    split_ifs
    · exact deg_X_mul _ _
    · simp
  have hddl : ∀ a b (f : P) k, f.totalDegree ≤ k + 1 → (dd ε a b f).totalDegree ≤ k := fun a b f k h => by
    unfold dd
    split_ifs
    · exact deg_pderiv _ _ _ h
    · simp
  have hdd0 : ∀ a b (f : P), f.totalDegree ≤ 0 → dd ε a b f = 0 := fun a b f h => by
    unfold dd
    split_ifs
    · exact pderiv_deg_zero _ _ h
    · simp
  refine ⟨Z ⊗[ℂ] P, inferInstance, inferInstance, fun c e => (M c e).rTensor P + (M' c e).lTensor Z,
    χ ∘ₗ (TensorProduct.rid ℂ Z).toLinearMap ∘ₗ cc.lTensor Z, z₀ ⊗ₜ 1,
    fun i => (a i).rTensor P + (y i).lTensor Z,
    fun i => if (i.1.1 : ℕ) < m then (d i).rTensor P else (dd ε i.1.1 i.1.2).lTensor Z,
    fun k => Submodule.span ℂ (S k),
    fun a b c e => kRel_tens (ε := allT n) (fun a b c d _ _ => hM a b c d) hM' a b c e rfl rfl, by simp [hcc, h1],
    fun c e t => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [hcc, hc, h0]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  · intro i j
    apply TensorProduct.ext'
    intro z f
    have e1 := LinearMap.congr_fun (hF.a_comm i j).eq z
    have e2 : y i (y j f) = y j (y i f) := by
      have hq : ∀ i, ∃ q : P, ∀ f, y i f = q * f := fun i => by
        simp only [y]
        split_ifs
        · exact ⟨_, fun _ => rfl⟩
        · exact ⟨0, fun f => (zero_mul f).symm⟩
      obtain ⟨q, hq1⟩ := hq i
      obtain ⟨q', hq2⟩ := hq j
      rw [hq1, hq2, hq2, hq1, mul_left_comm]
    simp only [Module.End.mul_apply] at e1
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add,
      e1, e2]
    abel
  · intro i j
    apply TensorProduct.ext'
    intro z f
    have e1 := LinearMap.congr_fun (hF.d_comm i j).eq z
    have e2 := LinearMap.congr_fun (dd_comm (ε := ε) i.1.1 i.1.2 j.1.1 j.1.2).eq f
    simp only [Module.End.mul_apply] at e1 e2
    split_ifs <;> simp [e1, e2]
  · intro i j hi
    apply TensorProduct.ext'
    intro z f
    by_cases h : (i.1.1 : ℕ) < m
    · have e1 := LinearMap.congr_fun (hF.da i j h) z
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at e1
      simp only [if_pos h, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, TensorProduct.add_tmul]
      split_ifs <;> simp
    · have e1 : dd ε i.1.1 i.1.2 (y j f) - y j (dd ε i.1.1 i.1.2 f) = if i = j then f else 0 := by
        simp only [y]
        by_cases hj : ε j.1.1 = true ∧ ε j.1.2 = false
        · rw [dif_pos hj]
          have := LinearMap.congr_fun (dd_yy i.1.1 i.1.2 (⟨j.1, hj⟩ : NC ε)) f
          simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
          rw [this]
          by_cases e : i = j
          · subst e; simp
          · rw [if_neg e, if_neg fun h' => e (Subtype.ext (Prod.ext h'.1 h'.2))]; rfl
        · rw [dif_neg hj, if_neg]
          · simp
          · rintro rfl
            have := i.2
            exact hj ⟨by simp only [ε, decide_eq_true_eq]; omega,
              by simp only [ε, decide_eq_false_iff_not]; rw [Fin.lt_def] at this; omega⟩
      simp only [if_neg h, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, TensorProduct.tmul_add]
      split_ifs <;> simp
  · intro k l hkl
    refine Submodule.span_mono ?_
    rintro _ ⟨k₁, z, f, hz, hf, rfl⟩
    exact ⟨k₁, z, f, hz, hf.trans hkl, rfl⟩
  · intro t
    have hm : ∀ {k l}, k ≤ l → Submodule.span ℂ (S k) ≤ Submodule.span ℂ (S l) := fun hkl =>
      Submodule.span_mono (by rintro _ ⟨k₁, z, f, hz, hf, rfl⟩; exact ⟨k₁, z, f, hz, hf.trans hkl, rfl⟩)
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul z f =>
      obtain ⟨k, hk⟩ := hF.exh z
      exact ⟨_, hin hk le_rfl⟩
    | add p q hp hq =>
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
  · refine fun i k => hmap _ k _ fun k₁ z f hz hf => ?_
    have := hy i f
    rw [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.add_mem _ (hin (hF.a_mem i _ z hz) (by omega)) (hin hz (by omega))
  · intro i k
    refine hmap (((M i.1.1 i.1.2).rTensor P + (M' i.1.1 i.1.2).lTensor Z) - ((a i).rTensor P + (y i).lTensor Z)) k _
      fun k₁ z f hz hf => ?_
    have e : (((M i.1.1 i.1.2).rTensor P + (M' i.1.1 i.1.2).lTensor Z) - ((a i).rTensor P + (y i).lTensor Z) :
        Module.End ℂ (Z ⊗[ℂ] P)) (z ⊗ₜ f) =
        (M i.1.1 i.1.2 z - a i z) ⊗ₜ f + z ⊗ₜ (M' i.1.1 i.1.2 f - y i f) := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    rw [e]
    refine Submodule.add_mem _ (hin (hF.r_mem i _ z hz) hf) (hin hz (le_trans (Nat.add_le_add_left ?_ _) hf))
    simp only [y]
    split_ifs with h
    · rw [hX ⟨i.1, h⟩]; simp [yy]
    · rw [LinearMap.zero_apply, sub_zero]
      refine hdeg _ _ _ ?_
      have := i.2
      rw [Fin.lt_def] at this
      simp only [ε, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
      exact decide_eq_decide.2 (by omega)
  · refine fun i k => hmap _ _ _ fun k₁ z f hz hf => ?_
    split_ifs
    · cases k₁ with
      | zero => rw [LinearMap.rTensor_tmul, hF.d_zero i z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
      | succ k₁ => rw [LinearMap.rTensor_tmul]; exact hin (hF.d_mem i _ z hz) (by omega)
    · rw [LinearMap.lTensor_tmul]
      cases hf' : f.totalDegree with
      | zero => rw [hdd0 _ _ f hf'.le, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | succ l => have := hddl i.1.1 i.1.2 f l hf'.le; exact hin hz (by omega)
  · refine fun i => hmap _ _ ⊥ fun k₁ z f hz hf => ?_
    obtain rfl : k₁ = 0 := by omega
    split_ifs
    · simp [hF.d_zero i z hz]
    · simp [hdd0 _ _ f (by omega)]

theorem free_all (n m : ℕ) : Free n m := by
  induction m with
  | zero =>
    exact ⟨ℂ, inferInstance, inferInstance, 0, LinearMap.id, 1, 0, 0, fun _ => ⊤, fun _ _ _ _ => by simp, rfl,
      by simp, fun _ _ => Commute.refl _, fun _ _ => Commute.refl _, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ => le_rfl, fun _ => ⟨0, trivial⟩, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial,
      fun _ _ _ _ => trivial, fun _ _ _ => rfl⟩
  | succ m ih => exact free_module_induction n m ih

theorem cover2_of (hA : AcycAbs) : Cover2 := by
  intro n ε V _ _ E hE
  obtain ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩ := free_all n n
  let S : ℕ → Set (V ⊗[ℂ] Z) := fun k => {t | ∃ v z, z ∈ Fil k ∧ t = v ⊗ₜ z}
  have hin : ∀ {k : ℕ} (v : V) {z : Z}, z ∈ Fil k → v ⊗ₜ[ℂ] z ∈ Submodule.span ℂ (S k) :=
    fun v _ hz => Submodule.subset_span ⟨_, _, hz, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (V ⊗[ℂ] Z)) (k : ℕ) (Q : Submodule ℂ (V ⊗[ℂ] Z)),
      (∀ v z, z ∈ Fil k → T (v ⊗ₜ z) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨v, z, hz, rfl⟩
    exact h v z hz
  have hm : Monotone fun k => Submodule.span ℂ (S k) := fun k l hkl =>
    Submodule.span_mono (by rintro _ ⟨v, z, hz, rfl⟩; exact ⟨v, z, hF.mono hkl hz, rfl⟩)
  refine ⟨V ⊗[ℂ] Z, inferInstance, inferInstance, fun c e => (E c e).rTensor Z + (M c e).lTensor V,
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ χ.lTensor V, kRel_tens hE hM, fun v => ⟨v ⊗ₜ z₀, by simp [h1]⟩,
    fun c e t => ?_, hA n ε _ _ (fun i => (a i).lTensor V) (fun i => (d i).lTensor V)
      (fun k => Submodule.span ℂ (S k)) (kRel_tens hE hM) ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · exact fun i j => (hF.a_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · exact fun i j => (hF.d_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · intro i j _
    have := congrArg (Module.End.lTensorAlgHom ℂ Z V) (hF.da i j i.1.1.2)
    rw [map_sub, map_mul, map_mul, apply_ite (Module.End.lTensorAlgHom ℂ Z V), map_one, map_zero] at this
    exact this
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul v z =>
      obtain ⟨k, hk⟩ := hF.exh z
      exact ⟨_, hin v hk⟩
    | add p q hp hq =>
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
  · exact fun i k => hmap _ k _ fun v z hz => hin v (hF.a_mem i _ z hz)
  · intro i k
    refine hmap (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V) k _ fun v z hz => ?_
    have e : (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V :
        Module.End ℂ (V ⊗[ℂ] Z)) (v ⊗ₜ z) = E i.1.1 i.1.2 v ⊗ₜ z + v ⊗ₜ (M i.1.1 i.1.2 z - a i z) := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.tmul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hin _ hz) (hin _ (hF.r_mem i _ z hz))
  · exact fun i k => hmap _ _ _ fun v z hz => hin v (hF.d_mem i _ z hz)
  · exact fun i => hmap _ _ ⊥ fun v z hz => by simp [hF.d_zero i z hz]

end CompanionTheory.D.LK
