import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open Function

universe u

section Comb

variable {V X Y : Type u} [AddCommGroup V]

theorem hd_succ' (n : ℕ) (F : (Fin (n + 2) → X) → V) (x : Fin (n + 3) → X) :
    hd (n + 1) F x = F (Fin.tail x) - hd n (fun y => F (Fin.cons (x 0) y)) (Fin.tail x) := by
  unfold hd
  rw [Fin.sum_univ_succ]
  have h0 : ((-1 : ℤ) ^ ((0 : Fin (n + 3)) : ℕ) • F fun j => x (Fin.succAbove 0 j)) = F (Fin.tail x) := by
    rw [Fin.val_zero, pow_zero, one_smul]; rfl
  have h1 : ∀ i : Fin (n + 2), ((-1 : ℤ) ^ (i.succ : ℕ) • F fun j => x (i.succ.succAbove j)) =
      -((-1 : ℤ) ^ (i : ℕ) • F (Fin.cons (x 0) fun j => Fin.tail x (i.succAbove j))) := by
    intro i
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
    congr 3
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_succAbove_succ, Fin.tail]
  rw [h0, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hd_zero' (F : (Fin 1 → X) → V) (x : Fin 2 → X) :
    hd 0 F x = F (Fin.tail x) - F (fun _ => x 0) := by
  unfold hd
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, sub_eq_add_neg]
  congr 2
  show F _ = F _
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
  subst hj; rfl

theorem hd_sub' (n : ℕ) (F G : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) :
    hd n (fun y => F y - G y) x = hd n F x - hd n G x := by
  simp [hd, smul_sub, Finset.sum_sub_distrib]

theorem hd_zero_fun (n : ℕ) (x : Fin (n + 2) → X) : hd n (fun _ : Fin (n + 1) → X => (0 : V)) x = 0 := by
  simp [hd]

theorem hd_comp' (n : ℕ) (F : (Fin (n + 1) → Y) → V) (c : X → Y) (x : Fin (n + 2) → X) :
    hd n (fun y => F fun i => c (y i)) x = hd n F (fun i => c (x i)) := rfl

noncomputable def prismOp (a b : X → Y) : (n : ℕ) → ((Fin (n + 2) → Y) → V) → (Fin (n + 1) → X) → V
  | 0, F, x => F (Fin.cons (a (x 0)) fun j => b (x j))
  | n + 1, F, x => F (Fin.cons (a (x 0)) fun j => b (x j)) -
      prismOp a b n (fun y => F (Fin.cons (a (x 0)) y)) (Fin.tail x)

theorem prismOp_zero (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F (Fin.cons (a (x 0)) fun j => b (x j)) := rfl

theorem prismOp_succ (a b : X → Y) (n : ℕ) (F : (Fin (n + 3) → Y) → V) (x : Fin (n + 2) → X) :
    prismOp a b (n + 1) F x = F (Fin.cons (a (x 0)) fun j => b (x j)) -
      prismOp a b n (fun y => F (Fin.cons (a (x 0)) y)) (Fin.tail x) := rfl

theorem prismOp_sub (a b : X → Y) (n : ℕ) : ∀ (F G : (Fin (n + 2) → Y) → V) (x : Fin (n + 1) → X),
    prismOp a b n (fun y => F y - G y) x = prismOp a b n F x - prismOp a b n G x := by
  induction n with
  | zero => intro F G x; rfl
  | succ n ih =>
    intro F G x
    rw [prismOp_succ, prismOp_succ, prismOp_succ, ih]
    abel

theorem prismOp_zero_fun (a b : X → Y) (n : ℕ) : ∀ (x : Fin (n + 1) → X),
    prismOp a b n (fun _ => (0 : V)) x = 0 := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [prismOp_succ, ih, sub_zero]

theorem cons_map (b : X → Y) {n : ℕ} (x0 : X) (y : Fin n → X) :
    (fun j => b (Fin.cons (α := fun _ => X) x0 y j)) = Fin.cons (b x0) fun j => b (y j) := by
  funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem map_eq_cons (b : X → Y) {n : ℕ} (x : Fin (n + 1) → X) :
    (fun j => b (x j)) = Fin.cons (b (x 0)) fun j => b (Fin.tail x j) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  exact cons_map b _ _

theorem prismOp_hd_zero (a b : X → Y) (F : (Fin 1 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 (hd 0 F) x = F (fun i => b (x i)) - F (fun i => a (x i)) := by
  rw [prismOp_zero, hd_zero', Fin.tail_cons, Fin.cons_zero]
  congr 2; funext i; rw [Subsingleton.elim i 0]

end Comb

section Key

variable {V X Y : Type u} [AddCommGroup V]

theorem hd_zero_eval (G : (Fin 1 → X) → V) (x : Fin 2 → X) : hd 0 G x = G ![x 1] - G ![x 0] := by
  rw [hd_zero']
  congr 2 <;> funext j <;> fin_cases j <;> rfl

theorem hd_one_eval (F : (Fin 2 → X) → V) (z : Fin 3 → X) :
    hd 1 F z = F ![z 1, z 2] - F ![z 0, z 2] + F ![z 0, z 1] := by
  unfold hd
  rw [Fin.sum_univ_three]
  have e0 : (fun j => z (Fin.succAbove (0 : Fin 3) j)) = ![z 1, z 2] := by funext j; fin_cases j <;> rfl
  have e1 : (fun j => z (Fin.succAbove (1 : Fin 3) j)) = ![z 0, z 2] := by funext j; fin_cases j <;> rfl
  have e2 : (fun j => z (Fin.succAbove (2 : Fin 3) j)) = ![z 0, z 1] := by funext j; fin_cases j <;> rfl
  rw [e0, e1, e2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul]
  norm_num
  abel

theorem prismOp_zero_eval (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F ![a (x 0), b (x 0)] := by
  rw [prismOp_zero]; congr 1; funext j; fin_cases j <;> rfl

theorem prismOp_one_eval (a b : X → Y) (K : (Fin 3 → Y) → V) (x : Fin 2 → X) :
    prismOp a b 1 K x = K ![a (x 0), b (x 0), b (x 1)] - K ![a (x 0), a (x 1), b (x 1)] := by
  rw [prismOp_succ, prismOp_zero]
  congr 2 <;> funext j <;> fin_cases j <;> rfl

theorem prismOp_key (a b : X → Y) (n : ℕ) : ∀ (F : (Fin (n + 2) → Y) → V) (x : Fin (n + 2) → X),
    hd n (prismOp a b n F) x + prismOp a b (n + 1) (hd (n + 1) F) x =
      F (fun i => b (x i)) - F (fun i => a (x i)) := by
  induction n with
  | zero =>
    intro F x
    rw [hd_zero_eval, prismOp_zero_eval, prismOp_zero_eval, prismOp_one_eval, hd_one_eval, hd_one_eval]
    have eb : (fun i => b (x i)) = ![b (x 0), b (x 1)] := by funext j; fin_cases j <;> rfl
    have ea : (fun i => a (x i)) = ![a (x 0), a (x 1)] := by funext j; fin_cases j <;> rfl
    rw [eb, ea]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    abel
  | succ k ih =>
    intro F x
    let G : (Fin (k + 2) → Y) → V := fun z => F (Fin.cons (a (x 0)) z)
    have sA : hd (k + 1) (prismOp a b (k + 1) F) x = prismOp a b (k + 1) F (Fin.tail x) -
        hd k (fun y => prismOp a b (k + 1) F (Fin.cons (x 0) y)) (Fin.tail x) := hd_succ' _ _ _
    have sBC : hd k (fun y => prismOp a b (k + 1) F (Fin.cons (x 0) y)) (Fin.tail x) =
        hd k (fun z => G (Fin.cons (b (x 0)) z)) (fun j => b (Fin.tail x j)) -
          hd k (prismOp a b k G) (Fin.tail x) := by
      rw [← hd_comp' k (fun z => G (Fin.cons (b (x 0)) z)) b (Fin.tail x), ← hd_sub']
      congr 1; funext y
      rw [prismOp_succ, Fin.cons_zero, Fin.tail_cons, cons_map]
    have sE : prismOp a b (k + 2) (hd (k + 2) F) x = hd (k + 2) F (Fin.cons (a (x 0)) fun j => b (x j)) -
        prismOp a b (k + 1) (fun z => hd (k + 2) F (Fin.cons (a (x 0)) z)) (Fin.tail x) :=
      prismOp_succ _ _ _ _ _
    have hbx : (fun j => b (x j)) = Fin.cons (b (x 0)) fun j => b (Fin.tail x j) := map_eq_cons b x
    have sF1 : hd (k + 2) F (Fin.cons (a (x 0)) fun j => b (x j)) =
        F (fun j => b (x j)) - hd (k + 1) G (fun j => b (x j)) := by
      rw [hd_succ', Fin.cons_zero, Fin.tail_cons]
    have sF2 : hd (k + 1) G (fun j => b (x j)) = G (fun j => b (Fin.tail x j)) -
        hd k (fun z => G (Fin.cons (b (x 0)) z)) (fun j => b (Fin.tail x j)) := by
      rw [hbx, hd_succ', Fin.cons_zero, Fin.tail_cons]
    have sG : (fun z => hd (k + 2) F (Fin.cons (a (x 0)) z)) = fun z => F z - hd (k + 1) G z := by
      funext z; rw [hd_succ', Fin.cons_zero, Fin.tail_cons]
    have hax : F (fun i => a (x i)) = G (fun i => a (Fin.tail x i)) := by
      show F _ = F _; rw [map_eq_cons a x]
    have e : G (fun i => a (Fin.tail x i)) = G (fun i => b (Fin.tail x i)) -
        (hd k (prismOp a b k G) (Fin.tail x) + prismOp a b (k + 1) (hd (k + 1) G) (Fin.tail x)) := by
      rw [ih G (Fin.tail x)]; abel
    rw [sA, sBC, sE, sF1, sF2, sG, prismOp_sub, hax, e]
    abel

end Key

section Top

variable {V X Y : Type u} [AddCommGroup V]

theorem cont_cons' {S Y : Type*} [TopologicalSpace S] [TopologicalSpace Y] {m : ℕ} (f : S → Y)
    (g : S → Fin m → Y) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun s => (Fin.cons (f s) (g s) : Fin (m + 1) → Y) := hf.finCons hg

theorem prismOp_cont [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (a b : X → Y) (ha : Continuous a) (hb : Continuous b) (n : ℕ) :
    ∀ {S : Type u} [TopologicalSpace S] (Φ : S → (Fin (n + 2) → Y) → V),
      Continuous (fun p : S × (Fin (n + 2) → Y) => Φ p.1 p.2) →
      ∀ v : S → Fin (n + 1) → X, Continuous v → Continuous fun s => prismOp a b n (Φ s) (v s) := by
  induction n with
  | zero =>
    intro S _ Φ hΦ v hv
    simp only [prismOp_zero]
    refine hΦ.comp (continuous_id.prodMk ?_)
    exact cont_cons' _ (fun s j => b (v s j)) (ha.comp ((continuous_apply 0).comp hv))
      (continuous_pi fun j => hb.comp ((continuous_apply j).comp hv))
  | succ k ih =>
    intro S _ Φ hΦ v hv
    simp only [prismOp_succ]
    refine Continuous.sub ?_ ?_
    · refine hΦ.comp (continuous_id.prodMk ?_)
      exact cont_cons' _ (fun s j => b (v s j)) (ha.comp ((continuous_apply 0).comp hv))
        (continuous_pi fun j => hb.comp ((continuous_apply j).comp hv))
    · refine ih (fun s y => Φ s (Fin.cons (a (v s 0)) y)) ?_ (fun s => Fin.tail (v s))
        (continuous_pi fun j => (continuous_apply _).comp hv)
      refine hΦ.comp (continuous_fst.prodMk ?_)
      exact cont_cons' (fun p : S × (Fin (k + 2) → Y) => a (v p.1 0)) (fun p => p.2)
        (ha.comp ((continuous_apply 0).comp (hv.comp continuous_fst))) continuous_snd

theorem prismOp_equiv {G : Type u} [SMul G X] [SMul G Y] (a b : X → Y)
    (ha : ∀ (g : G) x, a (g • x) = g • a x) (hb : ∀ (g : G) x, b (g • x) = g • b x)
    (g : G) (ρ : V →+ V) (n : ℕ) : ∀ (F F' : (Fin (n + 2) → Y) → V),
      (∀ y, F (fun i => g • y i) = ρ (F' y)) →
      ∀ x, prismOp a b n F (fun i => g • x i) = ρ (prismOp a b n F' x) := by
  have hc : ∀ {m : ℕ} (y0 : Y) (y : Fin m → Y),
      (Fin.cons (g • y0) fun j => g • y j : Fin (m + 1) → Y) = fun i => g • (Fin.cons y0 y : Fin (m + 1) → Y) i := by
    intro m y0 y; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  induction n with
  | zero =>
    intro F F' hF x
    simp only [prismOp_zero, ha, hb]
    rw [hc, hF]
  | succ k ih =>
    intro F F' hF x
    rw [prismOp_succ, prismOp_succ, map_sub]
    congr 1
    · simp only [ha, hb]; rw [hc, hF]
    · refine ih _ _ (fun y => ?_) (Fin.tail x)
      simp only [ha]; rw [hc, hF]

end Top

section Main

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def pullH (M : TRep R G) {X Y : Type u} [TopologicalSpace X] [MulAction G X]
    [TopologicalSpace Y] [MulAction G Y] (a : X → Y) (ha : Continuous a)
    (hga : ∀ (g : G) x, a (g • x) = g • a x) (n : ℕ) : hcoch M Y n →ₗ[R] hcoch M X n where
  toFun F := ⟨fun x => F.1 fun i => a (x i), F.2.1.comp (continuous_pi fun i => ha.comp (continuous_apply i)),
    fun g x => by simp only [hga]; exact F.2.2 g _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Main

open Cx in
theorem prism_holds : PrismStatement.{u} := by
  intro R _ G _ _ _ M X Y _ _ _ _ A B eA eB hA hB
  refine ⟨fun a ha hga => ?_, fun a b φ ψ ha hb hga hgb hφ hψ n => ?_⟩
  · refine ⟨⟨fun n => (eA n).symm.toLinearMap ∘ₗ pullH M a ha hga n ∘ₗ (eB n).toLinearMap, ?_⟩, ?_⟩
    · intro n F
      apply (eA (n + 1)).injective
      apply Subtype.ext
      funext x
      show (eA (n + 1) ((eA (n + 1)).symm (pullH M a ha hga (n + 1) (eB (n + 1) (B.d n F))))).1 x =
        (eA (n + 1) (A.d n ((eA n).symm (pullH M a ha hga n (eB n F))))).1 x
      rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
      show (eB (n + 1) (B.d n F)).1 (fun i => a (x i)) = hd n (fun y => (eB n F).1 fun i => a (y i)) x
      rw [hB]; rfl
    · intro n F x
      show (eA n ((eA n).symm (pullH M a ha hga n (eB n F)))).1 x = _
      rw [LinearEquiv.apply_symm_apply]; rfl
  · apply Submodule.linearMap_qext
    apply LinearMap.ext
    rintro ⟨F, hF⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Hom.H, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    show φ.f n F - ψ.f n F ∈ A.B n
    have hF0 : B.d n F = 0 := hF
    have hF' : hd n (eB n F).1 = 0 := by
      have h1 := hB n F
      rw [hF0, map_zero] at h1
      exact h1.symm
    cases n with
    | zero =>
      have h : φ.f 0 F = ψ.f 0 F := by
        apply (eA 0).injective; apply Subtype.ext; funext x
        rw [hφ, hψ]
        have h2 := prismOp_hd_zero a b (eB 0 F).1 x
        rw [hF'] at h2
        have h0 : prismOp a b 0 (0 : (Fin 2 → Y) → M.V) x = 0 := rfl
        exact (sub_eq_zero.mp (h2.symm.trans h0)).symm
      rw [h, sub_self]; exact Submodule.zero_mem _
    | succ n =>
      let F' := (eB (n + 1) F).1
      have hc : Continuous F' := (eB (n + 1) F).2.1
      let H : hcoch M X n := ⟨prismOp a b n F',
        prismOp_cont a b ha hb n (fun _ => F') (hc.comp continuous_snd) id continuous_id,
        fun g x => prismOp_equiv a b hga hgb g (M.rho g).toAddMonoidHom n F' F'
          (fun y => (eB (n + 1) F).2.2 g y) x⟩
      have hdH : A.d n ((eA n).symm H) = ψ.f (n + 1) F - φ.f (n + 1) F := by
        apply (eA (n + 1)).injective; apply Subtype.ext; funext x
        rw [hA, LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, Pi.sub_apply, hφ, hψ]
        have h2 := prismOp_key a b n F' x
        have h0 : prismOp a b (n + 1) (0 : (Fin (n + 3) → Y) → M.V) x = 0 := prismOp_zero_fun a b (n + 1) x
        rw [hF', h0, add_zero] at h2
        exact h2
      show φ.f (n + 1) F - ψ.f (n + 1) F ∈ LinearMap.range (A.d n)
      exact ⟨-(eA n).symm H, by rw [map_neg, hdH, neg_sub]⟩

end ReciprocityTheory.Coh
