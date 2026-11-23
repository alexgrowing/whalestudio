import ReciprocityTheory.DualLattices.MatEquivApply
import ReciprocityTheory.DualLattices.CokernelLengthComparisonOf
import ReciprocityTheory.DualLattices.StdJForm

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

lemma idem_free {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (P : Matrix (Fin g) (Fin g) R)
    (hP : P * P = P) : ∃ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R)) := by
  classical
  set f := Matrix.mulVecLin P with hf
  have hff : ∀ x, f (f x) = f x := by
    intro x
    simp only [hf, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  have hsplit : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    apply Subtype.ext
    first
    | exact hff y
    | simp [hff]
  haveI : Module.Projective R (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict hsplit
  haveI : Module.Free R (LinearMap.range f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_flat_of_localRing
    | infer_instance
  exact ⟨Module.finrank R (LinearMap.range f), ⟨(Module.finBasis R (LinearMap.range f)).equivFun⟩⟩

lemma hasLen_subsingleton {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (M : Type) [AddCommGroup M] [Module R M] [Subsingleton M] : HasLen v R M 1 := by
  unfold HasLen
  refine ⟨0, fun i => i.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, ?_⟩
  simp

section Inv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O}

def pi2 {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i)) :
    Equiv.Perm (Fin m) := by
  classical
  exact Equiv.ofBijective (fun k => if e k = 0 then k else π k) (by
    apply Finite.injective_iff_bijective.1
    intro a b hab
    simp only at hab
    by_cases ha : e a = 0 <;> by_cases hb : e b = 0
    · simpa [ha, hb] using hab
    · rw [if_pos ha, if_neg hb] at hab
      exfalso; apply hb
      have h := hσ b
      rw [← hab, ha] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_pos hb] at hab
      exfalso; apply ha
      have h := hσ a
      rw [hab, hb] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_neg hb] at hab
      exact π.injective hab)

lemma involutionPerm_apply {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) (hk : e k ≠ 0) : pi2 e π hσ k = π k := by
  unfold pi2
  simp [hk]

lemma involutionPerm_apply_zero {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) (hk : e k = 0) : pi2 e π hσ k = k := by
  unfold pi2
  simp [hk]

lemma involutionPerm_sigma {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) : σ (e k) = e (pi2 e π hσ k) := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, hk, map_zero]
  · rw [involutionPerm_apply e π hσ k hk]
    exact hσ k

lemma involutionPerm_involutive {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hinv : ∀ a, σ (σ a) = a) (k : Fin m) :
    pi2 e π hσ (pi2 e π hσ k) = k := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, involutionPerm_apply_zero e π hσ k hk]
  · have h1 : e (π k) ≠ 0 := by
      intro h0
      apply hk
      have h := hσ k
      rw [h0] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    rw [involutionPerm_apply e π hσ k hk, involutionPerm_apply e π hσ (π k) h1]
    by_contra hne
    have h2 : e (π (π k)) = e k := by
      rw [← hσ, ← hσ, hinv]
    have h3 := horth (π (π k)) k
    rw [if_neg hne, h2, horth k k, if_pos rfl] at h3
    exact hk h3

end Inv

theorem wdetLen : WdetLenStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw cw cwb hcw hcwb
  haveI := htd_domain hS
  haveI := isLocal_of_integers hS.integers
  by_cases hw0 : e w = 0
  · have he' : e (π w) = 0 := by
      have h := hσ w; rw [hw0, map_zero] at h; exact h.symm
    have hsubL : ∀ a : O, a = 0 → Subsingleton (LinearMap.range (Matrix.mulVecLin (H.ρL a))) := by
      rintro a rfl
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨x', hx⟩ := x.2; obtain ⟨y', hy⟩ := y.2
      rw [← hx, ← hy]; simp
    have hsubD : ∀ a : O, a = 0 → Subsingleton (lieDPart H a) := by
      rintro a rfl
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨x', hx⟩ := x.2; obtain ⟨y', hy⟩ := y.2
      rw [← hx, ← hy]; simp
    have hquot : ∀ {M : Type} [AddCommGroup M] [Module R M] [Subsingleton M] (N : Submodule R M),
        Subsingleton (M ⧸ N) := fun N => ⟨fun a b => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [Subsingleton.elim x y]⟩
    haveI := hsubL _ hw0
    haveI := hsubD _ hw0
    haveI := hsubD _ he'
    haveI : Subsingleton (qW H (e w) (e (π w))) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      funext k
      rcases k with k | k
      · have hx : ((x : Fin g ⊕ Fin g → R) ∘ Sum.inl) = 0 := by
          have := Subsingleton.elim (⟨_, x.2.1⟩ : lieDPart H (e (π w))) ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        have hy : ((y : Fin g ⊕ Fin g → R) ∘ Sum.inl) = 0 := by
          have := Subsingleton.elim (⟨_, y.2.1⟩ : lieDPart H (e (π w))) ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        exact (congrFun hx k).trans (congrFun hy k).symm
      · have hx : ((x : Fin g ⊕ Fin g → R) ∘ Sum.inr) = 0 := by
          have := Subsingleton.elim (⟨_, x.2.2⟩ : LinearMap.range (Matrix.mulVecLin (H.ρL (e w))))
            ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        have hy : ((y : Fin g ⊕ Fin g → R) ∘ Sum.inr) = 0 := by
          have := Subsingleton.elim (⟨_, y.2.2⟩ : LinearMap.range (Matrix.mulVecLin (H.ρL (e w))))
            ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        exact (congrFun hx k).trans (congrFun hy k).symm
    haveI : Subsingleton (htCoker H (e w) (e (π w))) := hquot _
    haveI : Subsingleton (htCoker H (e (π w)) (e w)) := hquot _
    haveI : Subsingleton (xMod H e π w) := hquot _
    have h1 : cw = 1 := hasLen_unique hS.integers hcw (hasLen_subsingleton v R _)
    have h2 : cwb = 1 := hasLen_unique hS.integers hcwb (hasLen_subsingleton v R _)
    exact ⟨0, 1, ⟨LinearEquiv.ofSubsingleton _ _⟩, hasLen_subsingleton v R _, by simp [h1, h2]⟩

  set ι := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hι
  have hpw : pi2 e π hσ w = π w := involutionPerm_apply e π hσ w hw0
  set π₂ := pi2 e π hσ
  set π' : Equiv.Perm (Fin (m + 1)) := Equiv.Perm.decomposeFin.symm (0, π₂) with hπ'
  have hπ'0 : π' 0 = 0 := by simp [hπ']
  have hπ's : ∀ k : Fin m, π' k.succ = (π₂ k).succ := by
    intro k; simp [hπ', Equiv.Perm.decomposeFin_symm_apply_succ]
  set εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R :=
    Fin.cons (ι H.P) (fun i => ι (H.ρ (e i))) with hεT
  set εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R :=
    Fin.cons H.PL (fun i => H.ρL (e i)) with hεL
  have hPcomm : ∀ i, H.P * H.ρ (e i) = 0 := fun i => by rw [H.projectors.2.2.2.1, hPT]
  have hPLcomm : ∀ i, H.PL * H.ρL (e i) = 0 := fun i => by rw [H.projectors.2.2.2.2, hPL]
  have hπinv : ∀ k, π' (π' k) = k := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [hπ'0, hπ'0]
    · rw [hπ's, hπ's, involutionPerm_involutive e π hσ horth hS.invol]
  have hTo : ∀ a b, εT a * εT b = if a = b then εT a else 0 := by
    intro a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp only [hεT, Fin.cons_zero, if_true, ← map_mul, H.projectors.1]
    · simp only [hεT, Fin.cons_zero, Fin.cons_succ, ← map_mul, hPcomm, map_zero,
        (Fin.succ_ne_zero j).symm, if_false]
    · simp only [hεT, Fin.cons_zero, Fin.cons_succ, ← map_mul, hPT, map_zero,
        Fin.succ_ne_zero i, if_false]
    · simp only [hεT, Fin.cons_succ, ← map_mul, ← map_mul H.ρ, horth, Fin.succ_inj]
      split_ifs <;> simp
  have hLo : ∀ a b, εL a * εL b = if a = b then εL a else 0 := by
    intro a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp only [hεL, Fin.cons_zero, if_true, H.projectors.2.1]
    · simp only [hεL, Fin.cons_zero, Fin.cons_succ, hPLcomm, (Fin.succ_ne_zero j).symm, if_false]
    · simp only [hεL, Fin.cons_zero, Fin.cons_succ, hPL, Fin.succ_ne_zero i, if_false]
    · simp only [hεL, Fin.cons_succ, ← map_mul, horth, Fin.succ_inj]
      split_ifs <;> simp
  have hTs : ∑ a, εT a = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [hεT, Fin.cons_zero, Fin.cons_succ]
    rw [← map_sum ι (fun i => H.ρ (e i)) Finset.univ, ← map_add, add_comm, hsT, map_one]
  have hLs : ∑ a, εL a = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [hεL, Fin.cons_zero, Fin.cons_succ]
    rw [add_comm, hsL]
  have hHt : ∀ a, H.Ht * εT a = (εL (π' a))ᵀ * H.Ht := by
    intro a
    refine Fin.cases ?_ (fun i => ?_) a
    · rw [hπ'0]; simp only [hεT, hεL, Fin.cons_zero]; exact H.Ht_equivariant.2
    · rw [hπ's]; simp only [hεT, hεL, Fin.cons_succ]
      rw [← involutionPerm_sigma e π hσ i]; exact H.Ht_equivariant.1 (e i)
  have hadj : ∀ a, (εT a)ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * εT (π' a) := by
    intro a
    refine Fin.cases ?_ (fun i => ?_) a
    · rw [hπ'0]; simp only [hεT, Fin.cons_zero, hι, RingHom.mapMatrix_apply]
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.projectors.2.2.1]
    · rw [hπ's]; simp only [hεT, Fin.cons_succ, hι, RingHom.mapMatrix_apply]
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant (e i),
        involutionPerm_sigma e π hσ i]
  obtain ⟨hua, hub, -⟩ := u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π'
    hπinv hTo hTs hLo hLs hHt hadj H.form_eq_alt
  have hbt : ∑ a, εL a * H.Bt * εT a = btP H e := by
    rw [Fin.sum_univ_succ]
    simp only [hεT, hεL, Fin.cons_zero, Fin.cons_succ, btP, hι, RingHom.mapMatrix_apply]
    rw [add_comm]
  rw [hbt] at hua hub
  have hidem : H.ρL (e w) * H.ρL (e w) = H.ρL (e w) := by rw [← map_mul, horth, if_pos rfl]
  obtain ⟨d, ⟨φ⟩⟩ := idem_free (H.ρL (e w)) hidem
  obtain ⟨hEt, -, hEdet⟩ := htd_E H
  have hcw' : HasLen v R (cokE H.Ht εT εL w.succ (π' w.succ)) cw := by
    rw [hπ's, hpw]; exact hcw
  have hcwb' : HasLen v R (cokE H.Ht εT εL (π' w.succ) w.succ) cwb := by
    rw [hπ's, hpw]; exact hcwb
  obtain ⟨X, hX, hXe⟩ := lenId C v R hS.integers g (m + 1) H.Ht (btP H e)
    (H.E.map (algebraMap ℤ_[p] R)) cp (htd_cp_ne hS) hEdet hua εT εL π' hπinv hTo hTs hLo hLs
    hHt hub hadj w.succ d ⟨φ⟩ cw cwb hcw' hcwb'
  refine ⟨d, X, ⟨φ⟩, ?_, hXe⟩
  have hX' : HasLen v R (qE εL w.succ (π' w.succ) ⧸
      ((LinearMap.range (Matrix.mulVecLin (εT w.succ))).map
        (Matrix.mulVecLin (fromRows H.Ht (btP H e)))).comap (qE εL w.succ (π' w.succ)).subtype) X := hX
  generalize hq : π' w.succ = q at hX'
  rw [hπ's, hpw] at hq
  subst hq
  exact hX'

end ReciprocityTheory.PGsh.Up
