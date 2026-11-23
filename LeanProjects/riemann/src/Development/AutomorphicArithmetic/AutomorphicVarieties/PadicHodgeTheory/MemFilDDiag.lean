import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemGKBot

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.R0

variable {l : ℕ} [Fact l.Prime]

section Map

variable {G A V V' : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V']

variable (l) in

def tm (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (f : V →ₗ[A] V') : V ⊗[ℚ_[l]] B →ₗ[A] V' ⊗[ℚ_[l]] B :=
  AlgebraTensorModule.map f LinearMap.id

theorem tm_tmul {B : Type} [AddCommGroup B] [Module ℚ_[l] B] (f : V →ₗ[A] V') (v : V) (b : B) :
    tm l B f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

variable (φ : G →* GQ l) {ρ : Representation A G V} {ρ' : Representation A G V'} (f : V →ₗ[A] V')

theorem tm_actC (g : G) (hf : ∀ x, f (ρ g x) = ρ' g (f x)) (y : V ⊗[ℚ_[l]] Bcr l) :
    tm l _ f (actC φ ρ g y) = actC φ ρ' g (tm l _ f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => exact congrArg (· ⊗ₜ _) (hf v)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tm_actD (g : G) (hf : ∀ x, f (ρ g x) = ρ' g (f x)) (y : V ⊗[ℚ_[l]] Bdr l) :
    tm l _ f (actD φ ρ g y) = actD φ ρ' g (tm l _ f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => exact congrArg (· ⊗ₜ _) (hf v)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tm_Dcr (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {y : V ⊗[ℚ_[l]] Bcr l} (hy : y ∈ Dcr φ ρ) :
    tm l _ f y ∈ Dcr φ ρ' :=
  (mem_Dcr _ _ _).2 fun g => by rw [← tm_actC φ f g (hf g), (mem_Dcr _ _ _).1 hy]

theorem tm_FilD (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {i : ℤ} {y : V ⊗[ℚ_[l]] Bdr l} (hy : y ∈ FilD φ ρ i) :
    tm l _ f y ∈ FilD φ ρ' i := by
  refine ⟨(mem_Ddr _ _ _).2 fun g => by rw [← tm_actD φ f g (hf g), (mem_Ddr _ _ _).1 hy.1], ?_⟩
  obtain ⟨z, rfl⟩ := hy.2
  refine ⟨tm l _ f z, ?_⟩
  clear hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tm_smulC (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 K)) (y : V ⊗[ℚ_[l]] Bcr l) :
    tm l _ f (smulC V K c y) = smulC V' K c (tm l _ f y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => exact congrArg (· ⊗ₜ _) (f.map_smul a v)
    | add x y hx hy => simp only [map_add, hx, hy]

theorem tm_smulD (K : FinExt l) (c : A ⊗[ℚ_[l]] ↥K.1) (y : V ⊗[ℚ_[l]] Bdr l) :
    tm l _ f (smulD V K c y) = smulD V' K c (tm l _ f y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => exact congrArg (· ⊗ₜ _) (f.map_smul a v)
    | add x y hx hy => simp only [map_add, hx, hy]

theorem smulC_one (K : FinExt l) (a : A) (y : V ⊗[ℚ_[l]] Bcr l) :
    smulC V K (a ⊗ₜ[ℚ_[l]] (1 : ↥(K0 K))) y = a • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v b => exact congrArg (_ ⊗ₜ ·) (one_smul ↥(K0 K) b)
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

end Map

section Diag

variable {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}

variable (l) in

abbrev pr (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (a : Fin n) :
    (Fin n → A) ⊗[ℚ_[l]] B →ₗ[A] A ⊗[ℚ_[l]] B := tm l B (LinearMap.proj a)

variable (l) in

abbrev inc (B : Type) [AddCommGroup B] [Module ℚ_[l] B] (a : Fin n) :
    A ⊗[ℚ_[l]] B →ₗ[A] (Fin n → A) ⊗[ℚ_[l]] B := tm l B (LinearMap.single A (fun _ => A) a)

variable {B : Type} [AddCommGroup B] [Module ℚ_[l] B]

theorem pr_inc (a b : Fin n) (x : A ⊗[ℚ_[l]] B) : pr l B a (inc l B b x) = if a = b then x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => by_cases h : a = b <;> simp [tm_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]; split_ifs <;> simp

theorem sum_inc_pr (y : (Fin n → A) ⊗[ℚ_[l]] B) : ∑ a, inc l B a (pr l B a y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tm_tmul, ← sum_tmul, Finset.univ_sum_single]
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

variable {ρ : G →* GL (Fin n) A} {κ : Fin n → G →* Aˣ}
  (hρ : ∀ g, (ρ g : Matrix (Fin n) (Fin n) A) = Matrix.diagonal fun a => (κ a g : A))

include hρ

theorem proj_diag (a : Fin n) (g : G) (x : Fin n → A) :
    (LinearMap.proj a : (Fin n → A) →ₗ[A] A) (colRep ρ g x) = chRep (κ a) g (LinearMap.proj (R := A) a x) := by
  simp [colRep, chRep, hρ, Matrix.mulVec_diagonal]

theorem single_diag (a : Fin n) (g : G) (x : A) :
    LinearMap.single A (fun _ => A) a (chRep (κ a) g x) = colRep ρ g (LinearMap.single A (fun _ => A) a x) := by
  ext b
  by_cases h : b = a <;> simp [colRep, chRep, hρ, Matrix.mulVec_diagonal, h]

theorem mem_FilD_diag (φ : G →* GQ l) (i : ℤ) (y : (Fin n → A) ⊗[ℚ_[l]] Bdr l) :
    y ∈ FilD φ (colRep ρ) i ↔ ∀ a, pr l _ a y ∈ FilD φ (chRep (κ a)) i := by
  refine ⟨fun h a => tm_FilD φ _ (proj_diag hρ a) h, fun h => ?_⟩
  rw [← sum_inc_pr y]
  exact Submodule.sum_mem _ fun a _ => tm_FilD φ _ (single_diag hρ a) (h a)

end Diag

section Types

variable {A : Type} [CommRing A] [Algebra ℚ_[l] A] {n : ℕ} {K : FinExt l}
  {ρ : ↥(GK K) →* GL (Fin n) A} {κ : Fin n → ↥(GK K) →* Aˣ}
  (hρ : ∀ g, (ρ g : Matrix (Fin n) (Fin n) A) = Matrix.diagonal fun a => (κ a g : A))

include hρ

theorem hodge_diag (w : Fin n → ℤ) (hw : Function.Injective w) (m : ℤ → ℕ)
    (hm1 : ∀ a, m (w a) = 1) (hm0 : ∀ i, (∀ a, w a ≠ i) → m i = 0)
    (hF : ∀ a i, (i ≤ w a → FilD (GK K).subtype (chRep (κ a)) i = Ddr (GK K).subtype (chRep (κ a))) ∧
      (w a < i → FilD (GK K).subtype (chRep (κ a)) i = ⊥))
    (hB : ∀ a, ∃ x ∈ Ddr (GK K).subtype (chRep (κ a)), ∀ y ∈ Ddr (GK K).subtype (chRep (κ a)),
      ∃! c : A ⊗[ℚ_[l]] ↥K.1, y = smulD A K c x) :
    HodgeType K (colRep ρ) m := by
  have step : ∀ a i, w a ≠ i → ∀ y ∈ FilD (GK K).subtype (chRep (κ a)) i,
      y ∈ FilD (GK K).subtype (chRep (κ a)) (i + 1) := by
    intro a i h y hy
    rcases lt_or_gt_of_ne h with h | h
    · rw [(hF a i).2 h, Submodule.mem_bot] at hy
      exact hy ▸ Submodule.zero_mem _
    · rw [(hF a _).1 (Int.add_one_le_of_lt h)]
      exact hy.1
  intro i
  by_cases h : ∃ a, w a = i
  · obtain ⟨a, rfl⟩ := h
    obtain ⟨x, hx, hb⟩ := hB a
    rw [hm1]
    refine ⟨fun _ => inc l _ a x, fun _ => tm_FilD _ _ (single_diag hρ a) (by rwa [(hF a _).1 le_rfl]),
      fun y hy => ?_⟩
    have hy' := (mem_FilD_diag hρ _ _ _).1 hy
    obtain ⟨c, hc, hcu⟩ := hb _ (hy' a).1
    refine ⟨fun _ => c, (mem_FilD_diag hρ _ _ _).2 fun b => ?_, fun c' hc' => ?_⟩
    · rw [Fin.sum_univ_one, map_sub, ← tm_smulD, pr_inc]
      split_ifs with hba
      · subst hba
        rw [← hc, sub_self]
        exact Submodule.zero_mem _
      · rw [sub_zero]
        exact step b _ (fun e => hba (hw e)) _ (hy' b)
    · have h1 := (mem_FilD_diag hρ _ _ _).1 hc' a
      rw [Fin.sum_univ_one, map_sub, ← tm_smulD, pr_inc, if_pos rfl, (hF a _).2 (lt_add_one _),
        Submodule.mem_bot, sub_eq_zero] at h1
      funext j
      rw [Subsingleton.elim j 0]
      exact hcu _ h1
  · push Not at h
    rw [hm0 i h]
    refine ⟨Fin.elim0, fun a => a.elim0, fun y hy => ⟨Fin.elim0, ?_, fun _ _ => Subsingleton.elim _ _⟩⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact (mem_FilD_diag hρ _ _ _).2 fun b => step b i (h b) _ ((mem_FilD_diag hρ _ _ _).1 hy b)

theorem crys_diag {L : FinExt l} (h : K.1 ≤ L.1) (hN : ((GK L).subgroupOf (GK K)).Normal)
    (hC : Crys L ((colRep ρ).comp (incl h))) (t : Fin n → ↥(GK K) → A) (x : Fin n → A ⊗[ℚ_[l]] Bcr l)
    (hx : ∀ a, x a ∈ Dcr (GK L).subtype (chRep ((κ a).comp (incl h))))
    (hB : ∀ a, ∀ y ∈ Dcr (GK L).subtype (chRep ((κ a).comp (incl h))),
      ∃! c : A ⊗[ℚ_[l]] ↥(K0 L), y = smulC A L c (x a))
    (ht : ∀ a γ, actC (GK K).subtype (chRep (κ a)) γ (x a) = t a γ • x a) :
    CrysTypeOver K L h (colRep ρ) n fun γ => ∑ a, t a γ := by
  have key : ∀ (c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L)) b,
      pr l _ b (∑ a, smulC (Fin n → A) L (c a) (inc l _ a (x a))) = smulC A L (c b) (x b) := by
    intro c b
    simp only [map_sum, ← tm_smulC, pr_inc, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨hN, hC, fun a => inc l _ a (x a), fun a => tm_Dcr _ _ (fun g => single_diag hρ a (incl h g)) (hx a),
    fun y hy => ?_, fun γ _ M hM => ?_⟩
  · choose c hc hcu using fun a => hB a _ (tm_Dcr _ _ (fun g => proj_diag hρ a (incl h g)) hy)
    refine ⟨c, ?_, fun c' hc' => funext fun b => hcu b _ ?_⟩
    · refine (sum_inc_pr y).symm.trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [← tm_smulC]
      exact congrArg _ (hc a)
    · exact (congrArg _ hc').trans (key c' b)
  · rw [sum_tmul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := congrArg (pr l _ b) (hM b)
    rw [key (fun a => M a b), tm_actC _ _ _ (proj_diag hρ b γ), pr_inc, if_pos rfl, ht] at h1
    exact (hB b _ (Submodule.smul_mem _ (t b γ) (hx b))).unique h1 (smulC_one L _ _).symm

end Types

end UpperTheory.V.Loc.R0
