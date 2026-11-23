import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}

theorem coe_diagPow (l : Fin N → ℤ) :
    ((Zls.diagPow k N l : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ l i : kˣ) : k) := by
  ext i j
  simp [Zls.diagPow, Matrix.diagonal_apply]

theorem diagPow_add (l l' : Fin N → ℤ) :
    Zls.diagPow k N (l + l') = Zls.diagPow k N l * Zls.diagPow k N l' := by
  apply Units.ext
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem diagPow_zero : Zls.diagPow k N 0 = 1 := by
  apply Units.ext
  rw [coe_diagPow]
  simp

theorem diagPow_neg (l : Fin N → ℤ) : Zls.diagPow k N (-l) = (Zls.diagPow k N l)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diagPow_add, neg_add_cancel, diagPow_zero]

theorem diagPow_pow (l : Fin N → ℤ) (j : ℕ) :
    Zls.diagPow k N l ^ j = Zls.diagPow k N ((j : ℤ) • l) := by
  induction j with
  | zero => simp [diagPow_zero]
  | succ j ih =>
    rw [pow_succ, ih, ← diagPow_add]
    congr 1
    funext i
    simp
    ring

theorem conj_apply (l : Fin N → ℤ) (y : GL (Fin N) k) (i j : Fin N) :
    ((Zls.diagPow k N l * y * (Zls.diagPow k N l)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      ((Zls.unifU k ^ (l i - l j) : kˣ) : k) * (y : Matrix (Fin N) (Fin N) k) i j := by
  rw [← diagPow_neg, Units.val_mul, Units.val_mul, coe_diagPow, coe_diagPow, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.neg_apply, sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
  ring

def contractMat (l : Fin N → ℤ) (s : k) (m : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun i j => if l j < l i then s ^ (l i - l j).toNat * m i j else (1 : Matrix (Fin N) (Fin N) k) i j

theorem continuous_contractMat (l : Fin N → ℤ) {X : Type} [TopologicalSpace X] {f : X → k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => contractMat l (f x) (g x) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : l j < l i
  · simp only [contractMat, Matrix.of_apply, h, if_true]
    exact (hf.pow _).mul (hg.matrix_elem i j)
  · simp only [contractMat, Matrix.of_apply, h, if_false]
    exact continuous_const

theorem contractMat_zero (l : Fin N → ℤ) (m : Matrix (Fin N) (Fin N) k) : contractMat l 0 m = 1 := by
  ext i j
  by_cases h : l j < l i
  · have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ h
    have he : (l i - l j).toNat ≠ 0 := by omega
    simp [contractMat, h, hij, he]
  · simp [contractMat, h]

theorem val_conj_eq (l : Fin N → ℤ) (c : ℕ) (y : GL (Fin N) k)
    (hy : ∀ i j, l i ≤ l j → (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) :
    ((Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) =
      contractMat l (((Zls.unifU k : kˣ) : k) ^ c) (y : Matrix (Fin N) (Fin N) k) := by
  ext i j
  rw [conj_apply]
  by_cases h : l j < l i
  · simp only [contractMat, Matrix.of_apply, h, if_true]
    congr 1
    have he : ((l i - l j).toNat : ℤ) = l i - l j := Int.toNat_of_nonneg (by omega)
    have : ((c : ℤ) • l) i - ((c : ℤ) • l) j = ((c * (l i - l j).toNat : ℕ) : ℤ) := by
      push_cast
      rw [he]
      simp
      ring
    rw [this, zpow_natCast, Units.val_pow_eq_pow_val, pow_mul]
  · have h' : l i ≤ l j := not_lt.1 h
    simp only [contractMat, Matrix.of_apply, h, if_false]
    rw [hy i j h']
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

theorem exists_contract (l : Fin N → ℤ) (J : Subgroup (GL (Fin N) k))
    (hJ : IsCompact (J : Set (GL (Fin N) k))) (S : Subgroup (GL (Fin N) k))
    (hS : ∀ y ∈ S, ∀ i j, l i ≤ l j →
      (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j)
    (U : Set (GL (Fin N) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ y ∈ J, y ∈ S →
      Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ ∈ U := by
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hU
  let Φ : k × GL (Fin N) k → Matrix (Fin N) (Fin N) k × (Matrix (Fin N) (Fin N) k)ᵐᵒᵖ := fun p =>
    (contractMat l p.1 (p.2 : Matrix (Fin N) (Fin N) k),
      MulOpposite.op (contractMat l p.1 ((p.2⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)))
  have hΦ : Continuous Φ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_)
    · exact continuous_contractMat l continuous_fst (Units.continuous_val.comp continuous_snd)
    · exact continuous_contractMat l continuous_fst
        (Units.continuous_val.comp (continuous_inv.comp continuous_snd))
  have hsub : ({0} : Set k) ×ˢ (J : Set (GL (Fin N) k)) ⊆ Φ ⁻¹' W := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    obtain rfl : s = 0 := hs
    have : Φ (0, y) = Units.embedProduct _ (1 : GL (Fin N) k) := by
      rw [map_one]
      show (contractMat l 0 _, MulOpposite.op (contractMat l 0 _)) = 1
      rw [contractMat_zero, contractMat_zero]
      rfl
    show Φ (0, y) ∈ W
    rw [this]
    exact h1
  obtain ⟨u, v, hu, -, h0u, hJv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hJ (hWo.preimage hΦ) hsub
  have hev := (GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow k).eventually (hu.mem_nhds (h0u rfl))
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨c₀, fun c hc y hyJ hyS => ?_⟩
  have hin : Φ (((Zls.unifU k : kˣ) : k) ^ c, y) ∈ W := huv ⟨hc₀ c hc, hJv hyJ⟩
  have hinv : (Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹)⁻¹ =
      Zls.diagPow k N ((c : ℤ) • l) * y⁻¹ * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ := by
    group
  show Units.embedProduct _ _ ∈ W
  have : Units.embedProduct _ (Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹) =
      Φ (((Zls.unifU k : kˣ) : k) ^ c, y) := by
    simp only [Units.embedProduct_apply, Φ]
    rw [hinv, val_conj_eq l c y (hS y hyS), val_conj_eq l c y⁻¹ (hS _ (inv_mem hyS))]
  rw [this]
  exact hin

variable {h : ℕ}

def zLevi (d : Fin h → ℕ) (w : Fin h → ℤ) : Levi k (Bl d) :=
  fun b => Matrix.GeneralLinearGroup.scalar (Fin (d b)) (Zls.unifU k ^ w b)

theorem coe_zLevi (d : Fin h → ℕ) (w : Fin h → ℤ) (b : Fin h) :
    ((zLevi d w b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) =
      Matrix.scalar (Fin (d b)) ((Zls.unifU k ^ w b : kˣ) : k) := rfl

theorem zLevi_comm (d : Fin h → ℕ) (w : Fin h → ℤ) (x : Levi k (Bl d)) :
    zLevi d w * x = x * zLevi d w := by
  funext b
  apply Units.ext
  show ((zLevi d w b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) * (x b : GL (Fin (d b)) k) =
    ((x b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) * (zLevi d w b : GL (Fin (d b)) k)
  rw [coe_zLevi]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _

theorem stdBlocks_ne (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (i : Fin (d a)) (j : Fin (d b))
    (hab : (⟨a, i⟩ : Σ a, Fin (d a)) ≠ ⟨b, j⟩) : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, j⟩ :=
  fun e => hab ((stdBlocks d hd).injective e)

theorem leviEmb_zLevi (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Fin h → ℤ) :
    leviEmb k (stdBlocks d hd) (zLevi d w) =
      Zls.diagPow k N (fun i => w (blk (stdBlocks d hd) i)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [coe_diagPow]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [coe_zLevi, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, blk_apply]
    · have hne := stdBlocks_ne d hd i j (fun e => hij (by simpa using e))
      rw [Matrix.diagonal_apply_ne _ hne, coe_zLevi, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  · have hne := stdBlocks_ne d hd i j (fun e => hab (congrArg Sigma.fst e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]

def lam (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Fin N → ℤ :=
  fun i => -(((blk (stdBlocks d hd) i : Fin h) : ℕ) : ℤ)

theorem one_block (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (i j : Fin (d a)) :
    (1 : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
      (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.one_apply_ne hij,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hij (by simpa using e)))]

theorem unip_entries (d : Fin h → ℕ) (hd : ∑ a, d a = N) (y : GL (Fin N) k)
    (hy : y ∈ unipRad k (stdBlocks d hd)) (i j : Fin N) (hl : lam d hd i ≤ lam d hd j) :
    (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : b ≤ a := by
    simp only [lam, blk_apply, neg_le_neg_iff, Nat.cast_le] at hl
    exact hl
  obtain ⟨hp, hdg⟩ := mem_unipRad.1 hy
  rcases hab.eq_or_lt with rfl | hlt
  · rw [hdg, one_block]
  · rw [mem_parab_iff.1 hp a b i j hlt,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hlt.ne' (congrArg Sigma.fst e)))]

theorem unipLower_entries (d : Fin h → ℕ) (hd : ∑ a, d a = N) (y : GL (Fin N) k)
    (hy : y ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) (hl : (-lam d hd) i ≤ (-lam d hd) j) :
    (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≤ b := by
    simp only [lam, Pi.neg_apply, blk_apply, neg_neg, Nat.cast_le] at hl
    exact hl
  obtain ⟨hp, hdg⟩ := (mem_unipRadLower k).1 hy
  rcases hab.eq_or_lt with rfl | hlt
  · rw [hdg, one_block]
  · rw [(mem_parabLower_iff k).1 hp a b i j hlt,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hlt.ne (congrArg Sigma.fst e)))]

theorem exists_central_strictlyDominant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∃ a : Levi k (Bl d), (∀ x : Levi k (Bl d), a * x = x * a) ∧ IsStrictlyDominant k N J d hd a ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ j : ℕ, ∀ y ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ * y * leviEmb k (stdBlocks d hd) a ^ j ∈ U := by
  intro k _ _ _ _ N h d hd J hJo hJc _ _
  have hc := fun (l : Fin N → ℤ) S hS U hU h1 => exists_contract (k := k) l J hJc S hS U hU h1
  obtain ⟨c₁, hc₁⟩ := hc (lam d hd) (unipRad k (stdBlocks d hd)) (unip_entries d hd) J hJo J.one_mem
  obtain ⟨c₂, hc₂⟩ := hc (-lam d hd) (unipRadLower k (stdBlocks d hd)) (unipLower_entries d hd) J hJo
    J.one_mem
  obtain ⟨c, hc1, hcc₁, hcc₂⟩ : ∃ c : ℕ, 1 ≤ c ∧ c₁ ≤ c ∧ c₂ ≤ c :=
    ⟨max c₁ c₂ + 1, by omega, by omega, by omega⟩
  let a : Levi k (Bl d) := zLevi d ((c : ℤ) • fun b : Fin h => -((b : ℕ) : ℤ))
  have hemb : leviEmb k (stdBlocks d hd) a = Zls.diagPow k N ((c : ℤ) • lam d hd) :=
    leviEmb_zLevi d hd _
  have hpow : ∀ j : ℕ, leviEmb k (stdBlocks d hd) a ^ j =
      Zls.diagPow k N (((j * c : ℕ) : ℤ) • lam d hd) := by
    intro j
    rw [hemb, diagPow_pow, smul_smul]
    push_cast
    rfl
  have hinv : ∀ j : ℕ, Zls.diagPow k N (((j * c : ℕ) : ℤ) • (-lam d hd)) =
      (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ := by
    intro j
    rw [smul_neg, diagPow_neg, hpow]
  have hemb' : Zls.diagPow k N ((c : ℤ) • (-lam d hd)) = (leviEmb k (stdBlocks d hd) a)⁻¹ := by
    rw [smul_neg, diagPow_neg, hemb]
  have hcent : ∀ x : Levi k (Bl d), a * x = x * a := zLevi_comm d _
  refine ⟨a, hcent, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro n hn
    refine ⟨?_, ?_⟩
    · rw [hemb]
      exact hc₁ c hcc₁ n hn.1 hn.2
    · exact (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k _ a) n).1 hn.2
  · intro n hn
    refine ⟨?_, ?_⟩
    · have := hc₂ c hcc₂ n hn.1 hn.2
      rwa [hemb', inv_inv] at this
    · have := (Subgroup.mem_normalizer_iff.1
        (inv_mem (leviEmb_mem_normalizer_lower k (stdBlocks d hd) a)) n).1 hn.2
      rwa [inv_inv] at this
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hcent x, mul_inv_cancel_right]
      exact hx
    · rw [mul_assoc, ← hcent x, inv_mul_cancel_left]
      exact hx
  · intro U hU h1
    obtain ⟨c₃, hc₃⟩ := hc (lam d hd) (unipRad k (stdBlocks d hd)) (unip_entries d hd) U hU h1
    refine ⟨c₃, fun n hn => ?_⟩
    rw [hpow]
    exact hc₃ _ (Nat.le_mul_of_pos_right _ hc1) n hn.1 hn.2
  · intro U hU h1
    obtain ⟨c₃, hc₃⟩ := hc (-lam d hd) (unipRadLower k (stdBlocks d hd)) (unipLower_entries d hd) U hU h1
    refine ⟨c₃, fun y hy => ?_⟩
    have := hc₃ _ (Nat.le_mul_of_pos_right _ hc1) y hy.1 hy.2
    rwa [hinv, inv_inv] at this

end GlobalTheory.CompanionTheory.CentralDom
