import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_adjugate {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n k} (h : IntM A) : IntM A.adjugate := by
  let B : Matrix n n 𝒪[k] := fun i j => ⟨A i j, h i j⟩
  have hB : A = (algebraMap 𝒪[k] k).mapMatrix B := by ext i j; rfl
  intro i j
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2

theorem mem_KO_of_intM_det {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (h : IntM g.val) (hd : g.val.det = 1) :
    g ∈ KO k n := by
  refine mem_KO.2 ⟨h, ?_⟩
  have : (g⁻¹).val = g.val.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hd]; simp
  rw [this]; exact intM_adjugate h
end

section Frame
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def dg (ϖ : kˣ) : n ⊕ Fin c → k := Sum.elim (fun _ => 1) (fun i => (ϖ : k) ^ (i.val + 1))

theorem dg_ne_zero (ϖ : kˣ) (r : n ⊕ Fin c) : dg ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [dg]

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (dg ϖ) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, SplitFlip.diagGL, dg, diagonal, fromBlocks, Matrix.one_apply]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal fun r => (dg ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal]
  rw [← diagonal_one]; congr 1; funext r; exact mul_inv_cancel₀ (dg_ne_zero ϖ r)

theorem conj_entry [Fintype ι] [DecidableEq ι] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL ι k) (r s : n ⊕ Fin c) :
    ((typeFrame ϖ ord).conj g).val r s = dg ϖ r * g.val (ord.symm r) (ord.symm s) * (dg ϖ s)⁻¹ := by
  rw [LatFrame.conj_apply, Units.val_mul, Units.val_mul, typeFrame_bas_inv_val, typeFrame_bas_val,
    mul_diagonal, diagonal_mul, reGL_val]
  rfl
end Frame

section Zero
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]

def ordZ (hc : 0 + c = c) : Fin κ ⊕ Fin c ≃ XIx (Fin κ) t 0 ⊕ Fin c :=
  (ixZero (Fin κ ⊕ Fin c) t).trans (stdOrd (Fin κ) t 0 c hc)

theorem ordZ_inl (hc : 0 + c = c) (i : Fin κ) : ordZ t hc (Sum.inl i) = Sum.inl (Sum.inl (Sum.inl i)) := rfl

theorem ordZ_inr (hc : 0 + c = c) (i : Fin c) : ordZ (κ := κ) t hc (Sum.inr i) = Sum.inr i := by
  have h := standardOrderExtendedBasis_apply_low_block (Fin κ) t 0 c hc i
  simp only [Fin.eta] at h
  exact h

def epsZ : Fin κ ≃ XIx (Fin κ) t 0 :=
  (Equiv.sumEmpty (Fin κ) (Fin 0)).symm.trans (Equiv.sumEmpty (Fin κ ⊕ Fin 0) (Fin 0 × t)).symm

theorem lev_ordZ_symm (hc : 0 + c = c) (p : ℕ) (z : XIx (Fin κ) t 0 ⊕ Fin c) :
    lev p ((ordZ t hc).symm z) = lev p z := by
  obtain ⟨w, rfl⟩ := (ordZ t hc).surjective z
  rw [Equiv.symm_apply_apply]
  rcases w with i | i
  · rw [ordZ_inl]; rfl
  · rw [ordZ_inr]; rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_reGL_val (ϖ : kˣ) (hc : 0 + c = c) (g : GL (Fin κ ⊕ Fin c) k) (r s : XIx (Fin κ) t 0 ⊕ Fin c) :
    ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)).val r s =
      dg ϖ r * g.val ((ordZ t hc).symm r) ((ordZ t hc).symm s) * (dg ϖ s)⁻¹ := by
  rw [conj_entry, reGL_val]; rfl

theorem conj_inN (ϖ : kˣ) (hc : 0 + c = c) (p : ℕ) {g : GL (Fin κ ⊕ Fin c) k} (hg : InN p g) :
    InN p ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)) := by
  intro r s hrs
  rw [conj_reGL_val, hg _ _ (by rw [lev_ordZ_symm, lev_ordZ_symm]; exact hrs)]
  by_cases h : r = s
  · subst h; simp [Matrix.one_apply, mul_inv_cancel₀ (dg_ne_zero ϖ r)]
  · have h' : (ordZ t hc).symm r ≠ (ordZ t hc).symm s := fun e => h ((ordZ t hc).symm.injective e)
    simp [Matrix.one_apply, h, h']

theorem conj_embX (ϖ : kˣ) (hc : 0 + c = c) (γ : GL (Fin κ) k) :
    (typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) (embX c γ)) =
      embX c (reGL (epsZ t) γ) := by
  have hs1 : ∀ i : Fin κ, (ordZ t hc).symm (Sum.inl (Sum.inl (Sum.inl i))) = Sum.inl i := fun i =>
    (ordZ t hc).symm_apply_eq.2 (ordZ_inl t hc i).symm
  have hs2 : ∀ i : Fin c, (ordZ t hc).symm (Sum.inr i) = Sum.inr i := fun i =>
    (ordZ t hc).symm_apply_eq.2 (ordZ_inr (κ := κ) t hc i).symm
  ext r s
  rw [conj_reGL_val, Radical.embX_val, Radical.embX_val, reGL_val]
  rcases r with ((i | i) | ⟨i, _⟩) | i
  · rcases s with ((j | j) | ⟨j, _⟩) | j
    · rw [hs1, hs1]; simp [dg]; rfl
    · exact j.elim0
    · exact j.elim0
    · rw [hs1, hs2]; simp [dg]
  · exact i.elim0
  · exact i.elim0
  · rcases s with ((j | j) | ⟨j, _⟩) | j
    · rw [hs2, hs1]; simp [dg]
    · exact j.elim0
    · exact j.elim0
    · rw [hs2, hs2]
      by_cases h : i = j
      · subst h; simp [dg, Matrix.one_apply]
      · simp [dg, Matrix.one_apply, h]
end Zero

end GlobalTheory.SymDec

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem GlobalTheory.SymChain.SymData.exists_N_mul_embX_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (hc : 0 + (s + 1) = s + 1) (x : S.P.J), ∃ (a b : S.P.J) (γ : GL (GlobalTheory.StepData.XIx (Fin κ) t 0) k),
    (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (a : GL (Fin κ ⊕ Fin (s + 1)) k)) ∈
        GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧
    (GlobalTheory.StepData.typeFrame S.ϖ (GlobalTheory.StepData.stdOrd (Fin κ) t 0 (s + 1) hc)).conj
      (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin κ ⊕ Fin (s + 1)) t) (b : GL (Fin κ ⊕ Fin (s + 1)) k)) =
        GlobalTheory.RootEx.embX (s + 1) γ ∧
    GlobalTheory.StepData.MaxM (((a * b : S.P.J) : GL (Fin κ ⊕ Fin (s + 1)) k).val - (x : GL (Fin κ ⊕ Fin (s + 1)) k).val) := by
  classical
  intro k _ _ _ _ s κ S t _ _ hc x
  have hx := (SymData.mem_J_iff_pattern k s κ S x).1 x.2
  let M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k := fun a b =>
    if FreeTop S.ρ a b then (x : GL _ k).val a b else (1 : Matrix _ _ k) a b
  have hM : MaxM (M - (x : GL _ k).val) := by
    intro a b
    rw [Matrix.sub_apply]
    simp only [M]
    split_ifs with h
    · simp
    · rw [← neg_sub, Valuation.map_neg]; exact hx.2 a b h
  obtain ⟨x', hx'J, hx'M⟩ := S.P.exists_of_congr x.2 hM
  obtain ⟨u, hu, γ₀, hγ₀, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ x' (fun a b hab => by
    rw [hx'M]; simp [M, hab])
  have hγv : ∀ i j, γ₀.val i j = x'.val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, u.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t; rw [hu _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp only [e1]; rw [← Matrix.mul_apply, Matrix.one_mul]
  have hxInt := intM_of_mem_KO hx.1
  have hγInt : IntM γ₀.val := by
    intro i j; rw [hγv, hx'M]; simp only [M]; split_ifs
    · exact hxInt _ _
    · exact intM_one _ _
  have hdet : γ₀.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ₀
  have hbKO : embX (s + 1) γ₀ ∈ KO k (Fin κ ⊕ Fin (s + 1)) := by
    refine GlobalTheory.SymDec.mem_KO_of_intM_det ?_ ?_
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨hγInt, intM_zero, intM_zero, intM_one⟩
    · rw [Radical.embX_val, det_fromBlocks_zero₂₁, det_one, mul_one, hdet]
  have hbJ : embX (s + 1) γ₀ ∈ S.P.J := by
    refine (SymData.mem_J_iff_pattern k s κ S _).2 ⟨hbKO, fun a b hab => ?_⟩
    have h1 : InN (S.ρ + 1) (1 : GL (Fin κ ⊕ Fin (s + 1)) k) := fun r s _ => rfl
    have := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 h1 γ₀ hγ₀ a b hab
    rw [one_mul] at this
    rw [this, sub_self, map_zero]; exact zero_lt_one
  have hue : u = x' * (embX (s + 1) γ₀)⁻¹ := by rw [e]; group
  have huJ : u ∈ S.P.J := by rw [hue]; exact S.P.J.mul_mem hx'J (S.P.J.inv_mem hbJ)
  refine ⟨⟨u, huJ⟩, ⟨embX (s + 1) γ₀, hbJ⟩, reGL (GlobalTheory.SymDec.epsZ t) γ₀, ?_, ?_, ?_⟩
  · exact (Radical.mem_N_iff _).2 (GlobalTheory.SymDec.conj_inN t S.ϖ hc (S.ρ + 1) hu)
  · exact GlobalTheory.SymDec.conj_embX t S.ϖ hc γ₀
  · change MaxM ((u * embX (s + 1) γ₀).val - (x : GL _ k).val)
    rw [← e, hx'M]; exact hM
