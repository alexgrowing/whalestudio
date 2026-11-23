import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymSupport

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def InR (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  (∀ l s, g (.inr l) (.inl s) = 0) ∧
    ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r → g r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)

theorem mem_R_of_inR {g : GL (n ⊕ Fin c) k} (h : InR g.val) : g ∈ R k n c 1 := by
  have e : g.val = fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂ 0 g.val.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks g.val]
    congr 1
    ext l s; exact h.1 l s
  have hd : g.val.toBlocks₁₁.det ≠ 0 := by
    have := g.det_ne_zero
    rw [e, det_fromBlocks_zero₂₁] at this
    exact left_ne_zero_of_mul this
  set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd with hγ
  have hv : γ.val = g.val.toBlocks₁₁ := rfl
  have e2 : (embX c γ⁻¹ * g).val = fromBlocks 1 ((γ⁻¹).val * g.val.toBlocks₁₂) 0 g.val.toBlocks₂₂ := by
    change fromBlocks (γ⁻¹).val 0 0 1 * g.val = _
    rw [e, fromBlocks_multiply]
    simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, ← hv, Units.inv_mul]
    simp
  have hn : InN 1 (embX c γ⁻¹ * g) := by
    rintro (r | r) (s | s) hl <;> rw [e2]
    · simp [Matrix.one_apply]
    · have : ∀ b, g.val (.inl b) (.inr s) = 0 := fun b => by simpa using h.2 (.inl b) s hl
      simp [Matrix.mul_apply, toBlocks₁₂, this]
    · simp
    · exact h.2 (.inr r) s hl
  have : g = embX c γ * (embX c γ⁻¹ * g) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hn))

theorem typeFrame_val {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← fromBlocks_diagonal]; simp

theorem typeFrame_inv_val {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem InR.conj {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL (n ⊕ Fin c) k} (h : InR g.val) :
    InR ((typeFrame ϖ ord).bas * g * (typeFrame ϖ ord).bas⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, typeFrame_val, typeFrame_inv_val]
  refine ⟨fun l s => by simp [h.1], fun r i hl => ?_⟩
  rw [mul_diagonal, diagonal_mul, h.2 r i hl, Matrix.one_apply]
  split_ifs with e
  · subst e; simp
  · simp

end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_int_inv {U : Matrix n n k} (hU : IntM U) (hd : U.det = 1) : ∃ V, IntM V ∧ U * V = 1 := by
  let U₀ : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨U i j, hU i j⟩
  have e : U = (algebraMap 𝒪[k] k).mapMatrix U₀ := rfl
  refine ⟨U.adjugate, fun i j => ?_, by rw [mul_adjugate, hd, one_smul]⟩
  rw [e, ← RingHom.map_adjugate]
  exact (U₀.adjugate i j).2

theorem exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (T : n → Prop)
    (h1 : ∀ l s, T s → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ r : GL (n ⊕ Fin c) k, InR r.val ∧ ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∃ u ∈ KOne k (n ⊕ Fin c), g = r * lowU D * u := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l, r = .inr l) (fun i => lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap, show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl⟩ := hP
        simpa using h1 l s hT
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r → M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  have e2 : (g * u * (lowU (V * M.toBlocks₂₁))⁻¹).val =
      fromBlocks (M.toBlocks₁₁ - M.toBlocks₁₂ * (V * M.toBlocks₂₁)) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [Units.val_mul, e]
    change M * fromBlocks 1 0 (-(V * M.toBlocks₂₁)) 1 = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    simp [← Matrix.mul_assoc, hUV, sub_eq_add_neg]
  refine ⟨g * u * (lowU (V * M.toBlocks₂₁))⁻¹, ?_, V * M.toBlocks₂₁, hV.mul fun i j => hM _ _, fun l s hT => ?_,
    u⁻¹, inv_mem hu, by simp⟩
  · rw [e2]
    refine ⟨fun l s => rfl, ?_⟩
    rintro (r | r) i hl
    · exact m2 _ i hl
    · exact m2 _ i hl
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have : M (.inr m) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr m) (.inl s) := if_pos ⟨hT, m, rfl⟩
    simp [toBlocks₂₁, this]

end Local

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_match {a t Y : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] [Fintype Y] [DecidableEq Y]
    (Q : TypeDatum k a) (μ : kˣ →* ℂˣ) (e : a ⊕ t ≃ Y) {G : GL Y k} (hG : G ∈ KO k Y) (Z : Matrix Y a k)
    (h : Q.Phi t μ (((G⁻¹).val * Z).submatrix e id) ≠ 0) :
    ∃ κ : GL Y k, (reGL e).symm κ ∈ Q.stepJ t ∧ ∀ r b, valuation k ((G * κ).val r (e (.inl b)) - Z r b) < 1 := by
  obtain ⟨⟨g, hg, eg⟩, hb⟩ := (Q.Phi_ne_zero_iff μ).1 h
  refine ⟨reGL e (embTop t g), ?_, ?_⟩
  · rw [MulEquiv.symm_apply_apply]
    refine Q.mem_stepJ_iff.2 ⟨?_, ⟨g, hg, by simp [embTop_val]⟩, by simpa [embTop_val] using maxM_zero⟩
    obtain ⟨g1, g2⟩ := mem_KO.1 (Q.le_KO hg)
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [embTop_val]; exact intM_fromBlocks.2 ⟨g1, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, embTop_val]; exact intM_fromBlocks.2 ⟨g2, intM_zero, intM_zero, intM_one⟩
  · have m : MaxM ((reGL e (embTop t g)).val.submatrix id (fun b => e (.inl b)) - (G⁻¹).val * Z) := by
      intro r b
      obtain ⟨r, rfl⟩ := e.surjective r
      rcases r with r | r
      · have : g.val r b = ((G⁻¹).val * Z) (e (.inl r)) b := by rw [eg]; rfl
        simp only [Matrix.sub_apply, ← this]
        simp [reGL_val, embTop_val]
      · have : valuation k (((G⁻¹).val * Z) (e (.inr r)) b) < 1 := hb r b
        rw [Matrix.sub_apply, Valuation.map_sub_swap]
        simpa [reGL_val, embTop_val] using this
    have := (intM_of_mem_KO hG).mul_maxM m
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at this
    exact this

theorem supportOne (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportOne t := by
  intro j c H h hh x₀ e hΦ
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  let B := (typeFrame S.ϖ o).bas
  let B' := (typeFrame S.ϖ o').bas
  have hG : B⁻¹ * h * B ∈ KO k _ := mem_stabLat.1 hh
  let Z := (B⁻¹).val * affPt 1 x₀ e * B'.val
  let J := (S.P.iter t S.μ S.tame (j + 1)).reindex o
  have hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0 := by
    have e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt 1 x₀ e) * B'.val := by
      simp only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]
    have e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o' := rfl
    rw [e2, e1]
    exact hΦ
  obtain ⟨κ₀, hκ, hc⟩ := exists_match _ _ _ hG _ hΦ'
  have hκ' : κ₀ ∈ J.J := hκ
  have hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r *
      affPt 1 x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1 + 1) => (S.ϖ : k) ^ (i.val + 1)) s := by
    intro r s
    simp only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]
  obtain ⟨r, hr, D, hD, hD0, u, hu, eq⟩ := exists_factor (mul_mem hG (J.le_KO hκ'))
    (fun s => ∃ i, s = .inl (.inl i)) (by
      rintro l _ ⟨i, rfl⟩
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) -
        Z (.inr l) (.inl (.inl (.inl i)))) < 1 := hc (.inr l) (.inl (.inl i))
      rwa [hZ, show affPt 1 x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free],
        mul_zero, zero_mul, sub_zero] at h1) (by
      intro r i hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) -
        Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1 := hc r (.inl (.inr ⟨i.val, by omega⟩))
      rw [standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ] at h1
      convert h1 using 3
      rcases r with r | r
      · have : i = 0 := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have : ¬ r < i := by simpa [lev] using hl
        by_cases hri : r = i
        · subst hri; simp [affPt, basePt, Free]
        · simp [affPt, basePt, Free, this, hri, Fin.val_inj])
  have hlow : lowU D ∈ J.J := by
    have hK : lowU D ∈ KO k _ := mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩,
      intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩
    refine (hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_KO.1 hK
      exact mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩
    · have : (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b) := by
        obtain ⟨a, rfl⟩ := o.symm.surjective a
        obtain ⟨b, rfl⟩ := o.symm.surjective b
        rw [o.apply_symm_apply, o.apply_symm_apply]
        rcases a with a | a <;> rcases b with b | b
        · simp [lowU, Matrix.one_apply]
        · simp [lowU]
        · have a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩) :=
            o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm
          rcases b with (b | b) | b
          · simpa [lowU] using hD0 a _ ⟨b, rfl⟩
          · have a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + 1 + b.val, by omega⟩) :=
              o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm
            rw [a1, a3] at hab
            exact absurd (show a.val < c + 1 + b.val by omega) hab
          · have a6 : o.symm (.inl (.inr b)) = .inr b := o.symm_apply_eq.2 rfl
            rw [a1, a6] at hab
            exact absurd trivial hab
        · simp [lowU, Matrix.one_apply]
      rw [reGL_symm_val, submatrix_apply, this]
      simp [Matrix.one_apply]
  have hJ : lowU D * u * κ₀⁻¹ ∈ J.J := mul_mem (mul_mem hlow (J.KOne_le hu)) (inv_mem hκ')
  refine ⟨B * r * B⁻¹, mem_R_of_inR (hr.conj S.ϖ o), B * (lowU D * u * κ₀⁻¹) * B⁻¹, ?_, ?_⟩
  · change (reGL o).symm (B⁻¹ * (B * (lowU D * u * κ₀⁻¹) * B⁻¹) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
    have : B⁻¹ * (B * (lowU D * u * κ₀⁻¹) * B⁻¹) * B = lowU D * u * κ₀⁻¹ := by group
    rw [this]; exact hJ
  · calc h = B * (B⁻¹ * h * B * κ₀) * κ₀⁻¹ * B⁻¹ := by group
      _ = _ := by rw [eq]; group

end Main

theorem supportOne_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportOne t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportOne s κ S t hP

end GlobalTheory.SymSupport
