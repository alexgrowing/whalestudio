import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C5

set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

namespace I

variable (L) in
theorem sum_split' {M : Type} [AddCommMonoid M] (f : Fin d.n → M) : ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]

theorem blk_mul {M N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)}
    (hM : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r (Sum.inl L.i₀))
    (hN : ∀ c, N (Sum.inr L.i₀) c = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) c) :
    (M * N).submatrix (emS L) (emS L) = M.submatrix (emS L) (emS L) * N.submatrix (emS L) (emS L) := by
  ext a a'
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine Bq.sum_emb (emS L) (emS_inj L) _ fun k hk => ?_
  rcases mem_out L hk with rfl | rfl
  · rw [hM, Matrix.one_apply_ne, zero_mul]
    exact fun h => not_inl L L.i₀ rfl ⟨a, h⟩
  · rw [hN, Matrix.one_apply_ne, mul_zero]
    exact fun h => not_inr L L.i₀ rfl ⟨a', h.symm⟩

theorem blk_one : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).submatrix (emS L) (emS L) = 1 := by
  ext a a'
  simp [Matrix.one_apply, (emS_inj L).eq_iff]

theorem rowy_cM (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (cM c) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  rw [cM_frame h]
  rcases k with k | k
  · simp
  · by_cases hk : k = L.i₀
    · subst hk
      simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L]
    · simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L, hk, Ne.symm hk]

theorem rowy_inv {x : d.G}
    (hx : ∀ k, inFrame d.b x (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b x⁻¹ (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  have h1 : (inFrame d.b x * inFrame d.b x⁻¹) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)] at h1
  · rwa [hx, Matrix.one_apply_eq, one_mul] at h1
  · intro j _ hj
    rw [hx, Matrix.one_apply_ne (Ne.symm hj), zero_mul]
  · simp

theorem rowy_j (g : G2 σ L.Y) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k :=
  (L.j_out g (Sum.inr L.i₀) (by simp) k).1

theorem blk_j (g : G2 σ L.Y) : (inFrame d.b (L.j g)).submatrix (emS L) (emS L) = inFrame L.b g := by
  ext a a'
  rw [Matrix.submatrix_apply, inFrame_j, padM_emS]

theorem inFrame_w1_emS_eq_one (h : Hyp L nb uM nb' w₁ cM δ) (a : Fin L.n ⊕ Fin L.n) (l : Fin d.n ⊕ Fin d.n) :
    inFrame d.b w₁ (emS L a) l = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (emS L a) l ∧
      inFrame d.b w₁ l (emS L a) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) l (emS L a) := by
  obtain ⟨a₀, b₀, -, -, hW⟩ := h.wf
  rw [hW]
  have hne := C4.em_ne L
  rcases a with a | a <;>
    simp [emS, Matrix.single_apply, Matrix.one_apply, hne a, Ne.symm (hne a)] <;>
    (constructor <;> congr)

theorem w1_frame_rows (h : Hyp L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧
    (∀ l, inFrame d.b w₁ (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then inclR (F := F) (AF F) b₀ else 0) ∧
    ∀ j l, inFrame d.b w₁ (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l := by
  obtain ⟨a₀, b₀, -, hb, hW⟩ := h.wf
  refine ⟨b₀, hb, fun l => ?_, fun j l => (inFrame_w1_emS_eq_one h (Sum.inr j) l).1⟩
  rw [hW]
  rcases l with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]

theorem smul_inclR_inj (hδ : δ ≠ 0) {a a' : AF F}
    (h : a • inclR (F := F) (E := E) (AF F) δ = a' • inclR (F := F) (E := E) (AF F) δ) : a = a' := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hδ
  set ψ : Module.Dual F E := (φ δ)⁻¹ • φ with hψ
  have hψδ : ψ δ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  let f : AF F ⊗[F] E →ₗ[F] AF F := (TensorProduct.rid F (AF F)).toLinearMap ∘ₗ LinearMap.lTensor (AF F) ψ
  have hf : ∀ t : AF F, f (t • inclR (F := F) (E := E) (AF F) δ) = t := by
    intro t
    rw [kfour.inclR_eq, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [f, LinearMap.lTensor_tmul, hψδ]
  have h2 := congrArg f h
  rwa [hf, hf] at h2

theorem row_eq {P Wm C C' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)} {b : AE F E}
    (hP : ∀ i, P (Sum.inr L.i₀) (Sum.inl i) = 0)
    (hWy : ∀ l, Wm (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then b else 0)
    (hWo : ∀ j l, Wm (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l)
    (hE : P * (Wm * C) = Wm * C') (k : Fin d.n ⊕ Fin d.n) :
    b * C' (Sum.inl L.i₀) k = P (Sum.inr L.i₀) (Sum.inr L.i₀) * (b * C (Sum.inl L.i₀) k) +
      ∑ j, P (Sum.inr L.i₀) (Sum.inr (L.em j)) * C (Sum.inr (L.em j)) k := by
  have hy : ∀ X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (Wm * X) (Sum.inr L.i₀) k = b * X (Sum.inl L.i₀) k := by
    intro X
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
    · rw [hWy, if_pos rfl]
    · intro l _ hl
      rw [hWy, if_neg hl, zero_mul]
    · simp
  have hem : ∀ j, (Wm * C) (Sum.inr (L.em j)) k = C (Sum.inr (L.em j)) k := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr (L.em j))]
    · rw [hWo, Matrix.one_apply_eq, one_mul]
    · intro l _ hl
      rw [hWo, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
    · simp
  have e := congrFun (congrFun hE (Sum.inr L.i₀)) k
  rw [← hy C', ← e, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hP, zero_mul, Finset.sum_const_zero, zero_add]
  rw [sum_split' L (fun i => P (Sum.inr L.i₀) (Sum.inr i) * (Wm * C) (Sum.inr i) k), hy C]
  simp only [hem]

theorem cx_em (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inl (L.em m)) = c.1 m := by
  rw [cM_frame h]
  simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L, L.inj.eq_iff,
    Ne.symm (C4.em_ne L _)]

theorem cx_emr (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr (L.em m)) = 0 := by
  rw [cM_frame h]
  simp [aB, Matrix.single_apply, C4.em_ne L, Ne.symm (C4.em_ne L _)]

theorem cx_y (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr L.i₀) = c.2 • inclR (F := F) (E := E) (AF F) δ := by
  rw [cM_frame h]
  simp [aB]

theorem cem_l (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (j : Fin L.n) (l : Fin d.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inl l) = 0 := by
  rw [cM_frame h]
  simp

theorem cem_em (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (j m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inr (L.em m)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) j m := by
  rw [cM_frame h]
  by_cases hjm : j = m
  · subst hjm
    simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L, Ne.symm (C4.em_ne L _)]
  · simp [uA, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, C4.em_ne L, Ne.symm (C4.em_ne L _),
      L.inj.eq_iff, hjm, Ne.symm hjm]

theorem inj_core (h : Hyp L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈ par2 σ d.Y) (hpr : p ∈ rat2 σ d.Y) {c c' : Cr L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') := by
  have hP21 : (inFrame d.b p).toBlocks₂₁ = 0 := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have hP : ∀ i k, inFrame d.b p (Sum.inr i) (Sum.inl k) = 0 := fun i k => congrFun (congrFun hP21 i) k
  refine ⟨?_, fun hγ => ?_⟩
  ·
    set g := γ'' * γ'⁻¹ with hg
    have key : w₁⁻¹ * p * w₁ * (cM c.1 * L.j γ') = cM c'.1 * L.j γ'' := by
      rw [mul_assoc (w₁⁻¹ * p), mul_assoc w₁⁻¹, e, inv_mul_cancel_left]
    have key2 : w₁⁻¹ * p * w₁ = cM c'.1 * L.j g * (cM c.1)⁻¹ := by
      rw [hg, map_mul, map_inv, ← mul_assoc (cM c'.1), ← key]
      group
    have hQ : (inFrame d.b (w₁⁻¹ * p * w₁)).submatrix (emS L) (emS L) = (inFrame d.b p).submatrix (emS L) (emS L) := by
      have hWQ : inFrame d.b w₁ * inFrame d.b (w₁⁻¹ * p * w₁) = inFrame d.b p * inFrame d.b w₁ := by
        rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
          one_mul]
      ext a a'
      have e1 := congrFun (congrFun hWQ (emS L a)) (emS L a')
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (emS L a), Finset.sum_eq_single (emS L a')] at e1
      · rw [(inFrame_w1_emS_eq_one h a (emS L a)).1, (inFrame_w1_emS_eq_one h a' (emS L a')).2, Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul, mul_one] at e1
        exact e1
      · intro l _ hl
        rw [(inFrame_w1_emS_eq_one h a' l).2, Matrix.one_apply_ne hl, mul_zero]
      · simp
      · intro l _ hl
        rw [(inFrame_w1_emS_eq_one h a l).1, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
      · simp
    have hfixC' := fix_cM' h c'.1
    have hC1 : (inFrame d.b (cM c.1)⁻¹).submatrix (emS L) (emS L) = 1 := by
      have h1 := blk_mul (L := L) (M := inFrame d.b (cM c.1)) (N := inFrame d.b (cM c.1)⁻¹) (fix_cM' h c.1)
        (rowy_inv (rowy_cM h c.1))
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, blk_one, emS_cM h, one_mul] at h1
      exact h1.symm
    have hR : (inFrame d.b (cM c'.1 * L.j g * (cM c.1)⁻¹)).submatrix (emS L) (emS L) = inFrame L.b g := by
      rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, blk_mul (fix_mul hfixC' (fix_j g)) (rowy_inv (rowy_cM h c.1)),
        GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, blk_mul hfixC' (rowy_j g), emS_cM h, blk_j, hC1, one_mul, mul_one]
    have hG : inFrame L.b g = (inFrame d.b p).submatrix (emS L) (emS L) := by
      rw [← hR, ← key2, hQ]
    refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame g).2 ?_
    ext i k
    rw [hG]
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, emS, Sum.map_inr,
      Sum.map_inl]
    exact hP _ _
  ·
    subst hγ
    have e2 : p * w₁ * cM c.1 = w₁ * cM c'.1 := by
      have h1 := congrArg (· * (L.j γ'')⁻¹) e
      simpa [mul_assoc] using h1
    have hE : inFrame d.b p * (inFrame d.b w₁ * inFrame d.b (cM c.1)) = inFrame d.b w₁ * inFrame d.b (cM c'.1) := by
      have h1 := congrArg (inFrame d.b) e2
      simpa only [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_assoc] using h1
    obtain ⟨b₀, hb₀, hWy, hWo⟩ := w1_frame_rows h
    have hrow := row_eq (fun i => hP L.i₀ i) hWy hWo hE
    set bA := inclR (F := F) (E := E) (AF F) b₀
    have hbinv : inclR (F := F) (E := E) (AF F) b₀⁻¹ * bA = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb₀, map_one]
    have canc : ∀ X Y : AE F E, bA * X = bA * Y → X = Y := by
      intro X Y hXY
      have h1 := congrArg (inclR (F := F) (E := E) (AF F) b₀⁻¹ * ·) hXY
      simpa only [← mul_assoc, hbinv, one_mul] using h1
    have hfixC := fix_cM' h c.1
    have hfixC' := fix_cM' h c'.1

    have hyy : inFrame d.b p (Sum.inr L.i₀) (Sum.inr L.i₀) = 1 := by
      have h1 := hrow (Sum.inl L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hfixC, Matrix.one_apply_ne (by simp), mul_zero]
      rw [hs, add_zero, hfixC', hfixC, Matrix.one_apply_eq, mul_one] at h1
      exact canc _ _ (by rw [mul_one, mul_comm]; exact h1.symm)

    have hd : ∀ l, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l)) = 0 := by
      intro l
      have h1 := hrow (Sum.inr (L.em l))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr (L.em l)) = inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l)) := by
        rw [Finset.sum_eq_single l]
        · rw [cem_em h, Matrix.one_apply_eq, mul_one]
        · intro j _ hj
          rw [cem_em h, Matrix.one_apply_ne hj, mul_zero]
        · simp
      rw [hs, cx_emr h, cx_emr h] at h1
      simp only [mul_zero, zero_add] at h1
      exact h1.symm

    have hu : ∀ m, c'.1.1 m = c.1.1 m := by
      intro m
      have h1 := hrow (Sum.inl (L.em m))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl (L.em m)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [cem_l h, mul_zero]
      rw [hs, add_zero, cx_em h, cx_em h, hyy, one_mul] at h1
      exact canc _ _ h1

    have ha : c'.1.2 = c.1.2 := by
      have h1 := hrow (Sum.inr L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hd, zero_mul]
      rw [hs, add_zero, cx_y h, cx_y h, hyy, one_mul] at h1
      exact smul_inclR_inj h.δ0 (canc _ _ h1)
    exact Subtype.ext (Prod.ext (funext fun m => (hu m).symm) ha.symm)

end I

end PositivityTheory.SiegelWeilFormula.Act.C6

end
