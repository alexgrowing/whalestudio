import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.Exchange

section General
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [T2Space k] in

theorem integral_shear {I : Type} [Fintype I] (J : I → Prop) (S : (I → k) → (I → k))
    (hS : Continuous S) (h0 : ∀ e i, ¬ J i → S e i = 0)
    (h1 : ∀ e e' : I → k, (∀ i, ¬ J i → e i = e' i) → S e = S e')
    (f : (I → k) → ℂ) (hf : Continuous f) :
    ∫ e, f (e + S e) ∂(Measure.pi fun _ => ν) = ∫ e, f e ∂(Measure.pi fun _ => ν) := by
  classical
  have hE := measurePreserving_piEquivPiSubtypeProd (fun _ : I => ν) (fun i => ¬ J i)
  set E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => k) (fun i => ¬ J i) with hEdef
  let g : ({i // ¬ J i} → k) → ({i // ¬ ¬ J i} → k) → ({i // ¬ ¬ J i} → k) :=
    fun a b => b + fun i => S (E.symm (a, 0)) i.1
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_snd.add (measurable_pi_lambda _ fun i => ?_)
    exact (measurable_pi_apply i.1).comp (hS.measurable.comp
      (E.symm.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hT := (MeasurePreserving.id (Measure.pi fun _ : {i // ¬ J i} => ν)).skew_product
    (μc := Measure.pi fun _ : {i // ¬ ¬ J i} => ν) (μd := Measure.pi fun _ : {i // ¬ ¬ J i} => ν) hgm
    (Filter.Eventually.of_forall fun a => map_add_right_eq_self _ _)
  have hall := (hE.symm E).comp (hT.comp hE)
  have heq : (fun e : I → k => e + S e) = E.symm ∘ (fun p => (id p.1, g p.1 p.2)) ∘ E := by
    funext e
    have : S (E.symm ((E e).1, 0)) = S e := by
      apply h1
      intro i hi
      simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
    funext i
    simp only [Function.comp, g, this, id]
    by_cases hi : J i
    · simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]
    · simp [hEdef, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi, h0 e i hi]
  rw [← heq] at hall
  conv_rhs => rw [← hall.map_eq]
  rw [integral_map hall.measurable.aemeasurable hf.aestronglyMeasurable]

open Classical in

def ext0 {I : Type} (P : I → Prop) (e : {i // P i} → k) : I → k :=
  fun i => if h : P i then e ⟨i, h⟩ else 0

omit [IsTopologicalAddGroup k] [T2Space k]
  [SecondCountableTopology k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] in
theorem continuous_wittExtendByZero {I : Type} (P : I → Prop) : Continuous (ext0 (k := k) P) := by
  refine continuous_pi fun i => ?_
  unfold ext0
  by_cases h : P i
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

omit [T2Space k] in

theorem integral_glue {I B : Type} [Fintype B] (P Q : I → Prop) [Fintype {i // P i}] [Fintype {i // Q i}]
    (j : B → I) (hj : Function.Injective j) (hPj : ∀ b, ¬ P (j b)) (hQ : ∀ i, Q i ↔ P i ∨ ∃ b, j b = i)
    (g : (B → k) → I → k) (hg1 : ∀ u b, g u (j b) = u b) (hg2 : ∀ u i, (∀ b, j b ≠ i) → g u i = 0)
    (f : (I → k) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ∫ u : B → k, (∫ e, f (ext0 P e + g u) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) =
      ∫ e, f (ext0 Q e) ∂(Measure.pi fun _ => ν) := by
  classical
  let s : {i // P i} ⊕ B → {i // Q i} :=
    Sum.elim (fun i => ⟨i.1, (hQ _).2 (Or.inl i.2)⟩) (fun b => ⟨j b, (hQ _).2 (Or.inr ⟨b, rfl⟩)⟩)
  have hs : Function.Bijective s := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [s, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [Subtype.ext h]
      · exact absurd (h ▸ a.2) (hPj b)
      · exact absurd (h ▸ b.2) (hPj a)
      · rw [hj h]
    · rintro ⟨i, hi⟩
      rcases (hQ i).1 hi with h | ⟨b, rfl⟩
      · exact ⟨Sum.inl ⟨i, h⟩, rfl⟩
      · exact ⟨Sum.inr b, rfl⟩
  let σ := Equiv.ofBijective s hs
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // Q i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // P i} ⊕ B => k) (fun _ => ν)
  have h3 := h1.comp h2
  have hint : Integrable (fun e => f (ext0 Q e)) (Measure.pi fun _ => ν) := by
    refine (hf.comp (continuous_wittExtendByZero Q)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (K := (fun (y : I → k) (i : {i // Q i}) => y i.1) '' tsupport f)
      (hc.isCompact.image (by fun_prop)) fun e he => ?_
    by_contra h
    refine he ⟨_, subset_tsupport _ h, ?_⟩
    funext i
    simp [ext0, i.2]
  have key : ∀ z : ({i // P i} → k) × (B → k), ext0 P z.1 + g z.2 =
      ext0 Q ((MeasurableEquiv.piCongrLeft (fun _ : {i // Q i} => k) σ ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // P i} ⊕ B => k)).symm) z) := by
    intro z
    funext i
    by_cases hq : Q i
    · obtain ⟨t, ht⟩ := σ.surjective ⟨i, hq⟩
      have hi : i = (σ t).1 := by rw [ht]
      simp only [ext0, hq, dite_true, Pi.add_apply, Function.comp, ← ht]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      rcases t with t | t
      · have hi' : i = t.1 := hi
        subst hi'
        have : g z.2 t.1 = 0 := hg2 _ _ fun b hb => hPj b (hb ▸ t.2)
        simp [this, t.2, MeasurableEquiv.sumPiEquivProdPi]
      · have hi' : i = j t := hi
        subst hi'
        simp [hg1, hPj, MeasurableEquiv.sumPiEquivProdPi]
    · have hp : ¬ P i := fun h => hq ((hQ i).2 (Or.inl h))
      have : g z.2 i = 0 := hg2 _ _ fun b hb => hq ((hQ i).2 (Or.inr ⟨b, hb⟩))
      simp [ext0, hq, hp, this]
  have hint2 := h3.integrable_comp_of_integrable hint
  rw [← h3.map_eq, integral_map (f := fun e => f (ext0 Q e)) h3.measurable.aemeasurable
    (hf.comp (continuous_wittExtendByZero Q)).aestronglyMeasurable]
  have := integral_prod_symm _ hint2
  simp only [Function.comp] at this key ⊢
  rw [this]
  simp only [← key]

end General

section Entries
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem det_lowU (C : Matrix (Fin c) n k) : Matrix.GeneralLinearGroup.det (lowU C) = 1 := by
  ext
  simp [lowU, Matrix.GeneralLinearGroup.val_det_apply]

theorem det_upU (C : Matrix n (Fin c) k) : Matrix.GeneralLinearGroup.det (upU C) = 1 := by
  ext
  simp [upU, Matrix.GeneralLinearGroup.val_det_apply]

theorem mul_rowE {m : Type} (q : Fin c) (u : n → k) (x : Matrix m (n ⊕ Fin c) k) (r : m) (s : n ⊕ Fin c) :
    (x * (rowE c (q.val + 1) u).val) r s = x r s + Sum.elim (fun s' => x r (Sum.inr q) * u s') 0 s := by
  rcases s with s | s <;>
    simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem colE_inv_mul {m : Type} (q : Fin c) (β : n → k) (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * x) r s =
      x r s + Sum.elim (fun r' => -(β r' * x (Sum.inr q) s)) 0 r := by
  rcases r with r | r <;>
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj, neg_ite, -Matrix.coe_units_inv]

def mat (x₀ : Matrix n n' k) (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := basePt c x₀ + Matrix.of fun r s => y (r, s)

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_eq (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e = mat x₀ (ext0 (Free p) e) := rfl

def gRow (q : Fin c) (u : n' → k) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k :=
  fun i => if i.1 = Sum.inr q then Sum.elim u 0 i.2 else 0

def gCol (q : Fin c) (β : n → k) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k :=
  fun i => if i.2 = Sum.inr q.castSucc then Sum.elim β 0 i.1 else 0

def sRow (q : Fin c) (u : n' → k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k :=
  fun i => Sum.elim (fun s' => ext0 (Free (q.val + 1)) e (i.1.1, Sum.inr q.castSucc) * u s') 0 i.1.2

def sCol (q : Fin c) (β : n → k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k :=
  fun i => Sum.elim (fun r' => -(β r' * ext0 (Free (q.val + 1)) e (Sum.inr q, i.1.2))) 0 i.1.1

omit [Fintype n] in
theorem affPt_mul_rowE (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val =
      mat x₀ (ext0 (Free (q.val + 1)) (e + sRow q u e) + gRow q u) := by
  ext r s
  have := mul_rowE q.castSucc u (affPt (q.val + 1) x₀ e) r s
  rw [Fin.val_castSucc] at this
  rw [this, affPt_eq]
  rcases r with r | r <;> rcases s with s | s
  · simp [mat, ext0, gRow, sRow, Free, basePt]
  · by_cases h : Free (q.val + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gRow, sRow, h]
  · rcases lt_trichotomy r q with h | h | h
    · have h' : r.val < q.val := h
      have h1 : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      have h2 : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr q.castSucc : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      simp [mat, ext0, gRow, sRow, basePt, h1, h2, h.ne, h'.ne]
    · subst h
      simp [mat, ext0, gRow, sRow, Free, basePt]
    · have h' : q.val < r.val := h
      simp [mat, ext0, gRow, sRow, Free, basePt, h'.le, h'.not_gt, h.ne', h'.ne']
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gRow, sRow, h]

omit [Fintype n'] in
theorem colE_inv_mul_affPt (q : Fin c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q.val + 1) x₀ e =
      mat x₀ (ext0 (Free (q.val + 1)) (e + sCol q β e) + gCol q (-β)) := by
  ext r s
  rw [colE_inv_mul, affPt_eq]
  rcases r with r | r <;> rcases s with s | s
  · simp [mat, ext0, gCol, sCol, Free, basePt]
  · rcases lt_trichotomy s q.castSucc with h | h | h
    · have h' : s.val < q.val := h
      simp [mat, ext0, gCol, sCol, Free, basePt, h'.not_gt, h.ne, h'.ne']
    · subst h
      simp [mat, ext0, gCol, sCol, Free, basePt]
    · have h' : q.val < s.val := h
      have h1 : Free (q.val + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      have h2 : Free (q.val + 1) ((Sum.inr q : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      simp [mat, ext0, gCol, sCol, basePt, h1, h2, h.ne', h'.ne]
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gCol, sCol, h]
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gCol, sCol, h]

end Entries

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem om_rowE (μ : kˣ →* ℂˣ) (p : ℕ) (u : n' → k) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    om μ (rowE (c + 1) p u) 1 Φ x = Φ (x * (rowE (c + 1) p u).val) := by
  have : Matrix.GeneralLinearGroup.det (rowE (c + 1) p u) = 1 := det_lowU _
  simp only [om, this, map_one, nabs_one]
  simp

theorem om_colE (μ : kˣ →* ℂˣ) (p : ℕ) (β : n → k) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    om μ 1 (colE c p β) Φ x = Φ (((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val * x) := by
  have : Matrix.GeneralLinearGroup.det (colE c p β) = 1 := det_upU _
  simp only [om, this, map_one, nabs_one]
  simp

def big (ψ : AddChar k Circle) (q : Fin c) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ℂ :=
  χ (fun s => x (Sum.inr q) (Sum.inl s)) * Φ x * (ψ (-ch x) : ℂ)

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem continuous_mat (x₀ : Matrix n n' k) : Continuous (mat (c := c) x₀) := by
  unfold mat
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [Matrix.of_apply]
  exact continuous_apply _

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem continuous_big {ψ : AddChar k Circle} (hψ : Continuous ψ) (q : Fin c) {χ : (n' → k) → ℂ}
    (hχ : Continuous χ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) :
    Continuous (big ψ q χ Φ) := by
  unfold big ch
  refine ((hχ.comp (continuous_pi fun s => continuous_id.matrix_elem _ _)).mul hΦ).mul
    (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
  exact continuous_finset_sum _ fun i _ => continuous_id.matrix_elem _ _

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem hasCompactSupport_big (ψ : AddChar k Circle) (q : Fin c) (χ : (n' → k) → ℂ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : HasCompactSupport Φ) (x₀ : Matrix n n' k) :
    HasCompactSupport fun y => big ψ q χ Φ (mat x₀ y) := by
  haveI := t2Space k
  refine HasCompactSupport.intro
    (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (i : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) =>
      x i.1 i.2 - basePt c x₀ i.1 i.2) '' tsupport Φ)
    (hΦ.isCompact.image (continuous_pi fun i => (continuous_id.matrix_elem _ _).sub continuous_const))
    fun y hy => ?_
  have : Φ (mat x₀ y) = 0 := by
    by_contra h
    refine hy ⟨_, subset_tsupport _ h, ?_⟩
    funext i
    simp [mat]
  simp [big, this]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] in
theorem row_mul_rowE (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    (fun s => (affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val) (Sum.inr q) (Sum.inl s)) = u := by
  classical
  funext s
  rw [affPt_mul_rowE]
  simp [mat, basePt, ext0, Free, gRow]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n'] [DecidableEq n'] in
theorem col_colE_inv_mul (q : Fin c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    (fun r => -(((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q.val + 1) x₀ e)
      (Sum.inl r) (Sum.inr q.castSucc)) = β := by
  classical
  funext s
  rw [colE_inv_mul_affPt]
  simp [mat, basePt, ext0, Free, gCol]

variable [MeasurableSpace k] [BorelSpace k]

open Classical in
theorem opE_rowE {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μ : kˣ →* ℂˣ) (q : Fin c) {χ : (n' → k) → ℂ} (hχ : Continuous χ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) (x₀ : Matrix n n' k) (u : n' → k) :
    χ u * opE ψ ν (q.val + 1) (om μ (rowE (c + 1) (q.val + 1) u) 1 Φ) x₀ =
      ∫ e, big ψ q χ Φ (mat x₀ (ext0 (Free (q.val + 1)) e + gRow q u)) ∂(Measure.pi fun _ => ν) := by
  haveI := t2Space k
  haveI := secondCountable k
  unfold opE
  rw [← integral_const_mul]
  refine Eq.trans ?_ (integral_shear ν (fun i => i.1.2.isLeft) (sRow q u) ?_ ?_ ?_
    (fun e => big ψ q χ Φ (mat x₀ (ext0 (Free (q.val + 1)) e + gRow q u)))
    ((continuous_big hψ q hχ hΦ).comp ((continuous_mat x₀).comp ((continuous_wittExtendByZero _).add continuous_const))))
  · congr 1
    funext e
    rw [← affPt_mul_rowE, big, row_mul_rowE, om_rowE, mul_assoc]
    congr 5
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    have := mul_rowE q.castSucc u (affPt (q.val + 1) x₀ e) (Sum.inr i) (Sum.inr i.succ)
    rw [Fin.val_castSucc] at this
    rw [this]; simp
  · refine continuous_pi fun ⟨⟨r, s⟩, h⟩ => ?_
    rcases s with s | s
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  · rintro e ⟨⟨r, s | s⟩, h⟩ hi
    · simp at hi
    · rfl
  · intro e e' h
    funext ⟨⟨r, s⟩, hi⟩
    rcases s with s | s
    · simp only [sRow, Sum.elim_inl, ext0]
      split_ifs with h1
      · rw [h ⟨_, h1⟩ (by simp)]
      · rfl
    · rfl

open Classical in
theorem opE_colE {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μ : kˣ →* ℂˣ) (q q' : Fin c) {χ : (n' → k) → ℂ} (hχ : Continuous χ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Continuous Φ) (x₀ : Matrix n n' k) (β : n → k) :
    opE ψ ν (q'.val + 1) (fun x => χ (fun s => x (Sum.inr q) (Sum.inl s)) *
        om μ 1 (colE c (q'.val + 1) β) Φ x) x₀ =
      ∫ e, big ψ q χ Φ (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' (-β))) ∂(Measure.pi fun _ => ν) := by
  haveI := t2Space k
  haveI := secondCountable k
  unfold opE
  refine Eq.trans ?_ (integral_shear ν (fun i => i.1.1.isLeft) (sCol q' β) ?_ ?_ ?_
    (fun e => big ψ q χ Φ (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' (-β))))
    ((continuous_big hψ q hχ hΦ).comp ((continuous_mat x₀).comp ((continuous_wittExtendByZero _).add continuous_const))))
  · congr 1
    funext e
    rw [← colE_inv_mul_affPt, big]
    simp only [om_colE, ch, colE_inv_mul, Sum.elim_inr, Pi.zero_apply, add_zero]
  · refine continuous_pi fun ⟨⟨r, s⟩, h⟩ => ?_
    rcases r with r | r
    · exact (continuous_const.mul ((continuous_apply _).comp (continuous_wittExtendByZero _))).neg
    · exact continuous_const
  · rintro e ⟨⟨r | r, s⟩, h⟩ hi
    · simp at hi
    · rfl
  · intro e e' h
    funext ⟨⟨r, s⟩, hi⟩
    rcases r with r | r
    · simp only [sCol, Sum.elim_inl, ext0]
      split_ifs with h1
      · rw [h ⟨_, h1⟩ (by simp)]
      · rfl
    · rfl

end Main

open Classical in

theorem opE_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x₀ : Matrix n n' k, (∀ χ : (n' → k) → ℂ, IsLocallyConstant χ → HasCompactSupport (fun u : n' → k => opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ) x₀) ∧ HasCompactSupport (fun β : n → k => opE ψ ν (p + 1) (om μ 1 (colE c (p + 1) β) Φ) x₀) ∧ ∫ u : n' → k, χ u * opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ) x₀ ∂(Measure.pi fun _ => ν) = ∫ β : n → k, opE ψ ν (p + 1) (fun x => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => x (Sum.inr l) (Sum.inl s)) else 0) * om μ 1 (colE c (p + 1) β) Φ x) x₀ ∂(Measure.pi fun _ => ν)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ ν _ μ Φ hΦ x₀ χ hχ
  haveI := t2Space k
  haveI := secondCountable k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨q', hq⟩ : ∃ q' : Fin c, q.val + 1 = q'.val := ⟨⟨_, hpc⟩, rfl⟩
  have hΦ1 : Continuous Φ := hΦ.1.continuous
  have hΦ2 : HasCompactSupport Φ := hΦ.2
  refine ⟨?_, ?_, ?_⟩
  · refine HasCompactSupport.intro
      (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (s : n') => x (Sum.inr q) (Sum.inl s)) '' tsupport Φ)
      (hΦ2.isCompact.image (continuous_pi fun i => continuous_id.matrix_elem _ _)) fun u hu => ?_
    unfold opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have : Φ (affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val) = 0 := by
      by_contra h
      exact hu ⟨_, subset_tsupport _ h, row_mul_rowE q u x₀ e⟩
    simp [om_rowE, this]
  · rw [hq]
    refine HasCompactSupport.intro
      (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r : n) =>
        -x (Sum.inl r) (Sum.inr q'.castSucc)) '' tsupport Φ)
      (hΦ2.isCompact.image (continuous_pi fun i => (continuous_id.matrix_elem _ _).neg)) fun β hβ => ?_
    unfold opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have : Φ (((colE c (q'.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q'.val + 1) x₀ e) = 0 := by
      by_contra h
      exact hβ ⟨_, subset_tsupport _ h, col_colE_inv_mul q' β x₀ e⟩
    simp only [om_colE, this, zero_mul, Pi.zero_apply]
  · have hsum : ∀ x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
        (∑ l : Fin c, if l.val + 1 = q.val + 1 then χ (fun s => x (Sum.inr l) (Sum.inl s)) else 0) =
          χ (fun s => x (Sum.inr q) (Sum.inl s)) := by
      intro x
      simp [Fin.val_inj]
    simp only [hsum, opE_rowE hψ ν μ q hχ.continuous hΦ1]
    rw [hq]
    simp only [opE_colE hψ ν μ q q' hχ.continuous hΦ1]
    have hf := (continuous_big hψ q hχ.continuous hΦ1).comp (continuous_mat x₀)
    have hc := hasCompactSupport_big ψ q χ hΦ2 x₀
    let Q : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop := fun i => Free q'.val i ∨ Free (q'.val + 1) i
    have h1 := integral_glue ν (Free q'.val) Q (fun s : n' => (Sum.inr q, Sum.inl s))
      (fun a b h => by simpa using h) (fun s => by simp [Free, hq]) (by
        rintro ⟨r | r, s | s⟩ <;> simp [Q, Free, Fin.ext_iff, ← hq] <;> omega)
      (gRow q) (fun u s => by simp [gRow]) (by
        rintro u ⟨r | r, s | s⟩ h <;> simp [gRow]
        rintro rfl
        exact absurd rfl (h s)) _ hf hc
    have h2 := integral_glue ν (Free (q'.val + 1)) Q (fun r : n => (Sum.inl r, Sum.inr q'.castSucc))
      (fun a b h => by simpa using h) (fun s => by simp [Free]) (by
        rintro ⟨r | r, s | s⟩ <;> simp [Q, Free, Fin.ext_iff, ← hq] <;> omega)
      (gCol q') (fun u s => by simp [gCol]) (by
        rintro u ⟨r | r, s | s⟩ h <;> simp [gCol]
        rintro rfl
        exact absurd rfl (h r)) _ hf hc
    haveI : ν.Regular := Measure.regular_of_isAddLeftInvariant (isCompact_int k)
      (by rw [(isOpen_int k).interior_eq]; exact ⟨0, zero_mem _⟩) (isCompact_int k).measure_ne_top
    haveI : ν.IsNegInvariant := inferInstance
    refine Eq.trans ?_ (integral_neg_eq_self (fun β : n → k => ∫ e, big ψ q χ Φ
      (mat x₀ (ext0 (Free (q'.val + 1)) e + gCol q' β)) ∂(Measure.pi fun _ => ν)) _).symm
    exact h1.trans h2.symm

end GlobalTheory.RootEx.Exchange
