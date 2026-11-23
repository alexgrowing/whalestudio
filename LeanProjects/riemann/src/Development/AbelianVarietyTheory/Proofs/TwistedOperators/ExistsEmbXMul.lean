import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem exists_embX_mul (m : GL (n ⊕ Fin c) k) (h1 : ∀ i r, m.val (Sum.inr i) r ∈ 𝒪[k])
    (h2 : ∀ i r, (m⁻¹).val r (Sum.inr i) ∈ 𝒪[k]) :
    ∃ g : GL n k, ∃ w ∈ KO k (n ⊕ Fin c), m = embX c g * w := by
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k _ (Sum.elim (fun _ => 0) (fun _ => 1)) m
  have hi := BlockLevi.blockTriangular_inv _ b hb
  obtain ⟨w1, w2⟩ := mem_KO.1 hw
  have b1 : ∀ i r, b.val (Sum.inr i) r ∈ 𝒪[k] := fun i r => by
    have : b.val = (b * w).val * (w⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_apply]
    exact sum_mem fun s _ => mul_mem (h1 i s) (w2 s r)
  have b2 : ∀ i r, (b⁻¹).val r (Sum.inr i) ∈ 𝒪[k] := fun i r => by
    have : (b⁻¹).val = w.val * ((b * w)⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_apply]
    exact sum_mem fun s _ => mul_mem (w1 r s) (h2 i s)
  have z1 : b.val.toBlocks₂₁ = 0 := by
    ext i j; exact hb (show Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inl j : n ⊕ Fin c) <
      Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inr i : n ⊕ Fin c) by simp)
  have z2 : (b⁻¹).val.toBlocks₂₁ = 0 := by
    ext i j; exact hi (show Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inl j : n ⊕ Fin c) <
      Sum.elim (fun _ => 0) (fun _ => 1) (Sum.inr i : n ⊕ Fin c) by simp)
  have e1 := b.mul_inv
  have e2 := b.inv_mul
  have hD : IntM b.val.toBlocks₂₂ := fun i j => b1 i _
  have hB' : IntM (b⁻¹).val.toBlocks₁₂ := fun i j => b2 j _
  have hD' : IntM (b⁻¹).val.toBlocks₂₂ := fun i j => b2 j _
  have f1 := fromBlocks_toBlocks b.val
  have f2 := fromBlocks_toBlocks (b⁻¹).val
  rw [z1] at f1
  rw [z2] at f2
  generalize b.val.toBlocks₁₁ = A, b.val.toBlocks₁₂ = B, b.val.toBlocks₂₂ = D at *
  generalize (b⁻¹).val.toBlocks₁₁ = A', (b⁻¹).val.toBlocks₁₂ = B', (b⁻¹).val.toBlocks₂₂ = D' at *
  rw [← f1, ← f2, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at e1 e2
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1 e2
  let g : GL n k := ⟨A, A', e1.1, e2.1⟩
  refine ⟨g, (embX c g)⁻¹ * b * w, mul_mem (mem_KO.2 ⟨?_, ?_⟩) hw, by group⟩
  · have : ((embX c g)⁻¹ * b).val = fromBlocks 1 (-(B' * D)) 0 D := by
      rw [← map_inv, Units.val_mul, ← f1]
      change fromBlocks A' 0 0 1 * _ = _
      simp [fromBlocks_multiply, e2.1, eq_neg_of_add_eq_zero_left e2.2.1]
    rw [this]
    rintro (r | r) (s | s)
    exacts [intM_one r s, (hB'.mul hD).neg r s, zero_mem _, hD r s]
  · have : (((embX c g)⁻¹ * b)⁻¹).val = fromBlocks 1 B' 0 D' := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← f2]
      change _ * fromBlocks A 0 0 1 = _
      simp [fromBlocks_multiply, e2.1]
    rw [this]
    rintro (r | r) (s | s)
    exacts [intM_one r s, hB' r s, zero_mem _, hD' r s]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n'] [DecidableEq n'] in
theorem tri_mul_affPt {p : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hM : M.BlockTriangular (lev p))
    (x₀ : Matrix n n' k) (e) (i : Fin c) (r : n ⊕ Fin c) (hr : i.val + 1 ≤ lev p r) :
    (M * affPt (c := c) p x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) r (Sum.inr i.castSucc) = M r (Sum.inr i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]
  · simp [affPt, basePt, Free]
  · intro s _ hs
    by_cases h : lev p s < lev p r
    · rw [hM h, zero_mul]
    · rcases s with s | s
      · have : ¬ p < i.val + 1 := by simp only [lev, Sum.elim_inl] at h hr; omega
        simp [affPt, basePt, Free, this]
      · have h1 : s.val ≠ i.val := fun e => hs (by rw [Fin.ext e])
        have : ¬ s < i := by
          rw [Fin.lt_def]
          simp only [lev, Sum.elim_inr] at h hr; omega
        simp [affPt, basePt, Free, this, h1]
  · simp

omit [Fintype n'] in

theorem mem_coset {p : ℕ} (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k)
    (e) (hA : IntM ((h⁻¹).val * affPt (c := c) p x₀ e))
    (hB : ∀ D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, (∀ r s, ¬ Free p (r, s) → D r s = 0) →
      IntM ((h⁻¹).val * D) → ch D ∈ 𝒪[k]) :
    ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w := by
  obtain ⟨b, hb, w, hw, rfl⟩ := iwasawa_blockTriangular k _ (lev p) h
  have hi := BlockLevi.blockTriangular_inv _ b hb
  obtain ⟨w1, w2⟩ := mem_KO.1 hw
  have hA' : IntM ((b⁻¹).val * affPt (c := c) p x₀ e) := by
    have : (b⁻¹).val = w.val * ((b * w)⁻¹).val := by rw [← Units.val_mul]; simp
    rw [this, Matrix.mul_assoc]
    exact w1.mul hA
  let m : GL (n ⊕ Fin c) k := ⟨BlockLevi.diagPart (lev p) b.val, BlockLevi.diagPart (lev p) (b⁻¹).val,
    BlockLevi.diagPart_mul_diagPart _ hb hi b.mul_inv, BlockLevi.diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  have hu : b * m⁻¹ ∈ N k n c p := by
    refine Subgroup.subset_closure fun r s h => ?_
    have : (b * m⁻¹).val = b.val * BlockLevi.diagPart (lev p) (b⁻¹).val := rfl
    rw [this, BlockLevi.mul_diagPart_apply _ hb hi h, b.mul_inv]
  obtain ⟨g, w', hw', hm⟩ := exists_embX_mul m (fun i r => by
    change (if lev p (Sum.inr i : n ⊕ Fin c) = lev p r then b.val (Sum.inr i) r else 0) ∈ _
    split_ifs with hr
    · have hr' : lev p r = i.val + 1 := hr.symm
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k := Matrix.single r (Sum.inr i.succ) 1
      have hE : IntM E := fun a a' => by
        simp only [E, Matrix.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _]
      have hbE : ∀ a a', (b.val * E) a a' = if a' = Sum.inr i.succ then b.val a r else 0 := by
        intro a a'
        split_ifs with h
        · subst h; simp [E]
        · simp [E, Matrix.mul_single_apply_of_ne, h]
      have := hB (b.val * E) (fun a a' ha => ?_) ?_
      · simpa [ch, hbE] using this
      · rw [hbE]
        split_ifs with h
        · subst h
          apply hb
          rw [hr']
          rcases a with a | a <;> simp [Free, lev] at ha ⊢ <;> omega
        · rfl
      · rw [← Matrix.mul_assoc, ← Units.val_mul]
        simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
        exact w2.mul hE
    · exact zero_mem _) (fun i r => by
    change (if lev p r = lev p (Sum.inr i : n ⊕ Fin c) then (b⁻¹).val r (Sum.inr i) else 0) ∈ _
    split_ifs with hr
    · rw [← tri_mul_affPt hi x₀ e i r hr.ge]
      exact hA' _ _
    · exact zero_mem _)
  refine ⟨b * m⁻¹ * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
    w' * w, mul_mem hw' hw, ?_⟩
  rw [mul_assoc, ← mul_assoc (embX c g), ← hm]; group

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_not_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : ¬ _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = _root_.GlobalTheory.RootEx.basePt c x₀ r s := by
  simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply, dif_neg hf, add_zero]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem intM_basePt_of_intM {x₀ : Matrix n n' k}
    (hx : _root_.GlobalTheory.StepData.IntM x₀) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.basePt c x₀) := by
  unfold _root_.GlobalTheory.RootEx.basePt
  refine _root_.GlobalTheory.StepData.intM_fromBlocks.mpr
    ⟨hx, _root_.GlobalTheory.StepData.intM_zero, _root_.GlobalTheory.StepData.intM_zero, fun l i => ?_⟩
  simp only [Matrix.of_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.intM_affPt {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun rs => ?_⟩
    · have hij := h (Sum.inl i) (Sum.inl j)
      rwa [affPt_apply_of_not_free x₀ e (by simp [_root_.GlobalTheory.RootEx.Free]),
        _root_.GlobalTheory.RootEx.basePt, Matrix.fromBlocks_apply₁₁] at hij
    · obtain ⟨⟨r, s⟩, hf⟩ := rs
      have hrs := h r s
      rwa [affPt_apply_of_free x₀ e hf] at hrs
  · rintro ⟨hx, he⟩ r s
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · rw [affPt_apply_of_free x₀ e hf]
      exact he _
    · rw [affPt_apply_of_not_free x₀ e hf]
      exact intM_basePt_of_intM hx r s

omit [Fintype n'] [DecidableEq n'] in
theorem intM_colE {p : ℕ} (hp : p + 1 ≤ c) (β : n → k) (x₀ : Matrix n n' k) (e) :
    IntM (((colE c (p + 1) β)⁻¹).val * affPt (c := c) (p + 1) x₀ e) ↔
      IntM (affPt (c := c) (p + 1) x₀ e) ∧ ∀ r, β r ∈ 𝒪[k] := by
  have hK : (∀ r, β r ∈ 𝒪[k]) → colE c (p + 1) β ∈ KO k (n ⊕ Fin c) := fun hβ => by
    have : IntM (Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0) := fun r i => by
      simp only [Matrix.of_apply]
      split_ifs
      exacts [hβ r, zero_mem _]
    refine mem_KO.2 ⟨?_, ?_⟩
    · rintro (r | r) (s | s)
      exacts [intM_one r s, this r s, zero_mem _, intM_one r s]
    · rintro (r | r) (s | s)
      exacts [intM_one r s, this.neg r s, zero_mem _, intM_one r s]
  constructor
  · intro h
    have hβ : ∀ r, β r ∈ 𝒪[k] := fun r => by
      have h1 := h (Sum.inl r) (Sum.inr (Fin.castSucc ⟨p, hp⟩))
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr ⟨p, hp⟩)] at h1
      · have : -β r ∈ 𝒪[k] := by simpa [affPt, basePt, Free, colE, upU] using h1
        simpa using neg_mem this
      · rintro (s | s) _ hs
        · simp [affPt, basePt, Free]
        · have : s.val ≠ p := fun e => hs (by rw [Fin.ext (show s.val = (⟨p, hp⟩ : Fin c).val from e)])
          simp [colE, upU, this]
      · simp
    refine ⟨?_, hβ⟩
    have := (mem_KO.1 (hK hβ)).1.mul h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
  · rintro ⟨h, hβ⟩
    exact (mem_KO.1 (hK hβ)).2.mul h

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.psi_eq_one {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k} (hx : x ∈ 𝒪[k]) : ψ x = 1 := by
  have h1 := (hψ x).mpr (by
    rw [Units.val_one, map_one]
    exact (Valuation.mem_integer_iff _ _).mp hx)
  exact h1 x le_rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.mem_of_psi {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff]
  have hmain := (hψ x).mp ?_
  · simpa using hmain
  intro y hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y = 0 := by simpa using hy
    simp [hy0]
  · have hv : valuation k (y / x) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have hyx := hx (y / x) ((Valuation.mem_integer_iff _ _).mpr hv)
    rwa [div_mul_cancel₀ y hx0] at hyx

variable [MeasurableSpace k] [BorelSpace k]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem ch_affPt_mem_of_integral {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) (he : ∀ rs, e rs ∈ 𝒪[k]) :
    _root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.RootEx.ch
  refine sum_mem fun i _ => ?_
  have hf : _root_.GlobalTheory.RootEx.Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by
    simp [_root_.GlobalTheory.RootEx.Free]
  rw [affPt_apply_of_free x₀ e hf]
  exact he _

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in
open Classical in
theorem _root_.GlobalTheory.RootEx.Unram.opE_of_ite {p : ℕ} {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {ν : Measure k} (hν : _root_.GlobalTheory.SplitWeil.IsUnitVol ν)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (P : Prop)
    (h : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) = if P ∧ ∀ rs, e rs ∈ 𝒪[k] then 1 else 0) :
    _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ = if P then 1 else 0 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI := hν.1
  set S : Set ({ rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k) :=
    Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => (_root_.GlobalTheory.SplitWeil.isOpen_int k).measurableSet
  have hint : ∀ e : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k,
      Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) *
          ((ψ (-_root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt p x₀ e)) : Circle) : ℂ) =
        if P then S.indicator (fun _ => (1 : ℂ)) e else 0 := by
    intro e
    rw [h e]
    by_cases hP : P
    · by_cases he : ∀ rs, e rs ∈ 𝒪[k]
      · have heS : e ∈ S := fun rs _ => he rs
        rw [if_pos ⟨hP, he⟩, if_pos hP, Set.indicator_of_mem heS,
          _root_.GlobalTheory.RootEx.Unram.psi_eq_one hψ
            (neg_mem (ch_affPt_mem_of_integral x₀ e he))]
        simp
      · have heS : e ∉ S := fun heS => he fun rs => heS rs (Set.mem_univ _)
        rw [if_neg (fun h' => he h'.2), if_pos hP, Set.indicator_of_notMem heS, zero_mul]
    · rw [if_neg (fun h' => hP h'.1), if_neg hP, zero_mul]
  unfold _root_.GlobalTheory.RootEx.opE
  simp_rw [hint]
  split_ifs with hP
  · rw [integral_indicator_const _ hSm, Measure.real_def, hS, Measure.pi_pi]
    simp [hν.2]
  · simp

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in

theorem _root_.GlobalTheory.RootEx.Unram.psi_ch_eq_one {p : ℕ} (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure]
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (h : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ ≠ 0)
    (D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hD : ∀ r s, ¬ _root_.GlobalTheory.RootEx.Free p (r, s) → D r s = 0)
    (hΨ : ∀ x, Ψ (x + D) = Ψ x) : ψ (-_root_.GlobalTheory.RootEx.ch D) = 1 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  set d : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k :=
    fun rs => D rs.1.1 rs.1.2 with hd
  have haff : ∀ e, _root_.GlobalTheory.RootEx.affPt p x₀ (e + d) = _root_.GlobalTheory.RootEx.affPt p x₀ e + D := by
    intro e
    ext r s
    simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply]
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · simp only [dif_pos hf, Pi.add_apply, hd]
      ring
    · simp only [dif_neg hf, hD r s hf, add_zero]
  have hch : ∀ A B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (A + B) =
        _root_.GlobalTheory.RootEx.ch A + _root_.GlobalTheory.RootEx.ch B := by
    intro A B
    simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib]
  have key : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ =
      ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ := by
    unfold _root_.GlobalTheory.RootEx.opE
    rw [← integral_const_mul, ← integral_add_right_eq_self _ d]
    congr 1
    ext e
    rw [haff, hΨ, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have h1 : ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) = 1 :=
    mul_right_cancel₀ h (key.symm.trans (one_mul _).symm)
  exact Circle.ext (h1.trans Circle.coe_one.symm)

theorem opE_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (_ : Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1), (∀ (h : GL (n ⊕ Fin c) k) (x₀ : Matrix n n' k), opE ψ ν p (om μ 1 h Φ) x₀ ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ KO k (n ⊕ Fin c), h = r * w) ∧ opE ψ ν p Φ = Set.indicator {x | ∀ r s, valuation k (x r s) ≤ 1} 1 ∧ ∀ β : n → k, p + 1 ≤ c → opE ψ ν (p + 1) (om μ 1 (colE c (p + 1) β) Φ) = Set.indicator {x | (∀ r s, valuation k (x r s) ≤ 1) ∧ ∀ r, valuation k (β r) ≤ 1} 1 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ hψ ν hν μ Φ hΦ
  classical
  have hΦ' : ∀ x, Φ x = if IntM x then 1 else 0 := fun x => by
    rw [hΦ, Set.indicator_apply]; exact if_congr Iff.rfl rfl rfl
  refine ⟨fun h x₀ hne => ?_, ?_, fun β hp => ?_⟩
  · have := hν.1
    have hA : ∃ e, IntM ((h⁻¹).val * affPt (c := c) p x₀ e) := by
      by_contra hn
      push Not at hn
      apply hne
      simp only [opE, om, hΦ', Units.val_one, Matrix.mul_one, hn, if_false, mul_zero, zero_mul, integral_zero]
    obtain ⟨e, he⟩ := hA
    refine mem_coset h x₀ e he fun D hD hI => mem_of_psi hψ fun t ht => ?_
    have := psi_ch_eq_one ψ ν _ x₀ hne ((-t) • D) (fun r s hf => by simp [hD r s hf]) fun x => by
      have h1 : IntM ((h⁻¹).val * ((-t) • D)) := by
        rw [Matrix.mul_smul]
        exact fun r s => mul_mem (neg_mem ht) (hI r s)
      have h2 : IntM ((h⁻¹).val * (x + (-t) • D)) ↔ IntM ((h⁻¹).val * x) := by
        rw [Matrix.mul_add]
        exact ⟨fun h => by simpa using h.add h1.neg, fun h => h.add h1⟩
      simp only [om, hΦ', Units.val_one, Matrix.mul_one, h2]
    simpa [ch, Finset.mul_sum] using this
  · funext x₀
    rw [opE_of_ite hψ hν Φ x₀ (IntM x₀) fun e => by simp only [hΦ', intM_affPt], Set.indicator_apply]
    exact if_congr Iff.rfl rfl rfl
  · funext x₀
    have hdet : Matrix.GeneralLinearGroup.det (colE c (p + 1) β) = 1 := by
      ext
      simp [colE, upU]
    rw [opE_of_ite hψ hν _ x₀ (IntM x₀ ∧ ∀ r, β r ∈ 𝒪[k]) fun e => by
      simp only [om, hΦ', hdet, Units.val_one, Matrix.mul_one, intM_colE hp, intM_affPt, and_right_comm]
      simp [nabs], Set.indicator_apply]
    exact @if_congr _ _ _ (_) (_) _ _ _ _ Iff.rfl rfl rfl

end GlobalTheory.RootEx.Unram
