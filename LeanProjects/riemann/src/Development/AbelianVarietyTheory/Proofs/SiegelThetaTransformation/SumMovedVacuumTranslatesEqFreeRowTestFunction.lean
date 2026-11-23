import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood

open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict
open scoped ComplexConjugate Real Classical

namespace GlobalTheory.Dict.SumFree

open GlobalTheory.SW.TensLat GlobalTheory.SW.RecSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}

section Tensor

variable {M : ℕ} {Λ Λ₁ Λ₂ : Lt E n} {𝔪 𝔞 𝔟 : Ideal (𝓞 E)} {N : Lt E r}
  {y : Matrix (Fin n) (Fin r) E}

theorem smul_tens (hΛ : Λ ∈ Vset E n M) {a : 𝓞 E} (ha : a ∈ 𝔞) (hy : y ∈ tens Λ N) :
    (a : E) • y ∈ tens Λ (𝔞 • N) := by
  rw [mem_tens_iff hΛ] at hy ⊢
  intro w hw
  rw [ctr_smul]
  exact Submodule.smul_mem_smul ha (hy w hw)

omit [IsCMField E] in
theorem tens_smul_le (h : ∀ b ∈ 𝔟, ∀ y ∈ tens Λ₁ N, (b : E) • y ∈ tens Λ₂ N) :
    tens Λ₁ (𝔟 • N) ≤ tens Λ₂ N := by
  refine tens_le fun v hv u hu => ?_
  refine Submodule.smul_induction_on hu (fun b hb u hu => ?_) fun x y hx hy => ?_
  · have e : vecMulVec v (b • u) = (b : E) • vecMulVec v u := by
      ext i j
      change v i * ((b : E) * u j) = (b : E) * (v i * u j)
      ring
    rw [e]
    exact h b hb _ (pure_mem hv hu)
  · rw [vecMulVec_add]; exact add_mem hx hy

omit [IsCMField E] in
theorem smul_tens_left {b : E} (h : ∀ v ∈ Λ₁, b • v ∈ Λ₂) (hy : y ∈ tens Λ₁ N) :
    b • y ∈ tens Λ₂ N := by
  refine tens_le (H := (tens Λ₂ N).comap (DistribMulAction.toAddMonoidHom _ b))
    (fun v hv u hu => ?_) hy
  change b • vecMulVec v u ∈ tens Λ₂ N
  rw [← smul_vecMulVec]
  exact pure_mem (h v hv) hu

omit [IsCMField E] in
theorem tens_shift (h : 𝔟 • Λ₁ ≤ Λ₂) : tens Λ₁ (𝔟 • N) ≤ tens Λ₂ N :=
  tens_smul_le fun _ hb _ hy => smul_tens_left (fun _ hv => h (Submodule.smul_mem_smul hb hv)) hy

omit [IsCMField E] in
theorem mul_tens {A : Matrix (Fin n) (Fin n) E} (h : ∀ v ∈ Λ₁, A *ᵥ v ∈ Λ₂) (hy : y ∈ tens Λ₁ N) :
    A * y ∈ tens Λ₂ N := by
  refine tens_le (H := (tens Λ₂ N).comap (AddMonoidHom.mk' (fun y => A * y)
    fun a b => Matrix.mul_add A a b)) (fun v hv u hu => ?_) hy
  change A * vecMulVec v u ∈ tens Λ₂ N
  rw [mul_vecMulVec]
  exact pure_mem (h v hv) hu

omit [IsCMField E] in
theorem int_smul_tens (a : 𝓞 E) (hy : y ∈ tens Λ N) : (a : E) • y ∈ tens Λ N :=
  smul_tens_left (fun _ hv => Λ.smul_mem a hv) hy

omit [IsCMField E] in

theorem glue {s : 𝓞 E} (hs : IsCoprime (Ideal.span {s}) 𝔪) (h1 : (s : E) • y ∈ tens Λ N)
    (h2 : ∀ m ∈ 𝔪, (m : E) • (m : E) • y ∈ tens Λ N) : y ∈ tens Λ N := by
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have e' : (a : E) * s + m = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) e
  have : y = ((a * (1 + m) : 𝓞 E) : E) • (s : E) • y + (m : E) • (m : E) • y := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((a * (1 + m) : 𝓞 E) : E) * s + (m : E) * m = 1 := by
      push_cast
      linear_combination (1 + (m : E)) * e'
    rw [this, one_smul]
  rw [this]
  exact add_mem (int_smul_tens _ h1) (h2 m hm)

theorem rows_loc (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) (hN : Near X 𝔪 N)
    (hy : y ∈ tens Λ (𝔟 • N)) (k : Fin n) : y k ∈ Lev.loc 𝔪 (𝔟 • X.Λ) := by
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM
  obtain ⟨t, ht, h1, -⟩ := hN
  refine ⟨t * s, cop_mul ht hs, ?_⟩
  rw [mul_smul]
  exact mul_smul_mem h1 𝔟 ((h _ y).1 hy k)

theorem loc_tens (hΛ : Λ ∈ Vset E n M) (hM : (M : 𝓞 E) ∈ 𝔪) (hN : Near X 𝔪 N)
    (hk : ∀ k, y k ∈ Lev.loc 𝔪 (𝔟 • X.Λ)) :
    ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ (s : E) • y ∈ tens Λ (𝔟 • N) := by
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM
  obtain ⟨t, ht, -, h1⟩ := hN
  choose p hp hq using hk
  have hP : IsCoprime (Ideal.span {∏ k, p k}) 𝔪 := by
    rw [← Ideal.prod_span_singleton]
    exact IsCoprime.prod_left fun k _ => hp k
  refine ⟨t * (s * ∏ k, p k), cop_mul ht (cop_mul hs hP), (mem_tens_iff hΛ _ _).2 fun w hw => ?_⟩
  have h2 := (h (𝔟 • X.Λ) (((∏ k, p k : 𝓞 E) : E) • y)).2 (fun k => by
    change (∏ k, p k) • y k ∈ _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Submodule.smul_mem _ _ (hq k)) w hw
  rw [ctr_smul] at h2 ⊢
  change (t * (s * ∏ k, p k)) • ctr y w ∈ _
  rw [mul_smul, mul_smul]
  exact mul_smul_mem h1 𝔟 h2

omit [IsCMField E] in
theorem exists_one (h : IsCoprime 𝔟 𝔪) : ∃ c ∈ 𝔟, 1 - c ∈ 𝔪 ∧ IsCoprime (Ideal.span {c}) 𝔪 := by
  obtain ⟨c, hc, m, hm, e⟩ := Ideal.isCoprime_iff_exists.1 h
  exact ⟨c, hc, by rwa [← e, add_sub_cancel_left], Lev.cop_iff.2 ⟨1, m, hm, by rwa [one_mul]⟩⟩

omit [IsCMField E] in
theorem loc_smul (h : IsCoprime 𝔟 𝔪) {u : Fin r → E} (hu : u ∈ Lev.loc 𝔪 N) :
    u ∈ Lev.loc 𝔪 (𝔟 • N) := by
  obtain ⟨c, hc, -, hc'⟩ := exists_one h
  obtain ⟨s, hs, hu⟩ := hu
  exact ⟨c * s, Lev.cop_mul hc' hs, by rw [mul_smul]; exact Submodule.smul_mem_smul hc hu⟩

omit [IsCMField E] in
theorem loc_glue (h : IsCoprime 𝔞 𝔟) {u : Fin r → E} (hu : u ∈ Lev.loc 𝔞 N)
    (hu' : u ∈ Lev.loc 𝔟 N) : u ∈ Lev.loc (𝔞 * 𝔟) N := by
  obtain ⟨s, hs, hu⟩ := hu
  obtain ⟨t, ht, hu'⟩ := hu'
  obtain ⟨a, b, hab⟩ := Lev.cop_glue h hs ht
  refine ⟨_, hab, ?_⟩
  rw [add_smul, mul_smul, mul_smul]
  exact add_mem (N.smul_mem _ hu) (N.smul_mem _ hu')

theorem cong_zero {u : Fin r → E} : Cong X 𝔪 u 0 ↔ u ∈ Lev.loc 𝔪 (𝔪 • X.Λ) := by
  rw [Lev.cong_iff, sub_zero]

end Tensor

section Diagonal

def lowD (r n : ℕ) (c : E) : Matrix (Fin n) (Fin n) E :=
  Matrix.diagonal fun k : Fin n => if (k : ℕ) < r then 1 else c

omit [NumberField E] [IsCMField E] in
theorem lowD_row {m : ℕ} (c : E) (y : Matrix (Fin n) (Fin m) E) (k : Fin n) :
    (lowD r n c * y) k = (if (k : ℕ) < r then 1 else c) • y k := by
  funext j
  simp only [lowD, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]

omit [NumberField E] [IsCMField E] in
theorem lowD_mul {c c' : E} (h : c * c' = 1) : lowD r n c * lowD r n c' = 1 := by
  rw [lowD, lowD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  split_ifs <;> simp [h]

end Diagonal

section Move

variable {D : SW.Level X} {M : ℕ} {𝔐 𝔍 𝔞 : Ideal (𝓞 E)} {α : 𝓞 E} {Λ Λ' Λ'' : Lt E n}
  {L N : Lt E r} {y : Matrix (Fin n) (Fin r) E}

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q :=
  fun _ ha => Lev.mem_conjI.2 (h (Lev.mem_conjI.1 ha))

theorem nat_mem_conjI {P : Ideal (𝓞 E)} (h : (M : 𝓞 E) ∈ P) : (M : 𝓞 E) ∈ conjI P :=
  Lev.mem_conjI.2 (by rwa [map_natCast])

theorem quot_mul (h0 : α ≠ 0) :
    cc (α : E) / (α : E) * ((α : E) / cc (α : E)) = 1 := by
  have h1 : (α : E) ≠ 0 := by exact_mod_cast h0
  have h2 : cc (α : E) ≠ 0 := by simpa [cc] using h1
  field_simp

omit [IsCMField E] in
theorem exists_cop (h𝔞 : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)})) :
    ∃ a ∈ 𝔞, ∀ P : Ideal (𝓞 E), (M : 𝓞 E) ∈ P → IsCoprime (Ideal.span {a}) P := by
  obtain ⟨a, ha, h, -⟩ := exists_one h𝔞
  refine ⟨a, ha, fun P hP => Lev.cop_iff.2 ⟨1, 1 - a, ?_, by ring⟩⟩
  exact (Ideal.span_singleton_le_iff_mem _).2 hP h

theorem smul_quot (h0 : α ≠ 0) (hα : Ideal.span {α} = 𝔍 * 𝔞) {a j : 𝓞 E} (ha : a ∈ 𝔞)
    (hj : j ∈ 𝔍) {u : Fin r → E} (hu : u ∈ N) :
    a • (cc (α : E) / (α : E)) • j • u ∈ N := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hα ▸ Ideal.mul_mem_mul hj ha)
  have h1 : (α : E) ≠ 0 := by exact_mod_cast h0
  have h2 : (c : E) * α = j * a := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hc
  have : a • (cc (α : E) / (α : E)) • j • u = (c * Lev.bar α) • u := by
    funext i
    change (a : E) * (cc (α : E) / α * ((j : E) * u i)) = ((c * Lev.bar α : 𝓞 E) : E) * u i
    rw [show ((c * Lev.bar α : 𝓞 E) : E) = c * cc (α : E) from by rw [← Lev.coe_bar]; rfl]
    field_simp
    linear_combination (-(cc (α : E)) * u i) * h2
  rw [this]
  exact N.smul_mem _ hu

theorem smul_quot' (h0 : α ≠ 0) (hα : Ideal.span {α} = 𝔍 * 𝔞) {a : 𝓞 E} (ha : a ∈ 𝔞)
    {u : Fin r → E} (hu : u ∈ 𝔍 • N) : a • (cc (α : E) / (α : E)) • u ∈ N := by
  refine Submodule.smul_induction_on hu (fun j hj u hu => smul_quot h0 hα ha hj hu)
    fun x y hx hy => ?_
  rw [smul_add, smul_add]; exact add_mem hx hy

theorem move (hm : Moves (lowD r n (cc (α : E) / (α : E))) Λ Λ'') (hy : y ∈ tens Λ N) :
    lowD r n (cc (α : E) / (α : E)) * y ∈ tens Λ'' N :=
  mul_tens (fun v hv => (hm v).1 hv) hy

theorem move' (h0 : α ≠ 0) (hm : Moves (lowD r n (cc (α : E) / (α : E))) Λ Λ'')
    (hy : y ∈ tens Λ'' N) : lowD r n ((α : E) / cc (α : E)) * y ∈ tens Λ N :=
  mul_tens (fun v hv => (hm _).2 (by
    rwa [Matrix.mulVec_mulVec, lowD_mul (quot_mul h0), Matrix.one_mulVec])) hy

theorem move_move' (h0 : α ≠ 0) (y : Matrix (Fin n) (Fin r) E) :
    lowD r n (cc (α : E) / (α : E)) * (lowD r n ((α : E) / cc (α : E)) * y) = y := by
  rw [← Matrix.mul_assoc, lowD_mul (quot_mul h0), Matrix.one_mul]

theorem smul_moved (hM : (M : 𝓞 E) ∈ 𝔍) (h0 : α ≠ 0) (hα : Ideal.span {α} = 𝔍 * 𝔞)
    (h𝔞 : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)})) (hΛ : Λ ∈ Vset E n M) (hΛ' : Λ' ∈ Vset E n M)
    {M'' : ℕ} (hΛ'' : Λ'' ∈ Vset E n M'') (hm : Moves (lowD r n (cc (α : E) / (α : E))) Λ Λ'')
    (h1 : (𝔍 * conjI 𝔍) • Λ'' ≤ Λ') :
    ∀ j ∈ 𝔍, ∀ z ∈ tens Λ'' N, (j : E) • z ∈ tens Λ' N := by
  intro j hj z hz
  have hM' := nat_mem_conjI hM
  obtain ⟨a, ha, ha'⟩ := exists_cop h𝔞
  obtain ⟨s, hs, h⟩ := what₂ (r := r) hΛ hM'
  obtain ⟨t, ht, h'⟩ := what₂ (r := r) hΛ' hM'
  refine glue (cop_mul ht (cop_mul (ha' _ hM') hs)) ?_ fun m hm => int_smul_tens _ ?_
  · rw [mem_tens_iff hΛ']
    intro w hw
    have h2 := (h' N (((a * s : 𝓞 E) : E) • (j : E) • z)).2 (fun k => ?_) w hw
    · rw [ctr_smul] at h2 ⊢
      rw [← Lev.O_smul] at h2 ⊢
      rwa [mul_smul]
    · have h3 := (h N _).1 (move' h0 hm hz) k
      change (a * s) • j • z k ∈ N
      rw [← move_move' h0 z, lowD_row]
      generalize (lowD r n ((α : E) / cc (α : E)) * z) k = u at h3
      split_ifs
      · rw [one_smul, mul_smul, smul_comm s j]
        exact N.smul_mem _ (N.smul_mem _ h3)
      · have := smul_quot h0 hα ha hj h3
        rwa [mul_smul, smul_comm j, smul_comm s, smul_comm s]
  · refine tens_shift h1 ?_
    rw [mul_comm, Submodule.mul_smul]
    exact smul_tens hΛ'' hm (smul_tens hΛ'' hj hz)

theorem tens_le_sh (Λ : Lt E n) : tens Λ (D.𝔪 • L) ≤ tens Λ (D.sh L) :=
  tens_mono Λ (Lev.smul_le_idq _ _ _)

theorem conj_smul_sh : conjI D.𝔪 • D.sh L ≤ D.𝔪 • L :=
  Submodule.smul_le.2 fun b hb _ hv => hv b hb

theorem cong_of_sh (hM : (M : 𝓞 E) ∈ D.𝔪) (hΛ' : Λ' ∈ Vset E n M) (hL : L ∈ D.lats)
    (hy : y ∈ tens Λ' (D.sh L)) (k : Fin n) : Cong X D.𝔪 (y k) 0 := by
  obtain ⟨c, hc, -, hc'⟩ := exists_one D.cop.symm
  exact cong_zero.2 (Lev.loc_loc hc' (rows_loc hΛ' hM (near_of_mem hL)
    (tens_mono _ conj_smul_sh (smul_tens hΛ' hc hy)) k))

variable (hM : (M : 𝓞 E) ∈ D.𝔪) (h𝔪 : D.𝔪 = 𝔐 * 𝔍) (hc : IsCoprime 𝔐 𝔍) (h0 : α ≠ 0)
  (hα : Ideal.span {α} = 𝔍 * 𝔞) (h𝔞 : IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}))
  (hΛ : Λ ∈ Vset E n M) (hΛ' : Λ' ∈ Vset E n M) (hΛ'' : Λ'' ∈ Vset E n 1)
  (hm : Moves (lowD r n (cc (α : E) / (α : E))) Λ Λ'')
  (h1 : (𝔍 * conjI 𝔍) • Λ'' ≤ Λ') (h2 : (𝔍 * conjI 𝔍) • Λ' ≤ Λ'') (hL : L ∈ D.lats)

include hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 hL in

theorem moved_mem (hy : y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L))
    (hk : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X D.𝔪 (y k) 0) :
    lowD r n (cc (α : E) / (α : E)) * y ∈ tens Λ' ((Ideal.span {2} * conjI D.𝔪) • L) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 ((lowD r n (cc (α : E) / (α : E)) * y) k) 0 := by
  have hJ : D.𝔪 ≤ 𝔍 := h𝔪 ▸ Ideal.mul_le_right
  obtain ⟨a, ha, ha'⟩ := exists_cop h𝔞
  have low : ∀ k : Fin n, r ≤ (k : ℕ) →
      (lowD r n (cc (α : E) / (α : E)) * y) k ∈ Lev.loc D.𝔪 (𝔐 • X.Λ) := fun k hk' => by
    obtain ⟨s, hs, h⟩ := cong_zero.1 (hk k hk')
    rw [lowD_row, if_neg (not_lt.2 hk')]
    refine ⟨a * s, cop_mul (ha' _ hM) hs, ?_⟩
    rw [h𝔪, mul_comm 𝔐, Submodule.mul_smul] at h
    rw [mul_smul, smul_comm s]
    exact smul_quot' h0 hα ha h
  refine ⟨?_, fun k hk' => ?_⟩
  · obtain ⟨s, hs, h⟩ := loc_tens (y := lowD r n (cc (α : E) / (α : E)) * y)
      (𝔟 := Ideal.span {2} * conjI D.𝔪) hΛ' hM (near_of_mem hL) fun k => by
        by_cases hk' : (k : ℕ) < r
        · rw [lowD_row, if_pos hk', one_smul]
          exact rows_loc hΛ hM (near_of_mem hL) hy k
        · exact loc_smul (cop_level D)
            (Lev.loc_mono Submodule.smul_le_right (low k (not_lt.1 hk')))
    exact glue hs h fun m hm' => int_smul_tens _
      (smul_moved (hJ hM) h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 m (hJ hm') _ (move hm hy))
  · obtain ⟨s, hs, h⟩ := low k hk'
    exact cong_zero.2 ⟨s, (h𝔪 ▸ hs).of_mul_right_left, h⟩

include hM h𝔪 hc h0 hα h𝔞 hΛ hΛ' hΛ'' hm h2 hL in

theorem mem_moved (hy : y ∈ tens Λ' ((Ideal.span {2} * conjI D.𝔪) • L))
    (hu : ∀ k : Fin n, (k : ℕ) < r → Cong X D.𝔪 (y k) 0)
    (hk : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0) : y ∈ tens Λ'' (D.sh L) := by
  have hJ : D.𝔪 ≤ 𝔍 := h𝔪 ▸ Ideal.mul_le_right
  have hαJ : α ∈ 𝔍 := Ideal.mul_le_left (hα ▸ Ideal.mem_span_singleton_self α)
  have hb : IsCoprime (Ideal.span {Lev.bar α}) D.𝔪 := by
    obtain ⟨a, ha, ha'⟩ := exists_cop h𝔞
    have h3 : IsCoprime (Ideal.span {α}) (conjI D.𝔪) := by
      rw [hα]
      have h4 : IsCoprime (𝔐 * 𝔍) (conjI D.𝔪) := by rw [← h𝔪]; exact D.cop
      refine IsCoprime.mul_left h4.of_mul_left_right ?_
      obtain ⟨x, m, hm, e⟩ := Lev.cop_iff.1 (ha' _ (nat_mem_conjI hM))
      exact Ideal.isCoprime_iff_exists.2 ⟨_, 𝔞.mul_mem_left x ha, m, hm, e⟩
    obtain ⟨x, m, hm, e⟩ := Lev.cop_iff.1 h3
    exact Lev.cop_iff.2 ⟨Lev.bar x, Lev.bar m, Lev.mem_conjI.1 hm, by
      rw [← map_mul, ← map_add, e, map_one]⟩
  obtain ⟨s, hs, h⟩ := loc_tens (y := lowD r n ((α : E) / cc (α : E)) * y) (𝔟 := D.𝔪) hΛ hM
    (near_of_mem hL) fun k => by
      rw [lowD_row]
      split_ifs with hk'
      · rw [one_smul]; exact cong_zero.1 (hu k hk')
      · have h3 : y k ∈ Lev.loc 𝔍 (𝔐 • X.Λ) := by
          obtain ⟨t, ht, h⟩ := rows_loc hΛ' hM (near_of_mem hL) hy k
          exact loc_smul hc ⟨t, (h𝔪 ▸ ht).of_mul_right_right, Submodule.smul_le_right h⟩
        obtain ⟨t, ht, h⟩ := loc_glue hc (cong_zero.1 (hk k (not_lt.1 hk'))) h3
        refine ⟨Lev.bar α * t, cop_mul hb (h𝔪 ▸ ht), ?_⟩
        have e : (Lev.bar α * t) • ((α : E) / cc (α : E)) • y k = α • t • y k := by
          have h4 : (α : E) ≠ 0 := by exact_mod_cast h0
          have h5 : cc (α : E) ≠ 0 := by simpa [cc] using h4
          funext i
          change ((Lev.bar α * t : 𝓞 E) : E) * ((α : E) / cc (α : E) * y k i) =
            (α : E) * ((t : E) * y k i)
          rw [show ((Lev.bar α * t : 𝓞 E) : E) = cc (α : E) * t from by rw [← Lev.coe_bar]; rfl]
          field_simp
        rw [e, h𝔪, mul_comm 𝔐, Submodule.mul_smul]
        exact Submodule.smul_mem_smul hαJ h
  refine glue hs ?_ fun m hm' => tens_le_sh _ (smul_tens hΛ'' hm' (tens_shift h2 ?_))
  · have := move hm (tens_le_sh _ h)
    rwa [Matrix.mul_smul, move_move' h0] at this
  · rw [Submodule.mul_smul]
    exact smul_tens hΛ' (hJ hm') (tens_mono _
      (Submodule.smul_mono_left (Ideal.mul_le_right.trans (conjI_mono hJ))) hy)

include hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 in

theorem exists_low (hy : y ∈ tens Λ'' (D.sh L)) :
    ∃ δ ∈ tens Λ'' ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L), y - δ ∈ tens Λ' (D.sh L) := by
  have hJ : D.𝔪 ≤ 𝔍 := h𝔪 ▸ Ideal.mul_le_right
  obtain ⟨c, hc, hc', -⟩ := exists_one (cop_level D)
  refine ⟨(c : E) • (c : E) • y, ?_, ?_⟩
  · rw [Submodule.mul_smul]
    exact smul_tens hΛ'' hc (tens_mono _ conj_smul_sh (smul_tens hΛ'' (Ideal.mul_le_right hc) hy))
  · have := smul_moved (hJ hM) h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 ((1 + c) * (1 - c))
      (hJ (Ideal.mul_mem_left _ _ hc')) y hy
    convert this using 1
    push_cast
    rw [smul_smul]
    conv_lhs => rw [← one_smul E y, smul_smul, mul_one, ← sub_smul]
    congr 1
    ring

include hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 hL in
theorem low_laws (hy : y ∈ tens Λ'' ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)) :
    y ∈ tens Λ' ((Ideal.span {2} * conjI D.𝔪) • L) ∧
      (∀ k : Fin n, (k : ℕ) < r → Cong X D.𝔪 (y k) 0) ∧ ∀ k : Fin n, Cong X 𝔐 (y k) 0 := by
  have hJ : D.𝔪 ≤ 𝔍 := h𝔪 ▸ Ideal.mul_le_right
  have hM' : (M : 𝓞 E) ∈ 𝔐 := Ideal.mul_le_left (h𝔪 ▸ hM)
  have h3 : y ∈ tens Λ' ((Ideal.span {2} * conjI D.𝔪 * 𝔐) • L) := by
    refine tens_smul_le (smul_moved (hJ hM) h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1) ?_
    rwa [← Submodule.mul_smul, mul_comm 𝔍, mul_assoc, ← h𝔪]
  refine ⟨tens_mono _ (Submodule.smul_mono_left Ideal.mul_le_left) h3, fun k hk => ?_,
    fun k => ?_⟩
  · have := cong_of_mem (y' := 0) hΛ hM (near_of_mem hL) (by rw [sub_zero]; exact move' h0 hm hy) k
    rwa [lowD_row, if_pos hk, one_smul] at this
  · obtain ⟨s, hs, h⟩ := near_of_mem hL
    exact cong_of_mem (y' := 0) hΛ' hM' ⟨s, (h𝔪 ▸ hs).of_mul_right_left, h⟩
      (by rw [sub_zero]; exact h3) k

end Move

section Datum

variable {D : SW.Level X} {𝔐 : Ideal (𝓞 E)} {hn : r ≤ n} {y y' : Matrix (Fin n) (Fin r) E}

theorem datF_eq {κ : D.J} (h1 : D.Red (fun i => y (Fin.castLE hn i)) κ)
    (h2 : ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0) : datF D 𝔐 hn y = (D.lam κ : ℂˣ) := by
  rw [datF, dif_pos ⟨⟨κ, h1⟩, h2⟩]
  congr 2
  exact Subtype.ext (Lev.red_unique (Exists.choose_spec (⟨κ, h1⟩ :
    ∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k)) h1)

theorem of_datF_ne (h : datF D 𝔐 hn y ≠ 0) :
    (∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin n, r ≤ (k : ℕ) → Cong X 𝔐 (y k) 0 := by
  by_contra h'
  exact h (dif_neg h')

theorem dat_eq : D.dat hn y = datF D D.𝔪 hn y := rfl

theorem cong_of_le {𝔍 : Ideal (𝓞 E)} {u v : Fin r → E} (h : Cong X (𝔐 * 𝔍) u v) :
    Cong X 𝔐 u v := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs.of_mul_right_left, Submodule.smul_mono_left Ideal.mul_le_left h⟩

theorem datF_congr {𝔍 : Ideal (𝓞 E)} (h𝔪 : D.𝔪 = 𝔐 * 𝔍) (h : ∀ k, Cong X D.𝔪 (y k) (y' k)) :
    datF D 𝔐 hn y = datF D 𝔐 hn y' := by
  have key : ∀ y y' : Matrix (Fin n) (Fin r) E, (∀ k, Cong X D.𝔪 (y k) (y' k)) →
      datF D 𝔐 hn y' ≠ 0 → datF D 𝔐 hn y = datF D 𝔐 hn y' := fun y y' h h0 => by
    obtain ⟨⟨κ, h1⟩, h2⟩ := of_datF_ne h0
    rw [datF_eq h1 h2, datF_eq (red_congr (fun i => h _) h1)
      fun k hk => cong_trans (cong_of_le (h𝔪 ▸ h k)) (h2 k hk)]
  by_cases h0 : datF D 𝔐 hn y' = 0
  · by_contra h1
    exact h1 (key y' y (fun k => cong_symm (h k)) (h0 ▸ h1)).symm
  · exact key y y' h h0

theorem cong_add {𝔪 : Ideal (𝓞 E)} {u v u' v' : Fin r → E} (h : Cong X 𝔪 u v)
    (h' : Cong X 𝔪 u' v') : Cong X 𝔪 (u + u') (v + v') := by
  rw [Lev.cong_iff, add_sub_add_comm]
  exact add_mem (Lev.cong_iff.1 h) (Lev.cong_iff.1 h')

theorem cong_sub {𝔪 : Ideal (𝓞 E)} {u v u' v' : Fin r → E} (h : Cong X 𝔪 u v)
    (h' : Cong X 𝔪 u' v') : Cong X 𝔪 (u - u') (v - v') := by
  rw [Lev.cong_iff, sub_sub_sub_comm]
  exact sub_mem (Lev.cong_iff.1 h) (Lev.cong_iff.1 h')

end Datum

section Vacua

variable {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
  (he : Even n)

theorem heisG_sum' {ι : Type} (y : Matrix (Fin n) (Fin r) E) (s : Finset ι) (f : ι → TF n g) :
    heisG X bas y (∑ i ∈ s, f i) = ∑ i ∈ s, heisG X bas y (f i) := by
  funext x; simp [heisG, heisS, Finset.sum_mul]

theorem ip_sum {ι : Type} (s : Finset ι) (f : ι → TF n g) (hf : ∀ i, IsSB (f i)) {v : TF n g}
    (hv : IsSB v) : SW.ip (∑ i ∈ s, f i) v = ∑ i ∈ s, SW.ip (f i) v := by
  induction s using Finset.induction_on with
  | empty => simpa using TensVac.ip_smul_left 0 hv hv
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      TensVac.ip_add_left (hf a) (isSB_sum s f hf) hv, ih]

include idx hs he

theorem sum_classes {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}
    (hA : TensVac.Good X w A) {v v' : TF n g} (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v')
    [Fintype (A ⧸ A'.addSubgroupOf A)] (δ : A ⧸ A'.addSubgroupOf A → A)
    (hδ : ∀ q, QuotientAddGroup.mk (δ q) = q) :
    ∑ q, epsW X w (δ q : Matrix (Fin n) (Fin r) E) • heisG X bas (δ q) v' =
      ((A'.relIndex A : ℕ) * SW.ip v' v) • v := by
  have hsb := fun q => TensVac.rho_sb (w := w) idx hs he (δ q : Matrix (Fin n) (Fin r) E) hv'.1
  have key : ∀ a b : A, (QuotientAddGroup.mk a : A ⧸ A'.addSubgroupOf A) = QuotientAddGroup.mk b →
      epsW X w (b : Matrix (Fin n) (Fin r) E) • heisG X bas b v' =
        epsW X w (a : Matrix (Fin n) (Fin r) E) • heisG X bas a v' := fun a b h => by
    have h1 : ((-a + b : A) : Matrix (Fin n) (Fin r) E) ∈ A' :=
      AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 h)
    have h2 := hA.rho_rho idx hs he a.2 (-a + b).2 hv'.1
    rw [hv'.2.2 _ h1] at h2
    rw [h2]
    simp
  rw [hA.uniq hs hv (isSB_sum _ _ hsb), ip_sum _ _ hsb hv.1]
  · congr 1
    rw [Finset.sum_congr rfl (g := fun _ => SW.ip v' v), Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    · rfl
    · intro q _
      rw [← TensVac.rho_ip (w := w) idx hs he (δ q) hv'.1 hv.1, hv.2.2 _ (δ q).2]
  · intro a ha
    rw [heisG_sum', Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk ⟨a, ha⟩)) _ _ fun q => ?_
    rw [hA.rho_rho idx hs he ha (δ q).2 hv'.1]
    have := key (δ (QuotientAddGroup.mk ⟨a, ha⟩ + q)) (⟨a, ha⟩ + δ q)
      (by rw [hδ, QuotientAddGroup.mk_add, hδ])
    rw [AddSubgroup.coe_add] at this
    rw [Equiv.coe_addLeft]
    exact this

theorem heis_heis {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r} (hL : SelfD X L)
    {𝔠 : Ideal (𝓞 E)} {y δ : Matrix (Fin n) (Fin r) E}
    (hy : y ∈ tens Λ ((Ideal.span {2} * 𝔠) • L)) (hδ : δ ∈ tens Λ ((Ideal.span {2} * 𝔠) • L))
    {v : TF n g} (hv : IsSB v) : heisG X bas y (heisG X bas δ v) = heisG X bas (y + δ) v := by
  obtain ⟨y', hy', rfl⟩ := half_mem hΛ hy
  obtain ⟨k, hk⟩ := (tens_selfDual hΛ hL y').1 (tens_mono Λ Submodule.smul_le_right hy') _
    (tens_mono Λ Submodule.smul_le_right hδ)
  have h3 : ∑ i, EF X ((2 • y') i) (δ i) = 2 * k := by
    rw [← hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (2 • y') i = 2 • y' i := rfl
    rw [e, EF_eq_bilin, EF_eq_bilin, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [(TensVac.laws idx hs he _ hv).2.2.1, h3,
    show -(π * I * (((2 : ℚ) * k : ℚ) : ℂ)) = ((-k : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, one_smul]

theorem phiF_eq_sum {D : SW.Level X} {M : ℕ} {Λ : Lt E n} {L : Lt E r} {𝔐 𝔍 : Ideal (𝓞 E)}
    (h𝔪 : D.𝔪 = 𝔐 * 𝔍) (hn : r ≤ n)
    (hM : (M : 𝓞 E) ∈ D.𝔪) (hΛ : Λ ∈ Vset E n M) (hL : L ∈ D.lats) (hS : SelfD X (D.sh L))
    (v₀ : Lt E r → TF n g)
    (hv : IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))))
    {ι : Type} [Fintype ι] (f : ι → Matrix (Fin n) (Fin r) E)
    (h1 : ∀ i, f i ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L))
    (h2 : ∀ i j, (∀ k, Cong X D.𝔪 (f i k) (f j k)) → i = j)
    (h3 : ∀ y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L), datF D 𝔐 hn y ≠ 0 →
      ∃ i, ∀ k, Cong X D.𝔪 (y k) (f i k)) :
    phiF bas D 𝔐 hn v₀ L Λ = ∑ i, datF D 𝔐 hn (f i) • heisG X bas (f i)
      (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) := by
  unfold phiF
  generalize unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) = v at hv ⊢
  let q : ι → tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _ :=
    fun i => QuotientAddGroup.mk ⟨f i, h1 i⟩
  have hq : ∀ c i, c = q i ↔ f i - (c.out : Matrix (Fin n) (Fin r) E) ∈
      tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L) := fun c i => by
    conv_lhs => rw [← QuotientAddGroup.out_eq' c]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    rfl
  have hc : ∀ i k, Cong X D.𝔪 (f i k) (((q i).out : Matrix (Fin n) (Fin r) E) k) := fun i =>
    cong_of_mem hΛ hM (near_of_mem hL) ((hq _ i).1 rfl)
  have hinj : Function.Injective q := fun i j e =>
    h2 i j fun k => cong_trans (hc i k) (e ▸ cong_symm (hc j k))
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image q), Finset.sum_image hinj.injOn]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [datF_congr h𝔪 (hc i), ← heis_add idx hs he D hΛ hL.1 hS hv (q i).out.2 ((hq _ i).1 rfl),
      add_sub_cancel]
  · intro c hc0
    obtain ⟨i, hi⟩ := h3 (c.out : Matrix (Fin n) (Fin r) E) c.out.2
      fun h => hc0 (by simp only [h, zero_smul])
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, ((hq c i).2 ?_).symm⟩)
    exact mem_of_cong hΛ hM (near_of_mem hL) (cop_level D) (sub_mem (h1 i) c.out.2)
      fun k => cong_symm (hi k)

theorem ip_unitv {D : SW.Level X} {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {S : Lt E r}
    (hS : SelfD X S) {v₀ : TF n g} (h0 : IsVac X bas D.w (tens (stdL E n) S) v₀) :
    ∃ a : ℝ, 0 < a ∧ projA X bas D.w (tens Λ S) v₀ =
      (a : ℂ) • unitv (projA X bas D.w (tens Λ S) v₀) := by
  obtain ⟨v, hv⟩ := (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M Λ hΛ).1
  obtain ⟨h1, h2⟩ := unitv_proj idx hs he hΛ hS h0 hv
  refine ⟨‖SW.ip v₀ v‖, norm_pos_iff.2 h1, ?_⟩
  have h3 : ((‖SW.ip v₀ v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h1
  rw [h2, smul_smul, mul_div_cancel₀ _ h3]
  exact (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS M Λ hΛ).2.2.1 v₀ h0.1 v hv

theorem ip_pos {D : SW.Level X} {Λ' Λ'' : Lt E n} (hΛ' : Λ' ∈ Vset E n 1) (hΛ'' : Λ'' ∈ Vset E n 1)
    {S : Lt E r} (hS : SelfD X S) {v₀ : TF n g} (h0 : IsVac X bas D.w (tens (stdL E n) S) v₀)
    (h : tens Λ' S ≤ (tens Λ' S ⊓ tens (stdL E n) S) ⊔ (tens Λ' S ⊓ tens Λ'' S)) :
    (tens Λ'' S).relIndex (tens Λ' S) ≠ 0 ∧
      SW.ip (unitv (projA X bas D.w (tens Λ' S) v₀)) (unitv (projA X bas D.w (tens Λ'' S) v₀)) =
        (Real.sqrt (((tens Λ'' S).relIndex (tens Λ' S) : ℝ)⁻¹) : ℝ) := by
  have hv' := isVac_unitv idx hs he hΛ' hS h0
  have hv'' := isVac_unitv idx hs he hΛ'' hS h0
  obtain ⟨a, ha, ha'⟩ := ip_unitv idx hs he hΛ' hS h0
  obtain ⟨b, hb, hb'⟩ := ip_unitv idx hs he hΛ'' hS h0
  have h1 := ProjProj.proj_proj E r X g bas idx n hs he D.w D.w_int D.w_tr S S S hS hS hS _
    (Base.stdL_mem_Vset n 1) _ hΛ' _ hΛ'' h v₀ h0
  have h2 := (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS 1 _ hΛ').2.2.2 S hS _
    hΛ'' _ _ hv' hv''
  generalize unitv (projA X bas D.w (tens Λ' S) v₀) = v' at *
  generalize unitv (projA X bas D.w (tens Λ'' S) v₀) = v'' at *
  rw [ha', hb', (TensVac.vacua E r X g bas idx n hs he D.w D.w_int D.w_tr S hS 1 _ hΛ'').2.2.1 _
    (TensVac.sb_smul _ hv'.1) _ hv'', TensVac.ip_smul_left _ hv'.1 hv''.1] at h1
  have h3 := congrArg (SW.ip · v'') h1
  simp only [TensVac.ip_smul_left _ hv''.1 hv''.1, hv''.2.1, mul_one] at h3
  have h4 : SW.ip v' v'' = ((b / a : ℝ) : ℂ) := by
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    rw [← h3, mul_div_cancel_left₀ _ this]
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (div_pos hb ha).le] at h2
  refine ⟨fun h => by simp [h] at h2, ?_⟩
  rw [h4, ← eq_inv_of_mul_eq_one_right h2, Real.sqrt_sq (div_pos hb ha).le]

end Vacua

theorem mem_Vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem le_sup_inf {M : ℕ} {Λ' Λ'' : Lt E n} {𝔭 : Ideal (𝓞 E)} (hΛ' : Λ' ∈ Vset E n M)
    (hM : ((M : 𝓞 E) * M) ∈ 𝔭) (h2 : 𝔭 • Λ' ≤ Λ'') (S : Lt E r) :
    tens Λ' S ≤ (tens Λ' S ⊓ tens (stdL E n) S) ⊔ (tens Λ' S ⊓ tens Λ'' S) := by
  intro y hy
  obtain ⟨s, -, hs, h1, -⟩ := hΛ'.2.2
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) ((M : ℤ) * M) :=
    (Nat.isCoprime_iff_coprime.2 hs).mul_right (Nat.isCoprime_iff_coprime.2 hs)
  have e : y = a • (s : E) • y + b • (((M : 𝓞 E) * M : 𝓞 E) : E) • y := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * (((M : 𝓞 E) * M : 𝓞 E) : E) = 1 := by
      have := congrArg (Int.cast : ℤ → E) hab
      push_cast at this ⊢
      exact this
    rw [this, one_smul]
  rw [e]
  refine AddSubgroup.add_mem_sup (zsmul_mem (AddSubgroup.mem_inf.2 ⟨?_, smul_tens_left h1 hy⟩) _)
    (zsmul_mem (AddSubgroup.mem_inf.2 ⟨int_smul_tens _ hy, smul_tens_left
      (fun v hv => h2 (Submodule.smul_mem_smul hM hv)) hy⟩) _)
  exact int_smul_tens (s : 𝓞 E) hy

theorem sum_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, ∀ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' → (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' → (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' → ∃ t : ℂ, t ≠ 0 ∧ ∀ L ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ ∑ y ∈ s, D.dat hn y • heisG X bas (h * y) (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) = t • phiF bas D 𝔐 hn v₀ L Λ' := by
  intro E _ _ _ r X g bas idx n hs he D hn M 𝔐 𝔍 𝔞 α _ hM h𝔪 hc h0 hα h𝔞 v₀ hv₀ h hh Λ hΛ Λ' hΛ'
    Λ'' hΛ'' hm h1 h2
  obtain rfl : h = lowD r n (cc (α : E) / (α : E)) := hh
  obtain ⟨hX, -, -, hl, -⟩ := level_laws E r X g bas idx n hs he D hn
  haveI := finite_J D
  haveI : Fintype D.J := Fintype.ofFinite _
  have hJ : D.𝔪 ≤ 𝔍 := h𝔪 ▸ Ideal.mul_le_right
  have hΛ₁ := mem_Vset_one hΛ'
  let c : ℂ := ((Λ'.toAddSubgroup.relIndex Λ''.toAddSubgroup ^ r : ℕ) : ℂ) *
    (Real.sqrt (((Λ''.toAddSubgroup.relIndex Λ'.toAddSubgroup ^ r : ℕ) : ℝ)⁻¹) : ℝ)
  suffices H : ∀ L ∈ D.lats, c ≠ 0 ∧ ∃ s : Finset (Matrix (Fin n) (Fin r) E),
      D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y
        (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧
      phiF bas D 𝔐 hn v₀ L Λ' = c • ∑ y ∈ s, D.dat hn y •
        heisG X bas (lowD r n (cc (α : E) / (α : E)) * y)
          (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) by
    refine ⟨c⁻¹, inv_ne_zero (H _ hX).1, fun L hL => ?_⟩
    obtain ⟨hc0, s, e1, e2⟩ := H L hL
    exact ⟨s, e1, by rw [e2, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  intro L hL
  have hS := (hl L hL).1
  have hv := isVac_unitv idx hs he hΛ hS (hv₀ L hL)
  have hv' := isVac_unitv idx hs he hΛ' hS (hv₀ L hL)
  have hv'' := isVac_unitv idx hs he hΛ'' hS (hv₀ L hL)
  have good : ∀ N, SelfD X N → ∀ Λ ∈ Vset E n 1, TensVac.Good X D.w (tens Λ N) :=
    fun N hN Λ hΛ => ⟨tens_fg hΛ hN.1, tens_selfDual hΛ hN,
      fun y hy => epsW_semichar hΛ hN D.w_int D.w_tr hy⟩
  have ind := fun Λ₁ hΛ₁ => (tens_selfDual_semichar_index E r X g bas idx n hs he D.w D.w_int D.w_tr
    _ hS 1 Λ₁ hΛ₁).2.2.2.2.2
  obtain ⟨i1, i2⟩ := ip_pos idx hs he hΛ₁ hΛ'' hS (hv₀ L hL) (le_sup_inf hΛ'
    (Ideal.mul_mem_mul (hJ hM) (nat_mem_conjI (hJ hM))) h2 _)
  have i3 : (tens Λ' (D.sh L)).relIndex (tens Λ'' (D.sh L)) ≠ 0 := fun h => by
    have := (good _ hS _ hΛ'').overlap idx hs he (good _ hS _ hΛ₁) hv'' hv'
    simp [h] at this
  have hc0 : c ≠ 0 := by
    rw [ind _ hΛ₁ _ hΛ''] at i1
    rw [ind _ hΛ'' _ hΛ₁] at i3
    refine mul_ne_zero (Nat.cast_ne_zero.2 i3) ?_
    exact_mod_cast (Real.sqrt_pos.2 (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero i1)))).ne'
  refine ⟨hc0, ?_⟩
  haveI : Finite (tens Λ'' (D.sh L) ⧸ (tens Λ' (D.sh L)).addSubgroupOf (tens Λ'' (D.sh L))) :=
    Nat.finite_of_card_ne_zero i3
  haveI := Fintype.ofFinite
    (tens Λ'' (D.sh L) ⧸ (tens Λ' (D.sh L)).addSubgroupOf (tens Λ'' (D.sh L)))
  have hsh : ∀ Λ : Lt E n, tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L) ≤ tens Λ (D.sh L) :=
    fun Λ => (tens_mono Λ (Submodule.smul_mono_left Ideal.mul_le_right)).trans (tens_le_sh Λ)
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : tens Λ'' (D.sh L) ⧸
      (tens Λ' (D.sh L)).addSubgroupOf (tens Λ'' (D.sh L)) → tens Λ'' (D.sh L),
      (∀ q, QuotientAddGroup.mk (δ q) = q) ∧ ∀ q, (δ q : Matrix (Fin n) (Fin r) E) ∈
        tens Λ'' ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L) := by
    have : ∀ q : tens Λ'' (D.sh L) ⧸ (tens Λ' (D.sh L)).addSubgroupOf (tens Λ'' (D.sh L)),
        ∃ d : tens Λ'' (D.sh L), QuotientAddGroup.mk d = q ∧ (d : Matrix (Fin n) (Fin r) E) ∈
          tens Λ'' ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L) := by
      intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨d, hd, hd'⟩ := exists_low hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 a.2
      refine ⟨⟨d, hsh _ hd⟩, QuotientAddGroup.eq.2 ?_, hd⟩
      rw [neg_add_eq_sub]
      exact hd'
    choose δ hδ hδ' using this
    exact ⟨δ, hδ, hδ'⟩
  have hlow := fun q => low_laws hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 hL (hδ' q)
  have hsum := sum_classes idx hs he (good _ hS _ hΛ'') hv'' hv' δ hδ
  rw [i2, ind _ hΛ₁ _ hΛ'', ind _ hΛ'' _ hΛ₁, Finset.sum_congr rfl
    (g := fun q => heisG X bas (δ q) (unitv (projA X bas D.w (tens Λ' (D.sh L)) (v₀ L))))
    (fun q _ => by
      obtain ⟨z, hz, e⟩ := half_mem hΛ' (hlow q).1
      rw [e, (good _ hL.1 _ hΛ₁).eps_two hs (tens_mono _ Submodule.smul_le_right hz), one_smul])]
    at hsum
  obtain ⟨f, f1, f2, f3, f4⟩ := exists_reps idx hs he hn hM hΛ (near_of_mem hL)
  have hinj : Function.Injective f := fun i j e => f2 i j fun k => e ▸ cong_refl _
  have f5 := fun i => of_datF_ne (D := D) (𝔐 := D.𝔪) (hn := hn) (y := f i) fun h => by
    have := f4 i
    rw [dat_eq, h, norm_zero] at this
    exact zero_ne_one this
  have f6 := fun i => moved_mem hM h𝔪 h0 hα h𝔞 hΛ hΛ' hΛ'' hm h1 hL (f1 i) (f5 i).2
  have up : ∀ (y : Matrix (Fin n) (Fin r) E) q (k : Fin n), (k : ℕ) < r →
      Cong X D.𝔪 ((lowD r n (cc (α : E) / (α : E)) * y + (δ q).1) k) (y k) := fun y q k hk => by
    have := cong_add (cong_refl (X := X) (𝔪 := D.𝔪) (y k)) ((hlow q).2.1 k hk)
    rw [add_zero] at this
    change Cong X D.𝔪 ((lowD r n (cc (α : E) / (α : E)) * y) k + _) _
    rwa [lowD_row, if_pos hk, one_smul]
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.sum_image hinj.injOn]
    exact phi_eq_sum idx hs he hn hM hΛ hL v₀ hv f f1 f2 f3
  rw [Finset.sum_image hinj.injOn, phiF_eq_sum idx hs he h𝔪 hn hM hΛ' hL hS v₀ hv'
    (fun p : D.J × _ => lowD r n (cc (α : E) / (α : E)) * f p.1 + (δ p.2).1)
    (fun p => add_mem (f6 p.1).1 (hlow p.2).1), Fintype.sum_prod_type, Finset.smul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, ← TensVac.heisG_smul, ← hsum, heisG_sum', Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨⟨κ, hκ⟩, h5⟩ := f5 i
    rw [heis_heis idx hs he hΛ' hL.1 (f6 i).1 (hlow q).1 hv'.1, dat_eq, datF_eq hκ h5,
      datF_eq (red_congr (fun a => up _ _ _ a.2) hκ) fun k hk => ?_]
    have := cong_add ((f6 i).2 k hk) ((hlow q).2.2 k)
    rw [add_zero] at this
    exact this
  · rintro ⟨i, q⟩ ⟨j, q'⟩ h
    obtain rfl : i = j := f2 i j fun k => by
      by_cases hk : (k : ℕ) < r
      · exact cong_trans (cong_symm (up _ q k hk)) (cong_trans (h k) (up _ q' k hk))
      · exact cong_trans ((f5 i).2 k (not_lt.1 hk)) (cong_symm ((f5 j).2 k (not_lt.1 hk)))
    have h3 := mem_of_cong hΛ' hM (near_of_mem hL) (cop_level D)
      (sub_mem (add_mem (f6 i).1 (hlow q).1) (add_mem (f6 i).1 (hlow q').1)) h
    rw [add_sub_add_left_eq_sub] at h3
    refine Prod.ext rfl ?_
    change q = q'
    rw [← hδ q, ← hδ q', eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
    exact hsh _ h3
  · intro x hx hx0
    obtain ⟨⟨κ, hκ⟩, h5⟩ := of_datF_ne hx0
    obtain ⟨i, hi⟩ := f3 (Matrix.of fun k => if (k : ℕ) < r then x k else 0) (by
      rw [dat_eq, datF_eq (κ := κ)]
      · exact (D.lam κ).ne_zero
      · refine red_congr (fun a => ?_) hκ
        change Cong X D.𝔪 (if _ then _ else _) _
        rw [if_pos (show ((Fin.castLE hn a : Fin n) : ℕ) < r from a.2)]
        exact cong_refl _
      · intro k hk
        change Cong X D.𝔪 (if _ then _ else _) _
        rw [if_neg (not_lt.2 hk)]
        exact cong_refl _)
    have h3 : x - lowD r n (cc (α : E) / (α : E)) * f i ∈ tens Λ'' (D.sh L) := by
      refine mem_moved hM h𝔪 hc h0 hα h𝔞 hΛ hΛ' hΛ'' hm h2 hL (sub_mem hx (f6 i).1)
        (fun k hk => ?_) fun k hk => ?_
      · have h4 := hi k
        change Cong X D.𝔪 (if _ then _ else _) _ at h4
        rw [if_pos hk] at h4
        change Cong X D.𝔪 (x k - (lowD r n (cc (α : E) / (α : E)) * f i) k) 0
        rw [lowD_row, if_pos hk, one_smul, cong_zero]
        exact h4
      · have := cong_sub (h5 k hk) ((f6 i).2 k hk)
        rw [sub_zero] at this
        exact this
    refine ⟨(i, QuotientAddGroup.mk ⟨_, h3⟩), fun k => ?_⟩
    have h4 := QuotientAddGroup.eq.1 (hδ (QuotientAddGroup.mk ⟨_, h3⟩))
    rw [neg_add_eq_sub] at h4
    have h6 := cong_zero.1 (cong_of_sh hM hΛ' hL h4 k)
    rw [Lev.cong_iff]
    convert h6 using 1
    change x k - (_ + _) = x k - _ - _
    rw [sub_add_eq_sub_sub]

end GlobalTheory.Dict.SumFree
