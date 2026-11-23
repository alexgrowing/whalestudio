import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

namespace GlobalTheory.HermWitt

open Module Matrix GlobalTheory.HermDiag

section Abstract

variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]

def quasiRefl (B : V →ₗ[E] V →ₛₗ[c] E) (v : V) (a : E) : V →ₗ[E] V :=
  LinearMap.id - (a⁻¹ • B.flip v).smulRight v

theorem quasiRefl_apply (B : V →ₗ[E] V →ₛₗ[c] E) (v : V) (a : E) (z : V) :
    quasiRefl B v a z = z - (a⁻¹ * B z v) • v := by
  simp [quasiRefl]

theorem quasiRefl_quasiRefl (B : V →ₗ[E] V →ₛₗ[c] E) {v : V} {a b : E} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b = B v v) (z : V) : quasiRefl B v b (quasiRefl B v a z) = z := by
  rw [quasiRefl_apply, quasiRefl_apply, LinearMap.map_sub₂, LinearMap.map_smul₂, ← hab, sub_sub,
    ← add_smul, smul_eq_mul]
  have : a⁻¹ * B z v + b⁻¹ * (B z v - a⁻¹ * B z v * (a + b)) = 0 := by
    field_simp
    ring
  rw [this, zero_smul, sub_zero]

theorem apply_quasiRefl_quasiRefl {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    {v : V} {a : E} (ha : a ≠ 0) (hab : a + c a = B v v) (z w : V) :
    B (quasiRefl B v a z) (quasiRefl B v a w) = B z w := by
  have hca : c a ≠ 0 := (map_ne_zero c).2 ha
  simp only [quasiRefl_apply, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, map_inv₀, hB, ← hab]
  field_simp
  ring

theorem exists_isometry_of_apply_sub_ne_zero {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {x y : V} (hxy : B x x = B y y) (ha : B x (x - y) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧
      ∀ u, B u (x - y) = 0 → γ u = u := by
  have hca : c (B x (x - y)) ≠ 0 := (map_ne_zero c).2 ha
  have hab : B x (x - y) + c (B x (x - y)) = B (x - y) (x - y) := by
    rw [hB]
    simp only [map_sub, LinearMap.sub_apply]
    linear_combination hxy
  refine ⟨LinearEquiv.ofLinear (quasiRefl B (x - y) (B x (x - y)))
    (quasiRefl B (x - y) (c (B x (x - y)))) ?_ ?_, ?_, ?_, ?_⟩
  · ext z
    exact quasiRefl_quasiRefl B hca ha (by rw [add_comm, hab]) z
  · ext z
    exact quasiRefl_quasiRefl B ha hca hab z
  · exact apply_quasiRefl_quasiRefl hB ha hab
  · rw [LinearEquiv.ofLinear_apply, quasiRefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]
  · intro u hu
    rw [LinearEquiv.ofLinear_apply, quasiRefl_apply, hu, mul_zero, zero_smul, sub_zero]

theorem exists_isometry_apply_eq (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {x y : V} (hxy : B x x = B y y) (hx : B x x ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧
      ∀ u, B u x = 0 → B u y = 0 → γ u = u := by
  by_cases ha : B x (x - y) = 0
  · have h1 : B x (x - -y) ≠ 0 := by
      have : B x (x - -y) = 2 * B x x := by
        simp only [map_sub, map_neg] at ha ⊢
        linear_combination -ha
      rw [this]
      exact mul_ne_zero h2 hx
    have h3 : B (-y) (-y - y) ≠ 0 := by
      have : B (-y) (-y - y) = 2 * B x x := by
        simp only [map_sub, map_neg, LinearMap.neg_apply, hxy]
        ring
      rw [this]
      exact mul_ne_zero h2 hx
    obtain ⟨γ₁, i₁, e₁, f₁⟩ := exists_isometry_of_apply_sub_ne_zero hB (by simpa using hxy) h1
    obtain ⟨γ₂, i₂, e₂, f₂⟩ := exists_isometry_of_apply_sub_ne_zero hB (by simp) h3
    refine ⟨γ₁.trans γ₂, fun z w => ?_, ?_, fun u hux huy => ?_⟩
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, i₂, i₁]
    · rw [LinearEquiv.trans_apply, e₁, e₂]
    · rw [LinearEquiv.trans_apply, f₁ u (by simp [hux, huy]), f₂ u (by simp [huy])]
  · obtain ⟨γ, i, e, f⟩ := exists_isometry_of_apply_sub_ne_zero hB hxy ha
    exact ⟨γ, i, e, fun u hux huy => f u (by simp [hux, huy])⟩

theorem exists_isometry_of_orthogonal (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {ι : Type*} [Finite ι] {x y : ι → V}
    (hx : ∀ i j, i ≠ j → B (x i) (x j) = 0) (hy : ∀ i j, i ≠ j → B (y i) (y j) = 0)
    (hxy : ∀ i, B (x i) (x i) = B (y i) (y i)) (hne : ∀ i, B (x i) (x i) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i, γ (x i) = y i := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι,
      ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i ∈ s, γ (x i) = y i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl E V, fun _ _ => rfl, by simp⟩
    | insert i s hi ih =>
      obtain ⟨γ, hγ, e⟩ := ih
      obtain ⟨δ, hδ, e', f⟩ := exists_isometry_apply_eq h2 hB (x := γ (x i)) (y := y i)
        (by rw [hγ, hxy]) (by rw [hγ]; exact hne i)
      refine ⟨γ.trans δ, fun z w => ?_, fun j hj => ?_⟩
      · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hδ, hγ]
      · rw [LinearEquiv.trans_apply]
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact e'
        · have hji : j ≠ i := fun h => hi (h ▸ hj)
          rw [f _ (by rw [hγ]; exact hx j i hji) (by rw [e j hj]; exact hy j i hji), e j hj]
  obtain ⟨γ, hγ, e⟩ := key Finset.univ
  exact ⟨γ, hγ, fun i => e i (Finset.mem_univ i)⟩

theorem exists_isometry_comp_eq_of_nondegenerate (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {g f : W →ₗ[E] V} (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b))
    (hW : ∀ a, (∀ b, B (g b) (g a) = 0) → a = 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 (finrank E W)
    (LinearMap.mk₂'ₛₗ (RingHom.id E) c (fun a b => B (g a) (g b))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp))
    (fun a b => hB _ _) rfl
  replace hv : ∀ i j, i ≠ j → B (g (v i)) (g (v j)) = 0 := hv
  obtain ⟨γ, hγ, e⟩ := exists_isometry_of_orthogonal h2 hB (x := fun i => g (v i))
    (y := fun i => f (v i)) hv (fun i j hij => by rw [hgf]; exact hv i j hij)
    (fun i => (hgf _ _).symm)
    (fun i hi => v.ne_zero i (hW _ fun b => by
      have : (B.flip (g (v i))) ∘ₗ g = 0 := v.ext fun j => by
        by_cases hij : j = i
        · subst hij
          exact hi
        · exact hv j i hij
      exact LinearMap.congr_fun this b))
  refine ⟨γ, hγ, fun a => ?_⟩
  have : γ.toLinearMap ∘ₗ g = f := v.ext e
  exact LinearMap.congr_fun this a

theorem exists_flip_eq [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (ψ : V →ₗ[E] E) : ∃ w, ∀ z, B z w = ψ z := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 (finrank E V) B hB rfl
  have hne : ∀ i, B (v i) (v i) ≠ 0 := fun i hi => v.ne_zero i (hV _ fun b => by
    have : B.flip (v i) = 0 := v.ext fun j => by
      by_cases hij : j = i
      · subst hij
        exact hi
      · exact hv j i hij
    exact LinearMap.congr_fun this b)
  refine ⟨∑ i, c (ψ (v i) / B (v i) (v i)) • v i, fun z => ?_⟩
  have : B.flip (∑ i, c (ψ (v i) / B (v i) (v i)) • v i) = ψ := v.ext fun j => by
    rw [LinearMap.flip_apply, map_sum, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, hc, smul_eq_mul, div_mul_cancel₀ _ (hne j)]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, hv j i hij.symm, smul_zero]
    · simp
  exact LinearMap.congr_fun this z

theorem exists_graph_lt [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (Γ : Submodule E (V × V))
    (h0 : ∀ p ∈ Γ, p.1 = 0 ↔ p.2 = 0) (hΓ : ∀ p ∈ Γ, ∀ q ∈ Γ, B p.2 q.2 = B p.1 q.1)
    {r : V × V} (hr : r ∈ Γ) (hr0 : r ≠ 0) (hrad : ∀ p ∈ Γ, B p.1 r.1 = 0) :
    ∃ Γ' : Submodule E (V × V), Γ < Γ' ∧ (∀ p ∈ Γ', p.1 = 0 ↔ p.2 = 0) ∧
      ∀ p ∈ Γ', ∀ q ∈ Γ', B p.2 q.2 = B p.1 q.1 := by
  have hr1 : r.1 ≠ 0 := fun h => hr0 (Prod.ext h ((h0 r hr).1 h))
  have hrad2 : ∀ p ∈ Γ, B p.2 r.2 = 0 := fun p hp => by rw [hΓ p hp r hr, hrad p hp]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, B w₀ r.1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hr1 (hV _ h)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, B w₁ r.1 = 1 :=
    ⟨(B w₀ r.1)⁻¹ • w₀, by simp [inv_mul_cancel₀ hw₀]⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.snd E V V ∘ₗ Γ.subtype) (by
      rw [LinearMap.ker_eq_bot']
      intro p hp
      exact Subtype.ext (Prod.ext ((h0 p p.2).2 hp) hp))
  obtain ⟨w, hw⟩ := exists_flip_eq h2 hc hB hV
    (B.flip w₁ ∘ₗ LinearMap.fst E V V ∘ₗ Γ.subtype ∘ₗ L)
  have hw' : ∀ p ∈ Γ, B p.2 w = B p.1 w₁ := fun p hp => by
    have h := LinearMap.congr_fun hL ⟨p, hp⟩
    have h' : L p.2 = ⟨p, hp⟩ := h
    rw [hw]
    simp [h']
  have hr1w : B r.1 w₁ = 1 := by rw [← hB, hw₁, map_one]
  have hr2w : B r.2 w = 1 := by rw [hw' r hr, hr1w]
  have hwr2 : B w r.2 = 1 := by rw [← hB, hr2w, map_one]
  obtain ⟨w₂, ha, hb⟩ : ∃ w₂, (∀ p ∈ Γ, B p.2 w₂ = B p.1 w₁) ∧ B w₂ w₂ = B w₁ w₁ := by
    have hs : c ((B w₁ w₁ - B w w) / 2) = (B w₁ w₁ - B w w) / 2 := by
      rw [map_div₀, map_sub, hB, hB, map_ofNat]
    refine ⟨w + ((B w₁ w₁ - B w w) / 2) • r.2, fun p hp => ?_, ?_⟩
    · rw [map_add, LinearMap.map_smulₛₗ, hrad2 p hp, smul_zero, add_zero, hw' p hp]
    · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        RingHom.id_apply, hs, smul_eq_mul, hr2w, hwr2, hrad2 r hr]
      field_simp
      ring
  have ha' : ∀ p ∈ Γ, B w₂ p.2 = B w₁ p.1 := fun p hp => by rw [← hB, ha p hp, hB]
  have hmem : ∀ p ∈ Γ ⊔ Submodule.span E {(w₁, w₂)},
      ∃ q ∈ Γ, ∃ t : E, p = (q.1 + t • w₁, q.2 + t • w₂) := by
    intro p hp
    obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨q, hq, t, rfl⟩
  refine ⟨Γ ⊔ Submodule.span E {(w₁, w₂)}, lt_of_le_of_ne le_sup_left fun h => ?_, ?_, ?_⟩
  · have : (w₁, w₂) ∈ Γ := by
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have h1 := hrad _ this
    rw [hw₁] at h1
    exact one_ne_zero h1
  · intro p hp
    obtain ⟨q, hq, t, rfl⟩ := hmem p hp
    have e1 : B (q.1 + t • w₁) r.1 = t := by simp [hrad q hq, hw₁]
    have e2 : B (q.2 + t • w₂) r.2 = t := by simp [hrad2 q hq, ha' r hr, hw₁]
    constructor
    · intro h
      dsimp only at h ⊢
      have ht : t = 0 := by rw [← e1, h]; simp
      subst ht
      simpa using (h0 q hq).1 (by simpa using h)
    · intro h
      dsimp only at h ⊢
      have ht : t = 0 := by rw [← e2, h]; simp
      subst ht
      simpa using (h0 q hq).2 (by simpa using h)
  · intro p hp p' hp'
    obtain ⟨q, hq, t, rfl⟩ := hmem p hp
    obtain ⟨q', hq', t', rfl⟩ := hmem p' hp'
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      hΓ q hq q' hq', ha q hq, ha' q' hq', hb]

theorem exists_isometry_of_graph [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (Γ : Submodule E (V × V))
    (h0 : ∀ p ∈ Γ, p.1 = 0 ↔ p.2 = 0) (hΓ : ∀ p ∈ Γ, ∀ q ∈ Γ, B p.2 q.2 = B p.1 q.1) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ p ∈ Γ, γ p.1 = p.2 := by
  induction Γ using WellFoundedGT.induction with
  | ind Γ ih =>
    by_cases h : ∃ r ∈ Γ, r ≠ 0 ∧ ∀ p ∈ Γ, B p.1 r.1 = 0
    · obtain ⟨r, hr, hr0, hrad⟩ := h
      obtain ⟨Γ', hlt, h0', hΓ'⟩ := exists_graph_lt h2 hc hB hV Γ h0 hΓ hr hr0 hrad
      obtain ⟨γ, hγ, e⟩ := ih Γ' hlt h0' hΓ'
      exact ⟨γ, hγ, fun p hp => e p (hlt.le hp)⟩
    · obtain ⟨γ, hγ, e⟩ := exists_isometry_comp_eq_of_nondegenerate h2 hB
        (g := LinearMap.fst E V V ∘ₗ Γ.subtype) (f := LinearMap.snd E V V ∘ₗ Γ.subtype)
        (fun a b => hΓ a a.2 b b.2)
        (fun a ha => by
          by_contra hne
          exact h ⟨a, a.2, fun h' => hne (Subtype.ext h'), fun p hp => ha ⟨p, hp⟩⟩)
      exact ⟨γ, hγ, fun p hp => e ⟨p, hp⟩⟩

theorem exists_isometry_comp_eq [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {W : Type*} [AddCommGroup W] [Module E W]
    {g f : W →ₗ[E] V} (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b)) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by
  obtain ⟨γ, hγ, e⟩ := exists_isometry_of_graph h2 hc hB hV (LinearMap.range (g.prod f))
    (by rintro _ ⟨a, rfl⟩; exact h0 a) (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hgf a b)
  exact ⟨γ, hγ, fun a => e _ ⟨a, rfl⟩⟩

theorem exists_isometry_extend [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {U U' : Submodule E V} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, B (f a) (f b) = B a b) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a : U, γ a = f a :=
  exists_isometry_comp_eq h2 hc hB hV (g := U.subtype) (f := U'.subtype ∘ₗ f.toLinearMap)
    (fun a => by simp) hf

end Abstract

section MatrixForm

variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in

theorem dotProduct_congr_mulVec {m : Type*} [Fintype m] (c : E →+* E) (G : Matrix n n E)
    (P : Matrix n m E) (x y : m → E) :
    x ⬝ᵥ (Pᵀ * G * P.map c) *ᵥ (c ∘ y) = (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) := by
  have h : c ∘ (P *ᵥ y) = P.map c *ᵥ (c ∘ y) := funext fun i => RingHom.map_mulVec c P y i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem isometry_iff_congr_eq (c : E →+* E) (G P : Matrix n n E) :
    (∀ x y, (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) = x ⬝ᵥ G *ᵥ (c ∘ y)) ↔ Pᵀ * G * P.map c = G := by
  constructor
  · intro h
    apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [toLinearMapₛₗ₂'_eq_dotProduct, toLinearMapₛₗ₂'_eq_dotProduct, dotProduct_congr_mulVec, h]
  · intro h x y
    rw [← dotProduct_congr_mulVec, h]

theorem eq_zero_of_forall_dotProduct_eq_zero {G : Matrix n n E} (hG : G.det ≠ 0) {x : n → E}
    (hx : ∀ y, y ⬝ᵥ G *ᵥ (c ∘ x) = 0) : x = 0 := by
  have h1 : G *ᵥ (c ∘ x) = 0 := by
    funext i
    simpa using hx (Pi.single i 1)
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hG h1
  funext i
  exact (map_eq_zero c).1 (congrFun h3 i)

theorem exists_gl_mulVec_eq (γ : (n → E) ≃ₗ[E] (n → E)) :
    ∃ g : GL n E, ∀ x, (g : Matrix n n E) *ᵥ x = γ x :=
  ⟨⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩,
    fun x => by simp [← Matrix.toLin'_apply]⟩

theorem exists_gl_isometry_mulVec_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x y : n → E}
    (hxy : x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y)) (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ (γ : Matrix n n E) *ᵥ x = y ∧
      ∀ u, u ⬝ᵥ G *ᵥ (c ∘ x) = 0 → u ⬝ᵥ G *ᵥ (c ∘ y) = 0 → (γ : Matrix n n E) *ᵥ u = u := by
  obtain ⟨γ, hγ⟩ := exists_isometry_apply_eq h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (x := x) (y := y) (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hxy)
    (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hx)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩

theorem exists_gl_isometry_comp_eq_of_nondegenerate (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {g f : W →ₗ[E] (n → E)}
    (hgf : ∀ a b, f a ⬝ᵥ G *ᵥ (c ∘ f b) = g a ⬝ᵥ G *ᵥ (c ∘ g b))
    (hW : ∀ a, (∀ b, g b ⬝ᵥ G *ᵥ (c ∘ g a) = 0) → a = 0) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a, (γ : Matrix n n E) *ᵥ g a = f a := by
  obtain ⟨γ, hγ⟩ := exists_isometry_comp_eq_of_nondegenerate h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (g := g) (f := f) (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hgf)
    (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hW)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩

theorem exists_gl_isometry_comp_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {W : Type*} [AddCommGroup W] [Module E W] {g f : W →ₗ[E] (n → E)}
    (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, f a ⬝ᵥ G *ᵥ (c ∘ f b) = g a ⬝ᵥ G *ᵥ (c ∘ g b)) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a, (γ : Matrix n n E) *ᵥ g a = f a := by
  obtain ⟨γ, hγ⟩ := exists_isometry_comp_eq h2 hc
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (fun x hx => eq_zero_of_forall_dotProduct_eq_zero hdet
      (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hx))
    (g := g) (f := f) h0 (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hgf)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩

theorem exists_gl_isometry_extend (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {U U' : Submodule E (n → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, (f a : n → E) ⬝ᵥ G *ᵥ (c ∘ (f b : n → E)) =
      (a : n → E) ⬝ᵥ G *ᵥ (c ∘ (b : n → E))) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a : U, (γ : Matrix n n E) *ᵥ (a : n → E) = f a :=
  exists_gl_isometry_comp_eq h2 hc hG hdet (g := U.subtype) (f := U'.subtype ∘ₗ f.toLinearMap)
    (fun a => by simp) hf

theorem exists_gl_isometry_mul_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {m : Type*} [Fintype m] {X Y : Matrix n m E} (h0 : ∀ a, X *ᵥ a = 0 ↔ Y *ᵥ a = 0)
    (hXY : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : GL n E, (γ : Matrix n n E)ᵀ * G * (γ : Matrix n n E).map c = G ∧
      (γ : Matrix n n E) * X = Y := by
  classical
  obtain ⟨γ, hγ, e⟩ := exists_gl_isometry_comp_eq h2 hc hG hdet (g := X.mulVecLin)
    (f := Y.mulVecLin) h0 (fun a b => by
      simp only [Matrix.mulVecLin_apply, ← dotProduct_congr_mulVec, hXY])
  refine ⟨γ, (isometry_iff_congr_eq c G _).1 hγ, Matrix.ext_of_mulVec_single fun a => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact e _

theorem exists_gl_isometry_mul_eq_of_det_ne_zero (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a)
    {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix n m E}
    (hX : (Xᵀ * G * X.map c).det ≠ 0) (hXY : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : GL n E, (γ : Matrix n n E)ᵀ * G * (γ : Matrix n n E).map c = G ∧
      (γ : Matrix n n E) * X = Y := by
  obtain ⟨γ, hγ, e⟩ := exists_gl_isometry_comp_eq_of_nondegenerate h2 hc hG (g := X.mulVecLin)
    (f := Y.mulVecLin) (fun a b => by
      simp only [Matrix.mulVecLin_apply, ← dotProduct_congr_mulVec, hXY])
    (fun a ha => eq_zero_of_forall_dotProduct_eq_zero (c := c) hX fun b => by
      rw [dotProduct_congr_mulVec]
      exact ha b)
  refine ⟨γ, (isometry_iff_congr_eq c G _).1 hγ, Matrix.ext_of_mulVec_single fun a => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact e _

theorem congr_of_fromBlocks_congr (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {m : Type*} [Fintype m] [DecidableEq m] {D : Matrix m m E} (hD : ∀ a b, c (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, c (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map c) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map c := by
  have hH : ∀ a b, c (fromBlocks D 0 0 G₁ a b) = fromBlocks D 0 0 G₁ b a := by
    rintro (a | a) (b | b) <;> simp [hD, hG]
  let J : Matrix (m ⊕ n) m E := fromRows 1 0
  have hJ : ∀ G : Matrix n n E, Jᵀ * fromBlocks D 0 0 G * J.map c = D := by
    intro G
    have : J.map c = J := by
      ext (a | a) b <;> simp [J, Matrix.one_apply]
    rw [this]
    simp [J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have hPJ : (P * J)ᵀ * fromBlocks D 0 0 G₁ * (P * J).map c = D := by
    rw [← hJ G₂]
    conv_rhs => rw [h]
    rw [hJ G₂, transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨γ, hγ, e⟩ := exists_gl_isometry_mul_eq_of_det_ne_zero h2 hc hH (X := P * J) (Y := J)
    (by rwa [hPJ]) (by rw [hPJ, hJ])
  have hQ : fromBlocks D 0 0 G₂ = ((γ : Matrix _ _ E) * P)ᵀ * fromBlocks D 0 0 G₁ *
      ((γ : Matrix _ _ E) * P).map c := by
    rw [h]
    conv_lhs => rw [← hγ]
    rw [transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hQd : ((γ : Matrix _ _ E) * P).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero γ) hP
  rw [← Matrix.mul_assoc] at e
  generalize (γ : Matrix _ _ E) * P = Q at hQ hQd e
  obtain ⟨A, B, C, F, rfl⟩ : ∃ A B C F, Q = fromBlocks A B C F :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Q).symm⟩
  have e' : A = 1 ∧ C = 0 := by
    simpa [J, fromBlocks_mul_fromRows, fromRows_ext_iff] using e
  obtain ⟨rfl, rfl⟩ := e'
  rw [det_fromBlocks_zero₂₁, det_one, one_mul] at hQd
  rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hQ
  obtain ⟨-, h12, -, h22⟩ := hQ
  have hB : D * B.map c = 0 := by simpa using h12.symm
  refine ⟨F, hQd, ?_⟩
  rw [h22]
  simp [Matrix.mul_assoc, hB]

end MatrixForm

section CM

open NumberField ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_gl_isometry_mulVec_eq_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) {x y : Fin r → E}
    (hxy : FD.herm G x x = FD.herm G y y) (hx : FD.herm G x x ≠ 0) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y ∧
      ∀ u, FD.herm G u x = 0 → FD.herm G u y = 0 → (γ : Matrix (Fin r) (Fin r) E) *ᵥ u = u := by
  simp only [herm_eq_dotProduct] at hxy hx ⊢
  exact exists_gl_isometry_mulVec_eq (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hxy hx

theorem congr_of_fromBlocks_congr_cc {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {D : Matrix m m E} (hD : ∀ a b, FD.cc (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, FD.cc (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map FD.cc) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map FD.cc :=
  congr_of_fromBlocks_congr (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hD hdet hG hP h

theorem exists_gl_isometry_extend_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hdet : G.det ≠ 0)
    {U U' : Submodule E (Fin r → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, FD.herm G (f a) (f b) = FD.herm G a b) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a := by
  simp only [herm_eq_dotProduct] at hf ⊢
  exact exists_gl_isometry_extend (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hdet f hf

end CM

theorem witt_theorem {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) (c : E →+* E)
    (hc : ∀ t, c (c t) = t) {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, c (G a b) = G b a) :
    (∀ x y : Fin r → E, x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y) → x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0 →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y) ∧
    (∀ {s : ℕ} (D : Matrix (Fin s) (Fin s) E), (∀ a b, c (D a b) = D b a) → D.det ≠ 0 →
      ∀ G' : Matrix (Fin r) (Fin r) E,
        (∃ P : Matrix (Fin s ⊕ Fin r) (Fin s ⊕ Fin r) E, P.det ≠ 0 ∧
          fromBlocks D 0 0 G' = Pᵀ * fromBlocks D 0 0 G * P.map c) →
        ∃ Q : Matrix (Fin r) (Fin r) E, Q.det ≠ 0 ∧ G' = Qᵀ * G * Q.map c) ∧
    (G.det ≠ 0 → ∀ (U U' : Submodule E (Fin r → E)) (f : U ≃ₗ[E] U'),
      (∀ a b : U, (f a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (f b : Fin r → E)) =
        (a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (b : Fin r → E))) →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a) := by
  refine ⟨fun x y hxy hx => ?_, fun D hD hdet G' ⟨P, hP, h⟩ => ?_, fun hdet U U' f hf => ?_⟩
  · obtain ⟨γ, h1, h3, -⟩ := exists_gl_isometry_mulVec_eq h2 hc hG hxy hx
    exact ⟨γ, h1, h3⟩
  · exact congr_of_fromBlocks_congr h2 hc hD hdet hG hP h
  · exact exists_gl_isometry_extend h2 hc hG hdet f hf

end GlobalTheory.HermWitt
