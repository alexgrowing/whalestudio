import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.HfDecompSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SubProjOrth

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

section
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
  (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
include hσ hJ he hff hef hfix h2i hδ hσδ

theorem move {s : ℕ} {a : Fin s → ι → K} (hae : ∀ j, hf σ J (a j) e = 0)
    (haf : ∀ j, hf σ J (a j) f = 0) (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal →
      m₂.IsMaximal → m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hν : IsUnit (hf σ J b b)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by
  obtain ⟨b1, r1, c1⟩ : ∃ b', Reach σ J e f a b b' ∧ IsCoprime (hf σ J b' f) (hf σ J b' e) := by
    apply stage1 (hmax := hmax) (hb := hb) (hν := hν) <;> first | exact hδ | exact hσδ | assumption
  have i1 : (∀ j, hf σ J b1 (a j) = 0) ∧ hf σ J b1 b1 = hf σ J b b := by
    apply reach_inv (h := r1) (hb := hb) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨b2, r2, u2⟩ : ∃ b', Reach σ J e f a b1 b' ∧ IsUnit (hf σ J b' e) := by
    apply stage2 (hcop := c1) <;> first | exact hδ | exact hσδ | assumption
  have i2' : (∀ j, hf σ J b2 (a j) = 0) ∧ hf σ J b2 b2 = hf σ J b1 b1 := by
    apply reach_inv (h := r2) (hb := i1.1) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨b3, r3, f3, u3⟩ : ∃ b', Reach σ J e f a b2 b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' e) := by
    apply stage3 (hb := i2'.1) (hβ := u2) <;> first | exact hδ | exact hσδ | assumption
  have i3 : (∀ j, hf σ J b3 (a j) = 0) ∧ hf σ J b3 b3 = hf σ J b2 b2 := by
    apply reach_inv (h := r3) (hb := i2'.1) <;> first | exact hδ | exact hσδ | assumption
  have c3 : IsCoprime (hf σ J b3 f) (hf σ J b3 e) :=
    ⟨0, ↑u3.unit⁻¹, by rw [zero_mul, zero_add]; exact u3.val_inv_mul⟩
  obtain ⟨b4, r4, f4, u4⟩ : ∃ b', Reach σ J e f a b3 b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' f) := by
    apply stage4 (hform := f3) (hcop := c3) <;> first | exact hδ | exact hσδ | assumption
  have i4 : (∀ j, hf σ J b4 (a j) = 0) ∧ hf σ J b4 b4 = hf σ J b3 b3 := by
    apply reach_inv (h := r4) (hb := i3.1) <;> first | exact hδ | exact hσδ | assumption
  have r5 : Reach σ J e f a b4 (e + (hf σ J b4 b4 * i2) • f) := by
    apply stage5 (hform := f4) (hα := u4) <;> first | exact hδ | exact hσδ | assumption
  have hν4 : hf σ J b4 b4 = hf σ J b b := by rw [i4.2, i3.2, i2'.2, i1.2]
  rw [hν4] at r5
  have t4 : Reach σ J e f a b3 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r4) (h2 := r5) <;> first | exact hδ | exact hσδ | assumption
  have t3 : Reach σ J e f a b2 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r3) (h2 := t4) <;> first | exact hδ | exact hσδ | assumption
  have t2 : Reach σ J e f a b1 (e + (hf σ J b b * i2) • f) := by
    apply reach_trans (h1 := r2) (h2 := t3) <;> first | exact hδ | exact hσδ | assumption
  apply reach_trans (h1 := r1) (h2 := t2) <;> first | exact hδ | exact hσδ | assumption

theorem fix_all_good {r : ℕ} (F : OFam σ J e f r) (hF : F.Spans) {h : Matrix ι ι K}
    (hpres : ∀ x y, hf σ J (h *ᵥ x) (h *ᵥ y) = hf σ J x y) (hfixa : ∀ j, h *ᵥ F.a j = F.a j) :
    h ∈ Good σ J e f := by
  have hae := F.ha_e
  have haf := F.ha_f
  have hlin : ∀ (k l : K) (x y z : ι → K),
      hf σ J (k • x + l • y) z = k * hf σ J x z + l * hf σ J y z := by
    intro k l x y z
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hsym : ∀ x y, hf σ J y x = σ (hf σ J x y) := fun x y => (hf_symm hσ hJ x y).symm
  have hfe : hf σ J f e = 1 := by rw [hsym, hef, map_one]
  have hea : ∀ j, hf σ J e (F.a j) = 0 := fun j => by rw [hsym, F.ha_e j, map_zero]
  have hfa : ∀ j, hf σ J f (F.a j) = 0 := fun j => by rw [hsym, F.ha_f j, map_zero]
  have hspan : ∀ x, (∀ j, hf σ J x (F.a j) = 0) → x = hf σ J x f • e + hf σ J x e • f := by
    intro x hx
    have h1 := hF x
    simp only [OFam.proj, hx, zero_mul, zero_smul, Finset.sum_const_zero, add_zero] at h1
    exact h1.symm
  have horth : ∀ (M : Matrix ι ι K), (∀ x y, hf σ J (M *ᵥ x) (M *ᵥ y) = hf σ J x y) →
      (∀ j, M *ᵥ F.a j = F.a j) → ∀ x, (∀ j, hf σ J x (F.a j) = 0) →
        ∀ j, hf σ J (M *ᵥ x) (F.a j) = 0 := by
    intro M hM hMa x hx j
    rw [← hMa j, hM, hx]

  set b := h *ᵥ e with hbdef
  set c := h *ᵥ f with hcdef
  clear_value b c
  have hba : ∀ j, hf σ J b (F.a j) = 0 := by rw [hbdef]; exact horth h hpres hfixa e hea
  have hca : ∀ j, hf σ J c (F.a j) = 0 := by rw [hcdef]; exact horth h hpres hfixa f hfa
  have hbform := hspan b hba
  have hcform := hspan c hca
  have hcb : hf σ J c b = 1 := by rw [hcdef, hbdef, hpres, hfe]
  have hcop : IsCoprime (hf σ J b f) (hf σ J b e) := by
    refine ⟨σ (hf σ J c e), σ (hf σ J c f), ?_⟩
    have h1 : hf σ J c f * σ (hf σ J b e) + hf σ J c e * σ (hf σ J b f) = 1 := by
      rw [← hcb]
      conv_rhs => rw [hcform]
      rw [hlin, hsym b e, hsym b f]
    have h2 := congrArg σ h1
    rw [map_add, map_mul, map_mul, hσ, hσ, map_one] at h2
    linear_combination h2
  obtain ⟨b4, r4, f4, u4⟩ : ∃ b', Reach σ J e f F.a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧
      IsUnit (hf σ J b' f) := by
    apply stage4 (hform := hbform) (hcop := hcop) <;> first | exact hδ | exact hσδ | assumption
  have i4 : (∀ j, hf σ J b4 (F.a j) = 0) ∧ hf σ J b4 b4 = hf σ J b b := by
    apply reach_inv (h := r4) (hb := hba) <;> first | exact hδ | exact hσδ | assumption
  have r5 : Reach σ J e f F.a b4 (e + (hf σ J b4 b4 * i2) • f) := by
    apply stage5 (hform := f4) (hα := u4) <;> first | exact hδ | exact hσδ | assumption
  have hbb : hf σ J b b = 0 := by rw [hbdef, hpres, he]
  rw [i4.2, hbb, zero_mul, zero_smul, add_zero] at r5
  have rt : Reach σ J e f F.a b e := by
    apply reach_trans (h1 := r4) (h2 := r5) <;> first | exact hδ | exact hσδ | assumption
  obtain ⟨p, hp, hpa, hpb⟩ := rt
  have gp : ∀ x y, hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
    intro x y; exact good_preserves hσ hJ he hff hef hae haf hp x y
  set g := p * h with hgdef
  clear_value g
  have hgpres : ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
    intro x y; rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp, hpres]
  have hga : ∀ j, g *ᵥ F.a j = F.a j := by
    intro j; rw [hgdef, ← Matrix.mulVec_mulVec, hfixa, hpa]
  have hge : g *ᵥ e = e := by rw [hgdef, ← Matrix.mulVec_mulVec, ← hbdef, hpb]
  set y := g *ᵥ f with hydef
  clear_value y
  have hya : ∀ j, hf σ J y (F.a j) = 0 := by rw [hydef]; exact horth g hgpres hga f hfa
  have hye : hf σ J y e = 1 := by rw [hydef, ← hge, hgpres, hfe]
  have hyy : hf σ J y y = 0 := by rw [hydef, hgpres, hff]
  set γ := hf σ J y f with hγ
  clear_value γ
  have hyform : y = γ • e + f := by
    have := hspan y hya
    rw [hye, one_smul, ← hγ] at this
    exact this
  have hγσ : γ + σ γ = 0 := by
    have h1 := hyy
    nth_rewrite 1 [hyform] at h1
    rw [show γ • e + f = γ • e + (1 : K) • f by rw [one_smul], hlin, hsym y e, hsym y f, hye,
      map_one, one_mul] at h1
    rw [hγ] at h1 ⊢
    linear_combination h1
  set E := eich σ J e 0 γ with hEdef
  clear_value E
  have hEm : E ∈ eichSet σ J e f :=
    Or.inl ⟨0, γ, by simp [hf], by simp [hf], by simp [hf, hγσ], hEdef⟩
  have hE : E ∈ Good σ J e f := by
    apply good_of_closure (hn := Submonoid.subset_closure hEm) <;> first | exact hδ | exact hσδ | assumption
  have h0 : ∀ x, hf σ J x 0 = 0 := fun x => by simp [hf]
  have key : ∀ x, g *ᵥ x = E *ᵥ x := by
    intro x
    have hx := hF x
    simp only [OFam.proj] at hx
    calc g *ᵥ x = g *ᵥ (hf σ J x f • e + hf σ J x e • f +
          ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j) := by rw [hx]
      _ = hf σ J x f • e + hf σ J x e • (γ • e + f) +
          ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j := by
        rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_sum, hge, ← hydef, hyform]
        simp only [Matrix.mulVec_smul, hga]
      _ = (hf σ J x f • e + hf σ J x e • f + ∑ j, (hf σ J x (F.a j) * F.inv j) • F.a j) +
          (γ * hf σ J x e) • e := by
        rw [smul_add, smul_smul, mul_comm (hf σ J x e) γ]; abel
      _ = E *ᵥ x := by rw [hx, hEdef, eich_mulVec, h0]; simp
  have hgE : g = E := Matrix.toLin'.injective (LinearMap.ext fun x => by
    simp only [Matrix.toLin'_apply]; exact key x)
  obtain ⟨p', hp', hp'p, -⟩ : ∃ g' ∈ Good σ J e f, g' * p = 1 ∧ p * g' = 1 := by
    apply good_inv (hg := hp) <;> first | exact hδ | exact hσδ | assumption
  have : h = p' * g := by rw [hgdef, ← mul_assoc, hp'p, one_mul]
  rw [this, hgE]
  apply good_mul (hg := hp') (hg' := hE) <;> first | exact hδ | exact hσδ | assumption

theorem SU_eq_closure (hdet : IsUnit J.det) [Nontrivial K]
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂) :
    SU σ J = (Submonoid.closure (eichSet σ J e f) : Set (Matrix ι ι K)) := by
  ext g
  constructor
  · intro hg
    have hdetg : g.det = 1 := hg.1
    have hpresg : ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
      intro x y; apply SU_preserves (hg := hg) <;> first | exact hδ | exact hσδ | assumption
    obtain ⟨r, F, hF⟩ : ∃ r, ∃ F : OFam σ J e f r, F.Spans := by
      apply exists_spans hσ hJ he hff hef hdet hfix
      all_goals first
        | exact hσδ | exact hδ | assumption
        | exact (Units.mkOfMulEqOne _ _ h2i).isUnit
    have gp : ∀ p ∈ Good σ J e f, ∀ x y, hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
      intro p hp x y; exact good_preserves hσ hJ he hff hef F.ha_e F.ha_f hp x y
    have hunit : ∀ k, IsUnit (hf σ J (F.a k) (F.a k)) := fun k =>
      (Units.mkOfMulEqOne _ (F.inv k) (by rw [mul_comm]; exact F.hinv k)).isUnit
    have step : ∀ k, k ≤ r → ∃ p ∈ Good σ J e f, ∀ j : Fin r, j.val < k →
        (p * g) *ᵥ F.a j = F.a j := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨1, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
        apply good_of_closure (hn := Submonoid.one_mem _) <;> first | exact hδ | exact hσδ | assumption
      | succ k ih =>
        intro hk
        obtain ⟨p, hp, hpa⟩ := ih (by omega)
        set a' : Fin k → ι → K := fun j => F.a ⟨j.val, by omega⟩ with ha'
        have hae' : ∀ j, hf σ J (a' j) e = 0 := fun j => F.ha_e _
        have haf' : ∀ j, hf σ J (a' j) f = 0 := fun j => F.ha_f _
        set kk : Fin r := ⟨k, by omega⟩ with hkk
        set b := (p * g) *ᵥ F.a kk with hbdef
        have hpg : ∀ x y, hf σ J ((p * g) *ᵥ x) ((p * g) *ᵥ y) = hf σ J x y := by
          intro x y; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp p hp, hpresg]
        have hne : ∀ j : Fin k, (⟨j.val, by omega⟩ : Fin r) ≠ kk := by
          intro j h
          have h1 := congrArg Fin.val h
          have h2 := j.isLt
          simp only [hkk, Fin.val_mk] at h1
          omega
        have hbk : ∀ j, hf σ J b (a' j) = 0 := by
          intro j
          show hf σ J b (F.a ⟨j.val, by omega⟩) = 0
          rw [← hpa ⟨j.val, by omega⟩ j.isLt, hbdef, hpg]
          exact F.ho _ _ (Ne.symm (hne j))
        have hak : ∀ j, hf σ J (F.a kk) (a' j) = 0 := fun j => F.ho _ _ (Ne.symm (hne j))
        have hbb : hf σ J b b = hf σ J (F.a kk) (F.a kk) := by rw [hbdef, hpg]
        have m1 : Reach σ J e f a' b (e + (hf σ J b b * i2) • f) := by
          apply move (hae := hae') (haf := haf') (hmax := hmax) (hb := hbk)
            (hν := by rw [hbb]; exact hunit kk) <;> first | exact hδ | exact hσδ | assumption
        have m2 : Reach σ J e f a' (F.a kk) (e + (hf σ J (F.a kk) (F.a kk) * i2) • f) := by
          apply move (hae := hae') (haf := haf') (hmax := hmax) (hb := hak) (hν := hunit kk) <;>
            first | exact hδ | exact hσδ | assumption
        rw [hbb] at m1
        have m3 : Reach σ J e f a' (e + (hf σ J (F.a kk) (F.a kk) * i2) • f) (F.a kk) := by
          apply reach_symm (h := m2) <;> first | exact hδ | exact hσδ | assumption
        have m4 : Reach σ J e f a' b (F.a kk) := by
          apply reach_trans (h1 := m1) (h2 := m3) <;> first | exact hδ | exact hσδ | assumption
        obtain ⟨q, hq, hqa, hqb⟩ := m4
        refine ⟨q * p, ?_, fun j hj => ?_⟩
        · apply good_mul (hg := hq) (hg' := hp) <;> first | exact hδ | exact hσδ | assumption
        · rw [mul_assoc, ← Matrix.mulVec_mulVec]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · rw [hpa j hj']
            have := hqa ⟨j.val, hj'⟩
            simpa [ha'] using this
          · have hjk : j = kk := Fin.ext (by simp [hkk, hj'])
            rw [hjk, ← hbdef, hqb]
    obtain ⟨p, hp, hpa⟩ := step r le_rfl
    have hpgood : p * g ∈ Good σ J e f := by
      apply fix_all_good (F := F) (hF := hF) (hpres := fun x y => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gp p hp, hpresg])
        (hfixa := fun j => hpa j j.isLt) <;> first | exact hδ | exact hσδ | assumption
    obtain ⟨p', hp', hp'p, -⟩ : ∃ g' ∈ Good σ J e f, g' * p = 1 ∧ p * g' = 1 := by
      apply good_inv (hg := hp) <;> first | exact hδ | exact hσδ | assumption
    have hgg : g ∈ Good σ J e f := by
      have : g = p' * (p * g) := by rw [← mul_assoc, hp'p, one_mul]
      rw [this]
      apply good_mul (hg := hp') (hg' := hpgood) <;> first | exact hδ | exact hσδ | assumption
    apply good_SU (hδ := hδ) (hσδ := hσδ) (hg := hgg) (hdet := hdetg) <;> first | exact hδ | exact hσδ | assumption
  · intro hg
    rw [SetLike.mem_coe] at hg
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact (by apply eichAlong_sub (he := he) <;> first | exact hδ | exact hσδ | assumption : eichAlong σ J e f ⊆ SU σ J) hx
      · exact (by apply eichAlong_sub (he := hff) <;> first | exact hδ | exact hσδ | assumption : eichAlong σ J f e ⊆ SU σ J) hx
    | one => apply one_mem_SU <;> first | exact hδ | exact hσδ | assumption
    | mul x y _ _ hx hy => apply mul_mem_SU (hg := hx) (hh := hy) <;> first | exact hδ | exact hσδ | assumption

end

end ReciprocityTheory.ChartRestriction.G.SA
