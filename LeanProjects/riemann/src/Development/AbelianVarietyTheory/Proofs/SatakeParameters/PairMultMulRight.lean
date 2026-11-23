import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelOps

variable {G : Type} [Group G]

def SameDC (K : Subgroup G) (a b : G) : Prop := ∃ k₁ ∈ K, ∃ k₂ ∈ K, b = k₁ * a * k₂

theorem SameDC.refl (K : Subgroup G) (a : G) : SameDC K a a :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem SameDC.symm {K : Subgroup G} {a b : G} (h : SameDC K a b) : SameDC K b a := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  exact ⟨k₁⁻¹, inv_mem h₁, k₂⁻¹, inv_mem h₂, by group⟩

theorem SameDC.trans {K : Subgroup G} {a b c : G} (h : SameDC K a b) (h' : SameDC K b c) : SameDC K a c := by
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h
  obtain ⟨l₁, i₁, l₂, i₂, rfl⟩ := h'
  exact ⟨l₁ * k₁, mul_mem i₁ h₁, k₂ * l₂, mul_mem h₂ i₂, by group⟩

theorem exists_dc_choice (K : Subgroup G) (a : G) :
    ∃ r : G → G, r a = a ∧ (∀ z, SameDC K z (r z)) ∧ ∀ b c, SameDC K b c → r b = r c := by
  classical
  let s : Setoid G := ⟨SameDC K, ⟨SameDC.refl K, SameDC.symm, SameDC.trans⟩⟩
  refine ⟨fun z => if SameDC K a z then a else (Quotient.mk s z).out, ?_, fun z => ?_, fun b c hbc => ?_⟩
  · simp [SameDC.refl K a]
  · by_cases hz : SameDC K a z
    · simpa [hz] using hz.symm
    · simp only [hz, if_false]
      exact SameDC.symm (Quotient.exact (s := s) (Quotient.out_eq (Quotient.mk s z)))
  · by_cases hb : SameDC K a b
    · simp [hb, hb.trans hbc]
    · have hc : ¬ SameDC K a c := fun h => hb (h.trans hbc.symm)
      simp only [hb, hc, if_false]
      rw [Quotient.sound (s := s) hbc]

theorem Reps.uniq {K : Subgroup G} {g a b c x : G} {R : Finset G} (h : Reps K g R) (ha : a ∈ R) (hb : b ∈ R)
    (e₁ : c⁻¹ * (x * a) ∈ K) (e₂ : c⁻¹ * (x * b) ∈ K) : a = b := by
  refine (h.2 b (h.1 b hb)).unique ⟨ha, ?_⟩ ⟨hb, by rw [inv_mul_cancel]; exact one_mem _⟩
  have := mul_mem (inv_mem e₁) e₂
  convert this using 1
  group

theorem Reps.exists_left {K : Subgroup G} {g γ k : G} {R R' : Finset G} (h : Reps K g R) (h' : Reps K g R')
    (hγ : γ ∈ R) (hk : k ∈ K) : ∃ δ ∈ R', δ⁻¹ * (k * γ) ∈ K := by
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h.1 γ hγ
  obtain ⟨δ, ⟨hδ, hd⟩, -⟩ := h'.2 (k * γ) ⟨k * k₁, mul_mem hk h₁, k₂, h₂, by rw [e]; group⟩
  exact ⟨δ, hδ, hd⟩

open Classical in

noncomputable def pairMult (K : Subgroup G) (R₁ R₂ : Finset G) (y : G) : ℕ :=
  ((R₁ ×ˢ R₂).filter fun p => (p.1 * p.2)⁻¹ * y ∈ K).card

theorem pairMult_le {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ y ≤ pairMult K R₁ R₂ (k * y) := by
  classical
  have ex1 : ∀ γ, γ ∈ R₁ → ∃ δ, δ ∈ R₁ ∧ δ⁻¹ * (k * γ) ∈ K := fun γ hγ =>
    (h₁.exists_left h₁ hγ hk).imp fun _ h => ⟨h.1, h.2⟩
  have ex2 : ∀ κ γ, κ ∈ K → γ ∈ R₂ → ∃ δ, δ ∈ R₂ ∧ δ⁻¹ * (κ * γ) ∈ K := fun κ γ hκ hγ =>
    (h₂.exists_left h₂ hγ hκ).imp fun _ h => ⟨h.1, h.2⟩
  choose! a ha using ex1
  choose! b hb using ex2
  unfold pairMult
  refine Finset.card_le_card_of_injOn (fun p => (a p.1, b ((a p.1)⁻¹ * (k * p.1)) p.2)) ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    have hκ := (ha _ p1).2
    have hb' := hb _ _ hκ p2
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(ha _ p1).1, hb'.1⟩, ?_⟩)
    have := mul_mem hb'.2 hp'.2
    convert this using 1
    simp only
    group
  · intro p hp q hq e
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp'.1
    obtain ⟨q1, q2⟩ := Finset.mem_product.1 hq'.1
    have e1 : a p.1 = a q.1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e2
    have f1 : p.1 = q.1 := h₁.uniq p1 q1 (ha _ p1).2 (e1 ▸ (ha _ q1).2)
    rw [e1, f1] at e2
    have hκ := (ha _ q1).2
    have f2 : p.2 = q.2 := h₂.uniq p2 q2 (hb _ _ hκ p2).2 (e2 ▸ (hb _ _ hκ q2).2)
    exact Prod.ext f1 f2

theorem pairMult_mul_left {K : Subgroup G} {g h k : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (hk : k ∈ K) (y : G) : pairMult K R₁ R₂ (k * y) = pairMult K R₁ R₂ y := by
  refine le_antisymm ?_ (pairMult_le h₁ h₂ hk y)
  simpa using pairMult_le h₁ h₂ (inv_mem hk) (k * y)

theorem pairMult_mul_right {K : Subgroup G} {k : G} (R₁ R₂ : Finset G) (hk : k ∈ K) (y : G) :
    pairMult K R₁ R₂ (y * k) = pairMult K R₁ R₂ y := by
  classical
  unfold pairMult
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [← mul_assoc, Subgroup.mul_mem_cancel_right _ hk]

theorem pairMult_dc {K : Subgroup G} {g h a b : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    (e : SameDC K a b) : pairMult K R₁ R₂ b = pairMult K R₁ R₂ a := by
  obtain ⟨k₁, i₁, k₂, i₂, rfl⟩ := e
  rw [pairMult_mul_right _ _ i₂, pairMult_mul_left h₁ h₂ i₁]

open Classical in
theorem sum_single_of_dc {K : Subgroup G} {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y) {M : Type} [AddCommMonoid M] (F : G → M)
    (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) {z x₀ : G} (hx₀ : x₀ ∈ T) (hz : SameDC K x₀ z) :
    F z = ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * z ∈ K then F y else 0 := by
  obtain ⟨y₀, ⟨hy₀, e⟩, hu⟩ := (hS x₀ hx₀).2 z hz
  rw [Finset.sum_eq_single x₀ ?_ (fun h => absurd hx₀ h), Finset.sum_eq_single y₀ ?_ (fun h => absurd hy₀ h),
    if_pos e]
  · have := hF y₀ _ e
    rwa [mul_inv_cancel_left] at this
  · intro y hy hne
    exact if_neg fun h => hne (hu y ⟨hy, h⟩)
  · intro x hx hne
    refine Finset.sum_eq_zero fun y hy => if_neg fun h => hne ?_
    have hxy : SameDC K x y := (hS x hx).1 y hy
    have hyz : SameDC K y z := ⟨1, one_mem _, _, h, by group⟩
    exact hT x hx x₀ hx₀ ((hxy.trans hyz).trans hz.symm)

theorem sum_pairs_eq {K : Subgroup G} {g h : G} {R₁ R₂ : Finset G} (h₁ : Reps K g R₁) (h₂ : Reps K h R₂)
    {T : Finset G} {S : G → Finset G} (hS : ∀ x ∈ T, Reps K x (S x))
    (hT : ∀ x ∈ T, ∀ y ∈ T, SameDC K x y → x = y)
    (hcov : ∀ p ∈ R₁ ×ˢ R₂, ∃ x ∈ T, SameDC K x (p.1 * p.2))
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ x, ∀ l ∈ K, F (x * l) = F x) :
    ∑ γ ∈ R₁, ∑ γ' ∈ R₂, F (γ * γ') = ∑ x ∈ T, pairMult K R₁ R₂ x • ∑ y ∈ S x, F y := by
  classical
  rw [← Finset.sum_product' (f := fun γ γ' => F (γ * γ'))]
  have e1 : ∀ p ∈ R₁ ×ˢ R₂, F (p.1 * p.2) =
      ∑ x ∈ T, ∑ y ∈ S x, if y⁻¹ * (p.1 * p.2) ∈ K then F y else 0 := fun p hp => by
    obtain ⟨x, hx, hd⟩ := hcov p hp
    convert sum_single_of_dc hS hT F hF hx hd
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← Finset.sum_filter, Finset.sum_const, ← pairMult_dc h₁ h₂ ((hS x hx).1 y hy : SameDC K x y)]
  unfold pairMult
  congr 2
  refine Finset.filter_congr fun p _ => ?_
  have e : (p.1 * p.2)⁻¹ * y = (y⁻¹ * (p.1 * p.2))⁻¹ := by group
  rw [e, inv_mem_iff]

theorem reps_mul_decomp : ∀ {G : Type} [Group G] (K : Subgroup G) (g h : G) (R₁ R₂ : Finset G), GlobalTheory.SphLabelOps.Reps K g R₁ → GlobalTheory.SphLabelOps.Reps K h R₂ → ∃ (T : Finset G) (m : G → ℕ), g * h ∈ T ∧ (∀ x ∈ T, 0 < m x ∧ ∃ γ ∈ R₁, ∃ γ' ∈ R₂, ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * (γ * γ') * k₂) ∧ (∀ x ∈ T, ∀ y ∈ T, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → x = y) ∧ ∀ (S : G → Finset G), (∀ x ∈ T, GlobalTheory.SphLabelOps.Reps K x (S x)) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M), (∀ k ∈ K, π k u = u) → ∑ γ ∈ R₁, ∑ γ' ∈ R₂, π (γ * γ') u = ∑ x ∈ T, m x • ∑ y ∈ S x, π y u := by
  intro G _ K g h R₁ R₂ h₁ h₂
  classical
  obtain ⟨r, r0, r1, r2⟩ := exists_dc_choice K (g * h)
  have rr : ∀ z, r (r z) = r z := fun z => (r2 _ _ (r1 z)).symm
  have fixT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), r x = x := fun x hx => by
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    exact rr _
  have hT : ∀ x ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)),
      ∀ y ∈ (R₁ ×ˢ R₂).image (fun p => r (p.1 * p.2)), SameDC K x y → x = y := fun x hx y hy e => by
    rw [← fixT x hx, ← fixT y hy]
    exact r2 _ _ e
  refine ⟨(R₁ ×ˢ R₂).image fun p => r (p.1 * p.2), pairMult K R₁ R₂, ?_, fun x hx => ?_, hT,
    fun S hS M _ _ π u hu => ?_⟩
  · obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h₁.2 g (SameDC.refl K g)
    obtain ⟨γ', ⟨hγ', e'⟩, -⟩ := h₂.2 (γ⁻¹ * g * h) ⟨_, e, 1, one_mem _, by group⟩
    refine Finset.mem_image.2 ⟨(γ, γ'), Finset.mem_product.2 ⟨hγ, hγ'⟩, ?_⟩
    have hd : SameDC K (γ * γ') (g * h) := ⟨1, one_mem _, _, e', by group⟩
    exact (r2 _ _ hd).trans r0
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p1, p2⟩ := Finset.mem_product.1 hp
    refine ⟨?_, p.1, p1, p.2, p2, r1 _⟩
    rw [pairMult_dc h₁ h₂ (r1 _)]
    refine Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩⟩
    rw [inv_mul_cancel]
    exact one_mem _
  · refine sum_pairs_eq h₁ h₂ hS hT (fun p hp => ⟨_, Finset.mem_image_of_mem _ hp, (r1 _).symm⟩)
      (fun z => π z u) fun x l hl => ?_
    rw [map_mul, Module.End.mul_apply, hu l hl]

end GlobalTheory.SphLabelOps
