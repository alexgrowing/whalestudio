import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.FibreCorr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}

theorem mem_O_of_isHom (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x : M.Z} {F : Ω} (hF : F ∈ M₁.O (π x)) : F ∈ M.O x := by
  simpa using hπ.map_mem_O hF

theorem norm_val_le_one' (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) {F : Ω} (hF : F ∈ M₁.O z) : ‖M.val (gPt q ≫ y) F‖ ≤ 1 :=
  RatModel.norm_val_le_one rfl (mem_O_of_isHom hπ (hy ▸ hF))

theorem bound_mono {r s t : ℝ} {Q : Ω → Prop} {g : Ω → ℝ} (hs : s ≤ r) (H : r ≤ t ∨ ∃ h, Q h ∧ r ≤ g h) :
    s ≤ t ∨ ∃ h, Q h ∧ s ≤ g h :=
  H.imp hs.trans fun ⟨h, hq, hr⟩ => ⟨h, hq, hs.trans hr⟩

theorem nonUnitAt_of_not_isUnit {z : M₁.Z} {h : M₁.O z} (hh : ¬ IsUnit h) : NonUnitAt M₁ z h := by
  refine ⟨h.2, ?_⟩
  by_cases h0 : (h : Ω) = 0
  · exact Or.inl h0
  · exact Or.inr fun hi => hh ((RatModel.isUnit_O_iff h).2 ⟨h0, hi⟩)

theorem exists_nonUnit_pow (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) (e : ℕ) : ∀ F ∈ maximalIdeal (M₁.O z) ^ e, ∃ h : M₁.O z, ¬ IsUnit h ∧
      ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) (h : Ω)‖ ^ e := by
  have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
  have hO : ∀ a : M₁.O z, (a : Ω) ∈ M.O (y (cPt q)) := fun a => mem_O_of_isHom hπ (hy ▸ a.2)
  have hadd : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_add hs (hO a) (hO b)
  have hmul : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a * b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a * M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_mul hs (hO a) (hO b)
  induction e with
  | zero =>
    intro F _
    refine ⟨0, not_isUnit_zero, ?_⟩
    rw [pow_zero]
    exact norm_val_le_one' hπ hy F.2
  | succ n ih =>
    intro F hF
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF ?_ ?_
    · intro a ha b hb
      obtain ⟨h, hh, hle⟩ := ih a ha
      have hb' : ¬ IsUnit b := (mem_maximalIdeal b).1 hb
      rw [hmul, norm_mul]
      rcases le_total ‖M.val (gPt q ≫ y) (h : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with hc | hc
      · refine ⟨b, hb', ?_⟩
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (hle.trans (pow_le_pow_left₀ (norm_nonneg _) hc n)) (norm_nonneg _)
      · refine ⟨h, hh, ?_⟩
        rw [pow_succ]
        exact mul_le_mul hle hc (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    · rintro a b ⟨h₁, hh₁, h₁le⟩ ⟨h₂, hh₂, h₂le⟩
      rw [hadd]
      rcases le_total ‖M.val (gPt q ≫ y) (h₁ : Ω)‖ ‖M.val (gPt q ≫ y) (h₂ : Ω)‖ with hc | hc
      · exact ⟨h₂, hh₂, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (h₁le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)) h₂le)⟩
      · exact ⟨h₁, hh₁, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le h₁le (h₂le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)))⟩

variable (hπ : M₁.IsHom M (AlgHom.id o Ω) π)

def approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) : Ideal (M₁.O z) where
  carrier := {F | ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U →
    ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨
      ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e}
  add_mem' := by
    intro a b ha hb q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
      RatModel.val_add hs (mem_O_of_isHom hπ (hy ▸ a.2)) (mem_O_of_isHom hπ (hy ▸ b.2))
    rw [e1]
    rcases le_total ‖M.val (gPt q ≫ y) (a : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with h | h
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h le_rfl)) (hb q y hy hU f hf)
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl h)) (ha q y hy hU f hf)
  zero_mem' := by
    intro q _ y hy hU f hf
    left
    simp [RatModel.val_zero]
  smul_mem' := by
    intro c a ha q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((c • a : M₁.O z) : Ω) = M.val (gPt q ≫ y) c * M.val (gPt q ≫ y) a :=
      RatModel.val_mul hs (mem_O_of_isHom hπ (hy ▸ c.2)) (mem_O_of_isHom hπ (hy ▸ a.2))
    rw [e1, norm_mul]
    exact bound_mono (mul_le_of_le_one_left (norm_nonneg _) (norm_val_le_one' hπ hy c.2)) (ha q y hy hU f hf)

def fibreIdeal (D : EffCartierData M.Z) (z : M₁.Z) : Ideal (M₁.O z) where
  carrier := {G | ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x'}
  add_mem' := by
    intro a b ha hb x' hx f hf
    rw [Subalgebra.coe_add, add_div]
    exact add_mem (ha x' hx f hf) (hb x' hx f hf)
  zero_mem' := by
    intro x' hx f hf
    simp
  smul_mem' := by
    intro c a ha x' hx f hf
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_div_assoc]
    exact mul_mem (mem_O_of_isHom hπ (by rw [hx]; exact c.2)) (ha x' hx f hf)

variable {hπ}

theorem mem_fibreIdeal {D : EffCartierData M.Z} {z : M₁.Z} {G : M₁.O z} :
    G ∈ fibreIdeal hπ D z ↔ ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x' := Iff.rfl

theorem approxIdeal_antitone (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) :
    Antitone (approxIdeal hπ U D z) := by
  intro e e' hee F hF q _ y hy hU f hf
  rcases hF q y hy hU f hf with h | ⟨h, hh, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hh, hle.trans (pow_le_pow_of_le_one (norm_nonneg _) (norm_val_le_one' hπ hy hh.1) hee)⟩

theorem pow_le_approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) :
    maximalIdeal (M₁.O z) ^ e ≤ approxIdeal hπ U D z e := by
  intro F hF q _ y hy hU f hf
  obtain ⟨h, hh, hle⟩ := exists_nonUnit_pow hπ hy e F hF
  exact Or.inr ⟨h, nonUnitAt_of_not_isUnit hh, hle⟩

theorem isNoetherianRing_O [ArithBase o Ω] (M : RatModel o Ω) (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

end GlobalTheory.FibreCorr
