import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_count_mono {α : Type} {X Y : Set α} (R : α → α → Prop) (h : X ⊆ Y) : cntCl X R ≤ cntCl Y R := by
  unfold cntCl
  have h1 : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} ⊆
      (fun O' : Set α => O' ∩ X) '' {O : Set α | ∃ a ∈ Y, O = {b | b ∈ Y ∧ R a b}} := by
    rintro O ⟨a, ha, rfl⟩
    refine ⟨{b | b ∈ Y ∧ R a b}, ⟨a, h ha, rfl⟩, ?_⟩
    ext b
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨h h2, h3⟩, h2⟩
  exact (Set.encard_le_encard h1).trans (Set.encard_image_le _ _)

section Num

variable (D : D7) (large₂ : SizeData₂ D)

theorem one_le_scale : (1 : ℝ) ≤ large₂.sc.b := by linarith [d_two_le_b D large₂]

theorem one_le_gram_size_generic (C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D large₂.sc.b C Z := by
  unfold sizeZ
  have h : ∀ τ : D.what₂.Tau, (1 : ℝ) ≤ ∏ l ∈ Finset.Icc 1 (D.R.rS + 1),
      max 1 (absDl D Z l τ / large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) := by
    intro τ
    calc (1 : ℝ) = ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_left _ _)
  calc (1 : ℝ) = ∏ τ : D.what₂.Tau, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun τ _ => h τ)

theorem pow_le_gram_height (C : ℝ) (Z : GramM D) :
    large₂.sc.b ^ (C ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) ≤ HHZ D large₂.sc.b C Z := by
  have hb := one_le_scale D large₂
  have hs := one_le_gram_size_generic D large₂ C Z
  unfold HHZ
  rw [← Real.rpow_mul (by linarith)]
  have h1 : C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * (D.R.m : ℝ)) = C ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f := by ring
  rw [h1]
  have h2 : (0 : ℝ) < large₂.sc.b ^ (C ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) := Real.rpow_pos_of_pos (by linarith) _
  have h3 : (1 : ℝ) ≤ sizeZ D large₂.sc.b C Z ^ 4 := one_le_pow₀ hs
  nlinarith

theorem one_le_gram_height (C : ℝ) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b C Z := by
  refine le_trans ?_ (pow_le_gram_height D large₂ C Z)
  exact Real.one_le_rpow (one_le_scale D large₂) (by positivity)

theorem one_le_m_alt : (1 : ℝ) ≤ D.R.m := by
  have := d_m_eq D
  exact_mod_cast (by omega : 1 ≤ D.R.m)

theorem norm_T_pos (u : D.what₂.Word) : 1 ≤ NT D u := by
  unfold NT
  exact one_le_pow₀ (by exact_mod_cast (D.mem u).A.T_prime.one_lt.le)

theorem scale_pow_le_gram_height {C K : ℝ} (hK : K ≤ C ^ 2) (Z : GramM D) :
    large₂.sc.b ^ (K * (D.R.m : ℝ) * D.R.f) ≤ HHZ D large₂.sc.b C Z := by
  refine le_trans ?_ (pow_le_gram_height D large₂ C Z)
  refine Real.rpow_le_rpow_of_exponent_le (one_le_scale D large₂) ?_
  have hm := one_le_m_alt D
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h1 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((D.R.m : ℝ) - 1), mul_nonneg (by linarith : (0:ℝ) ≤ (D.R.m:ℝ)) (by nlinarith : (0:ℝ) ≤ (D.R.m:ℝ)^2 - 1)]
  calc K * (D.R.m : ℝ) * D.R.f ≤ C ^ 2 * (D.R.m : ℝ) * D.R.f := by gcongr
    _ ≤ C ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f := by gcongr

theorem norm_T_le_pow {C' Cl Cg cb Cu cT CT C0 : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) :
    NT D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ) * D.R.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _, _⟩ := h.1
  have h23' : Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (h23 u).2
  have hb := one_le_scale D large₂
  unfold NT
  calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (CT * (D.R.m : ℝ))) ^ D.R.f := by
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) h23' _
    _ = large₂.sc.b ^ (CT * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]

theorem norm_T_sq_le_gram_height {C' Cl Cg cb Cu cT CT C0 C : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word)
    (hCT : 2 * CT ≤ C ^ 2) (Z : GramM D) : NT D u ^ 2 ≤ HHZ D large₂.sc.b C Z := by
  have hb := one_le_scale D large₂
  have h1 := norm_T_le_pow D large₂ h u
  have h0 := norm_T_pos D u
  calc NT D u ^ 2 ≤ (large₂.sc.b ^ (CT * (D.R.m : ℝ) * D.R.f)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 _
    _ = large₂.sc.b ^ (2 * CT * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    _ ≤ _ := scale_pow_le_gram_height D large₂ hCT Z

end Num

section C4

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PartnerThetaInclusion (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ∀ Z : GramM D,
  ∀ F'' ∈ Partners D Λ (lf D F0) F' Z,
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F'')

def GenericThetaSublattice (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → RelZ D (ZhatL (lf D F0) F') →
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
    latticeRank D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
    latticeDetW D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F')

end C4

section C4F

variable {eps : ℝ} (Fm : FamP eps)

def PositionCountFamilyGeneric (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    TermPositionCount (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def PartnerThetaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', PartnerThetaInclusion (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def GenericThetaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericThetaSublattice (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

end C4F

theorem class_count_fibres {α β : Type} (X : Set α) (R : α → α → Prop) (hR : Equivalence R) (φ : α → β) (B : Set β)
    (hφ : ∀ a ∈ X, φ a ∈ B) (K : ℝ≥0∞) (hK : ∀ y ∈ B, (cntCl {a | a ∈ X ∧ φ a = y} R : ℝ≥0∞) ≤ K) :
    (cntCl X R : ℝ≥0∞) ≤ (B.encard : ℝ≥0∞) * K := by
  set OO : Set (Set α) := {O | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} with hOO
  have hrep : ∀ O : OO, ∃ a ∈ X, (O : Set α) = {b | b ∈ X ∧ R a b} := fun O => O.2
  choose rep hrepX hrepE using hrep
  let S : β → Set (Set α) := fun y => {O | ∃ h : O ∈ OO, φ (rep ⟨O, h⟩) = y}
  have hS : ∀ y, (S y).encard ≤ cntCl {a | a ∈ X ∧ φ a = y} R := by
    intro y
    have hinj : Set.InjOn (fun O : Set α => O ∩ {a | φ a = y}) (S y) := by
      rintro O₁ ⟨h₁, hy₁⟩ O₂ ⟨h₂, hy₂⟩ hEq
      have e₁ := hrepE ⟨O₁, h₁⟩
      have e₂ := hrepE ⟨O₂, h₂⟩
      simp only at e₁ e₂
      have q₁ := Set.ext_iff.1 e₁
      have q₂ := Set.ext_iff.1 e₂
      have m₁ : rep ⟨O₁, h₁⟩ ∈ O₁ ∩ {a | φ a = y} := ⟨(q₁ _).2 ⟨hrepX _, hR.refl _⟩, hy₁⟩
      have hEq' : O₁ ∩ {a | φ a = y} = O₂ ∩ {a | φ a = y} := hEq
      have m₂ : rep ⟨O₁, h₁⟩ ∈ O₂ := ((Set.ext_iff.1 hEq' _).1 m₁).1
      have r21 : R (rep ⟨O₂, h₂⟩) (rep ⟨O₁, h₁⟩) := ((q₂ _).1 m₂).2
      ext b
      rw [q₁ b, q₂ b]
      constructor
      · rintro ⟨hb, hr⟩; exact ⟨hb, hR.trans r21 hr⟩
      · rintro ⟨hb, hr⟩; exact ⟨hb, hR.trans (hR.symm r21) hr⟩
    rw [← hinj.encard_image]
    unfold cntCl
    apply Set.encard_le_encard
    rintro _ ⟨O, ⟨h, hy⟩, rfl⟩
    refine ⟨rep ⟨O, h⟩, ⟨hrepX _, hy⟩, ?_⟩
    have e := hrepE ⟨O, h⟩
    simp only at e
    have q := Set.ext_iff.1 e
    show O ∩ {a | φ a = y} = _
    ext b
    constructor
    · rintro ⟨hbO, hy'⟩
      obtain ⟨hb, hr⟩ := (q b).1 hbO
      exact ⟨⟨hb, hy'⟩, hr⟩
    · rintro ⟨⟨hb, hy'⟩, hr⟩; exact ⟨(q b).2 ⟨hb, hr⟩, hy'⟩
  have hcover : OO ⊆ ⋃ y ∈ B, S y := by
    intro O hO
    simp only [Set.mem_iUnion]
    exact ⟨φ (rep ⟨O, hO⟩), hφ _ (hrepX _), hO, rfl⟩
  have hSK : ∀ y ∈ B, ((S y).encard : ℝ≥0∞) ≤ K := fun y hy =>
    le_trans (ENat.toENNReal_le.2 (hS y)) (hK y hy)
  show (OO.encard : ℝ≥0∞) ≤ _
  by_cases hB : B.Finite
  · have h1 : OO.encard ≤ ∑ y ∈ hB.toFinset, (S y).encard := by
      refine le_trans (Set.encard_le_encard ?_) (Finset.set_encard_biUnion_le hB.toFinset S)
      intro O hO
      have := hcover hO
      simpa using this
    have h2 : ((∑ y ∈ hB.toFinset, (S y).encard : ℕ∞) : ℝ≥0∞) = ∑ y ∈ hB.toFinset, ((S y).encard : ℝ≥0∞) :=
      map_sum ENat.toENNRealRingHom _ _
    calc (OO.encard : ℝ≥0∞) ≤ ((∑ y ∈ hB.toFinset, (S y).encard : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 h1
      _ = ∑ y ∈ hB.toFinset, ((S y).encard : ℝ≥0∞) := h2
      _ ≤ ∑ _y ∈ hB.toFinset, K := Finset.sum_le_sum fun y hy => hSK y (by simpa using hy)
      _ = (B.encard : ℝ≥0∞) * K := by
        rw [Finset.sum_const, nsmul_eq_mul, hB.encard_eq_coe_toFinset_card]; rfl
  · have hinf : B.encard = ⊤ := Set.Infinite.encard_eq hB
    rw [hinf, ENat.toENNReal_top]
    by_cases hK0 : K = 0
    · have hemp : OO = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro O hO
        have := hcover hO
        simp only [Set.mem_iUnion] at this
        obtain ⟨y, hy, hOy⟩ := this
        have h0 : ((S y).encard : ℝ≥0∞) ≤ 0 := hK0 ▸ hSK y hy
        have h0' : (S y).encard = 0 := by
          have : ((S y).encard : ℝ≥0∞) = 0 := le_antisymm h0 bot_le
          simpa using this
        rw [Set.encard_eq_zero] at h0'
        rw [h0'] at hOy
        exact hOy
      rw [hemp]; simp
    · rw [ENNReal.top_mul hK0]; exact le_top

section Mean

variable (D : D7)

theorem mean_le_of_mul {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (LatV D)) (N N' : LatV D → ℕ∞)
    {B K B2 : ℝ} (hB : 0 ≤ B) (h : MeanLe D F0 what₂ N' B)
    (hN : ∀ Λ ∈ what₂, (N Λ : ℝ≥0∞) ≤ (N' Λ : ℝ≥0∞) * ENNReal.ofReal K) (hle : B * K ≤ B2) :
    MeanLe D F0 what₂ N B2 := by
  unfold MeanLe at h ⊢
  calc ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N Λ : ℝ≥0∞)
      ≤ ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N' Λ : ℝ≥0∞) * ENNReal.ofReal K := by
        refine Finset.sum_le_sum fun Λ hΛ => ?_
        rw [mul_assoc]
        exact mul_le_mul_right (hN Λ hΛ) _
    _ = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N' Λ : ℝ≥0∞)) * ENNReal.ofReal K := by
        rw [Finset.sum_mul]
    _ ≤ (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal B * ENNReal.ofReal K := by
        exact mul_le_mul_left h _
    _ = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal (B * K) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul hB]
    _ ≤ _ := by
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hle) _

theorem mean_le_of_zero {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (LatV D)) (N : LatV D → ℕ∞)
    (B : ℝ) (hN : ∀ Λ ∈ what₂, N Λ = 0) : MeanLe D F0 what₂ N B := by
  unfold MeanLe
  have : ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N Λ : ℝ≥0∞) = 0 :=
    Finset.sum_eq_zero fun Λ hΛ => by rw [hN Λ hΛ]; simp
  rw [this]; exact bot_le

end Mean

end Formalism.MainNotions.BridgeLemma₂

end
