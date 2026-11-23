import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MoveLatticeIsTermSameDatumWithWitnessesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TraceRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}

theorem hf_add {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

theorem hf_neg_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a y : Fin n → E) :
    hf L Hm a (-y) = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_swap {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (v w : Fin n → E) :
    hf L Hm w v = L.cj (hf L Hm v w) := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_swap_zero {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {v w : Fin n → E}
    (h0 : hf L Hm v w = 0) : hf L Hm w v = 0 := by
  rw [hf_swap h, h0, map_zero]

variable {r k : ℕ} (S : Frames L r k)

theorem frame_perp (g : Fin (r + 1) → S.V) (T : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then T else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (b : Fin (r + 1)) :
    n (g b) ∈ perp L S.Hm (S.spanTo g r) := by
  refine (hn.2.1 (g b)).2 ?_
  intro y hy
  apply hf_swap_zero S.herm.1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hg, if_neg]
    rintro ⟨rfl, -⟩
    simp at hi
  | zero => exact hf_zero _ _
  | add a c _ _ ha hc => rw [hf_add, ha, hc, add_zero]
  | smul c a _ ha => rw [hf_smul, ha, mul_zero]

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mof_transport (Λ : Submodule L.O S.V) (Y : Submodule E S.V) (g g' g₁ g₁' : Fin (r + 1) → S.V)
    (x x' u : S.V) (h1 : ∀ b, g₁ b = g b - S.h (g b) u • x) (h1' : ∀ b, g₁' b = g' b + S.h (g' b) u • x')
    (hO : ∀ b, S.h (g' b) u ∈ L.O) (hΛ : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ) (hY : x + x' ∈ Y)
    (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ y₁ ∈ Λ, y₁ ∈ Y ∧ m - S.h m u • x + y₁ ∈ S.Mof g₁ g₁' := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
      rw [add_zero, ← h1]
      exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · refine ⟨S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')), Λ.smul_mem ⟨_, hO b⟩ hΛ,
        Y.smul_mem _ (Y.smul_mem _ hY), ?_⟩
      have : algebraMap F E S.th⁻¹ • (g' b - g b) - S.h (algebraMap F E S.th⁻¹ • (g' b - g b)) u • x +
          S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')) = algebraMap F E S.th⁻¹ • (g₁' b - g₁ b) := by
        rw [h1, h1']
        simp only [Frames.h, hf_smul, hf_sub]
        module
      simp only []
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  | zero =>
    refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
    simp [Frames.h, hf_zero]
  | add a c _ _ ha hc =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    obtain ⟨z, hz, hz', hc⟩ := hc
    refine ⟨y + z, Λ.add_mem hy hz, Y.add_mem hy' hz', ?_⟩
    have : a + c - S.h (a + c) u • x + (y + z) = (a - S.h a u • x + y) + (c - S.h c u • x + z) := by
      simp only [Frames.h, hf_add]
      module
    rw [this]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    refine ⟨(c : E) • y, Λ.smul_mem c hy, Y.smul_mem _ hy', ?_⟩
    have : c • a - S.h (c • a) u • x + (c : E) • y = (c : E) • (a - S.h a u • x + y) := by
      change (c : E) • a - S.h ((c : E) • a) u • x + (c : E) • y = _
      simp only [Frames.h, hf_smul]
      module
    rw [this]
    exact Submodule.smul_mem _ c ha

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

end GlobalTheory.HL.TraceRep

open GlobalTheory.HL.TraceRep in

theorem GlobalTheory.HL.TraceRep.class_from_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hmv hw Λ₁ hΛ₁ y hy
  obtain ⟨w, hwΛ, hwW, huw⟩ := hw
  obtain ⟨hsx, -, -, -, -, -, -, hux, hux', hxX, hxX'⟩ :=
    GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e1, e2, e3, e4, hW₁⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨hSD, hW, hMs, -, hf', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  have hΛe : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (e4.trans hΛ₁.symm)
  rw [hΛe] at hW₁
  have hM₁ := (GlobalTheory.HL.WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁).2.1
  obtain ⟨hx, hx', ⟨t, ht, hte⟩, -, huΛ, huY, -⟩ := hmv
  have hH := S.herm.1
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hSD.2 b).2 hb a ha
  have hp := frame_perp S S.f _ S.gram _ hW.2.2.1
  have hp' := frame_perp S S.f' _ S.gram' _ hW.2.2.2.1
  have hxME : x ∈ S.ME :=
    Submodule.mem_sup_left (spanTo_mono S S.f (Nat.le_succ r) hxX)
  have hyME : y ∈ S.ME := hy.2
  have hyΛ : eich L S.Hm x u s y ∈ Λ := by
    have : y ∈ (Λ₁ : Set S.V) := hy.1
    rw [hΛ₁] at this
    exact this
  have hκ : hf L S.Hm y x ∈ L.O := by
    have h1 := hint _ hyΛ _ hwΛ
    have h2 : hf L S.Hm y w = 0 := hf_swap_zero hH (hwW y hyME)
    have h3 : hf L S.Hm x w = 0 := hf_swap_zero hH (hwW x hxME)
    have h4 : hf L S.Hm u w = 1 := huw
    simp only [Frames.h, eich, hf_sub, hf_add, hf_smul, h2, h3, h4] at h1
    have := L.O.neg_mem h1
    simpa using this
  have hbΛ : y + hf L S.Hm y u • x ∈ Λ := by
    have : y + hf L S.Hm y u • x = eich L S.Hm x u s y + hf L S.Hm y x • (u + s • x) := by
      simp [eich]
    rw [this]
    exact Λ.add_mem hyΛ (Λ.smul_mem ⟨_, hκ⟩ (Λ.add_mem huΛ hsx))
  have hbs : y + hf L S.Hm y u • x ∈ S.sat Λ :=
    ⟨hbΛ, S.ME.add_mem hyME (S.ME.smul_mem _ hxME)⟩
  obtain ⟨y₀, hy₀Y, hm⟩ := (hlev _ hbs (j + 1)).1 (hF.2.2.1 _ hbs)
  have hy₀Λ : y₀ ∈ Λ := by
    have := Λ.sub_mem hbΛ (hMs hm).1
    simpa using this
  have hfrΛ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    (hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩) |>.1
  have hth : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ := by
    rw [hte, smul_smul, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_smul]
    exact ht
  obtain ⟨y₁, hy₁Λ, hy₁Y, hm₁⟩ := mof_transport S Λ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))
    (S.fr d Λ) (S.fr' d Λ) (fun b => (n₀⁻¹ * (S.wit d Λ).1) (S.f b))
    (fun b => (n'' * n₀' * (S.wit d Λ).2) (S.f' b)) x x' u
    (fun b => by
      change n₀⁻¹ (S.fr d Λ b) = _
      have h0 : hf L S.Hm (S.fr d Λ b) x = 0 := hp b x hxX
      rw [e1, eich, h0, hf_neg_right]
      simp [Frames.h, sub_eq_add_neg])
    (fun b => by
      change n'' (n₀' (S.fr' d Λ b)) = _
      have h0 : hf L S.Hm (S.fr' d Λ b) x' = 0 := hp' b x' hxX'
      rw [e3 (n₀' (S.fr' d Λ b)) ((hn₀'.2.1 _).2 (hp' b)), e2, eich, h0]
      simp [Frames.h])
    (fun b => hint _ (hfrΛ b) _ huΛ) hth (Submodule.add_mem_sup hx hx') _ hm
  refine ⟨y₀ - y₁, Λ.sub_mem hy₀Λ hy₁Λ, Submodule.sub_mem _ hy₀Y hy₁Y, ?_⟩
  rw [hM₁]
  have h5 : hf L S.Hm x u = 0 := hf_swap_zero hH hux
  have h6 : hf L S.Hm y₀ u = 0 := hf_swap_zero hH (huY y₀ hy₀Y)
  have : y - (y₀ - y₁) = y + hf L S.Hm y u • x - y₀ - S.h (y + hf L S.Hm y u • x - y₀) u • x + y₁ := by
    simp only [Frames.h, hf_sub, hf_add, hf_smul, h5, h6]
    module
  rw [this]
  exact hm₁
