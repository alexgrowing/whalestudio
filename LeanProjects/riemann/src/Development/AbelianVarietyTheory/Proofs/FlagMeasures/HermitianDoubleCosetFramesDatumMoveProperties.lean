import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveFacts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_form {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm y x = L.cj (hf L Hm x y) := by
  have h' : cT L Hm = Hm := h
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h' j) i
  unfold hf
  simp_rw [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hf_add_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → E) : hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (x y : Fin n → E) : hf L Hm (c • x) y = c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hf_zero_left_flag_measures (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin n → E) : hf L Hm 0 y = 0 := by
  simp [hf]

theorem form_zero_of_span {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (A : Set (Fin n → E)) (hA : ∀ a ∈ A, ∀ b ∈ A, hf L Hm a b = 0) :
    ∀ x ∈ Submodule.span E A, ∀ y ∈ Submodule.span E A, hf L Hm x y = 0 := by
  intro x hx y hy
  have h1 : ∀ a ∈ A, ∀ z ∈ Submodule.span E A, hf L Hm z a = 0 := by
    intro a ha z hz
    induction hz using Submodule.span_induction with
    | mem w hw => exact hA w hw a ha
    | zero => exact hf_zero_left_flag_measures L Hm a
    | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]
  induction hx using Submodule.span_induction with
  | mem w hw => rw [conj_form h y w, h1 w hw y hy, map_zero]
  | zero => exact hf_zero_left_flag_measures L Hm y
  | add u v _ _ hu hv => rw [hf_add_left_flag_measures', hu, hv, add_zero]
  | smul c u _ hu => rw [hf_smul_left_flag_measures', hu, mul_zero]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem iso_spanTo (g : Fin (r + 1) → S.V) (c : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then c else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : S.h x x = 0 := by
  have hH : IsHerm L S.Hm := S.herm.1
  show hf L S.Hm x x = 0
  refine form_zero_of_span hH (g '' {i | (i : ℕ) < r}) ?_ x hx x hx
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have ha' : (a : ℕ) < r := ha
  have hne : a ≠ Fin.last r := fun e => by subst e; simp at ha'
  rw [hg, if_neg (fun hc => hne hc.1)]

theorem mem_span_frame (g : Fin (r + 1) → S.V) (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r)
    (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    x ∈ Submodule.span E (Set.range fun b => n (g b)) := by
  have key : ∀ m : ℕ, m ≤ r → S.spanTo g m ≤ Submodule.span E (Set.range fun b => n (g b)) := by
    intro m
    induction m with
    | zero =>
      intro _
      unfold Frames.spanTo
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm
      have hm' : m < r := by omega
      have h0 : n ∈ S.Nof g := hn
      unfold Frames.Nof at h0
      have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h0).1).2
      have hU : n ∈ unipOn (S.spanTo g (m + 1)) (S.spanTo g m) := Subgroup.mem_iInf.mp hI ⟨m, hm'⟩
      have hU' : (∀ v, n v ∈ S.spanTo g (m + 1) ↔ v ∈ S.spanTo g (m + 1)) ∧
          ∀ v ∈ S.spanTo g (m + 1), n v - v ∈ S.spanTo g m := hU
      have hsub : S.spanTo g (m + 1) ≤ Submodule.span E (Set.range fun b => n (g b)) := by
        unfold Frames.spanTo
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        have hgi : g i ∈ S.spanTo g (m + 1) := Submodule.subset_span ⟨i, hi, rfl⟩
        have h2 := ih hm'.le (hU'.2 (g i) hgi)
        have h3 : n (g i) ∈ Submodule.span E (Set.range fun b => n (g b)) :=
          Submodule.subset_span ⟨i, rfl⟩
        have h4 := Submodule.sub_mem _ h3 h2
        rwa [sub_sub_cancel] at h4
      exact hsub
  exact key (j + 1) (Nat.succ_le_of_lt j.2) hx

theorem parts_of_mem_Mof (hth : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O)
    (g g' : Fin (r + 1) → S.V) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ ξ ∈ Submodule.span L.O (Set.range g), ∃ ξ' ∈ Submodule.span L.O (Set.range g'),
      algebraMap F E S.th • m = ξ + ξ' := by
  have hinv : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨algebraMap F E S.th • g b, ?_, 0, zero_mem _, by rw [add_zero]⟩
      exact Submodule.smul_mem _ (⟨algebraMap F E S.th, hO⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · refine ⟨-g b, neg_mem (Submodule.subset_span ⟨b, rfl⟩), g' b, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
      show algebraMap F E S.th • algebraMap F E S.th⁻¹ • (g' b - g b) = -g b + g' b
      rw [smul_smul, hinv, one_smul, sub_eq_neg_add]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    obtain ⟨b, hb, b', hb', e'⟩ := hv
    exact ⟨a + b, add_mem ha hb, a' + b', add_mem ha' hb', by rw [smul_add, e, e']; abel⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    refine ⟨c • a, Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', ?_⟩
    show algebraMap F E S.th • ((c : E) • u) = (c : E) • a + (c : E) • a'
    rw [smul_smul, mul_comm (algebraMap F E S.th) (c : E), ← smul_smul, e, smul_add]

theorem move_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hM
  obtain ⟨hx, hx', hin, -, -, huperp, ⟨c, hcO, hs⟩, -⟩ := hM
  obtain ⟨y, hyΛ, hxy⟩ := id hin
  obtain ⟨⟨-, -, hint⟩, -⟩ := hF
  have hj : (j : ℕ) + 1 ≤ r := Nat.succ_le_of_lt j.2
  have hxX : x ∈ S.X := spanTo_mono S S.f hj hx
  have hx'X : x' ∈ S.X' := spanTo_mono S S.f' hj hx'
  have hH : IsHerm L S.Hm := S.herm.1
  have hxx : S.h x x = 0 := iso_spanTo S S.f _ S.gram x hxX
  have hx'x' : S.h x' x' = 0 := iso_spanTo S S.f' _ S.gram' x' hx'X
  have hperp : ∀ z ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1), hf L S.Hm u z = 0 := huperp
  have hux : S.h u x = 0 := hperp x (Submodule.mem_sup_left hx)
  have hux' : S.h u x' = 0 := hperp x' (Submodule.mem_sup_right hx')
  obtain ⟨c0, hc0, he⟩ := hint x hxX x' hx'X x hxX x' hx'X hin hin
  have he' : hf L S.Hm x x' = algebraMap F E S.th * c0 := he
  have hcross : S.h x' x = algebraMap F E S.th * L.cj c0 := by
    show hf L S.Hm x' x = _
    rw [conj_form hH x x', he', map_mul, AlgEquiv.commutes]
  obtain ⟨-, hW, -, hfrL, hfr'L, hli, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -⟩ := hW
  obtain ⟨-, -, -, -, -, hth, hthO, -⟩ := GlobalTheory.FrameBasic.frames_basic L r k S
  obtain ⟨-, -, -, -, -, -, -, -, hMa, -, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT
  have hthE : algebraMap F E S.th ∈ L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).mpr hthO
  have hinv : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hth, map_one]
  have hsum : x + x' ∈ S.ME :=
    add_mem (Submodule.mem_sup_left (spanTo_mono S S.f (by omega) hx))
      (Submodule.mem_sup_right (spanTo_mono S S.f' (by omega) hx'))
  have hyeq : y = algebraMap F E S.th⁻¹ • (x + x') := by
    rw [hxy, smul_smul, hinv, one_smul]
  have hyME : y ∈ S.ME := by rw [hyeq]; exact Submodule.smul_mem _ _ hsum
  have hysat : y ∈ S.sat Λ := Submodule.mem_inf.mpr ⟨hyΛ, hyME⟩
  obtain ⟨ξ, hξ, ξ', hξ', hsplit⟩ :=
    parts_of_mem_Mof S hth hthE (S.fr d Λ) (S.fr' d Λ) _ (hMa y hysat)
  set P := algebraMap F E ((S.ϖ : F) ^ S.a) with hP
  have hsplit' : P • x + P • x' = ξ + ξ' := by
    rw [← smul_add, hxy, smul_comm]; exact hsplit
  have hxfr : x ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    mem_span_frame S S.f (S.wit d Λ).1 hn j x hx
  have hx'fr : x' ∈ Submodule.span E (Set.range (S.fr' d Λ)) :=
    mem_span_frame S S.f' (S.wit d Λ).2 hn' j x' hx'
  have hdis := (linearIndependent_sum.mp hli).2.2
  have hw1 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr d Λ)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hxfr)
      (Submodule.span_le_restrictScalars L.O E _ hξ)
  have hw2 : P • x - ξ ∈ Submodule.span E (Set.range (S.fr' d Λ)) := by
    have e : P • x - ξ = ξ' - P • x' := by
      rw [sub_eq_sub_iff_add_eq_add, hsplit', add_comm]
    rw [e]
    exact Submodule.sub_mem _ (Submodule.span_le_restrictScalars L.O E _ hξ')
      (Submodule.smul_mem _ _ hx'fr)
  have hPx : P • x = ξ := sub_eq_zero.mp ((Submodule.disjoint_def.mp hdis) _ hw1 hw2)
  have hPx' : P • x' = ξ' := by rw [hPx] at hsplit'; exact add_left_cancel hsplit'
  have hfrΛ : ∀ b, S.fr d Λ b ∈ Λ := fun b =>
    ((hfrL (r + 1) le_rfl (S.fr d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hfr'Λ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    ((hfr'L (r + 1) le_rfl (S.fr' d Λ b)).mpr (Submodule.subset_span ⟨b, b.2, rfl⟩)).1
  have hξΛ : ξ ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfrΛ b) hξ
  have hξ'Λ : ξ' ∈ Λ := Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact hfr'Λ b) hξ'
  have key : ∀ z, P • z ∈ Λ → s • z ∈ Λ ∧ L.cj s • z ∈ Λ := by
    intro z hz
    have hc' : L.cj c ∈ L.O := GlobalTheory.UnramOrder.cj_mem L hcO
    have h1 : s • z = (⟨c, hcO⟩ : L.O) • (P • z) := by
      rw [hs]; show (P * c) • z = c • (P • z); rw [smul_smul, mul_comm c P]
    have h2 : L.cj s • z = (⟨L.cj c, hc'⟩ : L.O) • (P • z) := by
      rw [hs, map_mul, AlgEquiv.commutes]; show (P * L.cj c) • z = L.cj c • (P • z)
      rw [smul_smul, mul_comm (L.cj c) P]
    exact ⟨h1 ▸ Λ.smul_mem _ hz, h2 ▸ Λ.smul_mem _ hz⟩
  have kx := key x (hPx ▸ hξΛ)
  have kx' := key x' (hPx' ▸ hξ'Λ)
  exact ⟨kx.1, kx.2, kx'.1, kx'.2, ⟨L.cj c0, GlobalTheory.UnramOrder.cj_mem L hc0, hcross⟩, hxx, hx'x',
    hux, hux', hxX, hx'X⟩

end GlobalTheory.HL.MoveFacts
