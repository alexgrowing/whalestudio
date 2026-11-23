import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports

namespace GlobalTheory.RootFin

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

open MvPowerSeries in
private lemma sum_dite_mem_eq_sum_equivFin {d : ℕ} (S : Finset (Fin d)) {M : Type*} [AddCommMonoid M] (F : S → M) :
    ∑ b, (if hb : b ∈ S then F ⟨b, hb⟩ else 0) = ∑ w : Fin S.card, F (S.equivFin.symm w) := by
  rw [Equiv.sum_comp S.equivFin.symm F,
    ← Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by simp [hb]), ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl (fun b _ => by simp [b.2])

open MvPowerSeries in
private lemma lc_sumF_eq_sum {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d m : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (g : Fin m → Fin d → PowerSeries C) (hg : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (g u)) (n : ℕ) :
    G.lc p (G.sumF g) n = ∑ u, G.lc p (g u) n := by
  funext c
  simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_sumF G g hg c, map_sum, Finset.sum_apply]

open MvPowerSeries in
private lemma lc_rescaleCurve_eq_pow_smul {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (p : ℕ)
    (x : C) {ga : Fin d → PowerSeries C} (hga : _root_.ReciprocityTheory.PGsh.IsCurve v ga) (n : ℕ) :
    G.lc p (_root_.ReciprocityTheory.PGsh.rescaleCurve x ga) n = x ^ (p ^ n) • G.lc p ga n := by
  funext c
  simp only [_root_.ReciprocityTheory.PGsh.LogFGL.lc, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_rescale G x (fun b => (hga b).1) c, PowerSeries.coeff_rescale, Pi.smul_apply, smul_eq_mul]

open MvPowerSeries in

theorem _root_.GlobalTheory.RootFin.root_fin : _root_.ReciprocityTheory.ChartRestriction.G.Sh.RootStatement → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (S : Finset (Fin d)),
      (∀ a ∈ S, _root_.ReciprocityTheory.PGsh.IsCurve v (γ a)) → (∀ a ∈ S, G.IsOfType p ty i (γ a)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C
          ((fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)))) ≤ j →
        ∃ (x y : Matrix (Fin d) (Fin d) C) (D : Finset (Fin d)), D ⊆ S ∧ D.card ≤ j ∧
          (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (x a b)) ∧ (∀ a b, _root_.ReciprocityTheory.PGsh.IsIntV v (y a b)) ∧
          (∀ a b, x a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧ (∀ a b, y a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧
          (∀ a c, a ∈ S → c ∈ S → ∑ b, x a b * y b c = if a = c then 1 else 0) ∧
          ∀ a ∈ S, a ∉ D → La (∑ b, x a b ^ (p ^ n) • G.lc p (γ b) n) = 0 := by
  intro hroot C _ _ _ v p hp hv d h ty i G γ S hcurve htype n j hn V _ _ La hrank
  set e : Fin S.card ≃ S := S.equivFin.symm with he
  set γS : Fin S.card → Fin d → PowerSeries C := fun u => γ (e u) with hγS
  have hcS : ∀ u, _root_.ReciprocityTheory.PGsh.IsCurve v (γS u) := fun u => hcurve _ (e u).2
  have htS : ∀ u, G.IsOfType p ty i (γS u) := fun u => htype _ (e u).2
  have hrange : Set.range (fun u => La (G.lc p (γS u) n)) = (fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨e u, (e u).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e.symm ⟨a, ha⟩, by simp [γS]⟩
  obtain ⟨T, hTint, hTdet, hrest⟩ := hroot C v p hp hv d h S.card ty i G γS hcS htS n j hn V La (hrange ▸ hrank)
  obtain ⟨-, -, hTzero⟩ := hrest
  have hTinv := _root_.ReciprocityTheory.ChartRestriction.G.Sh.pt_inv_int (fun a b => (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mp (hTint a b)) hTdet
  have hzero : _root_.ReciprocityTheory.PGsh.IsIntV v (0 : C) := (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (Subring.zero_mem _)
  set x : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hx
  set y : Matrix (Fin d) (Fin d) C := fun a b =>
    if ha : a ∈ S then if hb : b ∈ S then T⁻¹ (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) else 0 else 0 with hy
  set D : Finset (Fin d) := (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).image (fun w => (e w : Fin d)) with hD
  refine ⟨x, y, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
    exact (e w).2
  · refine Finset.card_image_le.trans ?_
    calc (Finset.univ.filter (fun w : Fin S.card => (w : ℕ) < j)).card ≤ (Finset.range j).card :=
          Finset.card_le_card_of_injOn (fun w => (w : ℕ)) (fun w hw => by simpa using hw)
            (fun a _ b _ hab => Fin.ext hab)
      _ = j := Finset.card_range j
  · intro a b
    simp only [hx]
    split_ifs
    · exact hTint _ _
    · exact hzero
    · exact hzero
  · intro a b
    simp only [hy]
    split_ifs
    · exact (_root_.ReciprocityTheory.ChartRestriction.G.Sh.ptIsIntV_iff _).mpr (hTinv.2 _ _)
    · exact hzero
    · exact hzero
  · intro a b hab
    simp only [hx] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a b hab
    simp only [hy] at hab
    split_ifs at hab with ha hb
    · exact ⟨ha, hb⟩
    · exact absurd rfl hab
    · exact absurd rfl hab
  · intro a c ha hc
    have hterm : ∀ b, x a b * y b c = if hb : b ∈ S then
        T (e.symm ⟨a, ha⟩) (e.symm ⟨b, hb⟩) * T⁻¹ (e.symm ⟨b, hb⟩) (e.symm ⟨c, hc⟩) else 0 := by
      intro b
      simp only [hx, hy, dif_pos ha, dif_pos hc]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T (e.symm ⟨a, ha⟩) (e.symm b) * T⁻¹ (e.symm b) (e.symm ⟨c, hc⟩))]
    simp only [← he, Equiv.symm_apply_apply]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hTinv.1, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
  · intro a ha haD
    set w := e.symm ⟨a, ha⟩ with hw
    have hjw : j ≤ (w : ℕ) := by
      by_contra hlt
      push_neg at hlt
      exact haD (Finset.mem_image.mpr ⟨w, by simp [hlt], by simp [hw]⟩)
    have key := hTzero w hjw
    have hp0 : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hterm : ∀ b, x a b ^ (p ^ n) • G.lc p (γ b) n = if hb : b ∈ S then
        T w (e.symm ⟨b, hb⟩) ^ (p ^ n) • G.lc p (γ b) n else 0 := by
      intro b
      simp only [hx, dif_pos ha, ← hw]
      split_ifs <;> simp [zero_pow hp0]
    rw [Finset.sum_congr rfl (fun b _ => hterm b),
      sum_dite_mem_eq_sum_equivFin S (fun b : S => T w (e.symm b) ^ (p ^ n) • G.lc p (γ b) n)]
    simp only [← he, Equiv.symm_apply_apply]
    rw [lc_sumF_eq_sum G p _ (fun u => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.isCurve_rescale (hTint w u) (hcS u))] at key
    rw [Finset.sum_congr rfl (fun u _ => lc_rescaleCurve_eq_pow_smul G p (T w u) (hcS u) n)] at key
    exact key

end GlobalTheory.RootFin
