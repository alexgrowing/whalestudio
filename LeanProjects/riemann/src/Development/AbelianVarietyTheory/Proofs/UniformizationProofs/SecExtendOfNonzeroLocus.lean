import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem mem_wchart_oneTerm {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (k : K) {j : K → L.ι} {x : X} :
    x ∈ LB.wchart L (fun _ : K => 𝟙 X) j ↔ x ∈ L.U (j k) :=
  ⟨fun h => Set.mem_iInter.1 h k, fun h => Set.mem_iInter.2 fun k' => by
    obtain rfl := Subsingleton.elim k k'; exact h⟩

theorem exists_sec_oneTerm {X : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Unique K] [Fintype K'] [Unique K']
    {e e' : ℤ} (he : e = e') (s : (LB.LinComb L (fun _ : K => 𝟙 X) (fun _ => e)).Sec) :
    ∃ s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e')).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (s'.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) := by
  subst he
  have le : ∀ j : K' → L.ι, LB.wchart L (fun _ : K' => 𝟙 X) j ≤
      LB.wchart L (fun _ : K => 𝟙 X) (fun _ => j default) := fun j x hx =>
    (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hx)
  let s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)).Sec :=
    secOfGerm (M := LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)) (fun j => resG X (le j) (s.f fun _ => j default))
      fun y j j' hj hj' => by
        refine (gs_res (𝟙 X) y (le j) hj _).trans ((sec_trans s (𝟙 X) y (le j hj) (le j' hj')).trans
          (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hj' _).symm))
        refine Eq.trans ?_ (gm_linComb L (fun _ : K' => 𝟙 X) (fun _ => e) (𝟙 X) y j j' hj hj').symm
        rw [trF, Fintype.prod_unique, Fintype.prod_unique]
  have hs : ∀ (x : X) (j : K' → L.ι), x ∈ LB.wchart L (fun _ : K' => 𝟙 X) j →
      gs (𝟙 X) x _ (s'.f j) = gs (𝟙 X) x _ (s.f fun _ => j default) := fun x j hx => gs_res (𝟙 X) x (le j) hx _
  refine ⟨s', nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y j hj => ?_,
    fun x i hx => hs x _ ((mem_wchart_oneTerm default).2 hx)⟩
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j default, (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hj)⟩
  · rw [hs y j hj]
    exact (mem_nonzeroLocus_iff_isUnit s (le j hj)).symm

theorem sec_extend_of_nonzeroLocus : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (N : ℕ) (s : H0 L N), (∀ a : Γ(X, nonzeroLocus s), ∃ (m : ℕ) (t : H0 L (N * m)), ∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = Geo.Tor.gs (𝟙 X) x _ (s.f j) ^ m * Geo.Tor.gs (𝟙 X) x _ a) ∧ ∀ (n : ℕ) (t : H0 L n), (∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = 0) → ∃ m : ℕ, ∀ j : Fin 1 → L.ι, (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from s.f j) ^ m * (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from t.f j) = 0 := by
  intro X _ _ L hL N s
  have hj : ∀ j : Fin 1 → L.ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
  have hJ : ∀ j : PUnit.{1} → L.ι, ∃ i, j = fun _ => i := fun j => ⟨j PUnit.unit, rfl⟩
  obtain ⟨s', hl, hs⟩ : ∃ s' : (lbPow L N).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn s' fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) :=
    exists_sec_oneTerm L (K' := PUnit) rfl s
  refine ⟨fun a => ?_, fun n t ht => ?_⟩
  · obtain ⟨m, hm⟩ := exists_sec_eq_pow_mul (m := 0) hL s' (fun J => resG X (inf_le_left.trans hl.le) a)
      (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' h hJ hJ' => by
        rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
        exact (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ⟩ a).trans
          (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ'⟩ a).symm)
    obtain ⟨u, hu⟩ := hm m le_rfl
    obtain ⟨t, -, ht⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((N * m : ℕ) : ℤ)) (by rw [zero_add]) u
    refine ⟨m, t, fun x j hx hxj => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hy : x ∈ nonzeroLocus s' ⊓ powChart L (fun _ => i) := ⟨hl.ge hx, mem_powChart.2 hxj⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, gs_res _ x _ hy, hs x i hxj] at e
    exact (ht x i hxj).trans e
  · obtain ⟨t', -, ht'⟩ : ∃ t' : (lbPow L n).Sec, nonzeroLocus t' = nonzeroLocus t ∧
        ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn t' fun _ => i) = gs (𝟙 X) x _ (t.f fun _ => i) :=
      exists_sec_oneTerm L (K' := PUnit) rfl t
    obtain ⟨m, hm⟩ := exists_pow_mul_powFn_eq_zero hL s' t' fun J => fn_ext fun y hy => by
      obtain ⟨i, rfl⟩ := hJ J
      rw [gs_res _ y _ hy, gs_zero _ y _ hy, ht' y i (mem_powChart.1 hy.2)]
      exact ht y _ (hl.le hy.1) (mem_powChart.1 hy.2)
    refine ⟨m, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hi : y ∈ L.U i := (mem_wchart_oneTerm (j := fun _ : Fin 1 => i) 0).1 hy
    have hp : y ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have e := congrArg (gs (𝟙 X) y _) (hm fun _ => i)
    rw [gs_mul _ y _ hp, gs_pow _ y _ hp, gs_zero _ y _ hp, hs y i hi, ht' y i hi] at e
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_zero _ y _ hy]
    exact e

end GlobalTheory
