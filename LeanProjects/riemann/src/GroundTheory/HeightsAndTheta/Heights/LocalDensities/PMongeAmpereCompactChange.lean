import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.CompactSupportStokes
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB

open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

namespace MongeAmpereCompactChange

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_perm (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (σ : Equiv.Perm (Fin e))
    (j : Fin A.n) (y : Fin e → ℂ) : locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
  unfold locDens maDens
  congr 2
  exact mdisc_comp_perm'
    (fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ

theorem integrableOn_indicator [T2Space X] (A : FinHolAtlas e X) (χ : ChartPartition A)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (k : Fin A.n) {K : Set X}
    (hK : IsCompact K) :
    IntegrableOn (fun y => χ.χ k ((A.chart k).symm y) * K.indicator 1 ((A.chart k).symm y) *
      locDens A Ψ k y) (A.chart k).target := by
  have hS : IsCompact (tsupport (χ.χ k) ∩ K) := hK.inter_left (isClosed_tsupport _)
  have hSk : tsupport (χ.χ k) ∩ K ⊆ (A.chart k).source :=
    inter_subset_left.trans (χ.tsupport_subset k)
  have hC : IsCompact ((A.chart k) '' (tsupport (χ.χ k) ∩ K)) :=
    hS.image_of_continuousOn ((A.chart k).continuousOn.mono hSk)
  have hCt : (A.chart k) '' (tsupport (χ.χ k) ∩ K) ⊆ (A.chart k).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart k).map_source (hSk hx)
  have hGc : ContinuousOn (fun y => χ.χ k ((A.chart k).symm y) * locDens A Ψ k y)
      (A.chart k).target :=
    (CompactSupportStokes.chi_contOn A χ k k).mul (locDensCont A Ψ hΨ k)
  have hM : MeasurableSet ((A.chart k).target ∩ (A.chart k).symm ⁻¹' K) := by
    have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' Kᶜ) :=
      (A.chart k).isOpen_inter_preimage_symm hK.isClosed.isOpen_compl
    have : (A.chart k).target ∩ (A.chart k).symm ⁻¹' K =
        (A.chart k).target \ ((A.chart k).target ∩ (A.chart k).symm ⁻¹' Kᶜ) := by
      ext y; simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]; tauto
    rw [this]
    exact (A.chart k).open_target.measurableSet.diff ho.measurableSet
  have h1 := ((hGc.mono hCt).integrableOn_compact (μ := volume) hC).indicator hM
  have h2 : IntegrableOn (fun y => χ.χ k ((A.chart k).symm y) * K.indicator 1 ((A.chart k).symm y) *
      locDens A Ψ k y) ((A.chart k) '' (tsupport (χ.χ k) ∩ K)) := by
    refine h1.congr_fun (fun y hy => ?_) hC.isClosed.measurableSet
    by_cases hyK : (A.chart k).symm y ∈ K
    · rw [indicator_of_mem (show y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' K from
        ⟨hCt hy, hyK⟩), indicator_of_mem hyK]
      simp
    · rw [indicator_of_notMem (fun h => hyK h.2), indicator_of_notMem hyK]
      simp
  refine h2.of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet ?_
  rintro y ⟨hy, hyC⟩
  by_cases hyK : (A.chart k).symm y ∈ K
  · have : (A.chart k).symm y ∉ tsupport (χ.χ k) := fun h =>
      hyC ⟨(A.chart k).symm y, ⟨h, hyK⟩, (A.chart k).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  · simp [indicator_of_notMem hyK]

theorem step [T2Space X] {n : ℕ} (A : FinHolAtlas (n + 1) X) (χ : ChartPartition A)
    (Ψ : Fin (n + 1) → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (a : Fin (n + 1)) (v : X → ℝ)
    (hv : A.Smooth v) (hvc : HasCompactSupport v) {K : Set X} (hK : IsCompact K)
    (hvK : tsupport v ⊆ K) :
    integralWith A χ (Function.update Ψ a (Ψ a + LocPot.ofFun v)) (K.indicator 1) =
      integralWith A χ Ψ (K.indicator 1) := by
  classical
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 a
  have hne : ∀ i : Fin n, σ i.succ ≠ a := by
    intro i h
    have : i.succ = σ a := by rw [← h, Equiv.swap_apply_self]
    rw [Equiv.swap_apply_right] at this
    exact Fin.succ_ne_zero i this
  set R : Fin n → LocPot X := fun i => Ψ (σ i.succ) with hRdef
  have hR : ∀ i, IsPotential A (R i) := fun i => hΨ _
  have hperm : ∀ Z : LocPot X, Function.update Ψ a Z ∘ σ = Fin.cons Z R := by
    intro Z
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [σ, Equiv.swap_apply_left]
    · simp [hRdef, Function.update_of_ne (hne i)]
  have hd : ∀ k, ∀ y ∈ (A.chart k).target,
      locDens A (Function.update Ψ a (Ψ a + LocPot.ofFun v)) k y =
        locDens A Ψ k y + locDens A (Fin.cons (LocPot.ofFun v) R) k y := by
    intro k y hy
    rw [← locDens_perm A _ σ, hperm, locDens_cons_add A _ _ R (hΨ a) (isPotential_ofFun A v hv) k hy,
      ← hperm (Ψ a), locDens_perm, Function.update_eq_self]
  have h0 : integralWith A χ (Fin.cons (LocPot.ofFun v) R) (K.indicator 1) = 0 := by
    rw [← CompactSupportStokes.stokes_compact_support A χ R hR v hv hvc]
    unfold integralWith
    refine Finset.sum_congr rfl fun k _ =>
      setIntegral_congr_fun (A.chart k).open_target.measurableSet fun y hy => ?_
    by_cases h : (A.chart k).symm y ∈ K
    · simp [indicator_of_mem h]
    · rw [st_locDens_cons_eq_zero A k v R hy (fun h' => h (hvK h'))]
      simp
  rw [← add_zero (integralWith A χ Ψ (K.indicator 1)), ← h0]
  unfold integralWith
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_add (integrableOn_indicator A χ Ψ hΨ k hK)
    (integrableOn_indicator A χ _ (st_isPotential_cons A hv hR) k hK)]
  refine setIntegral_congr_fun (A.chart k).open_target.measurableSet fun y hy => ?_
  rw [hd k y hy]
  ring

end MongeAmpereCompactChange

theorem MongeAmpereCompactChange.proof : MongeAmpereCompactChange.Statement := by
  intro e X _ _ A P v K hyp
  obtain ⟨hP, hv, hvc, hK, hvK⟩ := hyp
  classical
  unfold mInt
  split_ifs with h
  swap
  · rfl
  cases e with
  | zero =>
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n =>
    let Ψ : Finset (Fin (n + 1)) → Fin (n + 1) → LocPot X := fun S i =>
      if i ∈ S then P + LocPot.ofFun v else P
    have hΨ : ∀ S i, IsPotential A (Ψ S i) := by
      intro S i
      by_cases hi : i ∈ S
      · simp only [Ψ, if_pos hi]
        exact isPotentialAdd A _ _ hP (isPotential_ofFun A _ hv)
      · simp only [Ψ, if_neg hi]
        exact hP
    have key : ∀ S, integralWith A h.some (Ψ S) (K.indicator 1) =
        integralWith A h.some (Ψ ∅) (K.indicator 1) := by
      intro S
      induction S using Finset.induction_on with
      | empty => rfl
      | insert a S ha ih =>
        have hupd : Ψ (insert a S) = Function.update (Ψ S) a (Ψ S a + LocPot.ofFun v) := by
          funext i
          by_cases hi : i = a
          · subst hi
            simp [Ψ, ha]
          · simp [Ψ, hi]
        rw [hupd, MongeAmpereCompactChange.step A h.some (Ψ S) (hΨ S) a v hv hvc hK hvK, ih]
    have := key Finset.univ
    simpa [Ψ] using this

end GroundTheory.Heights₂.Heights.FourB
