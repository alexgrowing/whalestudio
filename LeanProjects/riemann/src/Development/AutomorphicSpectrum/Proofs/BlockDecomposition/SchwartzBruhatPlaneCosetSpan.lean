import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Decomp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem add_mem_Ln {n : ℤ} {u v : F × F} (hu : u ∈ Ln F n) (hv : v ∈ Ln F n) :
    u + v ∈ Ln F n :=
  ⟨add_mem hu.1 hv.1, add_mem hu.2 hv.2⟩

theorem neg_mem_Ln {n : ℤ} {u : F × F} (hu : u ∈ Ln F n) : -u ∈ Ln F n :=
  ⟨neg_mem hu.1, neg_mem hu.2⟩

theorem zero_mem_Ln (n : ℤ) : (0 : F × F) ∈ Ln F n :=
  ⟨zero_mem _, zero_mem _⟩

theorem Ln_anti {m n : ℤ} (h : m ≤ n) : Ln F n ⊆ Ln F m :=
  fun _ hv => ⟨valBall_antitone h hv.1, valBall_antitone h hv.2⟩

theorem isOpen_Ln (n : ℤ) : IsOpen (Ln F n) :=
  ((isOpen_valBall n).preimage continuous_fst).inter ((isOpen_valBall n).preimage continuous_snd)

theorem exists_Ln_subset {U : Set (F × F)} (hU : U ∈ 𝓝 (0 : F × F)) : ∃ n : ℤ, Ln F n ⊆ U := by
  rw [show (0 : F × F) = ((0 : F), (0 : F)) from rfl, mem_nhds_prod_iff] at hU
  obtain ⟨u, hu, v, hv, huv⟩ := hU
  obtain ⟨a, -, ha⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hu
  obtain ⟨b, -, hb⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hv
  refine ⟨max a b, fun w hw => huv ?_⟩
  exact ⟨ha (valBall_antitone (le_max_left a b) hw.1),
    hb (valBall_antitone (le_max_right a b) hw.2)⟩

theorem exists_periodic {Ψ : F × F → ℂ} (hl : IsLocallyConstant Ψ) (hc : HasCompactSupport Ψ) :
    ∃ n : ℤ, ∀ y, ∀ h ∈ Ln F n, Ψ (y + h) = Ψ y := by
  have hloc : ∀ x : F × F, ∃ n : ℤ, ∀ h ∈ Ln F n, Ψ (x + h) = Ψ x := by
    intro x
    have ho : IsOpen {h : F × F | Ψ (x + h) = Ψ x} :=
      (hl.isOpen_fiber (Ψ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_Ln_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh => hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover
    (fun x => {z : F × F | z - x ∈ Ln F (n x)})
    (fun x _ => ((isOpen_Ln _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simpa using zero_mem_Ln (n x)))
  obtain ⟨N, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport Ψ, ∀ h ∈ Ln F N, Ψ (y + h) = Ψ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : h ∈ Ln F (n x) := Ln_anti (hN _ (Finset.mem_image_of_mem n hxt)) hh
    have e1 : Ψ y = Ψ x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : Ψ (y + h) = Ψ x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by abel]; exact add_mem_Ln hyx hN')
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, fun y h hh => ?_⟩
  by_cases hy : y ∈ tsupport Ψ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Ψ
  · have := hval (y + h) hyh (-h) (neg_mem_Ln hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

theorem cosetInd_of_mem {n : ℤ} {x y : F × F} (h : y - x ∈ Ln F n) : cosetInd n x y = 1 := by
  unfold cosetInd
  rw [Set.indicator_of_mem (show y ∈ {v | v - x ∈ Ln F n} from h)]
  rfl

theorem cosetInd_of_notMem {n : ℤ} {x y : F × F} (h : y - x ∉ Ln F n) : cosetInd n x y = 0 := by
  unfold cosetInd
  exact Set.indicator_of_notMem (show y ∉ {v | v - x ∈ Ln F n} from h) _

theorem cosetInd_add {n : ℤ} (x y : F × F) {h : F × F} (hh : h ∈ Ln F n) :
    cosetInd n x (y + h) = cosetInd n x y := by
  by_cases hy : y - x ∈ Ln F n
  · rw [cosetInd_of_mem hy, cosetInd_of_mem]
    rw [show y + h - x = (y - x) + h by abel]
    exact add_mem_Ln hy hh
  · rw [cosetInd_of_notMem hy, cosetInd_of_notMem]
    intro hyh
    apply hy
    have := add_mem_Ln hyh (neg_mem_Ln hh)
    rwa [show y + h - x + -h = y - x by abel] at this

theorem mem_span_of_cover (n : ℤ) (t : Finset (F × F)) :
    ∀ Ψ : F × F → ℂ, (∀ y, ∀ h ∈ Ln F n, Ψ (y + h) = Ψ y) →
      (∀ y, Ψ y ≠ 0 → ∃ x ∈ t, y - x ∈ Ln F n) →
      Ψ ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro Ψ _ hs
    have : Ψ = 0 := by
      funext y
      by_contra hy
      obtain ⟨x, hx, -⟩ := hs y hy
      simp at hx
    rw [this]
    exact zero_mem _
  | insert x t _ ih =>
    intro Ψ hp hs
    have hmem : Ψ - Ψ x • cosetInd n x ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) := by
      refine ih _ (fun y h hh => ?_) (fun y hy => ?_)
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hp y h hh, cosetInd_add x y hh]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy
        by_cases hyx : y - x ∈ Ln F n
        · exfalso
          apply hy
          have := hp x (y - x) hyx
          rw [add_sub_cancel] at this
          rw [cosetInd_of_mem hyx, this]
          ring
        · rw [cosetInd_of_notMem hyx, mul_zero, sub_zero] at hy
          obtain ⟨x', hx', hyx'⟩ := hs y hy
          rcases Finset.mem_insert.mp hx' with rfl | hx''
          · exact absurd hyx' hyx
          · exact ⟨x', hx'', hyx'⟩
    have hx : cosetInd n x ∈ Submodule.span ℂ (Set.range (cosetInd (F := F) n)) :=
      Submodule.subset_span ⟨x, rfl⟩
    have := add_mem hmem (Submodule.smul_mem _ (Ψ x) hx)
    rwa [sub_add_cancel] at this

theorem exists_sum_cosetInd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ),
    GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ),
      Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := by
  intro F _ _ _ _ _ _ Ψ hΨ
  classical
  obtain ⟨n, hn⟩ := exists_periodic hΨ.1 hΨ.2
  obtain ⟨t, -, ht⟩ := hΨ.2.isCompact.elim_nhds_subcover
    (fun x => {z : F × F | z - x ∈ Ln F n})
    (fun x _ => ((isOpen_Ln _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simpa using zero_mem_Ln n))
  have hspan := mem_span_of_cover n t Ψ hn (fun y hy => by
    have := ht (subset_tsupport Ψ (Function.mem_support.mpr hy))
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨x, hx, hyx⟩)
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hspan
  exact ⟨n, c.support, c, by rw [← hc]; rfl⟩

end GlobalTheory.CompanionTheory.WS.Decomp
