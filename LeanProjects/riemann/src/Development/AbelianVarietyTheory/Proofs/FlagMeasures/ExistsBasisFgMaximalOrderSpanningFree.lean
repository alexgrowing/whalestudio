import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrderBasis

theorem exists_basis_pi {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (s t : E) (hs : IsUnit s) (ht : IsUnit t) :
    ∀ (m : ℕ) (Q : Submodule R (Fin m → E)), (∀ q ∈ Q, ∀ i, s * q i ∈ R) →
      (∀ i, (Pi.single i t : Fin m → E) ∈ Q) →
      ∃ b : Fin m → Fin m → E, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  intro m
  induction m with
  | zero =>
    intro Q _ _
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, Subsingleton.elim _ _⟩
  | succ m ih =>
    intro Q h1 h2
    let I : Ideal R :=
      { carrier := {r | ∃ q ∈ Q, s * q 0 = r}
        add_mem' := by
          rintro a b ⟨p, hp, hpa⟩ ⟨q, hq, hqb⟩
          exact ⟨p + q, Q.add_mem hp hq, by simp [mul_add, hpa, hqb]⟩
        zero_mem' := ⟨0, Q.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨p, hp, hpa⟩
          refine ⟨c • p, Q.smul_mem c hp, ?_⟩
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Subring.coe_mul, ← hpa]
          ring }
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
    obtain ⟨q0, hq0, hq0a⟩ := haI
    have hmul : ∀ q ∈ Q, ∃ c : R, q 0 = c * q0 0 := by
      intro q hq
      have : (⟨s * q 0, h1 q hq 0⟩ : R) ∈ I := ⟨q, hq, rfl⟩
      rw [ha, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨c, hs.mul_left_cancel ?_⟩
      have := congrArg Subtype.val hc
      simp only [smul_eq_mul, Subring.coe_mul] at this
      rw [← this, ← hq0a]; ring
    have hu : IsUnit (q0 0) := by
      obtain ⟨c, hc⟩ := hmul _ (h2 0)
      simp only [Pi.single_eq_same] at hc
      rw [hc] at ht
      exact isUnit_of_mul_isUnit_right ht
    let j : (Fin m → E) →ₗ[E] (Fin (m + 1) → E) :=
      LinearMap.pi (fun i => Fin.cases 0 (fun k => LinearMap.proj k) i)
    have j0 : ∀ v, j v 0 = 0 := fun v => by simp [j]
    have js : ∀ v k, j v (Fin.succ k) = v k := fun v k => by simp [j]
    obtain ⟨b, hb, hQ⟩ := ih (Q.comap (j.restrictScalars R))
      (fun q hq i => by have := h1 _ hq i.succ; simpa [js] using this)
      (fun i => by
        have : j (Pi.single i t) = Pi.single i.succ t := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
          · rw [js]; simp [Pi.single_apply]
        show j (Pi.single i t) ∈ Q
        rw [this]; exact h2 _)
    refine ⟨Fin.cons q0 (fun i => j (b i)), ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hg0 : g 0 = 0 := by
        have := congrFun hg 0
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, j0, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
        exact hu.mul_left_eq_zero.mp this
      have hgs : ∑ i, g (Fin.succ i) • b i = 0 := by
        funext k
        have := congrFun hg k.succ
        simpa [hg0, js, Finset.sum_apply] using this
      intro i
      refine Fin.cases hg0 (fun i => ?_) i
      exact Fintype.linearIndependent_iff.mp hb _ hgs i
    · apply le_antisymm
      · intro q hq
        obtain ⟨c, hc⟩ := hmul q hq
        have hq' : q - c • q0 ∈ Q := Q.sub_mem hq (Q.smul_mem c hq0)
        have he : j (fun k => (q - c • q0) k.succ) = q - c • q0 := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0]; simp [Subring.smul_def, hc]
          · rw [js]
        have hm : (fun k : Fin m => (q - c • q0) k.succ) ∈ Q.comap (j.restrictScalars R) := by
          show j _ ∈ Q
          rw [he]; exact hq'
        rw [hQ] at hm
        have hm2 := Submodule.mem_map_of_mem (f := j.restrictScalars R) hm
        rw [Submodule.map_span] at hm2
        have hm3 : q - c • q0 ∈ Submodule.span R
            (Set.range (Fin.cons q0 (fun i => j (b i)) : Fin (m + 1) → Fin (m + 1) → E)) := by
          rw [← he]
          refine Submodule.span_mono ?_ hm2
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i.succ, by simp⟩
        have : q = (q - c • q0) + c • q0 := by abel
        rw [this]
        exact Submodule.add_mem _ hm3 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases hq0 (fun i => ?_) i
        have : b i ∈ Q.comap (j.restrictScalars R) := by
          rw [hQ]; exact Submodule.subset_span ⟨i, rfl⟩
        simpa using this

theorem exists_common {E : Type} [CommRing E] (R : Subring E) {ι : Type} [Fintype ι]
    (P : ι → E → Prop) (hP : ∀ i d c, c ∈ R → P i d → P i (c * d))
    (h : ∀ i, ∃ d ∈ R, IsUnit d ∧ P i d) : ∃ d ∈ R, IsUnit d ∧ ∀ i, P i d := by
  choose d hdR hdu hd using h
  refine ⟨∏ i, d i, R.prod_mem fun i _ => hdR i, IsUnit.prod_iff.mpr fun i _ => hdu i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP _ _ _ (R.prod_mem fun i _ => hdR i) (hd i)

theorem exists_basis {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (hD : ∀ x : E, ∃ d ∈ R, IsUnit d ∧ d * x ∈ R) {V : Type} [AddCommGroup V] [Module E V]
    {m : ℕ} (y : Fin m → V) (hy : LinearIndependent E y) (Q : Submodule R V) (hQ : Q.FG)
    (hs : Submodule.span E (Q : Set V) = Submodule.span E (Set.range y)) :
    ∃ b : Fin m → V, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  let φ : (Fin m → E) →ₗ[E] V := Fintype.linearCombination E y
  have hφ : Function.Injective φ := hy.fintypeLinearCombination_injective
  have hr : ∀ q ∈ Q, ∃ v, φ v = q := by
    intro q hq
    have : q ∈ Submodule.span E (Set.range y) := hs ▸ Submodule.subset_span hq
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hmap : (Q.comap (φ.restrictScalars R)).map (φ.restrictScalars R) = Q :=
    Submodule.map_comap_eq_self fun q hq => hr q hq
  have hfg : (Q.comap (φ.restrictScalars R)).FG :=
    Submodule.fg_of_fg_map_injective (φ.restrictScalars R) hφ (by rw [hmap]; exact hQ)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  obtain ⟨s, -, hsu, hs1⟩ := exists_common R (fun (p : Fin k × Fin m) d => d * g p.1 p.2 ∈ R)
    (fun p d c hc h => by rw [mul_assoc]; exact R.mul_mem hc h) (fun p => hD _)
  have hsp : ∀ x ∈ Submodule.span E (Q : Set V), ∃ d ∈ R, IsUnit d ∧ d • x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, R.one_mem, isUnit_one, by simpa using hx⟩
    | zero => exact ⟨1, R.one_mem, isUnit_one, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hz⟩ := hz
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (x + z) = (⟨e, he⟩ : R) • d • x + (⟨d, hd⟩ : R) • e • z := by
        simp only [Subring.smul_def, smul_add, smul_smul, mul_comm]
      rw [this]
      exact Q.add_mem (Q.smul_mem _ hx) (Q.smul_mem _ hz)
    | smul c x _ hx =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hc⟩ := hD c
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (c • x) = (⟨e * c, hc⟩ : R) • d • x := by
        simp only [Subring.smul_def, smul_smul]
        congr 1; ring
      rw [this]
      exact Q.smul_mem _ hx
  obtain ⟨t, -, htu, ht1⟩ := exists_common R (fun (i : Fin m) d => d • y i ∈ Q)
    (fun i d c hc h => by rw [mul_smul]; exact Q.smul_mem (⟨c, hc⟩ : R) h)
    (fun i => hsp _ (hs ▸ Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨b, hb, hQb⟩ := exists_basis_pi R s t hsu htu m (Q.comap (φ.restrictScalars R))
    (by
      intro q hq i
      rw [← hg] at hq
      induction hq using Submodule.span_induction with
      | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hs1 (l, i)
      | zero => simp
      | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact R.add_mem hx hz
      | smul c x _ hx =>
        have : s * (c • x) i = c * (s * x i) := by
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
        rw [this]; exact R.mul_mem c.2 hx)
    (fun i => by
      show φ (Pi.single i t) ∈ Q
      simpa [φ, Fintype.linearCombination_apply_single] using ht1 i)
  refine ⟨φ ∘ b, hb.map' φ (LinearMap.ker_eq_bot.mpr hφ), ?_⟩
  rw [← hmap, hQb, Submodule.map_span, Set.range_comp]
  rfl

theorem order_basis : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Q : Submodule L.O (Fin n → E), Q.FG → Submodule.span E (Q : Set (Fin n → E)) = Submodule.span E (Set.range y) → ∃ b : Fin m → Fin n → E, LinearIndependent E b ∧ Q = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m y hy Q hQ hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  refine exists_basis L.O (fun x => ?_) y hy Q hQ hs
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨algebraMap 𝒪[F] E d, (L.O_def _).mpr isIntegral_algebraMap, ?_, (L.O_def _).mpr ?_⟩
  · rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    exact (IsLocalization.map_units F d).map _
  · rwa [Submonoid.smul_def, Algebra.smul_def] at hd

end GlobalTheory.OrderBasis
