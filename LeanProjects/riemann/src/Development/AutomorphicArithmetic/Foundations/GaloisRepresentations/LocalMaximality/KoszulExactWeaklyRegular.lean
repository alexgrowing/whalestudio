import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlacewiseToOutsideS
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

private theorem wd_eq' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd]

private theorem wd_wd' (w : σ → Module.End ℂ E) (hw : ∀ i j, Commute (w i) (w j))
    (c : Finset σ → E) : wd w (wd w c) = 0 :=
  _root_.UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_wd w hw c
end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']

private theorem wd_map' (r : κ → R) (π : N →ₗ[R] N') (c : Finset κ → N) (s : Finset κ) :
    wd (fun l => (Algebra.lsmul ℂ ℂ N' : R →ₐ[ℂ] Module.End ℂ N') (r l)) (fun s => π (c s)) s =
      π (wd (fun l => (Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r l)) c s) := by
  simp only [wd_eq', map_sum, map_zsmul, Algebra.lsmul_coe, map_smul]

private theorem mem_C' (r : κ → R) (n : ℤ) (c : Finset κ → N) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).C n ↔ ∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0 := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n <;> simp [h]

private theorem wd_C' (r : κ → R) (n : ℤ) (c : Finset κ → N)
    (hc : ∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0) (s : Finset κ) (hs : (s.card : ℤ) ≠ n + 1) :
    wd (fun l => (Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r l)) c s = 0 := by
  rw [wd_eq']
  refine Finset.sum_eq_zero fun i hi => ?_
  have h1 : ((s.erase i).card : ℤ) + 1 = s.card := by
    rw [← Finset.card_erase_add_one hi]; push_cast; ring
  rw [hc _ (fun h => hs (by omega))]
  simp
end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

private theorem koszulExact_weaklyRegular (hH : Htpy) (r : κ → R) (f : List R) :
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N],
      RingTheory.Sequence.IsWeaklyRegular N f → (∀ g ∈ f, InSp ⊤ r g) →
      KE (kos (Algebra.lsmul ℂ ℂ N) ⊤ r) (f.length : ℤ) := by
  induction f with
  | nil =>
    intro N _ _ _ _ _ _ m hm c hc
    have hz : c = 0 := by
      funext s
      refine (mem_C' r m c).1 hc.1 s ?_
      simp only [List.length_nil, Nat.cast_zero] at hm
      have : (0 : ℤ) ≤ s.card := Int.natCast_nonneg _
      omega
    rw [hz]
    exact Submodule.zero_mem _
  | cons g f' ih =>
    intro N _ _ _ _ hreg hf m hm c hc
    obtain ⟨hg, hreg'⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff N g f').1 hreg
    have hstab : Stab (Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) ⊤ ⊤ :=
      fun _ _ _ _ => Submodule.mem_top
    obtain ⟨y, hy, hyc⟩ := hH R N (Algebra.lsmul ℂ ℂ N) κ ⊤ ⊤ r hstab m c hc g
      (hf g List.mem_cons_self)
    have hyC := (mem_C' r _ y).1 hy
    have hyc' : ∀ s, wd (fun l => (Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r l)) y s
        = g • c s := fun s => congrFun hyc s
    let π : N →ₗ[R] QuotSMulTop g N := Submodule.mkQ _
    have hπ : Function.Surjective π := Submodule.mkQ_surjective _
    have hker : ∀ a : N, π a = 0 → ∃ b : N, g • b = a := by
      intro a ha
      have : a ∈ g • (⊤ : Submodule R N) := by
        simpa [π] using ha
      obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
      exact ⟨b, hb⟩
    have hgπ : ∀ a : N, π (g • a) = 0 := by
      intro a
      have : g • a ∈ g • (⊤ : Submodule R N) :=
        (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨a, Submodule.mem_top, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 this
    have hZ : (fun s => π (y s)) ∈ (kos (Algebra.lsmul ℂ ℂ (QuotSMulTop g N)) ⊤ r).Z (m - 1) := by
      refine ⟨(mem_C' r _ _).2 fun s hs => by simp [hyC s hs], ?_⟩
      show wd _ _ = 0
      funext s
      rw [wd_map', hyc', hgπ]
      rfl
    obtain ⟨t, ht, hty⟩ := ih (QuotSMulTop g N) hreg'
      (fun a ha => hf a (List.mem_cons_of_mem _ ha)) (m - 1)
      (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hm; omega) hZ
    have htC := (mem_C' r _ t).1 ht
    have hlift : ∀ s, ∃ a : N, π a = t s ∧ (t s = 0 → a = 0) := by
      intro s
      by_cases h0 : t s = 0
      · exact ⟨0, by simp [h0], fun _ => rfl⟩
      · obtain ⟨a, ha⟩ := hπ (t s)
        exact ⟨a, ha, fun h => absurd h h0⟩
    choose y' hy'1 hy'2 using hlift
    have hy'C : ∀ s : Finset κ, (s.card : ℤ) ≠ m - 1 - 1 → y' s = 0 :=
      fun s hs => hy'2 s (htC s hs)
    set W := wd (fun l => (Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r l)) with hW
    have hWy' : ∀ s, π (W y' s) = π (y s) := by
      intro s
      rw [hW, ← wd_map' r π y' s]
      have : (fun s => π (y' s)) = t := funext hy'1
      rw [this]
      exact congrFun hty s
    have hdiv : ∀ s, ∃ b : N, g • b = y s - W y' s := fun s =>
      hker _ (by rw [map_sub, hWy', sub_self])
    choose y'' hy'' using hdiv
    have hy''C : ∀ s : Finset κ, (s.card : ℤ) ≠ m - 1 → y'' s = 0 := by
      intro s hs
      apply hg
      show g • y'' s = g • 0
      rw [hy'', hyC s hs, smul_zero, wd_C' r (m - 1 - 1) y' hy'C s (by omega), sub_zero]
    refine ⟨y'', (mem_C' r _ _).2 hy''C, ?_⟩
    show W y'' = c
    funext s
    apply hg
    show g • W y'' s = g • c s
    have h1 : g • W y'' s = W (fun s => g • y'' s) s := by
      have := wd_map' r (LinearMap.lsmul R N g) y'' s
      simpa using this.symm
    have hcomm : ∀ i j, Commute ((Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r i))
        ((Algebra.lsmul ℂ ℂ N : R →ₐ[ℂ] Module.End ℂ N) (r j)) :=
      fun i j => (Commute.all (r i) (r j)).map _
    have h2 : (fun s => g • y'' s) = y - W y' := funext hy''
    rw [h1, h2, map_sub, wd_wd' _ hcomm, sub_zero, hyc']
end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
