import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyAlgebraisationAbelianQuotientTower

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LBReductions

theorem exists_kernel_approx {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) : ∃ e : ℕ, ∀ v : Fin a → R, (∀ j, D.mulVec v j ∈ I ^ (e + 1)) →
      ∃ w : Fin a → R, D.mulVec w = 0 ∧ ∀ k, v k - w k ∈ I := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range D.mulVecLin)
  refine ⟨c, fun v hv => ?_⟩
  have h₁ : D.mulVec v ∈ I ^ (c + 1) • (⊤ : Submodule R (Fin b → R)) ⊓ LinearMap.range D.mulVecLin := by
    refine ⟨?_, v, rfl⟩
    rw [pi_eq_sum_univ (D.mulVec v)]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hv j) trivial
  rw [hc (c + 1) (Nat.le_succ c), Nat.add_sub_cancel_left, pow_one] at h₁
  have h₂ : D.mulVec v ∈ Submodule.map D.mulVecLin (I • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h₁
  obtain ⟨u, hu, huv⟩ := h₂
  have h₃ : ∀ k, u k ∈ I := by
    refine Submodule.smul_induction_on hu (fun r hr n _ k => I.mul_mem_right _ hr)
      fun x y hx hy k => I.add_mem (hx k) (hy k)
  refine ⟨v - u, ?_, fun k => by simpa using h₃ k⟩
  rw [Matrix.mulVec_sub, sub_eq_zero]
  exact huv.symm

open GlobalTheory.AbLaw.Seesaw in

theorem mem_basicOpen_loc₀ {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf f N) {v w : Fin P.a → R} (h : ∀ k, v k - w k ∈ I)
    {i : P.I} {x : X} (hI : I ≤ (f x).asIdeal) (hx : x ∈ X.basicOpen (loc₀ P v i)) :
    x ∈ X.basicOpen (loc₀ P w i) := by
  have hi : x ∈ P.W i := X.basicOpen_le _ hx
  rw [X.mem_basicOpen _ x hi] at hx ⊢
  by_contra hw
  have e : loc₀ P v i = loc₀ P w i + ∑ k, cst f (P.W i) (v k - w k) * P.u k i := by
    simp only [loc₀, map_sub, sub_mul, Finset.sum_sub_distrib, add_sub_cancel]
  refine (IsLocalRing.notMem_maximalIdeal.2 hx) ?_
  rw [e, map_add, map_sum]
  refine Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hw) (Ideal.sum_mem _ fun k _ => ?_)
  rw [map_mul]
  refine Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
  exact (mem_basicOpen_cst f _ _ hi).1 ((X.mem_basicOpen _ x hi).2 hu) (hI (h k))

open GlobalTheory.AbLaw.Seesaw in

theorem triv_of_levels {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [UniversallyClosed f] {N : LB X} (hN : N.IsLB)
    (P : Perf f N) {Y : ℕ → Scheme.{0}} {b : ∀ e, Y e ⟶ X}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} (hb : ∀ e, IsPullback (b e) (q e) f (thick R I e))
    (ht : ∀ e, Triv (N.pull (b e))) : Triv N := by
  obtain ⟨e, he⟩ := exists_kernel_approx I P.D₀
  obtain ⟨v', hv', hu, -⟩ := loc_of_triv P (hb e) hN (ht e)
  choose v hv using fun k => Ideal.Quotient.mk_surjective (v' k)
  obtain rfl : Ideal.Quotient.mk (I ^ (e + 1)) ∘ v = v' := funext hv
  obtain ⟨w, hw, hvw⟩ := he v fun j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_mulVec]
    exact congrFun hv' j
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P w i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hG : ∀ x, x ∈ G := by
    intro x
    by_contra hx
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (f x).isPrime.ne_top
    have hsp : f x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    obtain ⟨x', hx', hfx⟩ := hsp.mem_closed hZ ⟨x, hx, rfl⟩
    have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
    have hr : f x' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hfx]
      exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hIm
    obtain ⟨z, hz⟩ := hr
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hb e) x' z hz.symm
    obtain ⟨i, hi⟩ := exists_mem P (b e y)
    have h₁ := hu i
    rw [loc_comp P (hb e)] at h₁
    have h₂ := mem_of_isUnit h₁ (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx' (TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_basicOpen_loc₀ P hvw (by rw [hfx]; exact hIm) h₂⟩)
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.AbTriv.triv_of_pull_id (triv_of_loc P hid (RingHom.id R ∘ w) ?_ fun y => ?_)
  · funext j
    rw [← RingHom.map_mulVec, hw]
    rfl
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hG y)
    refine ⟨i, ?_⟩
    rw [loc_comp P hid, ← Scheme.preimage_basicOpen]
    exact hi

theorem lbIso_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  intro R _ _ I hI X hs hp _ Y b hb M M' hM hM' w
  have := isProper_of_isProjBy R _ _ hp
  have hN := LB.isLB_div hM' hM
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R _ _ hs hp _ hN
  exact triv_of_levels (IsAdicComplete.le_jacobson_bot I) hN P hb fun e =>
    GlobalTheory.AlgTower.triv_chart (GlobalTheory.AlgTower.chartPullDiv M' M _) (w e)

end GlobalTheory.LBReductions
