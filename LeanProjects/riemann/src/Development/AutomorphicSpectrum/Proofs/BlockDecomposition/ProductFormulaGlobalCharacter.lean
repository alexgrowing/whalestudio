import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularGroup
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.HeckeUnit

open GlobalTheory.CompanionTheory.PlaceBlocks

variable {K : Type} [Field K] [NumberField K]

theorem card_fib_le (h2 : Module.finrank ℚ K = 2) (v : Pl) : (fib K v).card ≤ 2 := by
  classical
  haveI : NoZeroSMulDivisors (𝓞 ℚ) (𝓞 K) := by
    have hinj : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
      intro a b hab
      apply RingOfIntegers.ext
      apply (algebraMap ℚ K).injective
      exact congrArg (fun x : 𝓞 K => (x : K)) hab
    refine ⟨fun {a x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (h.trans (map_zero _).symm))
    · exact Or.inr h
  have h := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (p := v.asIdeal) v.ne_bot
  rw [h2] at h
  refine le_trans ?_ h
  rw [← Finset.card_image_of_injective (fib K v) (f := fun w : PlK K => w.asIdeal)
    (fun a b hab => HeightOneSpectrum.ext hab)]
  refine Finset.card_le_card fun P hP => ?_
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
  have hl : w.asIdeal.LiesOver v.asIdeal := (liesOver_iff w v).mpr (mem_fib.mp hw)
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
  exact ⟨w.isPrime, hl⟩

theorem finiteComponent_diagonal (w : PlK K) (κ : Kˣ) :
    IdeleGroup.finiteComponent w (IdeleGroup.toFinite K (IdeleGroup.diagonal K κ)) = atW w κ := by
  ext
  rfl

theorem global_prod (c : HeckeCharacter K) (κ : Kˣ) :
    (Function.mulSupport fun w : PlK K => cK c w κ).Finite ∧
      (∏ᶠ w : PlK K, cK c w κ) * ∏ w : InfinitePlace K, ((c.infiniteComponent w
        (IdeleGroup.infiniteComponent w (IdeleGroup.toInfinite K (IdeleGroup.diagonal K κ))) : Circle) : ℂ) = 1 := by
  have hc : ∀ w : PlK K, cK c w κ =
      (c.localComponent w (IdeleGroup.finiteComponent w (IdeleGroup.toFinite K (IdeleGroup.diagonal K κ))) : ℂ) := by
    intro w
    rw [finiteComponent_diagonal]
    rfl
  refine ⟨?_, ?_⟩
  · simp_rw [hc]
    exact c.finite_mulSupport_localComponent _
  · simp_rw [hc]
    rw [← c.toIdele_ofFinite_eq_finprod]
    have h := c.toIdele_diagonal κ
    rw [← IdeleGroup.ofFinite_mul_ofInfinite (IdeleGroup.diagonal K κ), map_mul, HeckeCharacter.toIdele_ofInfinite] at h
    have h' := congrArg (fun x : Circle => (x : ℂ)) h
    simp only [Circle.coe_mul, Circle.coe_one] at h'
    rw [show ((∏ w, c.infiniteComponent w (IdeleGroup.infiniteComponent w
      (IdeleGroup.toInfinite K (IdeleGroup.diagonal K κ))) : Circle) : ℂ) = _ from map_prod Circle.coeHom _ _] at h'
    exact h'

theorem cW_eq_prod (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl} (L : LM c v) (hL : L.ok) (κ : Kˣ) :
    cW L κ = ∏ w ∈ fib K v, cK c w κ := by
  classical
  cases L with
  | sp w₁ w₂ Φ =>
    have hne : w₁ ≠ w₂ := hL.1
    have e : fib K v = {w₁, w₂} := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact mem_fib.mpr ((liesOver_iff _ _).mp inferInstance)
        · rw [Finset.mem_singleton.mp hw]
          exact mem_fib.mpr ((liesOver_iff _ _).mp inferInstance)
      · rw [Finset.card_pair hne]
        exact card_fib_le h2 v
    rw [e, Finset.prod_pair hne]
    rfl
  | ns w σ η Φ =>
    have e : fib K v = {w} := by
      ext w'
      rw [mem_fib, Finset.mem_singleton]
      constructor
      · intro h
        exact hL.1 w' ((liesOver_iff _ _).mpr h)
      · rintro rfl
        exact (liesOver_iff _ _).mp inferInstance
    rw [e, Finset.prod_singleton]
    rfl

theorem finprod_regroup {N : Type*} [CommMonoid N] (f : PlK K → N) (hf : (Function.mulSupport f).Finite) :
    (Function.mulSupport fun v : Pl => ∏ w ∈ fib K v, f w).Finite ∧
      ∏ᶠ v : Pl, ∏ w ∈ fib K v, f w = ∏ᶠ w, f w := by
  classical
  set S0 : Finset Pl := hf.toFinset.image vOf with hS0
  have hsub : Function.mulSupport (fun v : Pl => ∏ w ∈ fib K v, f w) ⊆ (S0 : Set Pl) := by
    intro v hv
    obtain ⟨w, hw, hfw⟩ := Finset.exists_ne_one_of_prod_ne_one hv
    rw [Finset.mem_coe, hS0, Finset.mem_image]
    exact ⟨w, hf.mem_toFinset.mpr hfw, mem_fib.mp hw⟩
  refine ⟨S0.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_biUnion]
  · refine (finprod_eq_prod_of_mulSupport_subset f fun w hw => ?_).symm
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨vOf w, Finset.mem_image_of_mem _ (hf.mem_toFinset.mpr hw), mem_fib.mpr rfl⟩
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun w hw hw' => hab ?_
    exact (mem_fib.mp hw).symm.trans (mem_fib.mp hw')

theorem infinitePlace_eq (h2 : Module.finrank ℚ K = 2) [IsTotallyComplex K] (w : InfinitePlace K) :
    w = Classical.arbitrary (InfinitePlace K) := by
  have h1 : Module.finrank ℚ K = 2 * InfinitePlace.nrComplexPlaces K := IsTotallyComplex.finrank K
  have hc : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  exact Fintype.card_le_one_iff.mp hc.le _ _

theorem map_infiniteComponent_diagonal (w : InfinitePlace K) (hw : w = Classical.arbitrary (InfinitePlace K)) (κ : Kˣ) :
    Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
      (IdeleGroup.infiniteComponent w (IdeleGroup.toInfinite K (IdeleGroup.diagonal K κ))) = embU κ := by
  subst hw
  ext
  exact InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.equiv _ |>.symm (κ : K))

theorem cW_finprod_mul_chC : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, (∀ v, (M v).ok) → ∀ κ : Kˣ,
    (Function.mulSupport fun v : Pl => cW (M v) κ).Finite ∧
      (∏ᶠ v : Pl, cW (M v) κ) * chC n (Complex.I * t) (embU κ) = 1 := by
  intro K _ _ h2 hT DK c n t S hA M hM κ
  obtain ⟨hf, hp⟩ := global_prod c κ
  obtain ⟨hs, hr⟩ := finprod_regroup (fun w : PlK K => cK c w κ) hf
  have e : (fun v : Pl => cW (M v) κ) = fun v : Pl => ∏ w ∈ fib K v, cK c w κ :=
    funext fun v => cW_eq_prod h2 (M v) (hM v) κ
  rw [e]
  refine ⟨hs, ?_⟩
  rw [hr]
  have hu : ∀ w : InfinitePlace K, w = Classical.arbitrary (InfinitePlace K) := infinitePlace_eq h2
  haveI : Unique (InfinitePlace K) := ⟨⟨Classical.arbitrary _⟩, hu⟩
  rw [Fintype.prod_unique] at hp
  have hd : (default : InfinitePlace K) = Classical.arbitrary (InfinitePlace K) := hu _
  rw [hA.inf, map_infiniteComponent_diagonal _ hd] at hp
  exact hp

end GlobalTheory.CompanionTheory.FexTheta.HeckeUnit
