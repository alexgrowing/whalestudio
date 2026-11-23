import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SecCyclic
open GlobalTheory.AbLaw.Seesaw

theorem coker_equiv {R : Type} [CommRing R] {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v₀ : Fin a → R)
    (k : Fin a) (hk : IsUnit (v₀ k))
    (hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀)) :
    Nonempty (((Fin a → R) ⧸ LinearMap.range D.transpose.mulVecLin) ≃ₗ[R]
      (R ⧸ Ideal.span (Set.range (D.mulVec v₀)))) := by
  classical
  set N := LinearMap.range D.transpose.mulVecLin with hN
  set I := Ideal.span (Set.range (D.mulVec v₀)) with hI
  have hrow : ∀ i, ∑ j, D i j • N.mkQ (Pi.single j 1) = 0 := fun i => by
    simp only [← map_smul, ← map_sum]
    refine (Submodule.Quotient.mk_eq_zero N).2 ⟨Pi.single i 1, ?_⟩
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  obtain ⟨c, hc⟩ := hker (TrivSqZeroExt R ((Fin a → R) ⧸ N)) (TrivSqZeroExt.inlHom R ((Fin a → R) ⧸ N))
    (fun j => TrivSqZeroExt.inr (N.mkQ (Pi.single j 1))) (by
      funext i
      change ∑ j, TrivSqZeroExt.inl (D i j) * TrivSqZeroExt.inr (N.mkQ (Pi.single j 1)) = (0 : TrivSqZeroExt R ((Fin a → R) ⧸ N))
      have := congrArg (TrivSqZeroExt.inrHom R ((Fin a → R) ⧸ N)) (hrow i)
      rw [map_sum, map_zero] at this
      exact (Finset.sum_congr rfl fun j _ => TrivSqZeroExt.inl_mul_inr _ _).trans this)
  have he : ∀ j, N.mkQ (Pi.single j 1) = v₀ j • c.snd := fun j => by
    have := congrArg TrivSqZeroExt.snd (congrFun hc j)
    change _ = (c * TrivSqZeroExt.inl (v₀ j)).snd at this
    rw [_root_.mul_comm, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul] at this
    exact this
  have hx : ∀ x : Fin a → R, N.mkQ x = (x ⬝ᵥ v₀) • c.snd := fun x => by
    have : x = ∑ j, x j • (Pi.single j 1 : Fin a → R) := by
      funext j
      simp [Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, he, smul_smul, dotProduct, Finset.sum_smul]
  have hIq : ∀ r ∈ I, r • c.snd = 0 := fun r hr => by
    refine Submodule.span_induction (p := fun r _ => r • c.snd = 0) ?_ (zero_smul _ _) ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      rw [← hrow i]
      simp only [he, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    · intro x y _ _ h₁ h₂
      rw [add_smul, h₁, h₂, add_zero]
    · intro s x _ h
      rw [smul_eq_mul, mul_smul, h, smul_zero]
  let φ : (Fin a → R) →ₗ[R] R ⧸ I := I.mkQ ∘ₗ (dotProductBilin R R).flip v₀
  have hφ : ∀ x, φ x = I.mkQ (x ⬝ᵥ v₀) := fun _ => rfl
  have hs : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := I.mkQ_surjective y
    obtain ⟨u, hu⟩ := hk
    refine ⟨Pi.single k (r * u⁻¹.val), ?_⟩
    rw [hφ, single_dotProduct, ← hu, Units.inv_mul_cancel_right]
  have hk' : N = LinearMap.ker φ := by
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
    · intro h
      exact (Submodule.Quotient.mk_eq_zero N).1 ((hx x).trans (hIq _ h))
  exact ⟨(Submodule.quotEquivOfEq _ _ hk').trans (φ.quotKerEquivOfSurjective hs)⟩

theorem cyclic_ideal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → ∀ P : Perf f M, UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K), IsLocalHom g₀ → ∀ (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ I : Ideal R, Nonempty (((Fin P.a → R) ⧸ LinearMap.range P.D₀.transpose.mulVecLin) ≃ₗ[R] (R ⧸ I)) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ X f M hM P hcl hsurj K _ g₀ hloc X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  have unit_of : ∀ r : R, g₀ r ≠ 0 → IsUnit r := fun r hr => hloc.map_nonunit r hr.isUnit
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker₀⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  have hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) :=
    fun R' _ g => hker₀ R' g ((unit_of δ hδ).map g)
  obtain ⟨c₀, hc₀⟩ := hker K g₀ v hv
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : IsUnit (v₀ k) := unit_of _ fun h0 => hk (by
    rw [hc₀]
    change c₀ * g₀ (v₀ k) = 0
    rw [h0, mul_zero])
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    have h₁ := hu i
    rw [hc₀, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : IsUnit r₁ := unit_of r₁ hr₁
  refine ⟨Ideal.span (Set.range (P.D₀.mulVec v₀)), coker_equiv P.D₀ v₀ k hk' hker,
    fun R' _ g X' π f' h => ?_⟩
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      change r₁ ∉ (f (π y)).asIdeal
      exact fun hm => (f (π y)).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hr₁')
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.UU.SecCyclic
