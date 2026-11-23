import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadOnePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def defect (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R) (a : 𝓞 E) : R :=
  2 * r * LinearMap.trace R _ (M a) - ((p + q) * r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : R) +
    (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : R))

theorem map_defect (H : Host E) (p q : ℕ) {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K))
    (hM : ∀ a c, f ∘ M a c = M' a (f ∘ c)) (a : 𝓞 E) :
    f (defect H p q M r a) = 2 * f r * LinearMap.trace K _ (M' a) - ((p + q) * f r *
      ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) + (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K)) := by
  rw [defect, ← GlobalTheory.TraceSpread.map_trace f (M a) (M' a) (hM a)]
  simp only [map_sub, map_mul, map_add, map_natCast, map_intCast, map_ofNat]

theorem eq_zero_of_map (H : Host E) (p q : ℕ) {R : Type} [CommRing R] [IsDomain R] (hQ : ℚ →+* R) {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R))
    (hM : ∀ (K : Type) [Field K] (f : R →+* K), ∃ M' : 𝓞 E →+* Module.End K (Fin n → K), ∀ a c, f ∘ M a c = M' a (f ∘ c))
    (r : R) (hr : r ^ 2 = -(H.d : R)) (a : 𝓞 E) {K : Type} [Field K] (f : R →+* K)
    (hf : f (defect H p q M r a) = 0) : defect H p q M r a = 0 := by
  letI : Algebra ℚ R := hQ.toAlgebra
  let L := AlgebraicClosure (FractionRing R)
  let emb : R →+* L := (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  have hemb : Function.Injective emb :=
    (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero L := ((RingHom.charZero_iff (emb.comp hQ).injective).1 inferInstance)
  obtain ⟨ML, hML⟩ := hM L emb
  have hs : emb r ∈ integralClosure ℚ L := by
    have h2 : (emb r) ^ 2 = algebraMap ℚ L (-(H.d : ℚ)) := by
      rw [← map_pow, hr]; simp
    exact IsIntegral.of_pow (by norm_num : 0 < 2) (h2 ▸ isIntegral_algebraMap)
  have hφ : ∀ φ : E →+* L, φ (a : E) ∈ integralClosure ℚ L := fun φ =>
    (Algebra.IsIntegral.isIntegral (R := ℚ) (a : E)).map φ.toRatAlgHom
  have hint : emb (defect H p q M r a) ∈ integralClosure ℚ L := by
    rw [map_defect H p q M r emb ML hML a, GlobalTheory.TraceSpread.trace_eq_sum]
    have h2 : (2 : L) ∈ integralClosure ℚ L := by
      simpa using Subalgebra.natCast_mem (integralClosure ℚ L) 2
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h2 hs)
      (Subalgebra.sum_mem _ fun φ _ => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hφ φ)))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.add_mem _
        (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _)) hs) (Subalgebra.intCast_mem _ _))
        (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
          (Subalgebra.intCast_mem _ _)))
  have hR : IsIntegral ℚ (defect H p q M r a) :=
    (isIntegral_algHom_iff emb.toRatAlgHom hemb).1 hint
  by_contra h0
  exact (hR.isUnit h0).map f |>.ne_zero hf

end GlobalTheory.SpreadOnePoint

namespace GlobalTheory.SpreadOnePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem detCond_iff_defect {H : Host E} (D : Datum H) {A : Type} [CommRing A] (G : Over (Sp A)) [GrpObj G]
    [IsCommMonObj G] (act : OAct (𝓞 E) G) (d : ℕ) (hd : SmoothOfRelativeDimension d G.hom) (r : A)
    (v : Fin d → (epsR (Localization.Away r) ⟶
      (Over.pullback (spMap (algebraMap A (Localization.Away r)))).obj G)) (hv : IsLieBasis v) :
    ∃ M : 𝓞 E →+* Module.End (Localization.Away r) (Fin d → Localization.Away r),
      (∀ (K : Type) [Field K] (f : Localization.Away r →+* K),
        ∃ M' : 𝓞 E →+* Module.End K (Fin d → K), ∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : Localization.Away r →+* K) (ρ : A),
        (f (algebraMap A _ ρ)) ^ 2 = -(H.d : K) →
        (DetCond D act (spMap (f.comp (algebraMap A _))) (f (algebraMap A _ ρ)) ↔
          ∀ a, f (defect H D.p D.q M (algebraMap A _ ρ) a) = 0) := by
  let R := Localization.Away r
  let j : Sp R ⟶ Sp A := spMap (algebraMap A R)
  haveI : SmoothOfRelativeDimension d ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hd
  have hs : Smooth ((Over.pullback j).obj G).hom := SmoothOfRelativeDimension.smooth d _
  obtain ⟨act', hact'⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R _ act' d v hs hv
  refine ⟨M, fun K _ f => (hM K f).imp fun M' h => h.1, ?_⟩
  intro K _ _ _ f ρ hρ
  obtain ⟨M', hc, e⟩ := hM K f
  have hx : spMap (f.comp (algebraMap A R)) = spMap f ≫ j := by
    rw [← Spec.map_comp]; rfl
  have hpull : ∀ τ N, LieMult act (spMap (f.comp (algebraMap A R))) τ N ↔
      Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = N := by
    intro τ N
    rw [hx, ← GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ G _ j (pullback.fst _ _) act act'
      (isGrpPullback_pullback G j) (fun c => by rw [hact']; exact pullback.lift_fst _ _ _) K (spMap f) τ N, e]
  unfold DetCond
  simp only [hpull]
  rw [GlobalTheory.TraceSpread.finrank_iff_trace H D.p D.q M' _ hρ]
  refine forall_congr' fun x => ?_
  rw [map_defect H D.p D.q M _ f M' hc x, sub_eq_zero]

theorem detCond_of_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : A), IsAbelianScheme G → ρ ^ 2 = -(H.d : A) → Nonempty (ℚ →+* A) → ∀ (K₀ : Type) [Field K₀] [IsAlgClosed K₀] (g₀ : A →+* K₀), DetCond D act (spMap g₀) (g₀ ρ) → ∀ (K : Type) [Field K] [IsAlgClosed K] (g : A →+* K), DetCond D act (spMap g) (g ρ) := by
  intro E _ _ _ H D A _ _ _ G _ _ act ρ hG hρ hQ' K₀ _ _ g₀ h₀ K _ _ g
  obtain ⟨hQ⟩ := hQ'
  have := hG.smooth
  have := hG.geomConnected
  have hc : ConnectedSpace G.left := (GlobalTheory.GroupConn.connectedSpace_group _ G).1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom x
  have cz : ∀ (F : Type) [Field F] (f : A →+* F), CharZero F := fun F _ f =>
    (RingHom.charZero_iff (f.comp hQ).injective).1 inferInstance
  have key : ∀ (K₁ : Type) [Field K₁] [IsAlgClosed K₁] (g₁ : A →+* K₁) (K₂ : Type) [Field K₂] [IsAlgClosed K₂]
      (g₂ : A →+* K₂) (r : A), g₁ r ≠ 0 → g₂ r ≠ 0 →
      (∃ v : Fin d → (epsR (Localization.Away r) ⟶
        (Over.pullback (spMap (algebraMap A (Localization.Away r)))).obj G), IsLieBasis v) →
      DetCond D act (spMap g₁) (g₁ ρ) → DetCond D act (spMap g₂) (g₂ ρ) := by
    intro K₁ _ _ g₁ K₂ _ _ g₂ r h₁ h₂ ⟨v, hv⟩ hdet
    haveI := cz K₁ g₁
    haveI := cz K₂ g₂
    have hr0 : r ≠ 0 := fun e => h₁ (by rw [e, map_zero])
    haveI : IsDomain (Localization.Away r) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
    obtain ⟨M, hM, hiff⟩ := detCond_iff_defect D G act d hd r v hv
    let f₁ : Localization.Away r →+* K₁ := IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h₁)
    let f₂ : Localization.Away r →+* K₂ := IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h₂)
    have e₁ : f₁.comp (algebraMap A _) = g₁ := IsLocalization.lift_comp _
    have e₂ : f₂.comp (algebraMap A _) = g₂ := IsLocalization.lift_comp _
    have v₁ : f₁ (algebraMap A _ ρ) = g₁ ρ := by rw [← RingHom.comp_apply, e₁]
    have v₂ : f₂ (algebraMap A _ ρ) = g₂ ρ := by rw [← RingHom.comp_apply, e₂]
    have hρ₁ : (f₁ (algebraMap A _ ρ)) ^ 2 = -(H.d : K₁) := by rw [v₁, ← map_pow, hρ]; simp
    have hρ₂ : (f₂ (algebraMap A _ ρ)) ^ 2 = -(H.d : K₂) := by rw [v₂, ← map_pow, hρ]; simp
    have hρR : (algebraMap A (Localization.Away r) ρ) ^ 2 = -(H.d : Localization.Away r) := by
      rw [← map_pow, hρ]; simp
    have h := (hiff K₁ f₁ ρ hρ₁).1 (by rw [e₁, v₁]; exact hdet)
    have h' := (hiff K₂ f₂ ρ hρ₂).2 fun a => by
      rw [eq_zero_of_map H D.p D.q ((algebraMap A _).comp hQ) M hM _ hρR a f₁ (h a), map_zero]
    rwa [e₂, v₂] at h'
  let L := AlgebraicClosure (FractionRing A)
  let gen : A →+* L := (algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))
  have hgen : Function.Injective gen :=
    (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨r₀, hr₀, v₀⟩ := GlobalTheory.LieLoc.lie_locally_free A G d hd ⟨RingHom.ker g₀, RingHom.ker_isPrime g₀⟩
  have h₀r : g₀ r₀ ≠ 0 := fun e => hr₀ (RingHom.mem_ker.2 e)
  have hgr₀ : gen r₀ ≠ 0 := fun e => h₀r (by rw [hgen (e.trans (map_zero gen).symm), map_zero])
  have hdg := key K₀ g₀ L gen r₀ h₀r hgr₀ v₀ h₀
  obtain ⟨r, hr, v⟩ := GlobalTheory.LieLoc.lie_locally_free A G d hd ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  have hg : g r ≠ 0 := fun e => hr (RingHom.mem_ker.2 e)
  have hgr : gen r ≠ 0 := fun e => hg (by rw [hgen (e.trans (map_zero gen).symm), map_zero])
  exact key L gen K g r hgr hg v hdg

end GlobalTheory.SpreadOnePoint
