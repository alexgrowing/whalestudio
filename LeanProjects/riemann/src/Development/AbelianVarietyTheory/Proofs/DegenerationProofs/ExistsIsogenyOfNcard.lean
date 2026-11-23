import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfMemKL
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfFiniteEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemKLOfHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteMulKTriv
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.PrincIsog

theorem pow_eq_one_of_etale {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [GrpObj A] [GrpObj B]
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom] (ψ : A ⟶ B) [Etale ψ.left] (n : ℕ)
    (h : ∀ y : Over.mk (𝟙 (Sp k)) ⟶ A, y ≫ ψ = 1 → y ^ n = 1) (T : Over (Sp k)) (x : T ⟶ A)
    (hx : x ≫ ψ = 1) : x ^ n = 1 := by
  let K := pullback ψ η[B]
  let inc : K ⟶ A := pullback.fst ψ η[B]
  have hinc : inc ≫ ψ = 1 := by
    rw [pullback.condition, toUnit_unique (pullback.snd ψ η[B]) (toUnit K)]; rfl
  have hp := (IsPullback.of_hasPullback ψ η[B]).map (Over.forget (Sp k))
  have he : Etale (pullback.snd ψ η[B]).left := MorphismProperty.of_isPullback (P := @Etale) hp ‹_›
  have hw : (pullback.snd ψ η[B]).left = K.hom := by
    simpa using Over.w (pullback.snd ψ η[B])
  rw [hw] at he
  have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
  have key : inc ^ n = 1 := by
    refine Over.OverMorphism.ext ?_
    have : LocallyOfFiniteType ((inc ^ n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
      ((Over.w _).trans (Over.w _).symm)
    let p : Over.mk (𝟙 (Sp k)) ⟶ K := Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
    have e : p ≫ inc ^ n = p ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one]
      exact h _ (by rw [Category.assoc, hinc, MonObj.comp_one])
    have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint k)) e
    have hz' : p.left (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply K.hom z hz _
    simp only [Over.comp_left] at e'
    rw [← hz']
    exact e'
  have hx' : x ≫ ψ = toUnit T ≫ η[B] := hx
  rw [← pullback.lift_fst x (toUnit T) hx', ← MonObj.comp_pow]
  change _ ≫ inc ^ n = 1
  rw [key, MonObj.comp_one]

theorem exists_lift_point {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_isogeny_of_ncard (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (g N : ℕ) :
    ∀ (A : Over (Sp k)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      L.IsLB → Out.RelAmple A L → {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.ncard = N →
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ),
        IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧
          IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ L hA hg hL hamp hN
  obtain ⟨hfin, hmul, htriv⟩ := GlobalTheory.KTrivPoints.finite_mul_kTriv k A hA L hL hamp
  by_cases h1 : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, GlobalTheory.MemKL A L x → x = 1
  · exact ⟨A, inferInstance, L, 𝟙 A, 𝟙 A, 1, hA, hg, hL, hamp, htriv h1, inferInstance, inferInstance, le_rfl,
      by simp⟩
  push Not at h1
  obtain ⟨x, hxK, hx1⟩ := h1
  have hfin' : {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.Finite := hfin
  have hord : IsOfFinOrder x := by
    refine finite_powers.1 (hfin'.subset ?_)
    rintro _ ⟨j, rfl⟩
    induction j with
    | zero => simpa using GlobalTheory.memKL_one hL _
    | succ j hj => simpa [pow_succ] using hmul _ _ hj hxK
  have hn : 1 ≤ orderOf x := hord.orderOf_pos
  obtain ⟨A', _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points k A hA (Subgroup.zpowers x) (finite_zpowers.2 hord)
  obtain ⟨M, hM, hLM⟩ := GlobalTheory.CyclicDescent.exists_descent k A A' hA L hL x _ hn rfl hxK ψ hψ hψf hψe hψs hker
  have hamp' := GlobalTheory.SS.relAmple_of_finite_etale_isogeny k A A' hA hA' ψ hψ hψf hψe hψs L M hL hM hLM hamp
  have := hA.proper
  have := hA'.proper
  have := hA.comm
  have := hA'.comm
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover k _ _ ψ.left A'.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hg)
  have hxψ : x ≫ ψ = 1 := (hker k (𝟙 _) x).2 ⟨x, Subgroup.mem_zpowers x, by
    rw [show toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 (𝟙_ (Over (Sp k))) from toUnit_unique _ _]
    exact (Category.id_comp x).symm⟩
  have hlt : {y : 𝟙_ (Over (Sp k)) ⟶ A' | GlobalTheory.MemKL A' M y}.ncard < N := by
    rw [← hN]
    refine lt_of_le_of_lt ?_ (Set.ncard_sdiff_singleton_lt_of_mem (a := x) hxK hfin')
    refine (Set.ncard_le_ncard ?_ ((hfin'.sdiff).image (· ≫ ψ))).trans (Set.ncard_image_le hfin'.sdiff)
    intro y hy
    obtain ⟨b, hb⟩ := exists_lift_point (F := k) ψ.left y.left
    let b' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = y := Over.OverMorphism.ext hb
    by_cases hbx : b' = x
    · exact ⟨1, ⟨GlobalTheory.memKL_one hL _, fun h => hx1 (Eq.symm h)⟩, by
        rw [← hb', hbx, hxψ]; exact MonObj.one_comp ψ⟩
    · exact ⟨b', ⟨GlobalTheory.memKL_of_hom _ A A' ψ hψ L M hL hM hLM _ b' (hb' ▸ hy), hbx⟩, hb'⟩
  obtain ⟨B, _, M', i, r, m, hB, hgB, hM', hampB, hK, hi, hr, hm, hri⟩ := ih _ hlt A' M hA' hg' hM hamp' rfl
  have hmon : IsMonHom (𝟙 A ^ orderOf x) := GlobalTheory.GrpTangent.mulN_eq_pow A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN A _
  obtain ⟨⟨ψ', hψ', hc⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A' A ψ (𝟙 A ^ orderOf x) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine pow_eq_one_of_etale ψ _ (fun y hy => ?_) T z hz
      obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := (hker k (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow, MonObj.comp_one]
  have hc' : ψ' ≫ ψ = 𝟙 A' ^ orderOf x := by
    rw [← cancel_epi ψ, ← Category.assoc, hc, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
      Category.comp_id]
  refine ⟨B, inferInstance, M', ψ ≫ i, r ≫ ψ', m * orderOf x, hB, hgB, hM', hampB, hK, inferInstance,
    inferInstance, Nat.mul_pos hm hn, ?_⟩
  rw [Category.assoc, ← Category.assoc ψ', hc', MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, hri, pow_mul]

theorem exists_isogeny_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  intro k _ _ _ A _ g hA hg
  obtain ⟨L, m, s, hL, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple k A hA
  have := hA.proper
  exact exists_isogeny_of_ncard k g _ A L hA hg hL
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hL).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)) rfl

end GlobalTheory.SS.PrincIsog
