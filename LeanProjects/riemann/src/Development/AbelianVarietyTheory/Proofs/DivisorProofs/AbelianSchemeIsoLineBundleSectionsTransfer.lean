import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

theorem topEquiv_pull {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Sp R}
    {f' : X' ⟶ Sp R'} {π : X' ⟶ X} {g : R →+* R'} (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (M : LB X) (x : SecOnR f M ⊤) :
    SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M w ⊤ ⊤ le_top x) = secPull (SecOnR.topEquiv f M x) π := by
  refine DVR.SecOps.sec_ext fun i => ?_
  refine (congrArg (rs X' _) (SecOn.coord_pullLE π le_top x i)).trans ?_
  change (π.appLE _ _ _ ≫ X'.presheaf.map _).hom _ = (X.presheaf.map _ ≫ π.appLE _ _ _).hom _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem secMaps_congr {Y : Scheme.{0}} {L N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (w : LB.Iso L N)
    (hw : w.IsGen) (a : L.Sec) :
    SecMaps w a (SecOn.topEquiv N (SecOn.congr hL hN w hw ⊤ ((SecOn.topEquiv L).symm a))) := by
  intro p
  have e := SecOn.coord_congr hL hN w hw ((SecOn.topEquiv L).symm a) p.1 p.2 (O := N.U p.1 ⊓ L.U p.2)
    (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl
  rw [SecOn.topEquiv_symm_apply, GlobalTheory.LB.coord_ofSec, rs_self, rs_rs] at e
  rw [SecOn.topEquiv_f]
  exact (rs_rs _ _ _).trans e

theorem topEquiv_sum {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Sp R) (M : LB X) {n : ℕ}
    (c : Fin n → R) (x : Fin n → SecOnR f M ⊤) :
    SecOnR.topEquiv f M (∑ j, c j • x j) = ∑ j, cst f ⊤ (c j) • SecOnR.topEquiv f M (x j) := by
  simp only [map_sum, SecOnR.smul_def, map_smul]

theorem sum_f {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) :
    (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem veryAmpleBy_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [UniversallyClosed f]
    (H : LB X) {m n : ℕ} (s₁ : Fin (m + 1) → H.Sec) (s : Fin (n + 1) → H.Sec) (hs₁ : VeryAmpleBy f H s₁)
    (hsp : ∀ i, ∃ c : Fin (n + 1) → R, s₁ i = ∑ k, cst f ⊤ (c k) • s k) : VeryAmpleBy f H s := by
  have E : ∀ {p : ℕ} (u : Fin (p + 1) → H.Sec), VeryAmpleBy f H u ↔ AmpleSpan.EmbedsBy f u :=
    fun u => (AmpleSpan.embedsBy_spec_iff f u).symm
  refine (E s).2 (((E s₁).1 hs₁).of_inSpan fun i => ?_)
  obtain ⟨c, hc⟩ := hsp i
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c k), fun k' => ?_⟩
  rw [hc, sum_f]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.LB.smul_f]
  congr 1
  change rs X le_top (cst f ⊤ (c k)) = _
  rw [rs_cst]
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.Hom.appTop]
  rfl

end GlobalTheory.BasisMatch

namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

def basisOfExistsUnique {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ} (v : Fin n → V)
    (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) : Module.Basis (Fin n) R V :=
  Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun g hg i => by
      obtain ⟨c, -, hc⟩ := h 0
      exact congrFun ((hc g hg.symm).trans (hc 0 (by simp)).symm) i)
    (fun x _ => (Submodule.mem_span_range_iff_exists_fun R).2 (by
      obtain ⟨c, hc, -⟩ := h x
      exact ⟨c, hc.symm⟩))

theorem basisOfExistsUnique_apply {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (v : Fin n → V) (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) (j : Fin n) :
    basisOfExistsUnique v h j = v j := Module.Basis.mk_apply _ _ _

theorem core {K W K' : Type} [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K']
    [Module.Flat W K'] {XA XG Y : Scheme.{0}} (fA : XA ⟶ Sp K) (fG : XG ⟶ Sp W) (fY : Y ⟶ Sp K')
    (πA : Y ⟶ XA) (πG : Y ⟶ XG) [CompactSpace XA] [CompactSpace XG] [IsSeparated fA] [IsSeparated fG]
    [UniversallyClosed fA]
    (PA : IsPullback πA fY fA (spMap (algebraMap K K'))) (PG : IsPullback πG fY fG (spMap (algebraMap W K')))
    (H : LB XA) (M : LB XG) (w : LB.Iso (M.pull πG) (H.pull πA)) {m : ℕ} (s₁ : Fin (m + 1) → H.Sec)
    {N : ℕ} (t : Fin (N + 1) → M.Sec) (hH : H.IsLB) (hs₁ : VeryAmpleBy fA H s₁) (hM : M.IsLB)
    (hw : w.IsGen) (ht : ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, cst fG ⊤ (c j) • t j) :
    ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'),
      VeryAmpleBy fA H s ∧ IsUnit g.det ∧
      (∀ j, SecMaps w (secPull (t j) πG) (∑ k, cst fY ⊤ (g j k) • secPull (s k) πA)) ∧
      ∀ c c' : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
        ∑ k, cst fY ⊤ (c' k) • secPull (s k) πA → c = c' := by
  have hLy : (M.pull πG).IsLB := LB.isLB_pull hM _
  have hHy : (H.pull πA).IsLB := LB.isLB_pull hH _
  let bcA := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hH PA)
  let bcG := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hM PG)
  let ψ := SecOnR.linEquiv fY (R := K') (SecOn.congr hLy hHy w hw ⊤)
  have htt : ∀ x : SecOnR fG M ⊤, ∃! c : Fin (N + 1) → W,
      x = ∑ j, c j • (SecOnR.topEquiv fG M).symm (t j) := by
    intro x
    refine (existsUnique_congr fun c => ?_).1 (ht (SecOnR.topEquiv fG M x))
    refine Iff.trans ?_ (SecOnR.topEquiv fG M).injective.eq_iff
    rw [topEquiv_sum]
    simp only [LinearEquiv.apply_symm_apply]
  let bt := basisOfExistsUnique _ htt
  let tY := ((bt.baseChange K').map bcG).map ψ
  have hfr : Module.finrank K (SecOnR fA H ⊤) = N + 1 := by
    rw [← Module.finrank_baseChange (R := K') (S := K), Module.finrank_eq_card_basis (tY.map bcA.symm),
      Fintype.card_fin]
  haveI : Module.Finite K (SecOnR fA H ⊤) := Module.finite_of_finrank_eq_succ hfr
  let bs := Module.finBasisOfFinrankEq K _ hfr
  let s : Fin (N + 1) → H.Sec := fun k => SecOnR.topEquiv fA H (bs k)
  let bV := (bs.baseChange K').map bcA
  have hbV : ∀ k, SecOnR.topEquiv fY (H.pull πA) (bV k) = secPull (s k) πA := fun k => by
    simp only [bV, bcA, Module.Basis.map_apply, Module.Basis.baseChange_apply, LinearEquiv.ofBijective_apply]
    exact (congrArg (SecOnR.topEquiv fY (H.pull πA)) (one_smul K' (SecOnR.pull H PA.w ⊤ ⊤ le_top (bs k)))).trans
      (topEquiv_pull PA.w H _)
  have htY : ∀ j, SecOnR.topEquiv fY (H.pull πA) (tY j) =
      SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv (M.pull πG)).symm
        (secPull (t j) πG))) := fun j => by
    have e1 : SecOnR.topEquiv fY (M.pull πG) (bcG (1 ⊗ₜ bt j)) = secPull (t j) πG := by
      simp only [bcG, LinearEquiv.ofBijective_apply]
      refine (congrArg (SecOnR.topEquiv fY (M.pull πG))
        (one_smul K' (SecOnR.pull M PG.w ⊤ ⊤ le_top (bt j)))).trans ?_
      rw [topEquiv_pull]
      show secPull (SecOnR.topEquiv fG M (basisOfExistsUnique _ htt j)) πG = _
      rw [basisOfExistsUnique_apply, LinearEquiv.apply_symm_apply]
    rw [← e1]
    simp only [tY, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    show SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ (bcG (1 ⊗ₜ bt j))) =
      SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv _).symm (SecOn.topEquiv _ (bcG (1 ⊗ₜ bt j)))))
    exact congrArg (fun z => SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ z))
      ((SecOn.topEquiv (M.pull πG)).symm_apply_apply _).symm
  let g : Matrix (Fin (N + 1)) (Fin (N + 1)) K' := fun j k => bV.repr (tY j) k
  have hsum : ∀ c : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
      SecOnR.topEquiv fY (H.pull πA) (∑ k, c k • bV k) := fun c => by
    rw [topEquiv_sum]
    simp only [hbV]
  refine ⟨s, g, ?_, ?_, fun j => ?_, fun c c' h => ?_⟩
  · refine veryAmpleBy_of_span fA H s₁ s hs₁ fun i => ⟨bs.repr ((SecOnR.topEquiv fA H).symm (s₁ i)), ?_⟩
    conv_lhs => rw [← (SecOnR.topEquiv fA H).apply_symm_apply (s₁ i),
      ← bs.sum_repr ((SecOnR.topEquiv fA H).symm (s₁ i))]
    rw [topEquiv_sum]
  · have : g = Matrix.transpose (bV.toMatrix tY) := by
      ext j k
      rfl
    rw [this, Matrix.det_transpose]
    letI := bV.invertibleToMatrix tY
    exact Matrix.isUnit_det_of_invertible _
  · rw [hsum, bV.sum_repr (tY j), htY]
    exact secMaps_congr hLy hHy w hw _
  · rw [hsum, hsum] at h
    have h3 : bV.equivFun.symm c = bV.equivFun.symm c' := by
      simpa only [Module.Basis.equivFun_symm_apply] using (SecOnR.topEquiv fY (H.pull πA)).injective h
    exact bV.equivFun.symm.injective h3

end GlobalTheory.BasisMatch

open GlobalTheory.AbLaw GlobalTheory.Cartier in

theorem GlobalTheory.BasisMatch.exists_basis_match : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s₁ M w N t hH hs₁ hM hw ht
  haveI := hA.proper
  haveI := hG.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : Module.Flat W K' := IsLocalization.flat K' (nonZeroDivisors W)
  have PG : IsPullback (pullback.fst G.hom (spMap (algebraMap W K'))) (pullback.snd G.hom (spMap (algebraMap W K')))
      G.hom (spMap (algebraMap W K')) := IsPullback.of_hasPullback _ _
  have PA : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    refine (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).of_iso
      ((Over.forget _).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
      exact (Category.id_comp _).symm
    · have := Over.w e.inv
      simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      exact this.symm
    · simp
    · simp
  exact GlobalTheory.BasisMatch.core A.hom G.hom _ _ _ PA PG H M w s₁ t hH hs₁ hM hw ht
