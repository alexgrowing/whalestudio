import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmpleStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.CubicalFibreAmple

section General
variable {X X' Y : Scheme.{0}}

theorem pw_pw (H : LB X) (a b : ℤ) : pw (pw H a) b = pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_linComb_pw {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Triv (LB.LinComb L φ ε)) (d : ℤ) : Triv (LB.LinComb (pw L d) φ ε) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_⟩
  have e := congrArg (· ^ d) (ht i j)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
  exact (zpow_comm _ _ _).trans (congrArg (· ^ ε k)
    ((map_zpow _ _ d).symm.trans (congrArg _ (map_zpow (pullU (φ k) _) _ d).symm)))

theorem exists_pull_mem {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ z, π z ∈ nonzeroLocus s → z ∈ nonzeroLocus t := by
  obtain ⟨t, ht⟩ := SpreadSec.exists_pull s π
  refine ⟨t, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := AmpleSpan.exists_chart_of_mem s hz
  refine (mem_nonzeroLocus t z).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩
  rw [ht (fun _ => k) z hk]
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s π z hk).1 hz

theorem exists_mem_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {M : LB X} (hM : M.IsLB) (σ : LB.Sec (M.pull π)) {z : X'} (hz : z ∈ nonzeroLocus σ) :
    ∃ u : LB.Sec M, π z ∈ nonzeroLocus u := by
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have e := (AmpleSpan.mem_nonzeroLocus_iff_gs σ (𝟙 X') z (k := fun _ => k) (mem_pull.2 hk)).1 hz
  rw [hu z k hk] at e
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum e
  exact ⟨u i, (AmpleSpan.mem_nonzeroLocus_iff_gs _ π z hk).2 (isUnit_of_mul_isUnit_right hi)⟩

theorem exists_finite_cover [CompactSpace X] {M : LB X} (s₀ : LB.Sec M)
    (h : ∀ x, ∃ u : LB.Sec M, x ∈ nonzeroLocus u) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec M => (nonzeroLocus u : Set X)) (fun u => (nonzeroLocus u).isOpen)
    (fun y _ => Set.mem_iUnion.2 (h y))
  refine ⟨F.card, Fin.cons s₀ (fun i => (F.equivFin.symm i : LB.Sec M)), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end General

theorem exists_mem_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left) (hN : N.IsLB)
    (s : LB.Sec N) (x : G.left) (hx : x ∈ nonzeroLocus s) :
    ∃ t : LB.Sec N, ∃ y ∈ nonzeroLocus t, G.hom y = IsLocalRing.closedPoint V := by
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  have hmax : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have : IsIntegral (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GeometricallyIntegral.geometrically_isIntegral (thick V (IsLocalRing.maximalIdeal V) 0) _ _
      (IsPullback.of_hasPullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 fun j => by
      refine eq_zero_of_basicOpen_eq_bot (X := pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) _
        (le_bot_iff.1 fun z hz => ?_)
      let p := pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0)
      have hz' : p z ∈ G.left.basicOpen (σ.f j) :=
        (SetLike.ext_iff.1 (Scheme.preimage_basicOpen p (σ.f j)) z).2 hz
      refine hcon σ (p z) (TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz'⟩) ?_
      have e : G.hom (p z) = thick V (IsLocalRing.maximalIdeal V) 0
          (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0) z) :=
        congrArg (fun q => q z) (pullback.condition (f := G.hom) (g := thick V (IsLocalRing.maximalIdeal V) 0))
      rw [e]
      refine PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top fun a ha => ?_).symm
      change Ideal.Quotient.mk _ a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ k, s.f k = 0 :=
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN s fun n =>
        (ThickDiv.main V ϖ hϖ G N s n).2 (h1 n s)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  rw [h2, Scheme.basicOpen_zero] at hk
  exact hk

theorem exists_valuationRing (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A] :
    ∃ (O : ValuationSubring (AlgebraicClosure (FractionRing A))) (g : A →+* O), g.Flat ∧ IsLocalHom g := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A (AlgebraicClosure (FractionRing A)))
  refine ⟨O, _, ?_, hl⟩
  have inj : Function.Injective (algebraMap A (AlgebraicClosure (FractionRing A))) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A)]
    exact (algebraMap (FractionRing A) _).injective.comp (IsFractionRing.injective A _)
  letI := ((algebraMap A (AlgebraicClosure (FractionRing A))).codRestrict O.toSubring h).toAlgebra
  refine Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (eq_bot_iff.2 ?_)
  rintro x ⟨⟨a, ha⟩, e⟩
  have e' : algebraMap A (AlgebraicClosure (FractionRing A)) a * x.1 = 0 := congrArg Subtype.val e
  exact Subtype.ext ((mul_eq_zero.1 e').resolve_left
    ((map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero ha)))

theorem relAmple_of_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  intro _ _ A _ _ _ _ _ B _ _ hB M h
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  have hL := M.L.isLB
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ _ _ (LB.isLB_pull hL _)).1 (h _ (jK A))
  have hH := isLB_pw hL d

  have h₁ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x, x ∈ nonzeroLocus σ := by
    have hσ : ∃ (σ : LB.Sec ((pw M.L.L d).pull (pullback.fst B.hom (jK A)))) (z : _), z ∈ nonzeroLocus σ := by
      rw [GlobalTheory.TrivLocus.pull_pw]
      have hz : (η[(Over.pullback (jK A)).obj B]).left (default : PrimeSpectrum (FractionRing A)) ∈
          ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨s i, _, hi⟩
    obtain ⟨σ, z, hz⟩ := hσ
    obtain ⟨u, hu⟩ := exists_mem_of_flat (algebraMap A (FractionRing A))
      (RingHom.flat_algebraMap_iff.2 inferInstance) (IsPullback.of_hasPullback B.hom (jK A)) hH σ hz
    exact ⟨u, _, hu⟩
  have h₂ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x ∈ nonzeroLocus σ, B.hom x = IsLocalRing.closedPoint A := by
    obtain ⟨σ, x, hx⟩ := h₁
    by_cases hA : IsLocalRing.maximalIdeal A = ⊥
    · refine ⟨σ, x, hx, PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top) ?_)⟩
      exact hA.le.trans bot_le
    · have : IsDiscreteValuationRing A := { not_a_field' := hA }
      exact exists_mem_closed_fibre A B hB _ hH σ x hx
  obtain ⟨σ, x, hx, hxc⟩ := h₂

  obtain ⟨O, g, hg, hl⟩ := exists_valuationRing A
  let t : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom g)
  let π := pullback.fst B.hom t
  have ht : Function.Surjective t := by
    letI := g.toAlgebra
    have : Module.Flat A O := hg
    have : IsLocalHom (algebraMap A O) := hl
    have : Module.FaithfullyFlat A O := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := O)
  have hB' := CubeGen.isAb_baseChange hB t
  obtain ⟨_, _, c, -⟩ := exists_isCPMap M (toBase_mul_pullback B t) _ (pull_isLB hL π) _ (pullIso_isGen hL π)
  have cube : Triv (Theta ((Over.pullback t).obj B) ((pw M.L.L d).pull π)) := by
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact triv_linComb_pw ⟨c.t, c.isGen⟩ d
  obtain ⟨σ', hσ'⟩ := exists_pull_mem σ π
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) x
    (IsLocalRing.closedPoint O) (hxc.trans (IsLocalRing.comap_closedPoint g).symm)
  have hu := SquareGenerated.exists_secs_sq_generate O (AlgebraicClosure (FractionRing A)) _ hB' _
    (LB.isLB_pull hH π) cube σ' ⟨z, hσ' z (by rw [← hz₁] at hx; exact hx), hz₂⟩
  rw [← GlobalTheory.TrivLocus.pull_pw, pw_pw, show (d : ℤ) * 2 = ((d * 2 : ℕ) : ℤ) by push_cast; rfl] at hu
  obtain ⟨m, u, hu⟩ := hu

  have hH₂ := isLB_pw hL ((d * 2 : ℕ) : ℤ)
  have gen : ∀ y, ∃ v : LB.Sec (pw M.L.L ((d * 2 : ℕ) : ℤ)), y ∈ nonzeroLocus v := fun y => by
    obtain ⟨q, hq⟩ := ht (B.hom y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) y q hq.symm
    have hw' : w ∈ ⨆ i, nonzeroLocus (u i) := by rw [hu]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hw'
    rw [← hw]
    exact exists_mem_of_flat g hg (IsPullback.of_hasPullback B.hom t) hH₂ (u i) hi
  obtain ⟨m', v, hv⟩ := exists_finite_cover (gen x).choose gen
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample A _ B.hom M.L.L (d * 2) m' v (by omega) hB.proper hL hv (fun q hq =>
    ⟨q.ResidueField, inferInstance, algebraMap A _, Ideal.ker_algebraMap_residueField q, h _ _⟩)
  obtain ⟨e, he, hw⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci A _ B.hom _ m' v hH₂ hv aff
  rw [pw_pw, ← Nat.cast_mul] at hw
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B M.L.L hL).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hw⟩

end GlobalTheory.CubicalFibreAmple
