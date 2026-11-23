import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRealDimOneIsFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreOfAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ISupNonzeroLocusSecComb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionProjSpaceOfSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosets
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.GoodOut

open GlobalTheory.Points

theorem isIntegrallyClosed_overring {o Ω : Type} [CommRing o] [IsDedekindDomain o] [Field Ω] [Algebra o Ω]
    [IsFractionRing o Ω] (R : Subalgebra o Ω) : IsIntegrallyClosed R := by
  have hfr : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective (A := o) z
    exact ⟨algebraMap o R a, algebraMap o R b, h.symm⟩
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ?_
  let I : Ideal R := (LinearMap.range (Algebra.linearMap R Ω)).comap (LinearMap.toSpanSingleton R Ω x)
  by_contra hn
  have hI : I ≠ ⊤ := fun h => hn (by
    obtain ⟨a, ha⟩ : (1 : R) ∈ I := h ▸ Submodule.mem_top
    exact ⟨a, ha.trans (one_smul _ _)⟩)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  let p : Ideal o := m.comap (algebraMap o R)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hp' : ∀ y : Ω, ∃ a s : o, s ∉ p ∧ (y = algebraMap o Ω a * (algebraMap o Ω s)⁻¹ ∨
      y⁻¹ = algebraMap o Ω a * (algebraMap o Ω s)⁻¹) := fun y => by
    by_cases h0 : p = ⊥
    · obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := o) y
      exact ⟨a, b, h0 ▸ nonZeroDivisors.ne_zero hb, Or.inl (h.symm.trans (div_eq_mul_inv _ _))⟩
    · let V := Localization.subalgebra.ofField Ω p.primeCompl p.primeCompl_le_nonZeroDivisors
      have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o h0 V
      rcases ValuationRing.isInteger_or_isInteger V y with ⟨⟨_, a, s, hs, rfl⟩, h⟩ | ⟨⟨_, a, s, hs, rfl⟩, h⟩
      · exact ⟨a, s, hs, Or.inl h.symm⟩
      · exact ⟨a, s, hs, Or.inr h.symm⟩
  have := hm.isPrime
  let T := Localization.subalgebra.ofField Ω m.primeCompl m.primeCompl_le_nonZeroDivisors
  have : ValuationRing T := (ValuationRing.iff_isInteger_or_isInteger T Ω).2 fun y => by
    obtain ⟨a, s, hs, h⟩ := hp' y
    exact h.imp (fun h => ⟨⟨y, algebraMap o R a, algebraMap o R s, hs, h⟩, rfl⟩)
      (fun h => ⟨⟨y⁻¹, algebraMap o R a, algebraMap o R s, hs, h⟩, rfl⟩)
  obtain ⟨⟨_, a, s, hs, rfl⟩, h⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := T))
  refine hs (hIm ⟨a, ?_⟩)
  have hs0 : algebraMap R Ω s ≠ 0 := fun e => hs ((show s = 0 from Subtype.ext e) ▸ m.zero_mem)
  show algebraMap R Ω a = s • x
  rw [← h, Algebra.smul_def]
  show _ = algebraMap R Ω s * (algebraMap R Ω a * (algebraMap R Ω s)⁻¹)
  field_simp

theorem exists_hom_ker {R : Type} [CommRing R] (z : PrimeSpectrum R) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (f : R →+* K), ∀ t, f t = 0 ↔ t ∈ z.asIdeal :=
  ⟨AlgebraicClosure z.asIdeal.ResidueField, inferInstance, inferInstance,
    (algebraMap z.asIdeal.ResidueField _).comp (algebraMap R z.asIdeal.ResidueField), fun _ =>
    (map_eq_zero_iff (algebraMap z.asIdeal.ResidueField _) (RingHom.injective _)).trans
      Ideal.algebraMap_residueField_eq_zero⟩

theorem exists_unif (hL : Laws) {Z : Scheme.{0}} (P : PolAV Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (ξ : Sp R ⟶ Z) (U₁ : Set (Sp R))
    [IsCommMonObj ((Over.pullback ξ).obj P.A)] :
    ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
      (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj P.A)),
      LBIso U.LG.L (P.L.pull (pullback.fst P.A.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y U₁ := by
  have key : ∀ P' : PolAV (Sp R), ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
      (U : Unif (IsLocalRing.maximalIdeal R) D A P'.A), LBIso U.LG.L P'.L ∧ ∀ y, PsiUnitOn D.toPre y U₁ := by
    intro P'
    obtain ⟨A, eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK R) P'
    obtain ⟨D, rfl, hX⟩ := SelfUnif.exists_degData hL.cube (IsLocalRing.maximalIdeal R) P'
    refine ⟨D, A, ⟨SelfUnif.selfPre D A eA hA hw, fun k _ => SelfUnif.expBij D A eA hA hw hL.globalFns
      (IsAdicComplete.le_jacobson_bot _) k⟩, lbIso_refl D.toPre.P.isLB, fun y j V hV _ => ?_⟩
    obtain rfl : y = 0 := Subsingleton.elim _ _
    exact PsiCoordLocal.psiUnitOn_zero D.toPre D.tau_bimult j V hV (Set.subset_univ _)
  exact key (StrictPull.polPull P ξ)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

open GlobalTheory.CechPic EndoExtend in

theorem endo_and_isoExt [hA : ArithBase o Ω] {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)
    (hn : Geo.Tor.IsNormalScheme M.Z) :
    (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f →
      ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧
    (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ,
      LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt))
        ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) →
      LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  have := hA.ded
  have := hA.ft
  have := hA.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := isPreimmersion_pt M
  have := flat_pt M
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have hL := Q.L.isLB
  refine ⟨GlobalTheory.existsUnique_hom_extension_semiAbelian_normal GlobalTheory.existsUnique_hom_extension_semiAbelian _ _ M.pt
    ⟨hn, _, MinorModel.locallyOfFiniteType_int M, MinorModel.flat_int M _⟩ ‹_› ‹_› inferInstance inferInstance
    _ _ Q.semi Q.semi, fun n x x' hx ε ε' h => ?_⟩
  have := geometricallyIntegral_of_smooth Q.G.hom
  have := smooth_tensorObj_hom Q.G Q.G
  have := geometricallyIntegral_tensorObj_hom Q.G Q.G
  have h0 : CechPic.pull (eSec Q.G) (cls Q.L.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨Q.L.rig, Q.L.rigGen⟩
  have key : ∀ (y : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)) (δ : Fin n → ℤ), (∀ i, IsMonHom (y i)) →
      CechPic.pull (η[Q.G ⊗ Q.G]).left (cls _ (LB.isLB_linComb hL (fun i => (y i).left) δ)) = 0 := by
    intro y δ hy
    rw [cls_linComb hL, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, (hy i).one_hom]
    exact (congrArg (_ • ·) h0).trans (smul_zero _)
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    (pic_ext M.pt hn (Q.G ⊗ Q.G) (η[Q.G ⊗ Q.G]).left (Over.w _)
      ((key x ε fun i => (hx i).1).trans (key x' ε' fun i => (hx i).2).symm) ?_)
  exact (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2 h

theorem exists_th_notMem (hL : Laws) (hL₂ : Laws2) (ρ : S.Real) (z : PrimeSpectrum S.R) (a : S.Gam) :
    ∃ c : S.Gam, ρ.n • c = 0 ∧ (⟨S.th (a + c), S.th_mem _⟩ : S.R) ∉ z.asIdeal := by
  obtain ⟨K, _, _, f, hf⟩ := exists_hom_ker z
  let x : Sp K ⟶ Sp S.R := spMap f
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n * ρ.n ^ (j - 1 + ρ.k * 2) := by
    rw [hr, ρ.N_eq, ← pow_mul, ← pow_add, ← pow_succ']
    congr 1
    omega
  have hn : (ρ.n : K) ≠ 0 := by
    have h := (S.unit.map (f.comp (algebraMap o S.R))).ne_zero
    rw [map_natCast, hM, Nat.cast_mul] at h
    exact left_ne_zero_of_mul h
  obtain ⟨θ, hθ, hv⟩ := UnitTheta.exists_sec_of_baseOver S.R ρ.P ρ.th₁
  obtain ⟨y₀, hy₀, e₀⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
    (x (IsLocalRing.closedPoint K))
  let u : Over.mk x ⟶ baseOver (Sp S.R) := Over.homMk x (by simp)
  obtain ⟨y, hy, H⟩ := UnitTheta.exists_good_point_of_sec hL.polBaseChange hL.goodPt _ ρ.P θ K x ρ.n
    ρ.n_prime.two_le hn ⟨_, hθ y₀ hy₀, _, e₀.symm⟩ (u ≫ ρ.pt a)
  have := ρ.P.isAb.comm
  obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul ρ.pt ρ.pt_add
  obtain ⟨c, hc, -⟩ := ρ.pt_bij K x y (by rw [hM, pow_mul, hy, one_pow])
  obtain ⟨a₀, -, uniq⟩ := ρ.pt_bij K x 1 (one_pow _)
  refine ⟨c, (uniq _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
    (uniq _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun h => ?_⟩
  have e : (u ≫ ρ.pt a * y).left = spMap f ≫ (ρ.pt (a + c)).left := by
    rw [← hc, ρ.pt_add]
    exact congrArg CommaMorphism.left (MonObj.comp_mul u _ _).symm
  rw [e] at H
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (H (x := IsLocalRing.closedPoint K) trivial)
  have hk' := (le_preimage_iff _ _).2 hk
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hk'
  refine ((le_preimage_basicOpen_iff _ hU _).1 hk').ne_zero ?_
  rw [hv _ _ _ (ρ.th_val (a + c)) K f k hU, (hf _).2 h, zero_mul]

section Comb

variable {X Z : Scheme.{0}} (p : X ⟶ Z) {B : LB X} {J : Type} [Fintype J] (s : J → B.Sec) (W : Z.Opens)

def comb (c : J → Γ(Z, W)) (j : B.ι) : Γ(X, p ⁻¹ᵁ W ⊓ B.U j) :=
  ∑ l, (p.appLE W _ inf_le_left).hom (c l) * resG X inf_le_right ((s l).f j)

theorem comb_mem (c : J → Γ(Z, W)) : comb p s W c ∈ secOn B (p ⁻¹ᵁ W) := by
  intro i j
  have rr : ∀ {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)),
      resG X h' (resG X h f) = resG X (h'.trans h) f := fun h h' f => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  simp only [comb, map_sum, map_mul, Finset.mul_sum, LocThetaConv.resG_appLE, rr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm]
  congr 1
  have h := congrArg (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    p ⁻¹ᵁ W ⊓ B.U i ⊓ B.U j ≤ B.U i ⊓ B.U j)) ((s l).compat i j)
  rw [map_mul] at h
  exact (rr _ _ _).symm.trans (h.trans (congrArg _ (rr _ _ _)))

theorem valR_comb (c : J → Γ(Z, W)) {C : Type} [CommRing C] (x : Sp C ⟶ X) (j : B.ι)
    (hW : ⊤ ≤ (x ≫ p) ⁻¹ᵁ W) (hj : ⊤ ≤ x ⁻¹ᵁ B.U j) :
    valR x _ (comb p s W c j) = ∑ l, valR (x ≫ p) W (c l) * valR x _ ((s l).f j) := by
  have h : ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ W ⊓ B.U j) := fun y hy => ⟨hW hy, hj hy⟩
  refine (valR_eq x _ h _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ => (map_mul _ _ _).trans ?_))
  exact congrArg₂ (· * ·) ((valR_eq x _ h _).symm.trans (valR_appLE x p _ h _))
    ((valR_eq x _ h _).symm.trans (valR_res x inf_le_right h _))

variable [DecidableEq J] (b c : Matrix J J Γ(Z, W)) (hc : c * b = 1)
include hc

theorem mulVec_comb {C : Type} [CommRing C] (x : Sp C ⟶ X) (j : B.ι) (hW : ⊤ ≤ (x ≫ p) ⁻¹ᵁ W)
    (hj : ⊤ ≤ x ⁻¹ᵁ B.U j) :
    (c.map (valR (x ≫ p) W)).mulVec (fun i => valR x _ (comb p s W (b i) j)) = fun l => valR x _ ((s l).f j) := by
  have e : valR (x ≫ p) W = (valMap (x ≫ p) W hW).hom := funext (valR_eq _ W hW)
  have h : (fun i => valR x _ (comb p s W (b i) j)) =
      (b.map (valR (x ≫ p) W)).mulVec fun l => valR x _ ((s l).f j) := funext fun i => valR_comb p s W _ x j hW hj
  rw [h, Matrix.mulVec_mulVec, e, ← Matrix.map_mul, hc, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem exists_comb_ne_zero (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {K : Type} [Field K] (x : Sp K ⟶ X)
    (hW : ⊤ ≤ (x ≫ p) ⁻¹ᵁ W) : ∃ i j, valF x _ (comb p s W (b i) j) ≠ 0 := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ (x (IsLocalRing.closedPoint K))))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hl
  have hj' := (le_preimage_iff _ _).2 hj
  have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hj'
  by_contra! h
  refine ((le_preimage_basicOpen_iff _ hU _).1 hj').ne_zero ?_
  rw [← congrFun (mulVec_comb p s W b c hc x j hW hU) l,
    show (fun i => valR x _ (comb p s W (b i) j)) = 0 from funext fun i => h i j, Matrix.mulVec_zero]
  rfl

theorem comb_indep {K : Type} [Field K] (x : Sp K ⟶ Z) (hW : ⊤ ≤ x ⁻¹ᵁ W)
    (hs : ∀ a : J → K, (∀ (g : Sp K ⟶ X) (j), g ≫ p = x → ⊤ ≤ g ⁻¹ᵁ B.U j →
      ∑ l, a l * valR g _ ((s l).f j) = 0) → a = 0)
    (a : J → K) (ha : ∀ (g : Sp K ⟶ X) (j), g ≫ p = x → ∑ i, a i * valF g _ (comb p s W (b i) j) = 0) : a = 0 := by
  let v := (valMap x W hW).hom
  have h0 : Matrix.vecMul a (b.map v) = 0 := hs _ fun g j hg hj => by
    refine Eq.trans ?_ (ha g j hg)
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.map_apply, _root_.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Eq.trans ?_
      (congrArg (a l * ·) (valR_comb p s W (b l) g j (hg ▸ hW) hj)).symm
    rw [Finset.mul_sum, hg]
    exact Finset.sum_congr rfl fun m _ => by rw [valR_eq x W hW]
  have := congrArg (Matrix.vecMul · (c.map v)) h0
  rwa [Matrix.vecMul_vecMul, ← Matrix.map_mul, mul_eq_one_comm.1 hc, Matrix.map_one _ (map_zero v) (map_one v),
    Matrix.vecMul_one, Matrix.zero_vecMul] at this

theorem immersedBy_comb {o R : Type} [CommRing o] [CommRing R] [IsIntegral X] (hB : B.IsLB) (t : Z ⟶ Sp o)
    (t' : Z ⟶ Sp R) (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {m : ℕ} (e : Fin (m + 1) ≃ J) (φ : X ⟶ PSpace R m)
    [IsImmersion φ] (hφ : φ ≫ PSpace.str R m = p ≫ t')
    (hcrd : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd B s x v →
      Crd (ProjSpace.O1 R m) (ProjSpace.coord R m) (x ≫ φ) (fun i => v (e i))) :
    ImmersedBy p t B (p ⁻¹ᵁ W) (fun i => comb p s W (b i)) := by
  obtain ⟨π, hπ, hcl, hπc⟩ := CoordMap.exists_coordMap o X Z p t B (p ⁻¹ᵁ W) J (fun i => comb p s W (b i)) m e
    (fun i => comb_mem p s W _) (fun x hx => by
      let g := X.fromSpecResidueField x
      have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
      obtain ⟨i, j, hij⟩ := exists_comb_ne_zero p s W b c hc hs (K := X.residueField x) g
        (fun w _ => (congrArg (· ∈ p ⁻¹ᵁ W) (hg w)).mpr hx)
      have hU : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W ⊓ B.U j) := by
        by_contra h0
        exact hij (dif_neg h0)
      have := (le_preimage_basicOpen_iff (C := X.residueField x) g hU _).2 (Ne.isUnit hij)
        (x := IsLocalRing.closedPoint (X.residueField x)) trivial
      exact ⟨i, j, hg (IsLocalRing.closedPoint (X.residueField x)) ▸ this⟩)
  refine ⟨m, e, π, hπ, ?_, hcl⟩
  let V := p ⁻¹ᵁ W
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  refine LinFrame.isImmersion_lift_of_linear_change o _ _ t (V.ι ≫ p) m π hπ fun y => ?_
  have hy : (V.ι ≫ p) y ∈ W := y.2
  let Y := (V.ι ≫ p) ⁻¹ᵁ W
  have : Nonempty Y.toScheme := ⟨⟨y, hy⟩⟩
  have : IsIntegral Y.toScheme := isIntegral_of_isOpenImmersion (Y.ι ≫ V.ι)
  let K : Type := Y.toScheme.residueField (genericPoint Y.toScheme)
  let ξ : Sp K ⟶ Y.toScheme := Y.toScheme.fromSpecResidueField (genericPoint Y.toScheme)
  obtain ⟨j, hj⟩ := exists_le_preimage_of_iSup_eq_top ((ξ ≫ Y.ι) ≫ V.ι) hB.cover
  have hW : ⊤ ≤ (((ξ ≫ Y.ι) ≫ V.ι) ≫ p) ⁻¹ᵁ W := fun w _ => (ξ w).2
  refine ⟨W, R, inferInstance, W.ι ≫ t', Y.ι ≫ V.ι ≫ φ, c.submatrix e e, K, inferInstance, ξ, _, hy, inferInstance,
    ?_, ?_, ⟨?_⟩, Category.assoc ξ Y.ι π ▸ hπc K (ξ ≫ Y.ι) j hj, ?_⟩
  · rw [Category.assoc, Category.assoc, hφ, morphismRestrict_ι_assoc, Category.assoc]
  · rw [Matrix.det_submatrix_equiv_self]
    exact Matrix.isUnit_det_of_right_inverse hc
  · refine dense_iff_closure_eq.2 (top_unique ((genericPoint_spec Y.toScheme).ge.trans (closure_mono ?_)))
    exact Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply _ _⟩
  · have h := hcrd K ((ξ ≫ Y.ι) ≫ V.ι) (fun l => valR ((ξ ≫ Y.ι) ≫ V.ι) _ ((s l).f j))
      ⟨j, 1, hj, fun l => by rw [Units.val_one, _root_.one_mul]⟩
    have h' := mulVec_comb p s W b c hc _ j hW hj
    simp only [Category.assoc] at h h' ⊢
    convert h using 1
    funext i
    refine Eq.trans ?_ (congrFun h' (e i))
    exact e.sum_comp fun l => valR (ξ ≫ Y.ι ≫ V.ι ≫ p) W (c (e i) l) * valR (ξ ≫ Y.ι ≫ V.ι) _ (comb p s W (b l) j)

end Comb

section Transfer

variable {Z : Scheme.{0}} (P : PolAV Z)

def sect : P.A.left ⟶ (baseOver Z ⊗ P.A).left := (lift (toUnit P.A) (𝟙 P.A) : P.A ⟶ baseOver Z ⊗ P.A).left

theorem sect_snd : sect P ≫ (snd (baseOver Z) P.A).left = 𝟙 _ := by
  rw [sect, ← Over.comp_left, lift_snd, Over.id_left]

theorem sect_hom : sect P ≫ (baseOver Z ⊗ P.A).hom = P.A.hom := Over.w _

theorem sect_fst : sect P ≫ (fst (baseOver Z) P.A).left = P.A.hom :=
  (congrArg (sect P ≫ ·) ((Category.comp_id _).symm.trans (Over.w (fst (baseOver Z) P.A)))).trans (sect_hom P)

instance isIso_snd : IsIso (snd (baseOver Z) P.A).left := inferInstanceAs (IsIso (pullback.snd (𝟙 Z) P.A.hom))

instance isIso_sect : IsIso (sect P) := IsIso.of_isIso_fac_right (sect_snd P)

theorem snd_sect : (snd (baseOver Z) P.A).left ≫ sect P = 𝟙 _ := by
  rw [← cancel_mono (snd (baseOver Z) P.A).left, Category.assoc, sect_snd, Category.comp_id, Category.id_comp]

def tr {k : ℤ} (t : LB.Sec (LPow P.A P.L k (baseOver Z))) :
    LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => k)) :=
  chartSec (chartPullSame P.L _ _ _ (sect P) fun _ => (sect_snd P).symm) t

theorem valR_tr {k : ℤ} (t : LB.Sec (LPow P.A P.L k (baseOver Z))) {C : Type} [CommRing C] (x : Sp C ⟶ P.A.left)
    (j : Fin 1 → P.L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => k)).U j) :
    valR x _ ((tr P t).f j) = valR (x ≫ sect P) _ (t.f j) :=
  valR_appLE x (sect P) _ hj _

theorem nonzeroLocus_tr {k : ℤ} (t : LB.Sec (LPow P.A P.L k (baseOver Z))) :
    nonzeroLocus (tr P t) = sect P ⁻¹ᵁ nonzeroLocus t :=
  nonzeroLocus_chartSec _ _ fun y _ _ => exists_chart (LB.isLB_linComb P.isLB _ _) y

theorem le_chart_iff (k : ℤ) {Y : Scheme.{0}} (x : Y ⟶ P.A.left) (j : Fin 1 → P.L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => k)).U j ↔
      ⊤ ≤ (x ≫ sect P) ⁻¹ᵁ (LPow P.A P.L k (baseOver Z)).U j := by
  have e : ∀ y, (snd (baseOver Z) P.A).left ((x ≫ sect P) y) = x y := fun y => by
    rw [← Scheme.Hom.comp_apply, Category.assoc, sect_snd, Category.comp_id]
  exact ⟨fun h y hy => Set.mem_iInter.2 fun i => (congrArg (· ∈ P.L.U (j i)) (e y)).mpr (Set.mem_iInter.1 (h hy) i),
    fun h y hy => Set.mem_iInter.2 fun i => (congrArg (· ∈ P.L.U (j i)) (e y)).mp (Set.mem_iInter.1 (h hy) i)⟩

end Transfer

theorem valR_pow_g {X Y : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ X) (B : LB Y) (g : X ⟶ Y) (n : ℤ) (i j : B.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart B (fun _ : Fin 1 => g) (fun _ => i) ⊓
      LB.wchart B (fun _ : Fin 1 => g) (fun _ => j))) :
    valR x _ ((LB.LinComb B (K := Fin 1) (fun _ => g) (fun _ => n)).g (fun _ => i) (fun _ => j)).val =
      valR (x ≫ g) _ (B.g i j).val ^ n := by
  refine (congrArg (fun u => valR x _ (Units.val u)) (Fintype.prod_unique _)).trans ?_
  refine (TuplePoint.valR_zpow_unit x h _ n).trans ?_
  exact congrArg (· ^ n) ((TuplePoint.valR_res_unit x _ h _).trans (TuplePoint.valR_pullU x g (B.U i ⊓ B.U j) (B.g _ _)))

variable (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩)

open PreModel in

theorem genVal_comb (k : ℤ) {I : Type} [Fintype I] (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R))))
    (W : (affModel S).Z.Opens) (f : I → Γ((affModel S).Z, W)) (a : I → Ω)
    (h : (W : Set (affModel S).Z).Nonempty → ∀ i, valF (affModel S).pt W (f i) = a i) :
    GenVal ρ (affModel S) ⊤ (pre ρ c).u₀ (pre ρ c).G (pre ρ c).φ (pre ρ c).L.L (pre ρ c).w k t a _
      (comb (Z := Sp S.R) ρ.P.A.hom (fun i => tr ρ.P (t i)) W f) := by
  intro K _ β g r jP jL h₁ h₂ hP hL hV
  let x : Sp K ⟶ ρ.P.A.left := g ≫ pullback.fst ρ.P.A.hom (⊤ : (Sp S.R).Opens).ι
  have hr : r = x ≫ sect ρ.P := by
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, Category.assoc, sect_snd, Category.comp_id]
    exact h₂
  have hx : x ≫ ρ.P.A.hom = spMap β ≫ (affModel S).pt :=
    ((Category.assoc _ _ _).trans (congrArg (g ≫ ·) pullback.condition)).trans h₁
  have hW : ⊤ ≤ (x ≫ ρ.P.A.hom) ⁻¹ᵁ W := fun y _ => hV ⟨y, rfl⟩
  have hne : (W : Set (affModel S).Z).Nonempty := ⟨_, hW (x := IsLocalRing.closedPoint K) trivial⟩
  have cP : ⊤ ≤ x ⁻¹ᵁ (LB.LinComb ρ.P.L (K := Fin 1) (fun _ => 𝟙 ρ.P.A.left) (fun _ => k)).U (fun _ => jP) :=
    fun y _ => Set.mem_iInter.2 fun _ => hP ⟨y, rfl⟩
  have cL : ⊤ ≤ x ⁻¹ᵁ (LB.LinComb ρ.P.L (K := Fin 1) (fun _ => 𝟙 ρ.P.A.left) (fun _ => k)).U (fun _ => jL) :=
    fun y _ => Set.mem_iInter.2 fun _ => hL ⟨y, rfl⟩
  have dP := (le_chart_iff ρ.P k x _).1 cP
  have dL := (le_chart_iff ρ.P k x _).1 cL
  have hw : valF g _ ((pre ρ c).w.s (fun _ => jP, fun _ => jL)).val = valR x _ (ρ.P.L.g jP jL).val :=
    (TuplePoint.valR_linComb_g g ρ.P.L _ 1 (fun _ => jP) (fun _ => jL) fun z _ =>
      ⟨Set.mem_iInter.2 fun _ => hP ⟨z, rfl⟩, Set.mem_iInter.2 fun _ => hL ⟨z, rfl⟩⟩).trans (zpow_one _)
  refine Eq.trans ?_ (congrArg₂ (fun u v => u ^ k * v) hw
    (valR_comb (Z := Sp S.R) ρ.P.A.hom (fun i => tr ρ.P (t i)) W f x _ hW cL)).symm
  rw [Finset.mul_sum, hr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, valR_tr ρ.P _ x _ cL, hx]
  refine congrArg₂ (· * ·) ((congrArg β (h hne i).symm).trans
    (valR_spMap_comp β _ W ((affModel S).top_le_preimage_pt hne) _).symm) ?_
  refine (Specialise.valR_compat (t i) _ dP dL).trans (congrArg (· * _) ?_)
  refine (valR_pow_g _ ρ.P.L _ k jP jL fun y hy => ⟨dP hy, dL hy⟩).trans ?_
  rw [Category.assoc, sect_snd, Category.comp_id]

section Support

open PreModel

theorem mem_supI_of_notMem {z : PrimeSpectrum S.R} {a : S.Gam} (h : (⟨S.th a, S.th_mem a⟩ : S.R) ∉ z.asIdeal) :
    a ∈ S.supI (affModel S) z ∧ (S.th a)⁻¹ ∈ (affModel S).O z := by
  have := isFractionRing_R S
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  refine ⟨⟨fun e => h ((show (⟨S.th a, S.th_mem a⟩ : S.R) = 0 from Subtype.ext e) ▸ zero_mem _), fun j => ?_⟩, ?_⟩
  · exact (RatModel.mem_O_ofAffine (A := S.R) (z := z)).2 ⟨⟨_, S.th_mem j⟩, _, h, rfl⟩
  · exact (RatModel.mem_O_ofAffine (A := S.R) (z := z)).2 ⟨1, _, h, by rw [map_one, one_div]; rfl⟩

include ρ

theorem TT_eq_bot (hL : Laws) (hL₂ : Laws2) (z : (affModel S).Z) : S.TT (affModel S) z = ⊥ := by
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have h := ThetaReal.closure_eq_top_of_meets_torsion_cosets _ ρ.n (j + ρ.k * 2) (S.r * S.N) ρ.n_prime.one_le
    (by have := ρ.two_le; omega) (by rw [hr, ρ.N_eq, ← pow_mul, ← pow_add]) (S.supI (affModel S) z) fun a => by
      obtain ⟨y, hy, H⟩ := exists_th_notMem hL hL₂ ρ z a
      exact ⟨y, hy, (mem_supI_of_notMem H).1⟩
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, PreInh.perp_top]

theorem th_mem_and_inv_mem (hL : Laws) (hL₂ : Laws2) {z : (affModel S).Z} {a : S.Gam}
    (h : a ∈ S.supI (affModel S) z) : S.th a ∈ (affModel S).O z ∧ (S.th a)⁻¹ ∈ (affModel S).O z := by
  have := isFractionRing_R S
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  refine ⟨RatModel.algebraMap_mem_O_ofAffine (A := S.R) z ⟨_, S.th_mem a⟩, ?_⟩
  obtain ⟨y, -, H⟩ := exists_th_notMem hL hL₂ ρ z 0
  obtain ⟨h₁, h₂⟩ := mem_supI_of_notMem H
  have := mul_mem h₂ (h.2 (0 + y))
  rwa [div_eq_mul_inv, inv_mul_cancel_left₀ h₁.1] at this

end Support

theorem span_div (O : Subalgebra o Ω) {J : Type} (b : Matrix J J Ω) {u : Ω} (h₀ : u ≠ 0) (h₁ : u ∈ O) (h₂ : u⁻¹ ∈ O) :
    Submodule.span O (Set.range b) = Submodule.span O (Set.range (Matrix.of fun i l => b i l / u)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) <;> rintro _ ⟨i, rfl⟩
  · have e : b i = (⟨u, h₁⟩ : O) • (Matrix.of fun i l => b i l / u) i :=
      funext fun l => (mul_div_cancel₀ (b i l) h₀).symm
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have e : (Matrix.of fun i l => b i l / u) i = (⟨u⁻¹, h₂⟩ : O) • b i := funext fun l => div_eq_inv_mul (b i l) u
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open PreModel in

theorem nonempty_out (hL : Laws) (hL₂ : Laws2) [hA : ArithBase o Ω] [IsIntegrallyClosed S.R] :
    Nonempty (ZHOut ρ (affModel S) ⊤ (RatModel.Lat.const (affModel S) S.J)) := by
  have := hA.ded
  have : IsNoetherianRing S.R := isNoetherianRing_of_fg S.fg
  obtain ⟨c⟩ := (hL.cube (Sp S.R) ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  let Q := pre ρ c
  have hne : ((⊤ : (affModel S).Z.Opens) : Set (affModel S).Z).Nonempty := ⟨genericPoint _, trivial⟩
  obtain ⟨hSec, hAb, -⟩ := pre_sec ρ c
  obtain ⟨hEndo, hIso⟩ := endo_and_isoExt Q (ZJ.isNormalScheme_sp S.R)
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  have himm := immBy_of_spans hL.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists
  have hcov : ⨆ i, nonzeroLocus (tr ρ.P (ρ.s i)) = ⊤ := by
    have h := himm.1
    simp only [Set.mem_univ, iSup_pos] at h
    simp only [nonzeroLocus_tr]
    rw [← Scheme.Hom.preimage_iSup, h]
    rfl
  have hmat : ∀ (W : (affModel S).Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI (affModel S) z ∧
      (RatModel.Lat.const (affModel S) S.J).E z = Submodule.span ((affModel S).O z) (Set.range b)) →
      ∃ B C : Matrix S.J S.J Γ((affModel S).Z, W), C * B = 1 ∧ ∀ i, GenVal ρ (affModel S) ⊤ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N
        ρ.s (fun l => b i l / S.th x₀) _ (comb (Z := Sp S.R) ρ.P.A.hom (fun i => tr ρ.P (ρ.s i)) W (B i)) := by
    intro W x₀ b hb
    obtain ⟨B, C, h₁, h₂⟩ := PreSec.exists_matrix (affModel S) W (Matrix.of fun i l => b i l / S.th x₀) fun z hz =>
      (hb z hz).2.trans (span_div _ b (hb z hz).1.1 (th_mem_and_inv_mem ρ hL hL₂ (hb z hz).1).1
        (th_mem_and_inv_mem ρ hL hL₂ (hb z hz).1).2)
    exact ⟨B, C, h₁, fun i => genVal_comb ρ c _ _ W _ _ fun h => h₂ h i⟩
  exact ⟨{
    u₀ := Q.u₀
    u₀_gen := Q.u₀_gen
    G := Q.G
    grp := Q.grp
    comm := Q.comm
    semi := Q.semi
    dim := Q.dim
    qproj := Q.qproj
    φ := Q.φ
    cart := Q.cart
    L := Q.L
    cub := Q.cub
    sym := Q.sym
    w := Q.w
    w_gen := Q.w_gen
    w_rig := Q.w_rig
    hypS := ρ.hypS
    endo := hEndo
    isoExt := fun n x x' hx ε ε' _ _ => hIso n x x' hx ε ε'
    split := Q.split
    ab := hAb.trans (Set.eq_univ_of_forall fun z => TT_eq_bot ρ hL hL₂ z).symm
    pol := fun W _ => ⟨(StrictPull.polPull ρ.P W.ι).ample, (StrictPull.polPull ρ.P W.ι).ktriv⟩
    sec := hSec
    unif := fun R _ _ _ _ _ _ _ ξ _ h => @exists_unif hL _ ρ.P R _ _ _ _ _ ξ _ h
    theta := fun W x₀ hx => by
      obtain ⟨u, hu, h⟩ : ∃ u : Γ((affModel S).Z, W), IsUnit u ∧
          ((W : Set (affModel S).Z).Nonempty → valF (affModel S).pt W u = (S.th x₀)⁻¹) := by
        by_cases hW : (W : Set (affModel S).Z).Nonempty
        · obtain ⟨u, hu⟩ := (RatModel.mem_ringOn_iff_exists hW).1
            (RatModel.mem_ringOn.2 fun z hz => (th_mem_and_inv_mem ρ hL hL₂ (hx z hz)).2)
          obtain ⟨v, hv⟩ := (RatModel.mem_ringOn_iff_exists hW).1
            (RatModel.mem_ringOn.2 fun z hz => (th_mem_and_inv_mem ρ hL hL₂ (hx z hz)).1)
          refine ⟨u, IsUnit.of_mul_eq_one v ((affModel S).res_injective W hW ?_), fun _ => hu⟩
          rw [map_mul, map_one, RatModel.res_apply, RatModel.res_apply, hu, hv,
            inv_mul_cancel₀ (hx _ hW.some_mem).1]
        · exact ⟨1, isUnit_one, fun h => absurd h hW⟩
      refine ⟨comb (Z := Sp S.R) ρ.P.A.hom (fun _ : Unit => tr ρ.P ρ.th₁) W (fun _ => u), comb_mem _ _ _ _,
        genVal_comb ρ c 1 (fun _ : Unit => ρ.th₁) W _ _ fun hW _ => h hW, fun K _ _ x hxW => ?_⟩
      obtain ⟨y, hy, e⟩ := ThetaFibre.exists_mem_nonzeroLocus_fibre hL₂.secBaseChangeAny S.R ρ.P ρ.th₁ ρ.th₁_basis
        (x (IsLocalRing.closedPoint K))
      have hy' : (snd (baseOver (Sp S.R)) ρ.P.A).left y ∈ nonzeroLocus (tr ρ.P ρ.th₁) := by
        rw [nonzeroLocus_tr]
        exact (congrArg (fun q => q y ∈ nonzeroLocus ρ.th₁) (snd_sect ρ.P)).mpr hy
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
      have := ρ.P.isAb.smooth
      obtain ⟨g, hg, hO⟩ := LocThetaConv.exists_point (Y := Sp S.R) ρ.P.A.hom x _ _ hj e
      have hU := le_preimage_mono _ (Scheme.basicOpen_le _ _) hO
      have hW : ⊤ ≤ (g ≫ ρ.P.A.hom) ⁻¹ᵁ W := hg ▸ (top_le_preimage_iff _ _).2 hxW
      refine ⟨g, j, hg, fun h0 => ?_⟩
      have h1 := (valR_comb (Z := Sp S.R) ρ.P.A.hom (fun _ : Unit => tr ρ.P ρ.th₁) W (fun _ => u) g j hW
        hU).symm.trans h0
      rw [Fintype.sum_unique] at h1
      exact mul_ne_zero ((valR_eq _ W hW u).trans_ne (hu.map _).ne_zero)
        ((le_preimage_basicOpen_iff _ hU _).1 hO).ne_zero h1
    secOf := exists_secOn_genVal_of_bases o Ω S ρ _ _ _ Q hne fun W x₀ b hb => by
      obtain ⟨B, C, -, h⟩ := hmat W x₀ b hb
      exact ⟨_, fun i => ⟨comb_mem _ _ _ _, h i⟩⟩
    sections := fun W x₀ b hb => by
      obtain ⟨B, C, hC, h⟩ := hmat W x₀ b hb
      refine ⟨_, fun i => ⟨comb_mem _ _ _ _, h i⟩, fun K _ _ x hx => ?_⟩
      have hW := (top_le_preimage_iff _ _).2 hx
      refine ⟨fun g hg => exists_comb_ne_zero (Z := Sp S.R) ρ.P.A.hom _ W B C hC hcov g
        ((congrArg (⊤ ≤ · ⁻¹ᵁ W) hg).mpr hW), comb_indep (Z := Sp S.R) ρ.P.A.hom _ W B C hC x hW fun a ha => ?_⟩
      refine PreSec.indep_fibre hL.secBaseChange ρ.P (by omega) (by rw [ρ.card, ρ.g_eq]) ρ.s
        (fun σ => (ρ.s_basis σ).exists) x a fun r j hr hj => ?_
      have e : (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ≫ sect ρ.P = r := by
        rw [Category.assoc, snd_sect, Category.comp_id]
      have hj' := (le_chart_iff ρ.P S.N (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) j).2 (e.symm ▸ hj)
      refine Eq.trans ?_ (ha _ j (by rw [← sect_fst, ← Category.assoc, e, hr]) hj')
      exact Finset.sum_congr rfl fun l _ => congrArg (a l * ·)
        ((valR_tr ρ.P (ρ.s l) _ _ hj').trans (by rw [e])).symm
    imm := fun W x₀ b hb σ hσ => by
      obtain ⟨B, C, hC, h⟩ := hmat W x₀ b hb
      obtain rfl : σ = _ := funext fun i => Q.eq_of_genVal hne _ _ _ _ _ _ (hσ i).2 (h i)
      obtain ⟨m, hm⟩ : ∃ m, Fintype.card S.J = m + 1 := Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
      let e : Fin (m + 1) ≃ S.J := (Fintype.equivFinOfCardEq hm).symm
      obtain ⟨ψ, h₁, h₂, h₃⟩ := ImmProj.exists_closedImmersion_of_immBy _ _ _ _ _ ρ.s m e himm
      have : IsIntegral ρ.P.A.left := Q.isIntegral
      refine immersedBy_comb (Z := Sp S.R) ρ.P.A.hom _ W B C hC (LB.isLB_linComb ρ.P.isLB _ _) (affModel S).s (𝟙 _)
        hcov e (sect ρ.P ≫ ψ) (by rw [Category.assoc, h₂, sect_hom, Category.comp_id]) ?_
      rintro K _ x v ⟨j, u, hj, hv⟩
      rw [← Category.assoc]
      exact h₃ K _ v ⟨j, u, (le_chart_iff ρ.P _ x j).1 hj, fun l =>
        (hv l).trans (congrArg (_ * ·) (valR_tr ρ.P (ρ.s l) x j hj))⟩ }⟩

theorem exists_out_dim_one : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.g = 1 ∧ (U₀ : Set M.Z).Nonempty ∧ Nonempty (ZHOut ρ M U₀ EE) := by
  intro hL hL₂
  obtain ⟨o, Ω, _, _, _, hA, S, ρ, hg, -, hfr⟩ := RealInhabitant.exists_real_dim_one_isFractionRing hL hL₂
  have := hA.ded
  have := isIntegrallyClosed_overring S.R
  exact ⟨o, Ω, _, _, _, hA, S, ρ, _, ⊤, _, hg, ⟨genericPoint _, trivial⟩, nonempty_out ρ hL hL₂⟩

end GlobalTheory.ZH.GoodOut

end
