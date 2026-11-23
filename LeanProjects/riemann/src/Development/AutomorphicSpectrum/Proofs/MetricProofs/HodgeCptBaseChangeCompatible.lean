import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HcptFlat

theorem pull_eq {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (j : E →+ F)
    (p' : Cpt ξ') (hq : genPt ξ ⤳ f p'.1) :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, hq⟩ : Set E)) := by
  unfold Lat.pull
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨hq, e, he, rfl⟩

theorem noeth_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ) (q : Cpt ξ)
    (h : IsNoetherianRing (regAt ξ q)) : IsNoetherianRing (X.presheaf.stalk q.1) :=
  isNoetherianRing_of_ringEquiv (regAt ξ q) (RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun a b e => hg.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩).symm

theorem exists_genWeil {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (hW : Out.WeilSt) {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c)
    (t : SAB H X) (m : SABMap t Y.t f) (hj : ξ ≫ f = y₀ ≫ Y.j) (n : ℕ) (hn : 1 ≤ n)
    (ht : FullTorsion t.G ξ n) (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ n) : ∃ e, GenWeil t.G t.PP.L ξ n e := by
  obtain ⟨PP', cub, sym, adj, prim, n₁, -⟩ := sabPull Out.proved_CubePullSt ξ t
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₁
  rw [hj] at n₂
  obtain ⟨n₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₂
  have := GlobalTheory.T.exists_generic_weil_pairing hW E H D l _ _ _ X _ (GlobalTheory.ModelCompare.objOfSABMap Y.oF n₃) t ξ n₁ Ω (𝟙 _) n hn
    (by rwa [Category.id_comp]) hζ
  rwa [Category.id_comp] at this

theorem flat_ker {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : φ.Flat) {κ Ix : Type} [Fintype κ] [Fintype Ix]
    [DecidableEq κ] [DecidableEq Ix] (A : Matrix κ Ix R) (x : Ix → R') (hx : (A.map φ).mulVec x = 0) :
    ∃ (s : ℕ) (c : Fin s → R') (y : Fin s → Ix → R), (∀ l, A.mulVec (y l) = 0) ∧
      ∀ k, x k = ∑ l, c l * φ (y l k) := by
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  let X : (Ix → R) →ₗ[R] R' := Fintype.linearCombination R x
  let f : (κ → R) →ₗ[R] (Ix → R) := A.transpose.mulVecLin
  have h : X ∘ₗ f = 0 := by
    refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
    have := congrFun hx k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
    simp only [X, f, LinearMap.comp_apply, Fintype.linearCombination_apply, Matrix.mulVecLin_apply, LinearMap.single_apply,
      LinearMap.zero_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply, Algebra.smul_def]
    exact this
  obtain ⟨s, a, y, hxy, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free h
  refine ⟨s, fun l => y (Finsupp.single l 1), fun l k => a (Pi.single k 1) l, fun l => ?_, fun k => ?_⟩
  · funext k
    have h1 := congrArg (fun g => g (Pi.single k 1) l) ha
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : f (Pi.single k 1) = ∑ r, A k r • (Pi.single r 1 : Ix → R) := by
      funext t
      simp [f, Matrix.mulVec_single_one, Finset.sum_apply, Pi.single_apply]
    rw [h2, map_sum] at h1
    simpa [Matrix.mulVec, dotProduct, Finsupp.finset_sum_apply] using h1
  · have h1 := congrArg (fun g => g (Pi.single k 1)) hxy
    simp only [LinearMap.comp_apply] at h1
    have h2 : X (Pi.single k 1) = x k := by simp [X, Fintype.linearCombination_apply, Pi.single_apply]
    rw [← h2, h1]
    conv_lhs => rw [← Finsupp.sum_single (a (Pi.single k 1))]
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_one (a (Pi.single k 1) l), ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Algebra.smul_def, mul_comm]
    rfl

theorem flat_sys {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : φ.Flat) {κ Ix Mx : Type} [Fintype κ] [Fintype Ix]
    [Fintype Mx] [DecidableEq κ] [DecidableEq Ix] [DecidableEq Mx] (P : κ → Ix → R) (Q : Mx → Ix → R) (d : R) (x : Ix → R')
    (z : Mx → R') (h1 : ∀ q, ∑ l, φ (P q l) * x l = 0) (h2 : ∀ a, ∑ l, φ (Q a l) * x l + φ d * z a = 0) :
    ∃ (s : ℕ) (c : Fin s → R') (y : Fin s → Ix → R) (v : Fin s → Mx → R), (∀ n q, ∑ l, P q l * y n l = 0) ∧
      (∀ n a, ∑ l, Q a l * y n l + d * v n a = 0) ∧ (∀ l, x l = ∑ n, c n * φ (y n l)) ∧
      ∀ a, z a = ∑ n, c n * φ (v n a) := by
  let A : Matrix (κ ⊕ Mx) (Ix ⊕ Mx) R := Matrix.of fun r c => match r, c with
    | .inl q, .inl l => P q l
    | .inl _, .inr _ => 0
    | .inr a, .inl l => Q a l
    | .inr a, .inr b => if a = b then d else 0
  have hA : ∀ (w : Ix ⊕ Mx → R), A.mulVec w = 0 → (∀ q, ∑ l, P q l * w (.inl l) = 0) ∧
      ∀ a, ∑ l, Q a l * w (.inl l) + d * w (.inr a) = 0 := by
    intro w hw
    refine ⟨fun q => ?_, fun a => ?_⟩
    · have := congrFun hw (.inl q)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A] using this
    · have := congrFun hw (.inr a)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A] using this
  have hm : (A.map φ).mulVec (Sum.elim x z) = 0 := by
    funext r
    rcases r with q | a
    · simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A] using h1 q
    · simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A, apply_ite φ] using h2 a
  obtain ⟨s, c, y, hy, hc⟩ := flat_ker φ hφ A _ hm
  exact ⟨s, c, fun n l => y n (.inl l), fun n a => y n (.inr a), fun n => (hA _ (hy n)).1, fun n => (hA _ (hy n)).2,
    fun l => hc (.inl l), fun a => hc (.inr a)⟩

section Lin

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V']
  [Module Ω' V'] {j : V →+ V'} {r : ℕ} {b : Fin r → V}

theorem span_image_frame (hj : IsExtOver i j) (hsp : Submodule.span Ω' (Set.range j) = ⊤)
    (hbs : Submodule.span Ω (Set.range b) = ⊤) : Submodule.span Ω' (Set.range fun k => j (b k)) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  have he : e ∈ Submodule.span Ω (Set.range b) := hbs ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  simp only [SetLike.mem_coe, map_sum, hj.1]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem coef_zero (hj : IsExtOver i j) (hb : LinearIndependent Ω b) (f : V →ₗ[Ω] V) (f' : V' →ₗ[Ω'] V')
    (hf : ∀ e, f' (j e) = j (f e)) (C : Fin r → Fin r → Ω) (hC : ∀ l, f (b l) = ∑ k, C l k • b k) (c : Fin r → Ω')
    (h0 : f' (∑ l, c l • j (b l)) = 0) (k : Fin r) : ∑ l, c l * i (C l k) = 0 := by
  have hli : LinearIndependent Ω' fun k => j (b k) := hj.2 r b hb
  have hjf : ∀ l, f' (j (b l)) = ∑ k, i (C l k) • j (b k) := fun l => by
    rw [hf, hC, map_sum]
    exact Finset.sum_congr rfl fun k _ => hj.1 _ _
  have h1 : ∑ k, (∑ l, c l * i (C l k)) • j (b k) = 0 := by
    rw [← h0, map_sum]
    simp only [map_smul, hjf, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  exact Fintype.linearIndependent_iff.1 hli _ h1 k

theorem comb_ker (f : V →ₗ[Ω] V) (C : Fin r → Fin r → Ω) (hC : ∀ l, f (b l) = ∑ k, C l k • b k) (y : Fin r → Ω)
    (h0 : ∀ q, ∑ k, C k q * y k = 0) : f (∑ k, y k • b k) = 0 := by
  rw [map_sum]
  simp only [map_smul, hC, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  refine Finset.sum_eq_zero fun q _ => ?_
  have : ∑ k, y k * C k q = 0 := by rw [← h0 q]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [this, zero_smul]

end Lin

section Flat

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'} {R : Subring Ω} {R' : Subring Ω'} {φ : R →+* R'}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {j : V →+ V'} {r T m : ℕ}
  {b : Fin r → V}

theorem flat_lat (hφ : φ.Flat) (hφi : ∀ a, (φ a : Ω') = i a) (hj : IsExtOver i j) (hb : LinearIndependent Ω b)
    (f : Fin T → V →ₗ[Ω] V) (f' : Fin T → V' →ₗ[Ω'] V') (hf : ∀ t e, f' t (j e) = j (f t e))
    (hfL : ∀ t k, f t (b k) ∈ Submodule.span R (Set.range b)) (W : Submodule Ω V) (W' : Submodule Ω' V')
    (hW : W = ⨅ t, LinearMap.ker (f t)) (hW' : W' = ⨅ t, LinearMap.ker (f' t)) (L : Submodule R V)
    (hL : L = Submodule.span R (Set.range b)) :
    Submodule.span R' (j '' (L : Set V)) ⊓ W'.restrictScalars R' =
      Submodule.span R' (j '' ((L ⊓ W.restrictScalars R : Submodule R V) : Set V)) := by
  classical
  have hR : ∀ a ∈ R, i a ∈ R' := fun a ha => by rw [← hφi ⟨a, ha⟩]; exact (φ _).2
  apply le_antisymm
  · rintro e' ⟨he1, he2⟩

    have hle : Submodule.span R' (j '' (L : Set V)) ≤ Submodule.span R' (Set.range fun k => j (b k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ Submodule.span R (Set.range b) := hL ▸ he
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he'
      simp only [SetLike.mem_coe, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      have : j (c k • b k) = (⟨i (c k), hR _ (c k).2⟩ : R') • j (b k) := hj.1 (c k : Ω) (b k)
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 (hle he1)
    have hC : ∀ t l, ∃ C : Fin r → R, f t (b l) = ∑ k, (C k : Ω) • b k := fun t l => by
      obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hfL t l)
      exact ⟨C, hC.symm⟩
    choose C hC using hC
    have hx' : e' = ∑ l, (x l : Ω') • j (b l) := hx.symm
    have h0 : ∀ t, f' t e' = 0 := fun t => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (hW' ▸ he2) t)
    obtain ⟨s, cc, y, v, hy1, -, hxy, -⟩ := flat_sys φ hφ (fun (q : Fin T × Fin r) l => C q.1 l q.2)
      (fun (_ : Fin 0) _ => 0) 0 x (fun _ => 0)
      (fun q => by
        refine Subtype.ext ?_
        have := coef_zero hj hb (f q.1) (f' q.1) (hf q.1) (fun l k => (C q.1 l k : Ω)) (hC q.1) (fun l => (x l : Ω'))
          (by rw [← hx']; exact h0 q.1) q.2
        simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_zero, hφi]
        rw [← this]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
      (fun a => a.elim0)
    let Ee : Fin s → V := fun n => ∑ k, (y n k : Ω) • b k
    have hE : ∀ n, Ee n ∈ L ⊓ W.restrictScalars R := fun n => by
      refine ⟨?_, ?_⟩
      · rw [hL]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (y n k) (Submodule.subset_span ⟨k, rfl⟩)
      · show Ee n ∈ W
        rw [hW]
        refine (Submodule.mem_iInf _).2 fun t => LinearMap.mem_ker.2 ?_
        refine comb_ker (f t) (fun l k => (C t l k : Ω)) (hC t) _ fun q => ?_
        have := congrArg (Subtype.val) (hy1 n (t, q))
        simpa using this
    have hsum : e' = ∑ n, cc n • j (Ee n) := by
      have hjE : ∀ n, j (Ee n) = ∑ k, i (y n k) • j (b k) := fun n => by
        simp only [Ee, map_sum]
        exact Finset.sum_congr rfl fun k _ => hj.1 _ _
      show e' = ∑ n, (cc n : Ω') • j (Ee n)
      simp only [hjE, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm, hx']
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul, hxy k]
      simp [hφi]
    rw [hsum]
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Ee n, hE n, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, ⟨he1, he2⟩, rfl⟩
    refine ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ W'
    have he3 : e ∈ W := he2
    rw [hW] at he3
    rw [hW']
    refine (Submodule.mem_iInf _).2 fun t => LinearMap.mem_ker.2 ?_
    rw [hf, LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 he3 t), map_zero]

end Flat

section Flat2

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'} {R : Subring Ω} {R' : Subring Ω'} {φ : R →+* R'}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {j : V →+ V'} {r T m : ℕ}
  {b : Fin r → V}

theorem flat_dual (hφ : φ.Flat) (hφi : ∀ a, (φ a : Ω') = i a) (hj : IsExtOver i j)
    (hsp : Submodule.span Ω' (Set.range j) = ⊤) (jd : Module.Dual Ω V →+ Module.Dual Ω' V')
    (hjd : ∀ w e, jd w (j e) = i (w e)) (hb : LinearIndependent Ω b) (hbs : Submodule.span Ω (Set.range b) = ⊤)
    (f : Fin T → V →ₗ[Ω] V) (f' : Fin T → V' →ₗ[Ω'] V') (hf : ∀ t e, f' t (j e) = j (f t e))
    (hfL : ∀ t k, f t (b k) ∈ Submodule.span R (Set.range b)) (W : Submodule Ω V) (W' : Submodule Ω' V')
    (hW : W = ⨅ t, LinearMap.ker (f t)) (hW' : W' = ⨅ t, LinearMap.ker (f' t))
    (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (g : Fin m → Module.Dual Ω V)
    (hg : ω = Submodule.span R (Set.range g)) (hω' : ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V))))
    (hgR : ∀ a l, g a (b l) ∈ R) (N : ℕ) (hN : (N : Ω) ≠ 0)
    (hNω : ∀ u : Module.Dual Ω V, (∀ l, u (b l) ∈ R) → (N : Ω) • u ∈ ω) :
    Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} =
      Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  classical
  have hR : ∀ a ∈ R, i a ∈ R' := fun a ha => by rw [← hφi ⟨a, ha⟩]; exact (φ _).2
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨heW, heω⟩
    have hjs := span_image_frame hj hsp hbs
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω').1 (hjs ▸ Submodule.mem_top : e' ∈ _)
    replace hc := hc.symm
    have hev : ∀ w, jd w e' = ∑ l, c l * i (w (b l)) := fun w => by
      rw [hc, map_sum]
      simp [hjd]
    have hCe : ∀ t l, ∃ C : Fin r → R, f t (b l) = ∑ k, (C k : Ω) • b k := fun t l => by
      obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hfL t l)
      exact ⟨C, hC.symm⟩
    choose C hC using hCe
    have h0 : ∀ t, f' t e' = 0 := fun t => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (hW' ▸ heW) t)
    let B : Module.Basis (Fin r) Ω V := Module.Basis.mk hb hbs.ge
    have hBb : ∀ k l, B.coord l (b k) = if k = l then 1 else 0 := fun k l => by
      have : b k = B k := by simp [B]
      rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have hx1 : ∀ l, (N : Ω') * c l ∈ R' := fun l => by
      have hm : (N : Ω) • B.coord l ∈ ω := hNω _ fun k => by
        rw [hBb]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      have h2 := heω (jd ((N : Ω) • B.coord l)) (by
        rw [hω']
        exact Submodule.subset_span ⟨_, hm, rfl⟩)
      rw [hev] at h2
      simp only [LinearMap.smul_apply, hBb, smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite i, map_natCast, map_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      rw [_root_.mul_one, map_natCast] at h2
      rw [mul_comm]
      exact h2
    have hx2 : ∀ a, jd (g a) e' ∈ R' := fun a => heω _ (by
      rw [hω', hg]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)
    obtain ⟨s, cc, y, v, hy1, hy2, hxy, hzv⟩ := flat_sys φ hφ (fun (q : Fin T × Fin r) l => C q.1 l q.2)
      (fun a l => (⟨g a (b l), hgR a l⟩ : R)) (-(N : R)) (fun l => (⟨_, hx1 l⟩ : R')) (fun a => (⟨_, hx2 a⟩ : R'))
      (fun q => by
        refine Subtype.ext ?_
        have := coef_zero hj hb (f q.1) (f' q.1) (hf q.1) (fun l k => (C q.1 l k : Ω)) (hC q.1) c
          (by rw [← hc]; exact h0 q.1) q.2
        simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_zero, hφi]
        calc ∑ l, i (C q.1 l q.2) * ((N : Ω') * c l) = (N : Ω') * ∑ l, c l * i (C q.1 l q.2) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by rw [this, mul_zero])
      (fun a => by
        refine Subtype.ext ?_
        simp only [map_neg, map_natCast, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_zero, Subring.coe_add,
          Subring.coe_neg, hφi, Subring.coe_natCast]
        rw [hev, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun l _ => ?_
        ring)
    let Ee : Fin s → V := fun n => (N : Ω)⁻¹ • ∑ k, (y n k : Ω) • b k
    have hgE : ∀ n a, g a (Ee n) = v n a := fun n a => by
      have h3 := congrArg Subtype.val (hy2 n a)
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_zero, Subring.coe_add, Subring.coe_neg,
        Subring.coe_natCast] at h3
      simp only [Ee, map_smul, map_sum, smul_eq_mul]
      have h4 : ∑ k, (y n k : Ω) * g a (b k) = (N : Ω) * v n a := by
        have e1 : ∑ k, (y n k : Ω) * g a (b k) = ∑ k, g a (b k) * (y n k : Ω) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [e1]
        linear_combination h3
      rw [h4, inv_mul_cancel_left₀ hN]
    have hE : ∀ n, Ee n ∈ {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} := fun n => by
      refine ⟨?_, fun w hw => ?_⟩
      · rw [hW]
        refine (Submodule.mem_iInf _).2 fun t => LinearMap.mem_ker.2 ?_
        rw [map_smul, comb_ker (f t) (fun l k => (C t l k : Ω)) (hC t) _ fun q => ?_, smul_zero]
        have := congrArg (Subtype.val) (hy1 n (t, q))
        simpa using this
      · rw [hg] at hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          rw [hgE]
          exact (v n a).2
        | zero => simpa using R.zero_mem
        | add u w _ _ hu hw => simpa using R.add_mem hu hw
        | smul a w _ hw =>
          show (a : Ω) * _ ∈ R
          exact R.mul_mem a.2 hw
    have hsum : e' = ∑ n, cc n • j (Ee n) := by
      have hN' : (N : Ω') ≠ 0 := fun e => hN (i.injective (by simpa using e))
      have hjE : ∀ n, j (Ee n) = (N : Ω')⁻¹ • ∑ k, i (y n k) • j (b k) := fun n => by
        simp only [Ee]
        rw [hj.1, map_sum, map_inv₀, map_natCast]
        congr 1
        exact Finset.sum_congr rfl fun k _ => hj.1 _ _
      show e' = ∑ n, (cc n : Ω') • j (Ee n)
      simp only [hjE, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      conv_lhs => rw [hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul]
      have h5 : (N : Ω') * c k = ∑ n, (cc n : Ω') * i (y n k) := by
        have := congrArg Subtype.val (hxy k)
        simpa [hφi] using this
      congr 1
      rw [show c k = (N : Ω')⁻¹ * ((N : Ω') * c k) from (inv_mul_cancel_left₀ hN' _).symm, h5, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum]
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨Ee n, Submodule.subset_span (hE n), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ W ∧ ∀ w ∈ ω, w e ∈ R := by
      induction he using Submodule.span_induction with
      | mem x hx => exact hx
      | zero => exact ⟨W.zero_mem, fun w _ => by simpa using R.zero_mem⟩
      | add x y _ _ hx hy =>
        exact ⟨W.add_mem hx.1 hy.1, fun w hw => by simpa using R.add_mem (hx.2 w hw) (hy.2 w hw)⟩
      | smul a x _ hx =>
        refine ⟨W.smul_mem (a : Ω) hx.1, fun w hw => ?_⟩
        have : w (a • x) = (a : Ω) * w x := by
          show w ((a : Ω) • x) = _
          rw [map_smul, smul_eq_mul]
        rw [this]
        exact R.mul_mem a.2 (hx.2 w hw)
    refine Submodule.subset_span ⟨?_, fun w hw => ?_⟩
    · have he3 := he'.1
      rw [hW] at he3
      rw [hW']
      refine (Submodule.mem_iInf _).2 fun t => LinearMap.mem_ker.2 ?_
      rw [hf, LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 he3 t), map_zero]
    · rw [hω'] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨w₀, hw₀, rfl⟩ := hw
        rw [hjd]
        exact hR _ (he'.2 w₀ hw₀)
      | zero => simpa using R'.zero_mem
      | add u w _ _ hu hw => simpa using R'.add_mem hu hw
      | smul a w _ hw =>
        show (a : Ω') * _ ∈ R'
        exact R'.mul_mem a.2 hw

end Flat2

theorem eigSp_eq_iInf {Ω V O : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [CommRing O] (ρ : O →+* Module.End Ω V)
    (σ : O →+* Ω) {T : ℕ} (β : Fin T → O) (hβ : Submodule.span ℤ (Set.range β) = ⊤) :
    eigSp ρ σ = ⨅ t, LinearMap.ker (ρ (β t) - σ (β t) • LinearMap.id) := by
  refine le_antisymm (le_iInf fun t => iInf_le _ _) fun e he => ?_
  refine (Submodule.mem_iInf _).2 fun a => LinearMap.mem_ker.2 ?_
  have ha : a ∈ Submodule.span ℤ (Set.range β) := hβ ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 he t)
  | zero => simp
  | add x y _ _ hx hy =>
    have : (ρ (x + y) - σ (x + y) • LinearMap.id : Module.End Ω V) e =
        (ρ x - σ x • LinearMap.id : Module.End Ω V) e + (ρ y - σ y • LinearMap.id : Module.End Ω V) e := by
      simp [add_smul]
      abel
    rw [this, hx, hy, add_zero]
  | smul n x _ hx =>
    have : (ρ (n • x) - σ (n • x) • LinearMap.id : Module.End Ω V) e = n • (ρ x - σ x • LinearMap.id : Module.End Ω V) e := by
      simp [smul_sub, ← Int.cast_smul_eq_zsmul Ω, mul_smul]
    rw [this, hx, smul_zero]

theorem exists_flat_regAt {X Z : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ Z} {h : Z ⟶ X} {i : Ω →+* Ω'} (hg : IsCptGen ξ) (hg' : IsCptGen ξ') [Flat h]
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ h i) (p' : Cpt ξ') (hq : genPt ξ ⤳ h p'.1) :
    ∃ φ : regAt ξ ⟨h p'.1, hq⟩ →+* regAt ξ' p', φ.Flat ∧ ∀ a, (φ a : Ω') = i a := by
  let e := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.regAtEquivStalk hg ⟨h p'.1, hq⟩
  let e' := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.regAtEquivStalk hg' p'
  refine ⟨(e'.toRingHom.comp (h.stalkMap p'.1).hom).comp e.symm.toRingHom, ?_, fun a => ?_⟩
  · exact (RingHom.Flat.of_bijective e.symm.bijective).comp
      ((Flat.stalkMap h p'.1).comp (RingHom.Flat.of_bijective e'.bijective))
  · obtain ⟨s, rfl⟩ := e.surjective a
    have h1 := GlobalTheory.CompanionTheory.Ar.RegAtDom.genMap_stalkMap hd p'.1 p'.2 hq s
    show ((e' ((h.stalkMap p'.1).hom (e.symm (e s))) : regAt ξ' p') : Ω') = i (e s : regAt ξ ⟨h p'.1, hq⟩)
    rw [RingEquiv.symm_apply_apply]
    exact h1

set_option maxHeartbeats 1000000 in

theorem hodgeCpt_pull_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω') ⟶ Z) (h : Z ⟶ A.X), (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (seg y') → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → Smooth h → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li), A'.ξ ≫ e.hom = ξ' ∧ HodgeOver A' A (e.hom ≫ h) i j ∧ A'.R = A.R ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A Z ξ' h hall htie hnorm hdom hsmh
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  haveI := hsmh
  haveI : AlgebraicGeometry.Flat h := inferInstance
  have hgen := A.tie.gen
  have hgen' := htie.gen
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
    infer_instance
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open E H D l Xo c _ _ Y S Ω K J y A hmono
  obtain ⟨x, hx⟩ : ∃ x : Sp Ω ⟶ Xo.XF c, A.ξ ≫ A.f = x ≫ Y.j := by
    refine ⟨spMap A.fn ≫ x₀, ?_⟩
    have hd : A.ξ ≫ A.f = spMap A.fn ≫ A.ξ₀ := A.fn_over
    rw [hd, hx₀, Category.assoc]
  obtain ⟨t', ⟨mh⟩⟩ : ∃ t' : SAB H Z, Nonempty (SABMap t' A.t h) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM Out.proved_CubePullSt h A.t⟩⟩
  obtain ⟨mf, hmf⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m mh
  obtain ⟨Li', acg', mod', ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Z t'.G Ω' ξ'
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act Z t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j (𝓞 E) A.t.act.act t'.act.act A.ρ ρ'
    hdom mh.cart hj A.act hρ' (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li Li' j hext hspan
  have hW : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ Z Ω' ξ' h i hdom
  have hsp : ∀ p' : Cpt ξ', genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt ξ' p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt ξ' p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt ξ'), InFibre ξ' p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian Z Ω' ξ' ℤ _ _ htie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt ξ', IsIntegrallyClosed (Z.presheaf.stalk q.1) := fun q => (hnorm q.1).2
  have htors : ∀ p ∈ S, FullTorsion t'.G ξ' (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt ξ', 0 < D.p + D.q → M'.htOm t'.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt ξ' p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y Z (h ≫ A.f) t' mf Ω' ξ' (spMap i ≫ x) (by
      rw [← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) Z Ω' ξ' s0' o' t' m0' Li' M' (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := GlobalTheory.T.omega_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq ξ' h _ jd p' (hsp p'), h1.2.2]

  have hfl : ∀ p' : Cpt ξ', ∃ φ : regAt A.ξ ⟨h p'.1, hsp p'⟩ →+* regAt ξ' p', φ.Flat ∧ ∀ a, (φ a : Ω') = i a := fun p' =>
    exists_flat_regAt hgen hgen' hdom p' (hsp p')

  have hLi := (GlobalTheory.T.lie_omega_lattice_vector_bundle A.X Ω A.ξ A.t.G A.Li A.M hgen hsm).1
  have hfr : ∀ q : Cpt A.ξ, ∃ b : Fin (Module.finrank Ω A.Li) → A.Li, LinearIndependent Ω b ∧
      Submodule.span Ω (Set.range b) = ⊤ ∧ A.M.lat q = Submodule.span (regAt A.ξ q) (Set.range b) := fun q => by
    obtain ⟨U, hU, b, hb, hf⟩ := hLi q trivial
    obtain ⟨h1, h2⟩ := hf q trivial hU
    exact ⟨b, h1, hb, h2⟩

  let βb := Module.finBasis ℤ (𝓞 E)
  have hβ : Submodule.span ℤ (Set.range fun t => βb t) = ⊤ := βb.span_eq
  let ff : (CMType H ⊕ CMType H) → Fin (Module.finrank ℤ (𝓞 E)) → A.Li →ₗ[Ω] A.Li := fun s t =>
    (A.ρ (βb t) - A.emb s (βb t) • LinearMap.id : Module.End Ω A.Li)
  let ff' : (CMType H ⊕ CMType H) → Fin (Module.finrank ℤ (𝓞 E)) → Li' →ₗ[Ω'] Li' := fun s t =>
    (ρ' (βb t) - ((i.comp A.cst).comp (labelEmb c s)) (βb t) • LinearMap.id : Module.End Ω' Li')
  have hff : ∀ s, A.Vgen s = ⨅ t, LinearMap.ker (ff s t) := fun s => eigSp_eq_iInf A.ρ (A.emb s) _ hβ
  have hff' : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = ⨅ t, LinearMap.ker (ff' s t) := fun s =>
    eigSp_eq_iInf ρ' _ _ hβ
  have hffj : ∀ s t e, ff' s t (j e) = j (ff s t e) := fun s t e => by
    show ρ' (βb t) (j e) - i (A.emb s (βb t)) • j e = j (A.ρ (βb t) e - A.emb s (βb t) • e)
    rw [hρj, map_sub, hext.1]
  have hffL : ∀ s (q : Cpt A.ξ) (b : Fin (Module.finrank Ω A.Li) → A.Li),
      A.M.lat q = Submodule.span (regAt A.ξ q) (Set.range b) → ∀ t k,
      ff s t (b k) ∈ Submodule.span (regAt A.ξ q) (Set.range b) := fun s q b hL t k => by
    have hbk : b k ∈ A.M.lat q := hL ▸ Submodule.subset_span ⟨k, rfl⟩
    have h1 := GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act q (βb t) (b k) hbk
    have h2 : A.emb s (βb t) • b k ∈ A.M.lat q :=
      Submodule.smul_mem (A.M.lat q) (⟨_, hint s q (βb t)⟩ : regAt A.ξ q) hbk
    rw [← hL]
    exact Submodule.sub_mem _ h1 h2

  have hco : ∀ p ∈ S, 0 < D.p + D.q → (A.M.htOm A.t.PP.L (p ^ A.R p)).IsCohOn Set.univ ∧ ∀ q : Cpt A.ξ,
      (∀ u ∈ A.M.omLat q, (p ^ A.R p) • u ∈ A.M.htOm A.t.PP.L (p ^ A.R p) q) := by
    intro p hp hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    haveI : IsNoetherian A.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).2 A.all).1
    have hNc : GlobalTheory.CompanionTheory.Ar.Flat.NormalCpt A.ξ := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen hgen A.normal
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
    have hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p) :=
      (GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p)
        ⟨genPt A.ξ, specializes_rfl⟩ hgen hN (A.tors p hp) (hic _) (noeth_stalk hgen _ (hnoeth _))).2.1 hpos
    obtain ⟨e, he⟩ := exists_genWeil GlobalTheory.firstFiveLaws.1.weil Y A.ξ A.f x A.t A.m hx (p ^ A.R p) hN
      (A.tors p hp) hζ
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hodge_tate_omega_coherent A.X Ω A.ξ hgen hNc A.t.G A.t.semi A.t.PP.L (p ^ A.R p) hN (A.tors p hp) e he A.Li A.M
    exact ⟨h1, fun q => (h2 q).1⟩
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ',
      M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt ξ' p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p'
    by_cases hpq : 0 < D.p + D.q
    · obtain ⟨φ, hφ, hφi⟩ := hfl p'
      obtain ⟨b, hb, hbs, hL⟩ := hfr ⟨h p'.1, hsp p'⟩
      obtain ⟨hcoh, hbet⟩ := hco p hp hpq
      obtain ⟨U, hU, m, g, hg⟩ := hcoh ⟨h p'.1, hsp p'⟩ trivial
      have hgq := hg ⟨h p'.1, hsp p'⟩ trivial hU
      have hN : ((p ^ A.R p : ℕ) : Ω) ≠ 0 :=
        Nat.cast_ne_zero.2 (pow_pos (A.S_prime p hp).pos _).ne'
      refine flat_dual hφ hφi hext hspan jd hjd hb hbs (ff s) (ff' s) (hffj s) (hffL s _ b hL) _ _ (hff s) (hff' s) _ _ g hgq
        (hω p hp p' hpq) (fun a l => ?_) (p ^ A.R p) hN fun u hu => ?_
      · have h1 : g a ∈ A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ := hgq ▸ Submodule.subset_span ⟨a, rfl⟩
        have h2 : b l ∈ A.M.lat ⟨h p'.1, hsp p'⟩ := hL ▸ Submodule.subset_span ⟨l, rfl⟩
        exact (A.M.htOm_le _ _ _ h1) _ h2
      · have h1 : u ∈ A.M.omLat ⟨h p'.1, hsp p'⟩ := fun e he => by
          rw [hL] at he
          induction he using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨l, rfl⟩ := hx
            exact hu l
          | zero => simpa using (regAt _ _).zero_mem
          | add x y _ _ hx hy => simpa using (regAt _ _).add_mem hx hy
          | smul a x _ hx =>
            have : u (a • x) = (a : Ω) * u x := by
              show u ((a : Ω) • x) = _
              rw [map_smul, smul_eq_mul]
            rw [this]
            exact (regAt _ _).mul_mem a.2 hx
        have h2 := hbet ⟨h p'.1, hsp p'⟩ u h1
        rwa [← Nat.cast_smul_eq_nsmul Ω] at h2
    · have hr : labelRk D s = 0 := by
        rcases s with τ | τ
        · show D.p = 0
          omega
        · show D.q = 0
          omega
      have hbot : A.Vgen s = ⊥ := by
        obtain ⟨U, hU, b, hb, -⟩ := A.vb s ⟨h p'.1, hsp p'⟩ trivial
        haveI : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
        rw [Set.range_eq_empty, Submodule.span_empty] at hb
        exact hb.symm
      have hbot' : eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = ⊥ := by
        rw [hW s, hbot]
        simp
      apply le_antisymm
      · intro e he
        have h1 := LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he
        rw [hbot', Submodule.mem_bot] at h1
        rw [h1]
        exact Submodule.zero_mem _
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨e, he, rfl⟩
        have h1 := LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he
        have h2 : e ∈ A.Vgen s := h1
        rw [hbot, Submodule.mem_bot] at h2
        rw [h2, map_zero]
        exact Submodule.zero_mem _
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ',
      M'.htW t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt ξ' p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p'
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p')
  have hV : ∀ s, Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull ξ' h j := by
    intro s
    funext p'
    rw [pull_eq ξ' h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre ξ' p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p'
      · exact hdual p hp _ p'
    · have hc' : ∀ p ∈ S, ¬ InFibre ξ' p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      show M'.lat p' ⊓ _ = _
      rw [hlat, pull_eq ξ' h _ j p' (hsp p')]
      obtain ⟨φ, hφ, hφi⟩ := hfl p'
      obtain ⟨b, hb, -, hL⟩ := hfr ⟨h p'.1, hsp p'⟩
      exact flat_lat hφ hφi hext hb (ff s) (ff' s) (hffj s) (hffL s _ b hL) _ _ (hff s) (hff' s) _ hL
  have hvb' : ∀ s, (Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s)).IsVB (labelRk D s)
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))) := by
    intro s
    rw [hV s, hW s]
    have h3 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ A.Li Z Ω' ξ' h i Li' j (A.V s) Set.univ (labelRk D s) (A.Vgen s) hdom hext.1 hext.2
      (A.vb s)
    intro p' _
    obtain ⟨U, hU, b, hb, hfr⟩ := h3 p' ⟨hsp p', trivial⟩
    exact ⟨U, hU, b, hb, fun q _ hq => hfr q ⟨hsp q, trivial⟩ hq⟩
  refine ⟨{ X := Z, ξ := ξ', all := hall, tie := htie, normal := hnorm, f := h ≫ A.f, Ω₀ := A.Ω₀, ξ₀ := A.ξ₀,
            gen₀ := A.gen₀, cst := i.comp A.cst, cst_over := ?_, fn := i.comp A.fn, fn_over := ?_, t := t', m := mf,
            Li := Li', M := M', ρ := ρ', act := hρ', S_prime := A.S_prime, R := A.R, R_ge := A.R_ge, tors := htors,
            vb := hvb' }, Iso.refl Z, j, ?_, ⟨?_, ?_, rfl, hext, ?_⟩, rfl, hspan, ?_⟩
  · have e : ξ' ≫ h = spMap i ≫ A.ξ := hdom
    have e2 : ξ' ≫ h ≫ A.f ≫ Y.s = spMap i ≫ A.ξ ≫ A.f ≫ Y.s := by
      rw [← Category.assoc, e, Category.assoc]
    simp only [Category.assoc]
    rw [e2, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← Category.assoc, hdom, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp
  · have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    show GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ ((Iso.refl Z).hom ≫ h) i
    rw [e]
    exact hdom
  · show h ≫ A.f = ((Iso.refl Z).hom ≫ h) ≫ A.f
    simp
  · intro w
    show (M'.pt (j w)).left ≫ mf.φ = _
    rw [hmf, ← Category.assoc, hj w, Category.assoc]
  · intro s
    have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    refine (hV s).trans ?_
    exact congrArg (fun g => (A.V s).pull ξ' g j) e.symm

end GlobalTheory.CompanionTheory.Ar.HcptFlat
