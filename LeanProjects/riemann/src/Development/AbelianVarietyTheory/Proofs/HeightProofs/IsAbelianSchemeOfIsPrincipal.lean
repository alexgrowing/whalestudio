import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFibres
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

theorem comb_transfer {S : Scheme.{0}} {G : Over S} {A A' : Over (Sp R)} [GrpObj G] [GrpObj A] [GrpObj A']
    {f : Sp R ⟶ S} {φ : A.left ⟶ G.left} {φ' : A'.left ⟶ G.left} (h : IsGrpPullback A G f φ)
    (h' : IsGrpPullback A' G f φ') {n : ℕ} {v : Fin n → (epsR R ⟶ A)} {v' : Fin n → (epsR R ⟶ A')}
    (e : ∀ i, (v' i).left ≫ φ' = (v i).left ≫ φ) {c : Fin n → R} {w : epsR R ⟶ A} (hw : IsLieComb c v w) :
    ∃ w', IsLieComb c v' w' ∧ w'.left ≫ φ' = w.left ≫ φ := by
  obtain ⟨i, hi, hφ⟩ := grpPullback_iso h h'
  have : v' = fun j => v j ≫ i.hom := funext fun j => Over.OverMorphism.ext
    (h'.1.hom_ext (by rw [e, Over.comp_left, Category.assoc, hφ]) ((Over.w _).trans (Over.w _).symm))
  subst this
  exact ⟨w ≫ i.hom, DiffCoord.isLieComb_comp_hom i.hom hw, by rw [Over.comp_left, Category.assoc, hφ]⟩

theorem isLieBasis_iso {A A' : Over (Sp R)} [GrpObj A] [GrpObj A'] (i : A ≅ A') [IsMonHom i.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ A)} (hv : IsLieBasis v) : IsLieBasis fun j => v j ≫ i.hom := by
  refine ⟨fun j => DiffCoord.isTangent_comp_hom _ (hv.1 j), fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hv.2 _ (DiffCoord.isTangent_comp_hom i.inv hw)
  refine ⟨c, by simpa using DiffCoord.isLieComb_comp_hom i.hom hc, fun c' hc' => hu c' ?_⟩
  simpa using DiffCoord.isLieComb_comp_hom i.inv hc'

theorem card_le_of_isLieBasis {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {n m : ℕ}
    {v : Fin n → (epsR k ⟶ A)} {v' : Fin m → (epsR k ⟶ A)} (hv : IsLieBasis v) (hv' : IsLieBasis v') : n ≤ m := by
  obtain ⟨M, hM⟩ := DiffCoord.exists_linearMap (𝟙 A) hv hv'
  have a := LieComb.lieComb_algebra k A n v hv.1
  have a' := LieComb.lieComb_algebra k A m v' hv'.1
  have hi : Function.Injective M := fun c c' e => by
    obtain ⟨w, hw⟩ := (a.1 c).exists
    obtain ⟨w', hw'⟩ := (a.1 c').exists
    have h₁ := hM c w hw
    have h₂ := hM c' w' hw'
    rw [Category.comp_id] at h₁ h₂
    obtain rfl : w = w' := (a'.1 (M c')).unique (e ▸ h₁) h₂
    exact (hv.2 w (a.2.1 c w hw)).unique hw hw'
  simpa using LinearMap.finrank_le_finrank_of_injective hi

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

theorem isVec_unique {c : Fin G.g → K} {x x' : Sp (DualNumber K) ⟶ t.G.left} (h : G.IsVec c x) (h' : G.IsVec c x') :
    x = x' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  rw [((LieComb.lieComb_algebra K _ _ G.v G.basis.1).1 c).unique hw hw']

theorem coord_unique {c c' : Fin G.g → K} {x : Sp (DualNumber K) ⟶ t.G.left} (h : G.IsVec c x) (h' : G.IsVec c' x) :
    c = c' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', e⟩ := h'
  obtain rfl : w = w' := Over.OverMorphism.ext (G.m.cart.1.hom_ext e ((Over.w _).trans (Over.w _).symm))
  exact (G.basis.2 w ((LieComb.lieComb_algebra K _ _ G.v G.basis.1).2.1 c w hw)).unique hw hw'

theorem isVec_smul (a : K) {c : Fin G.g → K} {x : Sp (DualNumber K) ⟶ t.G.left} (h : G.IsVec c x) :
    G.IsVec (a • c) (spMap (epsScaleR a) ≫ x) := by
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨IntCoord.sc a ≫ w, ?_, (Category.assoc _ _ _).symm⟩
  have := (LieComb.lieComb_algebra K _ _ G.v G.basis.1).2.2.1 1 ![c] ![w] ![a] _
    (fun i => by fin_cases i; exact hw) ((IntCoord.isLieComb_one_iff a w _).2 rfl)
  simpa using this

theorem exists_isDiff_act (a : 𝓞 E) : ∃ r, G.IsDiff G (t.act.act a) r := by
  have := G.tK.act.hom a
  obtain ⟨r, hr⟩ := DiffCoord.exists_linearMap (G.tK.act.act a) G.basis G.basis
  refine ⟨r, ?_⟩
  rintro c _ ⟨w, hw, rfl⟩
  exact ⟨_, hr c w hw, by rw [Over.comp_left, Category.assoc, Category.assoc]; exact congrArg _ (G.m.act a).symm⟩

theorem mem_eigenSp_iff (τ : E →+* K) (c : Fin G.g → K) : c ∈ G.eigenSp τ ↔ G.IsEigenVec τ c := by
  choose r hr using exists_isDiff_act G
  have key : ∀ c, G.IsEigenVec τ c ↔ ∀ a, r a c = τ (a : E) • c := fun c => by
    refine forall_congr' fun a => ⟨fun h => ?_, fun h x hx => h ▸ hr a c x hx⟩
    obtain ⟨x, hx⟩ := G.exists_isVec c
    exact coord_unique G (hr a c x hx) (h x hx)
  refine ⟨fun h => (key c).2 fun a => ?_, fun h => Submodule.subset_span h⟩
  refine Submodule.span_induction (p := fun c _ => r a c = τ (a : E) • c) (fun c hc => (key c).1 hc a) (by simp)
    (fun x y _ _ hx hy => by rw [map_add, hx, hy, smul_add]) (fun b x _ hx => by rw [map_smul, hx, smul_comm]) h

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

abbrev Partner.fib {F : GenFib T.pol} (Q : Partner F) : EigenLatticeFibres.GenFib T.t := ⟨Q.tK, Q.m, F.P₀.g, Q.v, Q.basis⟩

theorem nonempty_partner (F : GenFib T.pol) : Nonempty (Partner F) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap (𝓞 K) K)) T.t
  obtain ⟨i, hi, e⟩ := grpPullback_iso F.fib.2.1 m.cart
  exact ⟨⟨_, m, fun j => F.v j ≫ i.hom, isLieBasis_iso i F.basis, fun j => by
    rw [Over.comp_left, Category.assoc]; exact congrArg _ e⟩⟩

theorem exists_partner (G : EigenLatticeFibres.GenFib T.t) : ∃ (F : GenFib T.pol) (Q : Partner F), Q.fib = G := by
  obtain ⟨⟨T', e, hg⟩, w⟩ := PAT.exists_of_sabMap E H _ _ _ T G.tK G.m
  obtain ⟨t, ab, g, dim, sym, ample, ktriv⟩ := T'
  dsimp only at e hg
  subst e
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ dim
  obtain rfl : g = G.g := le_antisymm (card_le_of_isLieBasis hv G.basis) (card_le_of_isLieBasis G.basis hv)
  exact ⟨⟨(⟨G.tK, ab, G.g, dim, sym, ample, ktriv⟩ : PAT H (Sp K)).pol, G.m.φ, ⟨hg, G.m.cart, w⟩, G.v, G.basis⟩,
    ⟨G.tK, G.m, G.v, G.basis, fun _ => rfl⟩, rfl⟩

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

theorem isVec_iff (c : Fin F.P₀.g → K) (x : Sp (DualNumber K) ⟶ T.t.G.left) :
    Q.fib.IsVec c x ↔ ∃ w, IsLieComb c F.v w ∧ x = w.left ≫ F.φ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w', h, e⟩ := comb_transfer Q.m.cart F.fib.2.1 (fun i => (Q.same i).symm) hw
    exact ⟨w', h, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w', h, e⟩ := comb_transfer F.fib.2.1 Q.m.cart Q.same hw
    exact ⟨w', h, e.symm⟩

theorem isCoord_iff (u : epsR (𝓞 K) ⟶ T.t.G) (c : Fin F.P₀.g → K) :
    F.IsCoord u c ↔ IsTangent u ∧ Q.fib.IsVec c (spMap (Chart.dualMapR (algebraMap (𝓞 K) K)) ≫ u.left) := by
  rw [Q.isVec_iff]
  exact and_congr_right fun _ => exists_congr fun w => ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩

theorem isCoord_of_isVec {u : epsR (𝓞 K) ⟶ T.t.G} {c : Fin F.P₀.g → K}
    (h : Q.fib.IsVec c (spMap (Chart.dualMapR (algebraMap (𝓞 K) K)) ≫ u.left)) : F.IsCoord u c := by
  obtain ⟨w, hw, e⟩ := (Q.isVec_iff _ _).1 h
  have := F.P₀.isAb.comm
  have : IsSeparated T.pol.A.hom := T.t.semi.separated
  exact ⟨LieGlue.isTangent_of_isVecOver RingOfIntegers.coe_injective F.fib.2.1 e.symm
    ((LieComb.lieComb_algebra K _ _ F.v F.basis.1).2.1 c w hw), w, e.symm, hw⟩

theorem lieLat_eq : F.lieLat = Q.fib.lieLat :=
  congrArg (Submodule.span (𝓞 K)) (Set.ext fun c => exists_congr fun u => Q.isCoord_iff u c)

theorem exists_smul_isCoord (F : GenFib T.pol) (c : Fin F.P₀.g → K) :
    ∃ n : 𝓞 K, n ≠ 0 ∧ ∃ u, F.IsCoord u ((n : K) • c) := by
  have hc : c ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) :=
    (LieLattice.lieLat_fg_and_span_eq_top K _ F).2 ▸ Submodule.mem_top
  have hl := (integral_tangent_coordinates K _ F).2.2.2.2.1
  suffices h : ∃ n : 𝓞 K, n ≠ 0 ∧ n • c ∈ F.lieLat from h.imp fun n hn => ⟨hn.1, (hl _).1 hn.2⟩
  refine Submodule.span_induction (p := fun c _ => ∃ n : 𝓞 K, n ≠ 0 ∧ n • c ∈ F.lieLat)
    (fun c hc => ⟨1, one_ne_zero, by rwa [one_smul]⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_ hc
  · rintro x y - - ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine F.lieLat.add_mem ?_ ?_
    · rw [_root_.mul_comm, mul_smul]; exact F.lieLat.smul_mem _ hx
    · rw [mul_smul]; exact F.lieLat.smul_mem _ hy
  · rintro a x - ⟨n, hn, hx⟩
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hs' := nonZeroDivisors.ne_zero hs
    refine ⟨n * s, mul_ne_zero hn hs', ?_⟩
    have hs'' : algebraMap (𝓞 K) K s ≠ 0 := fun h => hs' (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
    have : (n * s) • (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • x = r • n • x := by
      rw [← algebraMap_smul K (n * s), ← algebraMap_smul K r, ← algebraMap_smul K n, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact F.lieLat.smul_mem _ hx

theorem isDiffOf_iff (f : T.t.G ⟶ T'.t.G) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) :
    F.IsDiffOf F' f M ↔ Q.fib.IsDiff Q'.fib f M := by
  refine ⟨fun h c x hx => ?_, fun h u c hu => Q'.isCoord_of_isVec ?_⟩
  · obtain ⟨n, hn, u, hu⟩ := exists_smul_isCoord F c
    have hn' : (n : K) ≠ 0 := fun h => hn (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
    have h₁ := isVec_smul Q.fib (n : K)⁻¹ ((Q.isCoord_iff _ _).1 hu).2
    have h₂ := isVec_smul Q'.fib (n : K)⁻¹ ((Q'.isCoord_iff _ _).1 (h u _ hu)).2
    rw [inv_smul_smul₀ hn'] at h₁
    rw [map_smul, inv_smul_smul₀ hn'] at h₂
    rw [isVec_unique Q.fib hx h₁]
    simpa using h₂
  · simpa using h c _ ((Q.isCoord_iff u c).1 hu).2

theorem eigLat_eq (τ : 𝓞 E →+* 𝓞 K) (τ' : E →+* K) (hτ : ∀ a : 𝓞 E, τ' (a : E) = (τ a : K)) :
    F.eigLat T.t.act τ = Q.fib.eigenLat τ' := by
  obtain ⟨-, h₂, -, h₄, h₅, h₆⟩ := integral_tangent_coordinates K _ F
  ext c
  rw [h₆, EigenLatticeFibres.GenFib.eigenLat, Submodule.mem_inf, ← Q.lieLat_eq, h₅, Submodule.restrictScalars_mem,
    mem_eigenSp_iff]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨⟨u, hu⟩, fun a x hx => ?_⟩
    have := ((Q.isCoord_iff _ _).1 (h₄ _ _ _ _ hu (he a))).2
    rw [isVec_unique Q.fib hx ((Q.isCoord_iff _ _).1 hu).2, hτ, Category.assoc]
    exact this
  · rintro ⟨⟨u, hu⟩, he⟩
    refine ⟨u, hu, fun a => ?_⟩
    have h := he a _ ((Q.isCoord_iff _ _).1 hu).2
    rw [hτ, Category.assoc] at h
    have h' := (IntCoord.isLieComb_one_iff (τ a) u _).2 rfl
    rw [h₂ _ _ _ (Q.isCoord_of_isVec (u := u ≫ T.t.act.act a) h) (h₄ _ _ _ _ hu h')]
    exact h'

end Partner

section Metric

theorem exists_cxFib {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t) (s : K →+* ℂ) {A : Over (Sp ℂ)} [GrpObj A]
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ G.tK.G.left} (hφ : IsGrpPullback A G.tK.G (spMap s) φ)
    (w : LBIso L (G.tK.PP.L.pull φ)) {g : ℕ} (hg : g = G.g) (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} (hu : u.IsAH Hm χ) {v' : Fin G.g → (epsR ℂ ⟶ A)} {W : Fin G.g → Fin g → ℂ}
    (hv : ∀ i, IsVecOver s φ (G.v i) (v' i) ∧ u.IsDiff (W i) (v' i)) :
    ∃ C : G.CxFib s, ∀ x y, C.piH x y = Real.pi * hermForm Hm (∑ i, s (x i) • W i) (∑ i, s (y i) • W i) := by
  subst hg
  obtain ⟨w, hw⟩ := w
  have hM := pull_isLB G.tK.PP.isLB φ
  exact ⟨⟨A, φ, hφ, TorsionTauCompare.transport hL hM hw u, Hm, χ, TorsionTauCompare.isAH_transport hL hM hw u hu,
    v', fun i => (hv i).1, W, fun i => (hv i).2⟩, fun _ _ => rfl⟩

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

theorem Partner.lbIso {Z : Scheme.{0}} {a : Z ⟶ F.P₀.A.left} {b : Z ⟶ Q.tK.G.left} (e : a ≫ F.φ = b ≫ Q.m.φ) :
    LBIso (F.P₀.L.pull a) (Q.tK.PP.L.pull b) := by
  have h₁ := EllComp.lbIso_pull_comp F.fib.2.2 a
  have h₂ := EllComp.lbIso_pull_comp (PAT.exists_of_sabMap E H _ _ _ T Q.tK Q.m).2 b
  rw [e] at h₁
  exact LBIso.trans (pull_isLB F.P₀.isLB _) (pull_isLB T.t.PP.isLB _) (pull_isLB Q.tK.PP.isLB _) h₁.symm h₂

theorem Partner.isHerm_iff (h : HermFam K (Fin F.P₀.g → K)) : F.IsHerm h ↔ Q.fib.IsPiH h := by
  obtain ⟨i, hi, e⟩ := grpPullback_iso F.fib.2.1 Q.m.cart
  have hv : ∀ j, Q.v j = F.v j ≫ i.hom := fun j => Over.OverMorphism.ext
    (Q.m.cart.1.hom_ext ((Q.same j).trans (by rw [Over.comp_left, Category.assoc]; exact congrArg _ e.symm))
      ((Over.w _).trans (Over.w _).symm))
  refine forall_congr' fun s => ⟨?_, ?_⟩
  · rintro ⟨P, ψ, v', u, Hm, χ, W, hψ, hu, hW, hh⟩
    obtain ⟨C, hC⟩ := exists_cxFib Q.fib s P.isLB (φ := ψ ≫ i.hom.left)
      ((hψ.2.1.comp (isGrpPullback_of_iso i)).congr (Category.comp_id _) rfl)
      (LBIso.trans P.isLB (pull_isLB F.P₀.isLB _) (pull_isLB Q.tK.PP.isLB _) hψ.2.2.symm
        (Q.lbIso (by rw [Category.assoc]; exact congrArg _ e.symm))) hψ.1 u hu (v' := v') (W := W)
      fun j => ⟨by
        have := (hW j).1
        unfold IsVecOver at this ⊢
        rw [← Category.assoc, this, Category.assoc]
        exact congrArg _ (congrArg (·.left) (hv j)).symm, (hW j).2⟩
    exact ⟨C, fun x y => by rw [hC, HermHom.form_eq h s Hm W _ hh]⟩
  · rintro ⟨C, hC⟩
    have : IsMonHom i.symm.hom := inferInstanceAs (IsMonHom i.inv)
    have hp : IsGrpPullback C.A F.P₀.A (spMap s) (C.φ ≫ i.inv.left) :=
      (C.cart.comp (isGrpPullback_of_iso i.symm)).congr (Category.comp_id _) rfl
    have := F.P₀.isAb.comm
    have := PolPull.isCommMonObj_of_isGrpPullback hp
    have e' : i.inv.left ≫ F.φ = Q.m.φ := by
      rw [← e, ← Category.assoc, ← Over.comp_left, i.inv_hom_id]; exact Category.id_comp _
    obtain ⟨w, hw⟩ := (Q.lbIso (a := C.φ ≫ i.inv.left) (b := C.φ) (by rw [Category.assoc, e'])).symm
    have hL := pull_isLB Q.tK.PP.isLB C.φ
    have hM := pull_isLB F.P₀.isLB (C.φ ≫ i.inv.left)
    refine ⟨TorsionTauCompare.polOfPullback F.P₀ C.A hp, C.φ ≫ i.inv.left, C.vC,
      TorsionTauCompare.transport hL hM hw C.u, C.Hm, C.χ, C.W, ⟨rfl, hp, PolBaseChange.lbIso_refl hM⟩,
      TorsionTauCompare.isAH_transport hL hM hw C.u C.ah, fun j => ⟨?_, C.diff j⟩, fun j k => ?_⟩
    · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ i.inv.left) (C.vC_base j)).trans
        ((Category.assoc _ _ _).trans (congrArg _ ?_)))
      change (Q.v j ≫ i.inv).left = _
      rw [hv, Category.assoc, i.hom_inv_id, Category.comp_id]
    · have hs : ∀ j, C.vec (Pi.single j 1) = C.W j := fun j => by
        simp [EigenLatticeFibres.GenFib.CxFib.vec, Pi.single_apply, apply_ite s]
      rw [hC, EigenLatticeFibres.GenFib.CxFib.piH, hs, hs]
      rfl

end Metric

section Embeddings

theorem injective_of_charZero {k : Type} [CommRing k] [CharZero k] (β : 𝓞 K →+* k) : Function.Injective β := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
  simpa [RingHom.mem_ker] using hn

theorem mapRingHom_bijective (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] :
    Function.Bijective (RingOfIntegers.mapRingHom : (E →+* K) → (𝓞 E →+* 𝓞 K)) := by
  refine ⟨fun f g e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_), fun τ => ?_⟩
  · exact congrArg (fun x : 𝓞 E →+* 𝓞 K => (x a : K)) e
  · have hi := injective_of_charZero ((algebraMap (𝓞 K) K).comp τ)
    exact ⟨IsFractionRing.lift hi, RingHom.ext fun a => Subtype.ext (IsFractionRing.lift_algebraMap hi a)⟩

theorem splits_iff (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] :
    Splits E K ↔ EigenLatticeFibres.SplitsE E K := by
  rw [Splits, EigenLatticeFibres.SplitsE, Nat.card_eq_of_bijective _ (mapRingHom_bijective E K)]

theorem hasSig_iff {G : Over (Sp (𝓞 K))} [GrpObj G] (act : OAct (𝓞 E) G) (ρ : 𝓞 K) (p q : ℕ) :
    CMCurveHermitianForms.HasSig H p q act ρ ↔ ρ ^ 2 = -(H.d : 𝓞 K) ∧ HasType H act ρ p q :=
  and_congr_right fun _ => ⟨fun h k _ _ β hβ =>
    have : CharZero k := charZero_of_injective_ringHom hβ
    h k β, fun h k _ _ _ β => h k β (injective_of_charZero β)⟩

end Embeddings

section Isogeny

theorem isFinFlatSurj_of_onto (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A) (hg : P.g = P'.g)
    [hΦ : IsMonHom Φ] (h : ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A,
      ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) : EigenLatticeFibres.IsFinFlatSurj Φ := by
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hs := (OntoSurj.surjective_of_onto_complex_points _ _ (injective_of_charZero _) _ _ Φ P'.isAb P.isAb h).1
  obtain ⟨N, ψ, hN, -, h₁, -⟩ := LamF.exists_inverse_isogeny_ringOfIntegers thetaUnifAV_all hL
    homExtension_semiAbelian_dvr_unconditional K σ P P' Φ hg hΦ h
  have := P.isAb.proper
  have := P'.isAb.proper
  have := P.isAb.smooth
  have := P.isAb.comm
  have : IsSeparated ψ.left := by
    have : IsSeparated (ψ.left ≫ P.A.hom) := by rw [Over.w]; infer_instance
    exact IsSeparated.of_comp ψ.left P.A.hom
  have hf : IsFinite Φ.left := by
    have : IsFinite (Φ.left ≫ ψ.left) := by
      rw [← Over.comp_left, h₁]
      exact (hL.mulN _ P N hN).1
    exact IsFinite.of_comp Φ.left ψ.left
  refine ⟨hf, flat_of_isFinite_of_flat_geometric_fibres _ _ _ Φ inferInstance inferInstance hf fun k _ _ t => ?_, hs⟩
  refine (isogeny_of_surjective_of_dim_eq hL k
    (TorsionTauCompare.polOfPullback P _ (isGrpPullback_pullback P.A t)) _ ((Over.pullback t).map Φ)
    (PolPull.isAbelianScheme_of_isGrpPullback P'.isAb (isGrpPullback_pullback P'.A t)) ?_
    (inferInstanceAs (IsMonHom ((Over.pullback t).map Φ)))
    (MorphismProperty.of_isPullback (P := @Surjective) (AbLaw.MulN.isPullback_baseChange t Φ) hs)).2.1
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_pullback P'.A t).1
    (hg ▸ P'.smoothDim)

theorem comp_sumMap {S : Scheme.{0}} {A A' B Z : Over S} [GrpObj B] [IsCommMonObj B] {p q : ℕ} (f : Fin p → (A ⟶ B))
    (f' : Fin q → (A' ⟶ B)) (x : Z ⟶ (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A')) :
    x ≫ EigenLatticeFibres.sumMap f f' = (∏ i, (x ≫ fst _ _ ≫ Pi.π _ i) ≫ f i) * ∏ j, (x ≫ snd _ _ ≫ Pi.π _ j) ≫ f' j := by
  simp only [EigenLatticeFibres.sumMap, EigenLatticeFibres.sumPow, List.prod_ofFn, MonObj.comp_mul, LamF.IsogSum.comp_prod, Category.assoc]

theorem isFinFlatSurj_sumMap_iff (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) [IsCommMonObj B.A] {p q : ℕ}
    (f : Fin p → (A.A ⟶ B.A)) (f' : Fin q → (A'.A ⟶ B.A)) (hf : ∀ i, IsMonHom (f i)) (hf' : ∀ i, IsMonHom (f' i))
    (hg : B.g = p * A.g + q * A'.g) :
    EigenLatticeFibres.IsFinFlatSurj (EigenLatticeFibres.sumMap f f') ↔ ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A,
      ∃ (x : Fin p → (_ ⟶ A.A)) (x' : Fin q → (_ ⟶ A'.A)), y = (∏ i, x i ≫ f i) * ∏ j, x' j ≫ f' j := by
  constructor
  · rintro ⟨h₁, -, h₃⟩ y
    obtain ⟨z, hz⟩ := GeomSurj.exists_lift_of_surjective (EigenLatticeFibres.sumMap f f').left y.left
    let x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (∏ᶜ fun _ : Fin p => A.A) ⊗ (∏ᶜ fun _ : Fin q => A'.A) :=
      Over.homMk z (by rw [← Over.w (EigenLatticeFibres.sumMap f f'), ← Category.assoc, ← hz]; exact Over.w y)
    exact ⟨_, _, (Over.OverMorphism.ext hz : y = x ≫ _).trans (comp_sumMap f f' x)⟩
  · intro hs
    obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A p
    obtain ⟨P', pP', hP'⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A' q
    obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g GlobalTheory.T.abelianScheme_laws_unconditional.1 (𝓞 K) P P'
    have := pP.hom
    have := pP'.hom
    have := Q.isAb.comm
    have := A.isAb.comm
    have := A'.isAb.comm
    let a := pP.lim.conePointUniqueUpToIso (productIsProduct fun _ : Fin p => A.A)
    let b := pP'.lim.conePointUniqueUpToIso (productIsProduct fun _ : Fin q => A'.A)
    have ha : ∀ i, a.hom ≫ Pi.π _ i = pP.pr i := fun i =>
      pP.lim.conePointUniqueUpToIso_hom_comp (productIsProduct fun _ : Fin p => A.A) ⟨i⟩
    have hb : ∀ i, b.hom ≫ Pi.π _ i = pP'.pr i := fun i =>
      pP'.lim.conePointUniqueUpToIso_hom_comp (productIsProduct fun _ : Fin q => A'.A) ⟨i⟩
    let e : Q.A ≅ (∏ᶜ fun _ : Fin p => A.A) ⊗ (∏ᶜ fun _ : Fin q => A'.A) := asIso (lift u v) ≪≫ (a ⊗ᵢ b)
    have e₁ : e.hom ≫ fst _ _ = u ≫ a.hom := by simp [e]
    have e₂ : e.hom ≫ snd _ _ = v ≫ b.hom := by simp [e]
    have hΦ : ∀ {Z : Over (Sp (𝓞 K))} (x : Z ⟶ Q.A), x ≫ e.hom ≫ EigenLatticeFibres.sumMap f f' =
        (∏ i, (x ≫ u ≫ pP.pr i) ≫ f i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ f' i := fun x => by
      rw [← Category.assoc, comp_sumMap]
      simp only [Category.assoc, reassoc_of% e₁, reassoc_of% e₂, ← ha, ← hb]
    have hm : IsMonHom (e.hom ≫ EigenLatticeFibres.sumMap f f') := LamF.IsogSum.isMonHom_of_points _ fun Z x y => by
      simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
      exact mul_mul_mul_comm _ _ _ _
    obtain ⟨h₁, h₂, h₃⟩ := isFinFlatSurj_of_onto σ Q B (e.hom ≫ EigenLatticeFibres.sumMap f f') (by rw [hQ, hP, hP', hg])
      fun y => by
        obtain ⟨x, x', hx⟩ := hs y
        obtain ⟨z, hz, hz'⟩ := LamF.IsogSum.exists_point pP pP' u v x x'
        exact ⟨z, by rw [hΦ, hx]; simp only [hz, hz']⟩
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    have he : (EigenLatticeFibres.sumMap f f').left = e.inv.left ≫ (e.hom ≫ EigenLatticeFibres.sumMap f f').left := by
      rw [← Over.comp_left, e.inv_hom_id_assoc]
    unfold EigenLatticeFibres.IsFinFlatSurj
    rw [he]
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end Isogeny

section Object

theorem polId_iff (σ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f) (h : 𝓞 E) :
    EigenLatticeFibres.PolId f h ↔ WeilEq B.t.PP.L f f A.t.PP.L (A.t.act.act h) (𝟙 _) (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  refine ⟨fun w n x y c hn hx hy => w n hn _ x y hx hy (unitOn c), fun w k hk Z x y hx hy c => ?_⟩
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have h₁ : IsMonHom (𝟙 A.pol.A) := inferInstance
  exact PairingScheme.weilIs_iff_of_lamEq hL (𝓞 K) A.pol A.pol B.pol A.pol _ _ _ _ hf hf (A.t.act.hom h) h₁
    ((PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol _ _ _ _ hf hf (A.t.act.hom h) h₁ ℂ
      (σ.comp (algebraMap (𝓞 K) K))).2 inferInstance (injective_of_charZero _) w) Z k x y c hk hx hy

theorem isLinHom_iff {S : Scheme.{0}} {t t' : SAB H S} (f : t.G ⟶ t'.G) :
    EigenLatticeFibres.IsLinHom f ↔ Serre.IsLinearHom t.act t'.act f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isPrincipal {S : Scheme.{0}} (T : PAT H S) : CMCurveHermitianForms.IsPrincipal T.t := ⟨T.ab.proper, T.ample, T.ktriv⟩

theorem isAbelianScheme_of_isPrincipal {S : Scheme.{0}} {t : SAB H S} (h : CMCurveHermitianForms.IsPrincipal t) :
    IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩

theorem exists_dim {t : SAB H (Sp (𝓞 K))} (h : CMCurveHermitianForms.IsPrincipal t) : ∃ g, SmoothOfRelativeDimension g t.G.hom :=
  have : ConnectedSpace (Sp (𝓞 K)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum (𝓞 K)))
  AbelianDim.exists_relDim_of_connected t.G (isAbelianScheme_of_isPrincipal h)

def patOf (t : SAB H (Sp (𝓞 K))) (h : CMCurveHermitianForms.IsPrincipal t) : PAT H (Sp (𝓞 K)) where
  t := t
  ab := isAbelianScheme_of_isPrincipal h
  g := (exists_dim h).choose
  dim := (exists_dim h).choose_spec
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := h.ample
  ktriv := h.ktriv

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

theorem prod_ofFn_sum {M : Type} [CommMonoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod = (∏ i, f (Sum.inl i)) * ∏ j, f (Sum.inr j) := by
  rw [List.prod_ofFn, Equiv.prod_comp finSumFinEquiv.symm f, Fintype.prod_sum_type]

theorem isog_iff {ρ : 𝓞 K} {p q : ℕ} (σ : K →+* ℂ) (hs : Splits E K) (hρ : ρ ^ 2 = -(H.d : 𝓞 K))
    (A : Bool → PAT H (Sp (𝓞 K))) (B : PAT H (Sp (𝓞 K))) (h₁ : HasType H (A true).t.act ρ 1 0)
    (h₂ : HasType H (A false).t.act ρ 0 1) (h₃ : HasType H B.t.act ρ p q)
    (φ : ∀ j : Fin p ⊕ Fin q, (A j.isLeft).t.G ⟶ B.t.G) (hφ : ∀ j, IsMonHom (φ j)) :
    EigenLatticeFibres.IsFinFlatSurj (EigenLatticeFibres.sumMap (A := (A true).t.G) (A' := (A false).t.G) (fun i => φ (Sum.inl i))
      fun j => φ (Sum.inr j)) ↔
    ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.t.G,
      ∃ x : ∀ j : Fin p ⊕ Fin q, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (A j.isLeft).t.G,
        y = (List.ofFn fun i : Fin (p + q) => x (finSumFinEquiv.symm i) ≫ φ (finSumFinEquiv.symm i)).prod := by
  refine (isFinFlatSurj_sumMap_iff σ (A true).pol (A false).pol B.pol _ _ (fun i => hφ (Sum.inl i))
    (fun i => hφ (Sum.inr i)) ?_).trans (forall_congr' fun y => ⟨?_, ?_⟩)
  · change B.g = p * (A true).g + q * (A false).g
    rw [dim_eq _ hs h₁ hρ, dim_eq _ hs h₂ hρ, dim_eq _ hs h₃ hρ]
    ring
  · rintro ⟨x, x', h⟩
    exact ⟨fun j => Sum.rec (motive := fun j => _ ⟶ (A j.isLeft).t.G) x x' j,
      h.trans (prod_ofFn_sum fun j => Sum.rec (motive := fun j => _ ⟶ (A j.isLeft).t.G) x x' j ≫ φ j).symm⟩
  · rintro ⟨x, h⟩
    exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), h.trans (prod_ofFn_sum fun j => x j ≫ φ j)⟩

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

def toIndefiniteRowSideFullHecke (X : CMObj H K ρ σ₁ p q) : EigenLatticeFibres.CMObj H K ρ p q where
  A := (X.A true).t
  A' := (X.A false).t
  B := X.B.t
  prinA := isPrincipal _
  prinA' := isPrincipal _
  prinB := isPrincipal _
  sigA := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeP⟩
  sigA' := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeM⟩
  sigB := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeB⟩
  ph i := X.φ (Sum.inl i)
  ph' j := X.φ (Sum.inr j)
  lin i := (isLinHom_iff _).2 (X.lin (Sum.inl i))
  lin' j := (isLinHom_iff _).2 (X.lin (Sum.inr j))
  isog := (isog_iff σ₁ X.split X.ρ_sq X.A X.B X.typeP X.typeM X.typeB X.φ fun j => (X.lin j).1).2 X.onto
  h i := X.hh (Sum.inl i)
  h' j := X.hh (Sum.inr j)
  pol i := (polId_iff σ₁ (X.A true) X.B _ (X.lin (Sum.inl i)).1 _).2 (X.weil (Sum.inl i))
  pol' j := (polId_iff σ₁ (X.A false) X.B _ (X.lin (Sum.inr j)).1 _).2 (X.weil (Sum.inr j))

def pure (Y : EigenLatticeFibres.CMObj H K ρ p q) : Bool → PAT H (Sp (𝓞 K))
  | true => patOf Y.A Y.prinA
  | false => patOf Y.A' Y.prinA'

def homs (Y : EigenLatticeFibres.CMObj H K ρ p q) : ∀ j : Fin p ⊕ Fin q, (pure Y j.isLeft).t.G ⟶ Y.B.G
  | Sum.inl i => Y.ph i
  | Sum.inr j => Y.ph' j

theorem homs_lin (Y : EigenLatticeFibres.CMObj H K ρ p q) : ∀ j, Serre.IsLinearHom (pure Y j.isLeft).t.act Y.B.act (homs Y j)
  | Sum.inl i => (isLinHom_iff _).1 (Y.lin i)
  | Sum.inr j => (isLinHom_iff _).1 (Y.lin' j)

def split_model_to_place_model (hs : EigenLatticeFibres.SplitsE E K) (σ₁ : K →+* ℂ) (Y : EigenLatticeFibres.CMObj H K ρ p q) : CMObj H K ρ σ₁ p q where
  split := (splits_iff E K).2 hs
  ρ_sq := Y.sigB.1
  A := pure Y
  B := patOf Y.B Y.prinB
  typeP := ((hasSig_iff _ _ _ _).1 Y.sigA).2
  typeM := ((hasSig_iff _ _ _ _).1 Y.sigA').2
  typeB := ((hasSig_iff _ _ _ _).1 Y.sigB).2
  hh := Sum.elim Y.h Y.h'
  φ := homs Y
  lin := homs_lin Y
  onto := (isog_iff σ₁ ((splits_iff E K).2 hs) Y.sigB.1 (pure Y) (patOf Y.B Y.prinB) ((hasSig_iff _ _ _ _).1 Y.sigA).2
    ((hasSig_iff _ _ _ _).1 Y.sigA').2 ((hasSig_iff _ _ _ _).1 Y.sigB).2 (homs Y) fun j => (homs_lin Y j).1).1 Y.isog
  weil
    | Sum.inl i => (polId_iff σ₁ (patOf Y.A Y.prinA) (patOf Y.B Y.prinB) _ (Y.lin i).1 _).1 (Y.pol i)
    | Sum.inr j => (polId_iff σ₁ (patOf Y.A' Y.prinA') (patOf Y.B Y.prinB) _ (Y.lin' j).1 _).1 (Y.pol' j)

theorem toCMObj_ofCMObj (hs : EigenLatticeFibres.SplitsE E K) (σ₁ : K →+* ℂ) (Y : EigenLatticeFibres.CMObj H K ρ p q) :
    toIndefiniteRowSideFullHecke (split_model_to_place_model hs σ₁ Y) = Y := rfl

theorem pat_ext {S : Scheme.{0}} {T T' : PAT H S} (h : T.t = T'.t) (hg : T.g = T'.g) : T = T' := by
  cases T
  cases T'
  cases h
  cases hg
  rfl

theorem toCMObj_injective : Function.Injective (toIndefiniteRowSideFullHecke : CMObj H K ρ σ₁ p q → _) := by
  intro X X' h
  have hA : X.A = X'.A := funext fun
    | true => pat_ext (congrArg EigenLatticeFibres.CMObj.A h)
      ((dim_eq _ X.split X.typeP X.ρ_sq).trans (dim_eq _ X.split X'.typeP X.ρ_sq).symm)
    | false => pat_ext (congrArg EigenLatticeFibres.CMObj.A' h)
      ((dim_eq _ X.split X.typeM X.ρ_sq).trans (dim_eq _ X.split X'.typeM X.ρ_sq).symm)
  have hB : X.B = X'.B := pat_ext (congrArg EigenLatticeFibres.CMObj.B h)
    ((dim_eq _ X.split X.typeB X.ρ_sq).trans (dim_eq _ X.split X'.typeB X.ρ_sq).symm)
  obtain ⟨_, _, A, B, _, _, _, hh, φ, _, _, _⟩ := X
  obtain ⟨_, _, A', B', _, _, _, hh', φ', _, _, _⟩ := X'
  cases hA
  cases hB
  unfold toIndefiniteRowSideFullHecke at h
  injection h with _ _ _ h₁ h₂ h₃ h₄
  obtain rfl : φ = φ' := funext fun
    | Sum.inl i => congrFun h₁ i
    | Sum.inr i => congrFun h₂ i
  obtain rfl : hh = hh' := funext fun
    | Sum.inl i => congrFun h₃ i
    | Sum.inr i => congrFun h₄ i
  rfl

def cmObjEquiv (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) :
    CMObj H K ρ σ₁ p q ≃ {_Y : EigenLatticeFibres.CMObj H K ρ p q // EigenLatticeFibres.SplitsE E K} where
  toFun X := ⟨toIndefiniteRowSideFullHecke X, (splits_iff E K).1 X.split⟩
  invFun Y := split_model_to_place_model Y.2 σ₁ Y.1
  left_inv _ := toCMObj_injective rfl
  right_inv _ := rfl

end Object

theorem typings_agree (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] :
    (∀ T : PAT H (Sp (𝓞 K)),
      (∀ F : GenFib T.pol, Nonempty (Partner F)) ∧
      (∀ G : EigenLatticeFibres.GenFib T.t, ∃ (F : GenFib T.pol) (Q : Partner F), Q.fib = G) ∧
      ∀ (F : GenFib T.pol) (Q : Partner F),
        (∀ u c, F.IsCoord u c ↔
          IsTangent u ∧ Q.fib.IsVec c (spMap (Chart.dualMapR (algebraMap (𝓞 K) K)) ≫ u.left)) ∧
        F.lieLat = Q.fib.lieLat ∧
        (∀ τ : E →+* K, F.eigLat T.t.act (RingOfIntegers.mapRingHom τ) = Q.fib.eigenLat τ) ∧
        (∀ h, F.IsHerm h ↔ Q.fib.IsPiH h) ∧
        ∀ (T' : PAT H (Sp (𝓞 K))) (F' : GenFib T'.pol) (Q' : Partner F') (f : T.t.G ⟶ T'.t.G) M,
          F.IsDiffOf F' f M ↔ Q.fib.IsDiff Q'.fib f M) ∧
    (∀ t : SAB H (Sp (𝓞 K)), CMCurveHermitianForms.IsPrincipal t ↔ ∃ T : PAT H (Sp (𝓞 K)), T.t = t) ∧
    Function.Bijective (RingOfIntegers.mapRingHom : (E →+* K) → (𝓞 E →+* 𝓞 K)) ∧
    (Splits E K ↔ EigenLatticeFibres.SplitsE E K) ∧
    ∀ (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ),
      ∃ e : CMObj H K ρ σ₁ p q ≃ {_Y : EigenLatticeFibres.CMObj H K ρ p q // EigenLatticeFibres.SplitsE E K}, ∀ X,
        (e X).1.A = (X.A true).t ∧ (e X).1.A' = (X.A false).t ∧ (e X).1.B = X.B.t ∧
        (∀ i, HEq ((e X).1.ph i) (X.φ (Sum.inl i)) ∧ (e X).1.h i = X.hh (Sum.inl i)) ∧
        ∀ j, HEq ((e X).1.ph' j) (X.φ (Sum.inr j)) ∧ (e X).1.h' j = X.hh (Sum.inr j) :=
  ⟨fun _ => ⟨nonempty_partner, exists_partner, fun _ Q => ⟨Q.isCoord_iff, Q.lieLat_eq,
      fun τ => Q.eigLat_eq _ τ fun _ => rfl, Q.isHerm_iff, fun _ _ Q' => Q.isDiffOf_iff Q'⟩⟩,
    fun t => ⟨fun h => ⟨patOf t h, rfl⟩, fun ⟨T, h⟩ => h ▸ isPrincipal T⟩,
    mapRingHom_bijective E K, splits_iff E K, fun ρ σ₁ p q => ⟨cmObjEquiv H K ρ σ₁ p q, fun _ =>
      ⟨rfl, rfl, rfl, fun _ => ⟨HEq.rfl, rfl⟩, fun _ => ⟨HEq.rfl, rfl⟩⟩⟩⟩

end GlobalTheory.CMSharedCompare
