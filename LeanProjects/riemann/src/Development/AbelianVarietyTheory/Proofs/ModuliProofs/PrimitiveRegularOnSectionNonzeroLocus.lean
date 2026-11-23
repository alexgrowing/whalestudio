import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowEqThetaLevelChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.PrimitiveRegular

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

private theorem top_le_preimage_iff_mem' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ V ↔ x (default : PrimeSpectrum ℂ) ∈ V :=
  ⟨fun h => h (show (default : PrimeSpectrum ℂ) ∈ (⊤ : (Sp ℂ).Opens) from trivial),
    fun h q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum ℂ)]; exact h⟩

theorem top_le_preimage_iSup {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (U : κ → X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (⨆ k, U k) ↔ ∃ k, ⊤ ≤ x ⁻¹ᵁ U k := by
  simp only [top_le_preimage_iff_mem']
  exact TopologicalSpace.Opens.mem_iSup

theorem mem_basicOpen (u : HolUnif A L g) {n : ℕ} {σ : (lbPow L n).Sec} {θ : (Fin g → ℂ) → ℂ}
    (hθ : u.IsFnPow n σ θ) (k : (lbPow L n).ι) (z : Fin g → ℂ) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k)
    (hz : θ z ≠ 0) : valAt' (u.ex z).left ((lbPow L n).U k) (σ.f k) ≠ 0 := by
  rw [hθ k z hk]
  refine mul_ne_zero hz (pow_ne_zero _ (u.11 _ z ?_))
  have hU : (lbPow L n).U k ≤ L.U (k PUnit.unit) := by
    intro p hp
    have hp' := Set.mem_iInter.mp hp PUnit.unit
    simpa using hp'
  exact fun q hq => hU (hk hq)

private theorem valAt'_eq_ΓSpecIso_appLE {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt' y W f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((y.appLE W ⊤ hW).hom f) := by
  unfold valAt' valAt
  rw [dif_pos hW]

private theorem valAt'_presheaf_map_of_le_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' y V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' y W f := by
  rw [valAt'_eq_ΓSpecIso_appLE y hV, valAt'_eq_ΓSpecIso_appLE y (hV.trans fun q hq => hVW hq)]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_mul_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(Y, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  simp only [valAt'_eq_ΓSpecIso_appLE y hW, map_mul]

private theorem valAt'_pow_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (m : ℕ) : valAt' y W (f ^ m) = valAt' y W f ^ m := by
  simp only [valAt'_eq_ΓSpecIso_appLE y hW, map_pow]

private theorem top_le_comap_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (hf : valAt' y W f ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen f := by
  rw [valAt'_eq_ΓSpecIso_appLE y hW] at hf
  have hu : IsUnit ((y.appLE W ⊤ hW).hom f) := by
    have h2 := (IsUnit.mk0 _ hf).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h2
  have h3 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h4 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) ≤ y ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact inf_le_right
  exact h3.symm.le.trans h4

theorem local_extension (u : HolUnif A L g) (hL : L.IsLB) {I : Type} (O : I → A.left.Opens)
    (c : ∀ i i', Γ(A.left, O i ⊓ O i')) (h : I → (Fin g → ℂ) → ℂ) (hO : ⨆ i, O i = ⊤)
    (hh : ∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i})
    (hc : ∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') →
      valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z)
    (i : I) {n : ℕ} (σ : (lbPow L n).Sec) (hσ : Out.nonzeroLocus σ ≤ O i) {θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (hθ : u.IsFnPow n σ θ) (x : A.left) :
    ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * h i z = F z := by
  obtain ⟨i', hxi'⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ i, O i from hO ▸ trivial)
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ j, L.U j from hL.1 ▸ trivial)
  let k : (lbPow L n).ι := fun _ => j
  have hUk : (lbPow L n).U k ≤ L.U j := fun p hp => by simpa using Set.mem_iInter.mp hp PUnit.unit
  have hxk : x ∈ (lbPow L n).U k := Set.mem_iInter.mpr fun _ => by simpa using hxj
  have hB : TopologicalSpace.Opens.IsBasis A.left.affineOpens := by
    first
      | exact AlgebraicGeometry.isBasis_affineOpens A.left
      | exact AlgebraicGeometry.Scheme.isBasis_affineOpens A.left
  obtain ⟨V, hVa, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB) (show x ∈ O i' ⊓ (lbPow L n).U k from ⟨hxi', hxk⟩)
  have hV1 : V ≤ O i' := hVle.trans inf_le_left
  have hV2 : V ≤ (lbPow L n).U k := hVle.trans inf_le_right
  set sV := (A.left.presheaf.map (homOfLE hV2).op).hom (σ.f k) with hsV
  have hD : A.left.basicOpen sV ≤ O i ⊓ O i' := by
    refine le_inf ?_ ((A.left.basicOpen_le sV).trans hV1)
    refine le_trans ?_ hσ
    rw [hsV, Scheme.basicOpen_res]
    refine inf_le_right.trans ?_
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact le_iSup (fun k => A.left.basicOpen (σ.f k)) k
  obtain ⟨N, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen A.left V hVa sV
    ((A.left.presheaf.map (homOfLE hD).op).hom (c i i'))
  have hS1 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i'} :=
    fun z hz q hq => hV1 (hz hq)
  have hS2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j} :=
    fun z hz q hq => hUk (hV2 (hz hq))
  refine ⟨V, N, fun z => θ z ^ N * h i' z - valAt' (u.ex z).left V a * (u.fr j z ^ (n * N))⁻¹, hxV, ?_, ?_⟩
  · have hfrd : DifferentiableOn ℂ (fun z => u.fr j z ^ (n * N)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} :=
      ((u.10 j).mono hS2).pow _
    exact ((hd.pow N).differentiableOn.mul ((hh i').mono hS1)).sub
      ((u.8 V a).2.mul (hfrd.inv fun z hz => pow_ne_zero _ (u.11 j z (hS2 hz))))
  · intro z hz hz0
    have hzk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := hz.trans fun q hq => hV2 hq
    have hfr : u.fr j z ≠ 0 := u.11 j z (hS2 hz)
    have hs : valAt' (u.ex z).left V sV = θ z * u.fr j z ^ n := by
      rw [hsV, valAt'_presheaf_map_of_le_of_whole_le_preimage _ hV2 hz]
      exact hθ k z hzk
    have hzD : ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen sV :=
      top_le_comap_basicOpen_of_valAt'_ne_zero _ hz sV (by rw [hs]; exact mul_ne_zero hz0 (pow_ne_zero _ hfr))
    have hc' := hc i i' z (hzD.trans fun q hq => hD hq)
    have key := congrArg (valAt' (u.ex z).left (A.left.basicOpen sV)) ha
    rw [valAt'_mul_of_whole_le_preimage _ hzD, valAt'_pow_of_whole_le_preimage _ hzD] at key
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at key
    rw [valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, hs, hc'] at key
    beta_reduce
    rw [key]
    field_simp
    ring

private theorem top_le_preimage_iff_point_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ V ↔ x (default : PrimeSpectrum ℂ) ∈ V :=
  ⟨fun h => h (show (default : PrimeSpectrum ℂ) ∈ (⊤ : (Sp ℂ).Opens) from trivial),
    fun h q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum ℂ)]; exact h⟩

theorem entire_extension (u : HolUnif A L g) [CompactSpace A.left] (f θ : (Fin g → ℂ) → ℂ)
    (hd : Differentiable ℂ θ)
    (hloc : ∀ x : A.left, ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * f z = F z) :
    ∃ M : ℕ, 0 < M ∧ Differentiable ℂ fun z => θ z ^ M * f z := by
  choose Q N F hxQ hF hQ using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (Q x : Set A.left))
    (fun x => (Q x).isOpen) (fun p _ => Set.mem_iUnion.mpr ⟨p, hxQ p⟩)
  refine ⟨t.sup N + 1, Nat.succ_pos _, fun z => ?_⟩
  obtain ⟨x, hxt, hx⟩ : ∃ x ∈ t, (u.ex z).left (default : PrimeSpectrum ℂ) ∈ Q x := by
    simpa using ht (Set.mem_univ ((u.ex z).left (default : PrimeSpectrum ℂ)))
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ Q x} := (u.8 (Q x) 0).1
  have hz : z ∈ {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ Q x} := (top_le_preimage_iff_point_mem _ _).2 hx
  have hN : N x < t.sup N + 1 := Nat.lt_succ_of_le (Finset.le_sup hxt)
  have hD : DifferentiableAt ℂ (fun w => θ w ^ (t.sup N + 1 - N x) * F x w) z :=
    ((hd z).pow _).mul ((hF x).differentiableAt (hS.mem_nhds hz))
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [hS.mem_nhds hz] with w hw
  by_cases h0 : θ w = 0
  · rw [h0, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.sub_ne_zero_of_lt hN), zero_mul, zero_mul]
  · rw [← hQ x w hw h0, ← _root_.mul_assoc, ← _root_.pow_add, Nat.sub_add_cancel hN.le]

private theorem valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt' y W f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((y.appLE W ⊤ hW).hom f) := by
  unfold valAt' valAt
  rw [dif_pos hW]

private theorem valAt'_presheaf_map_of_le_of_whole_le_preimage' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' y V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' y W f := by
  rw [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hV, valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y (hV.trans fun q hq => hVW hq)]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_mul_of_top_le_preimage_open {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(Y, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_mul]

private theorem valAt'_pow_of_whole_le_preimage' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (m : ℕ) : valAt' y W (f ^ m) = valAt' y W f ^ m := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_pow]

private theorem point_mem_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (hf : valAt' y W f ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen f := by
  rw [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW] at hf
  have hu : IsUnit ((y.appLE W ⊤ hW).hom f) := by
    have h2 := (IsUnit.mk0 _ hf).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h2
  have h3 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h4 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) ≤ y ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact inf_le_right
  exact h3.symm.le.trans h4

private theorem valAt'_one_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) :
    valAt' y W 1 = 1 := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_one]

end GlobalTheory.PrimitiveRegular

namespace GlobalTheory

open PrimitiveRegular

theorem primitive_regular_on_nonzeroLocus : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by
  intro P₀ u Hm χ hG I O c h hO hh hc i n σ hσ
  have hL : P₀.L.IsLB := P₀.7
  have : CompactSpace P₀.A.left := by
    have : IsProper P₀.A.hom := by
      exact P₀.3.3
    have hc0 := QuasiCompact.isCompact_preimage (f := P₀.A.hom) Set.univ isOpen_univ isCompact_univ
    exact ⟨by simpa using hc0⟩
  obtain ⟨θ, hθd, hθ, -, hθper⟩ := GlobalTheory.ThetaBundleSec.exists_fn u hL n σ
  have hOi : ∀ z, θ z ≠ 0 → ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i := by
    intro z hz
    obtain ⟨j, hj⟩ := (PrimitiveRegular.top_le_preimage_iSup (u.ex z).left P₀.L.U).mp
      (by rw [hL.1]; exact fun q _ => trivial)
    let k : (lbPow P₀.L n).ι := fun _ => j
    have hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P₀.L n).U k :=
      fun q hq => Set.mem_iInter.mpr fun _ => by simpa using hj hq
    have hb := point_mem_basicOpen_of_valAt'_ne_zero _ hk (σ.f k) (PrimitiveRegular.mem_basicOpen u hθ k z hk hz)
    refine hb.trans fun q hq => hσ ?_
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact (le_iSup (fun k => P₀.A.left.basicOpen (σ.f k)) k) hq
  obtain ⟨M, hM, hdiff⟩ := PrimitiveRegular.entire_extension u (h i) θ hθd
    (PrimitiveRegular.local_extension u hL O c h hO (fun i => (hh i).1) hc i σ hσ hθd hθ)
  have hTh : u.IsThetaFn Hm χ (n * M) (fun z => θ z ^ M * h i z) := by
    refine ⟨hdiff, fun l z => ?_⟩
    beta_reduce
    have hw := hθper z (z + l)
      (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l))
      (GlobalTheory.SectionTheta.ex_add_lattice u z l) (fun j hj => hG.ah.2.2.2 l j z hj)
    by_cases h0 : θ z = 0
    · have h0' : θ (z + l) = 0 := by rw [hw, h0, mul_zero]
      simp only [h0, h0', zero_pow hM.ne', zero_mul, mul_zero]
    · rw [hw, (hh i).2 l z (hOi z h0), pow_mul, mul_pow]
      ring
  obtain ⟨s, hs⟩ := hG.sec (n * M) _ hTh
  refine (existsUnique_section_of_locally_regular P₀ u Hm χ hG (Out.nonzeroLocus σ) (h i) ?_).exists
  intro z hz
  have hz' := hz
  unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus at hz'
  obtain ⟨k, hk⟩ := (PrimitiveRegular.top_le_preimage_iSup (u.ex z).left _).mp hz'
  have hle : P₀.A.left.basicOpen (σ.f k) ≤ Out.nonzeroLocus σ := by
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact le_iSup (fun k => P₀.A.left.basicOpen (σ.f k)) k
  have hUk := P₀.A.left.basicOpen_le (σ.f k)
  have hu : IsUnit ((P₀.A.left.presheaf.map (homOfLE hUk).op).hom (σ.f k)) := by
    exact RingedSpace.isUnit_res_basicOpen _ (σ.f k)
  refine ⟨P₀.A.left.basicOpen (σ.f k),
    (P₀.A.left.presheaf.map (homOfLE hUk).op).hom (s.f k) * ((hu.unit⁻¹ : _ˣ) : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) ^ M,
    hle, hk, fun z' hz'' => ?_⟩
  have hzk : ⊤ ≤ (u.ex z').left ⁻¹ᵁ (lbPow P₀.L n).U k := hz''.trans fun q hq => hUk hq
  have hr : valAt' (u.ex z').left _ (hu.unit : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) = θ z' * u.fr (k PUnit.unit) z' ^ n := by
    rw [IsUnit.unit_spec, valAt'_presheaf_map_of_le_of_whole_le_preimage' _ _ hz'']
    exact hθ k z' hzk
  have hinv : valAt' (u.ex z').left _ (hu.unit : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) *
      valAt' (u.ex z').left _ ((hu.unit⁻¹ : _ˣ) : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) = 1 := by
    rw [← valAt'_mul_of_top_le_preimage_open _ hz'', Units.mul_inv, valAt'_one_of_whole_le_preimage _ hz'']
  have hne : θ z' * u.fr (k PUnit.unit) z' ^ n ≠ 0 := by
    rw [← hr]; exact left_ne_zero_of_mul_eq_one hinv
  have hθ0 : θ z' ≠ 0 := left_ne_zero_of_mul hne
  have hfr0 : u.fr (k PUnit.unit) z' ^ n ≠ 0 := right_ne_zero_of_mul hne
  rw [hr] at hinv
  rw [valAt'_mul_of_top_le_preimage_open _ hz'', valAt'_pow_of_whole_le_preimage' _ hz'']
  erw [valAt'_presheaf_map_of_le_of_whole_le_preimage' (W := (lbPow P₀.L (n * M)).U k) _ hUk hz'']
  rw [eq_inv_of_mul_eq_one_right hinv, hs k z' (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (lbPow P₀.L (n * M)).U k from hzk)]
  have hθM : θ z' ^ M ≠ 0 := pow_ne_zero _ hθ0
  have hfrM : u.fr (k PUnit.unit) z' ^ (n * M) ≠ 0 := by
    rw [pow_mul]
    exact pow_ne_zero _ hfr0
  beta_reduce
  rw [inv_pow, mul_pow, ← pow_mul]
  calc _ = (θ z' ^ M * u.fr (k PUnit.unit) z' ^ (n * M)) *
        (θ z' ^ M * u.fr (k PUnit.unit) z' ^ (n * M))⁻¹ * h i z' := by ring
    _ = h i z' := by rw [mul_inv_cancel₀ (mul_ne_zero hθM hfrM), _root_.one_mul]

end GlobalTheory
