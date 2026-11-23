import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientSStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDualStatement

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TransDual

open Formalism.HermitianLatticesTheory (localization₂)

section General

variable {K : Type} [Field K] [NumberField K]

theorem mem_of_forall_locP {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (A : Submodule (𝓞 K) V) (x : V)
    (hx : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ localization₂ w.asIdeal A) : x ∈ A := by
  by_contra hxA
  let I : Ideal (𝓞 K) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x) A
  have hmem : ∀ r : 𝓞 K, r ∈ I ↔ r • x ∈ A := by
    intro r
    simp [I]
  have hI : I ≠ ⊤ := by
    intro h
    apply hxA
    have h1 : (1 : 𝓞 K) ∈ I := h ▸ Submodule.mem_top
    simpa using (hmem 1).mp h1
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp.isPrime, hp0⟩
  exact hs (hIp ((hmem s).mpr hsx))

theorem mem_localization_of_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {A : Submodule (𝓞 K) V} {x : V} (hx : x ∈ A) : x ∈ localization₂ w.asIdeal A :=
  ⟨1, Submonoid.one_mem _, by simpa using hx⟩

variable [StarRing K]

theorem conj_not_mem (w : HeightOneSpectrum (𝓞 K)) {t : 𝓞 K} (ht : t ∈ (conjPl w).asIdeal.primeCompl) :
    cO K t ∈ w.asIdeal.primeCompl := by
  intro h
  apply ht
  have h1 : cO K (cO K t) ∈ (conjPl w).asIdeal := Ideal.mem_map_of_mem (cO K) h
  have h2 : cO K (cO K t) = t := RingOfIntegers.ext (star_star (t : K))
  rwa [h2] at h1

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem pair_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (t : 𝓞 K) (y x : V) : h (t • y) x = cO K t • h y x := by
  rw [← algebraMap_smul K t y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul,
    Algebra.smul_def]
  rfl

theorem pair_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (t : 𝓞 K) (y x : V) : h y (t • x) = t • h y x := by
  rw [← algebraMap_smul K t x, map_smul, algebraMap_smul]

theorem pair_locP (h : V →ₗ⋆[K] V →ₗ[K] K) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) V) (x : V) :
    (∀ y ∈ localization₂ (conjPl w).asIdeal T, h y x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ↔
      ∀ y ∈ T, h y x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  refine ⟨fun H y hy => H y (mem_localization_of_mem _ hy), ?_⟩
  rintro H y ⟨t, ht, hy⟩
  obtain ⟨s, hs, hsy⟩ := H _ hy
  refine ⟨s * cO K t, Submonoid.mul_mem _ hs (conj_not_mem w ht), ?_⟩
  rwa [pair_smul_left, smul_smul] at hsy

theorem pair_denom (h : V →ₗ⋆[K] V →ₗ[K] K) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) V) (hT : T.FG)
    (x : V) (H : ∀ y ∈ T, h y x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) :
    ∃ s ∈ w.asIdeal.primeCompl, ∀ y ∈ T, h y (s • x) ∈ (1 : Submodule (𝓞 K) K) := by
  classical
  obtain ⟨S, rfl⟩ := hT
  have H' : ∀ y : S, ∃ s ∈ w.asIdeal.primeCompl, s • h y x ∈ (1 : Submodule (𝓞 K) K) :=
    fun y => H y (Submodule.subset_span y.2)
  choose s hs hsy using H'
  refine ⟨∏ y, s y, Submonoid.prod_mem _ fun y _ => hs y, ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [pair_smul_right, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : S)), mul_smul]
    exact Submodule.smul_mem _ _ (hsy ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply]
    exact add_mem hy hz
  | smul r y _ hy =>
    rw [pair_smul_left]
    exact Submodule.smul_mem _ _ hy

theorem mem_localization_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (w : HeightOneSpectrum (𝓞 K)) (U : Submodule K V)
    (T D : Submodule (𝓞 K) V) (hT : T.FG)
    (hD : ∀ x ∈ U, x ∈ D ↔ ∀ y ∈ T, h y x ∈ (1 : Submodule (𝓞 K) K)) {x : V} (hx : x ∈ U) :
    x ∈ localization₂ w.asIdeal D ↔
      ∀ y ∈ localization₂ (conjPl w).asIdeal T, h y x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  rw [pair_locP]
  have hU : ∀ s : 𝓞 K, s • x ∈ U := fun s => by
    rw [← algebraMap_smul K s x]
    exact U.smul_mem _ hx
  constructor
  · rintro ⟨s, hs, hsx⟩ y hy
    refine ⟨s, hs, ?_⟩
    rw [← pair_smul_right]
    exact (hD _ (hU s)).1 hsx y hy
  · intro H
    obtain ⟨s, hs, hsy⟩ := pair_denom h w T hT x H
    exact ⟨s, hs, (hD _ (hU s)).2 hsy⟩

theorem pair_integral_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (T : Submodule (𝓞 K) V) (x : V) :
    (∀ y ∈ T, h y x ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ w : HeightOneSpectrum (𝓞 K),
      ∀ y ∈ localization₂ (conjPl w).asIdeal T, h y x ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K) := by
  simp only [pair_locP]
  exact ⟨fun H w y hy => mem_localization_of_mem w (H y hy), fun H y hy => mem_of_forall_locP _ _ fun w => H w y hy⟩

end General

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}

def gramForm (G : Matrix (Fin n) (Fin n) K) : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun y x => star y ⬝ᵥ (G *ᵥ x))
    (fun y z x => by rw [star_add, add_dotProduct])
    (fun c y x => by rw [star_smul, smul_dotProduct]; rfl)
    (fun y x z => by rw [Matrix.mulVec_add, dotProduct_add])
    (fun c y x => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl)

omit [StarRing K] in
theorem mem_colLat (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∀ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j ∈ (1 : Submodule (𝓞 K) K) := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  have key : ∀ c : Fin n → 𝓞 K, (∑ j, c j • fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ fun j => algebraMap (𝓞 K) K (c j) := by
    intro c
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  constructor
  · rintro ⟨c, rfl⟩ j
    rw [key, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.mem_one.2 ⟨c j, rfl⟩
  · intro H
    choose c hc using fun j => Submodule.mem_one.1 (H j)
    refine ⟨c, ?_⟩
    rw [key, show (fun j => algebraMap (𝓞 K) K (c j)) = _ from funext hc, Matrix.mulVec_mulVec, Units.mul_inv,
      Matrix.one_mulVec]

omit [StarRing K] in
theorem colLat_fg (B : GL (Fin n) K) : (colLat B).FG := Submodule.fg_span (Set.finite_range _)

theorem mem_colLat_dual (G : Matrix (Fin n) (Fin n) K) (B B' : GL (Fin n) K)
    (hB : (B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K) = 1) (x : Fin n → K) :
    x ∈ colLat B' ↔ ∀ y ∈ colLat B, gramForm G y x ∈ (1 : Submodule (𝓞 K) K) := by
  have e : ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K)ᴴ * G := by
    rw [← Matrix.one_mul ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← hB, Matrix.mul_assoc _ (B' : Matrix (Fin n) (Fin n) K),
      Units.mul_inv, Matrix.mul_one]
  have e2 : ∀ j, (((B : Matrix (Fin n) (Fin n) K)ᴴ * G) *ᵥ x) j =
      gramForm G (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) x := by
    intro j
    rw [← Matrix.mulVec_mulVec]
    rfl
  rw [mem_colLat, e]
  simp only [e2]
  constructor
  · intro H y hy
    unfold colLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact H j
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, LinearMap.add_apply]
      exact add_mem hy hz
    | smul r y _ hy =>
      rw [pair_smul_left]
      exact Submodule.smul_mem _ _ hy
  · intro H j
    exact H _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isBasisAt_hdual (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG)
    (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K) (h : IsBasisAt (conjPl w) M B)
    (hB : (B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K) = 1) :
    IsBasisAt w (hdualFr G M) B' := by
  ext x
  rw [mem_localization_dual (gramForm G) w ⊤ M (hdualFr G M) hM (fun _ _ => Iff.rfl) Submodule.mem_top,
    mem_localization_dual (gramForm G) w ⊤ (colLat B) (colLat B') (colLat_fg B)
      (fun x _ => mem_colLat_dual G B B' hB x) Submodule.mem_top]
  unfold IsBasisAt at h
  rw [h]

omit [NumberField K] in
theorem exists_dual_frame (G : Matrix (Fin n) (Fin n) K) (hG : IsUnit G.det) (B : GL (Fin n) K) :
    ∃ B' : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K) = 1 := by
  have hu : IsUnit ((B : Matrix (Fin n) (Fin n) K)ᴴ * G) := by
    refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det G).2 hG)
    exact (Units.isUnit B).star
  obtain ⟨u, hu⟩ := hu
  exact ⟨u⁻¹, by rw [← hu, Units.mul_inv]⟩

end Frames

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}

theorem dual_of_local (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (T T' P P' : Submodule (𝓞 K) (Pol K ι n)) (hT : T.FG)
    (hD : ∀ x ∈ VV K lam, x ∈ T' ↔ ∀ y ∈ T, pairP lam (fun _ => 1) y x ∈ (1 : Submodule (𝓞 K) K))
    (hP : ∀ F ∈ P, F ∈ VV K lam)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 K), ∃ B B' : ι → GL (Fin n) K,
      (∀ τ, (B τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (B' τ : Matrix (Fin n) (Fin n) K) = 1) ∧
      localization₂ (conjPl w).asIdeal P = (localization₂ (conjPl w).asIdeal T).map ((actP lam B).restrictScalars (𝓞 K)) ∧
      localization₂ w.asIdeal P' = (localization₂ w.asIdeal T').map ((actP lam B').restrictScalars (𝓞 K))) :
    Formalism.HermitianLatticesTheory.dual (pairK lam G) (P.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) =
      P'.comap ((VV K lam).subtype.restrictScalars (𝓞 K)) := by
  ext x
  have h1 : x ∈ Formalism.HermitianLatticesTheory.dual (pairK lam G) (P.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔
      ∀ y ∈ P, pairP lam G y x.1 ∈ (1 : Submodule (𝓞 K) K) := by
    have h0 : x ∈ Formalism.HermitianLatticesTheory.dual (pairK lam G) (P.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔
        ∀ y ∈ P.comap ((VV K lam).subtype.restrictScalars (𝓞 K)), pairK lam G y x ∈ (1 : Submodule (𝓞 K) K) := by
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
    rw [h0]
    constructor
    · intro H y hy
      have := H ⟨y, hP y hy⟩ hy
      rwa [pairK_apply] at this
    · intro H y hy
      rw [pairK_apply]
      exact H _ hy
  have h2 : ∀ w : HeightOneSpectrum (𝓞 K),
      (∀ y ∈ localization₂ (conjPl w).asIdeal P, pairP lam G y x.1 ∈ localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ↔
        x.1 ∈ localization₂ w.asIdeal P' := by
    intro w
    obtain ⟨B, B', hB, e1, e2⟩ := hloc w
    have hx : actP lam B' (actP lam B'⁻¹ x.1) = x.1 := by
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
    have ht : ∀ y, pairP lam G (actP lam B y) x.1 = pairP lam (fun _ => 1) y (actP lam B'⁻¹ x.1) := by
      intro y
      conv_lhs => rw [← hx]
      rw [pairTransport K ι n lam G B B']
      simp only [hB]
    have h3 : x.1 ∈ localization₂ w.asIdeal P' ↔ actP lam B'⁻¹ x.1 ∈ localization₂ w.asIdeal T' := by
      rw [e2]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have hzx' : actP lam B' z = x.1 := hzx
        rw [← hzx', ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
        exact hz
      · intro H
        exact ⟨_, H, hx⟩
    rw [h3, mem_localization_dual (pairP lam fun _ => 1) w (VV K lam) T T' hT hD (polyAction_mem_VV lam _ x.2), e1]
    constructor
    · intro H y hy
      rw [← ht]
      exact H _ ⟨y, hy, rfl⟩
    · rintro H _ ⟨y, hy, rfl⟩
      have := H y hy
      rw [← ht] at this
      exact this
  rw [h1, pair_integral_iff]
  simp only [h2]
  exact ⟨fun H => mem_of_forall_locP P' x.1 H, fun H w => mem_localization_of_mem w H⟩

end Main

theorem nabDelDual : NabDelDual := by
  intro K _ _ _ ι _ n lam G M _ hG hM
  have hone : ∀ a : K, a ∈ (algebraMap (𝓞 K) K).range ↔ a ∈ (1 : Submodule (𝓞 K) K) := fun a => by
    rw [Submodule.mem_one, RingHom.mem_range]
  have hM' : ∀ τ, Submodule.IsLattice K (hdualFr (G τ) (M τ)) := fun τ =>
    (GlobalTheory.DualLat.dualFr_lattice_and_hdual.1 K n (G τ) (M τ) (hG τ) (hM τ)).2
  have hfr : ∀ w : HeightOneSpectrum (𝓞 K), ∃ B B' : ι → GL (Fin n) K,
      (∀ τ, (B τ : Matrix (Fin n) (Fin n) K)ᴴ * G τ * (B' τ : Matrix (Fin n) (Fin n) K) = 1) ∧
      (∀ τ, IsBasisAt (conjPl w) (M τ) (B τ)) ∧ ∀ τ, IsBasisAt w (hdualFr (G τ) (M τ)) (B' τ) := by
    intro w
    choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) (conjPl w)
    choose B' hB' using fun τ => exists_dual_frame (G τ) (hG τ) (B τ)
    exact ⟨B, B', hB', hB, fun τ =>
      isBasisAt_hdual (G τ) (M τ) (Submodule.IsLattice.fg (self := hM τ)) w (B τ) (B' τ) (hB τ) (hB' τ)⟩
  have hnab : ∀ F ∈ nabP lam M, F ∈ VV K lam := GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.2.2 K ι n lam M hM
  have hdel : ∀ F ∈ delP lam M, F ∈ VV K lam := fun F hF =>
    hnab F (transLat_mono lam (delStd_le_nabStd K lam) M hF)
  constructor
  · refine dual_of_local lam G (nabStd K lam) (delStd K lam) _ _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).1 ?_ hnab ?_
    · intro x hx
      rw [← (GlobalTheory.T.standard_weyl_lattices_fock_dual K ι n lam x hx).2]
      simp only [hone]
    · intro w
      obtain ⟨B, B', h1, h2, h3⟩ := hfr w
      exact ⟨B, B', h1, (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam M hM _ B h2).1, (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam _ hM' _ B' h3).2⟩
  · refine dual_of_local lam G (delStd K lam) (nabStd K lam) _ _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.1 ?_ hdel ?_
    · intro x hx
      rw [← (GlobalTheory.T.standard_weyl_lattices_fock_dual K ι n lam x hx).1]
      simp only [hone]
    · intro w
      obtain ⟨B, B', h1, h2, h3⟩ := hfr w
      exact ⟨B, B', h1, (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam M hM _ B h2).2, (GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace.1 K ι n lam _ hM' _ B' h3).1⟩

end GlobalTheory.TransDual
