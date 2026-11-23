import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralWeylBasisSpanningAllRingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylLatticeAddIffDetPowMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.DelStd

theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  omega

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Fin.pos a
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, hn, dif_pos] at *
  omega

theorem linInd_map {σ P : Type} [Fintype P] (K : Type) [Field K] [CharZero K] (b : P → MvPolynomial σ ℤ)
    (hb : LinearIndependent ℤ b) : LinearIndependent K fun i => MvPolynomial.map (Int.castRingHom K) (b i) := by
  classical
  let e := Fintype.equivFin P
  have h1 : LinearIndependent ℤ (b ∘ e.symm) := hb.comp _ e.symm.injective
  have h1' := h1.map' (MvPolynomial.basisMonomials σ ℤ).repr.toLinearMap (LinearEquiv.ker _)
  have h2 := GlobalTheory.LatBC.linInd_mapRange (O := ℤ) (K := K) (P := σ →₀ ℕ) (Int.castRingHom K) (fun _ _ h => Int.cast_injective h) h1'
  have h3 := h2.comp e e.injective
  refine LinearIndependent.of_comp (MvPolynomial.basisMonomials σ K).repr.toLinearMap ?_
  convert h3 using 1
  funext i
  ext m
  have hZ : ∀ f : MvPolynomial σ ℤ, (MvPolynomial.basisMonomials σ ℤ).repr f m = coeff m f := fun _ => rfl
  have hK : ∀ f : MvPolynomial σ K, (MvPolynomial.basisMonomials σ K).repr f m = coeff m f := fun _ => rfl
  simp [hZ, hK, MvPolynomial.coeff_map]

theorem detPol_ne_zero (C : Type) [Field C] (n : ℕ) : detPol C n ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) C

theorem map_detPol {R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (n : ℕ) :
    MvPolynomial.map f (detPol R n) = detPol C n := by
  unfold detPol
  rw [RingHom.map_det]
  congr 1
  ext a s : 2
  simp

theorem linInd_det {P : Type} {C : Type} [Field C] {n : ℕ} (k : ℕ) (b : P → MvPolynomial (Fin n × Fin n) C)
    (hb : LinearIndependent C b) : LinearIndependent C fun i => detPol C n ^ k * b i := by
  have := hb.map' (LinearMap.mulLeft C (detPol C n ^ k)) (LinearMap.ker_eq_bot.2
    (mul_right_injective₀ (pow_ne_zero k (detPol_ne_zero C n))))
  exact this

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_sum {C : Type} [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {P : ι → Type} [∀ τ, Fintype (P τ)]
    (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) C) (a : ∀ τ, P τ → C) :
    (ten fun τ => ∑ j, a τ j • u τ j) = ∑ i : ∀ τ, P τ, (∏ τ, a τ (i τ)) • ten fun τ => u τ (i τ) := by
  unfold ten
  simp only [map_sum, map_smul]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_smul]

theorem map_map_int {σ R C : Type} [CommRing R] [CommRing C] (f : R →+* C) (b : MvPolynomial σ ℤ) :
    MvPolynomial.map f (MvPolynomial.map (Int.castRingHom R) b) = MvPolynomial.map (Int.castRingHom C) b := by
  rw [MvPolynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom C)]

theorem latD_coords {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (lamW : ι → ℕ → ℕ) (F : Frame l ι n)
    (hF : ∀ x : F.O, ‖F.emb x‖ ≤ 1) {P : ι → Type} [∀ τ, Fintype (P τ)] (u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l))
    (hu : ∀ τ, ∀ x0 ∈ weyl F.O n n le_rfl (res n (lamW τ)), ∃ a : P τ → F.O,
      MvPolynomial.map F.emb x0 = ∑ j, F.emb (a j) • u τ j)
    {z : NablaT (PadicAlgCl l) n lamW} (hz : z ∈ F.latD lamW) :
    ∃ r : (∀ τ, P τ) → PadicAlgCl l, (∀ i, ‖r i‖ ≤ 1) ∧
      mulMap (PadicAlgCl l) n lamW z = ∑ i, r i • ten fun τ => u τ (i τ) := by
  unfold Frame.latD at hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, x, hx, rfl⟩ := hy
    choose x0 hx0 hx1 using hx
    choose a ha using fun τ => hu τ (x0 τ) (hx0 τ)
    refine ⟨fun i => F.emb c * ∏ τ, F.emb (a τ (i τ)), fun i => ?_, ?_⟩
    · beta_reduce
      rw [← map_prod, ← map_mul]; exact hF _
    · rw [map_smul, mulMap_tprod]
      have : (fun τ => (x τ : MvPolynomial (Fin n × Fin n) (PadicAlgCl l))) = fun τ => ∑ j, F.emb (a τ j) • u τ j := by
        funext τ; rw [← hx1, ha]
      rw [this, ten_sum u fun τ j => F.emb (a τ j), Finset.smul_sum]
      simp only [smul_smul]
  | zero => exact ⟨0, fun i => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨s, hs, hy⟩ := hy
    refine ⟨r + s, fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr i) (hs i)), ?_⟩
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_smul]
  | neg x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    refine ⟨-r, fun i => by simpa using hr i, ?_⟩
    rw [map_neg, hx, ← Finset.sum_neg_distrib]
    simp only [Pi.neg_apply, neg_smul]

theorem smul_mem_locP {K M : Type} [Field K] [NumberField K] [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) M) (x : M) (a : K) (s t : 𝓞 K)
    (hs : s ∉ w.asIdeal) (hst : (s : K) * a = t) (hx : x ∈ L) : a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  refine ⟨s, hs, ?_⟩
  have h1 : s • a • x = t • x := by
    rw [← algebraMap_smul K s, ← algebraMap_smul K t, smul_smul]
    exact congrArg (· • _) hst
  rw [h1]
  exact L.smul_mem _ hx

theorem mem_localization_standardWeylLattice : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → (∀ x : F.O, ‖F.emb x‖ ≤ 1) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, Φ v ∈ F.latD lamW → (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  intro K _ _ l _ w e0 ι _ _ n lam lamW c F Φ hw hF hS hΦ v hv
  classical
  choose P fP b hb hspan hdual using fun τ => GlobalTheory.T.exists_integral_weylBasis_spanning_all_rings n (lam τ).natW (natW_anti (lam τ))

  let bK : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) K := fun τ i => MvPolynomial.map (Int.castRingHom K) (b τ i)
  let u : ∀ τ, P τ → MvPolynomial (Fin n × Fin n) (PadicAlgCl l) := fun τ i =>
    detPol (PadicAlgCl l) n ^ lamW τ (n - 1) * MvPolynomial.map (Int.castRingHom (PadicAlgCl l)) (b τ i)
  have hKspan := (tensorBasis K K ι n n P (fun τ => nablaSq K n (lam τ)) bK (fun τ => linInd_map K _ (hb τ))
    (fun τ => (hdual τ K).symm)).2
  have huind := (tensorBasis (PadicAlgCl l) (PadicAlgCl l) ι n n P _ u
    (fun τ => linInd_det _ _ (linInd_map (PadicAlgCl l) _ (hb τ))) (fun τ => rfl)).1
  have hbK : ∀ τ i, bK τ i ∈ nablaSq K n (lam τ) := fun τ i => by
    unfold nablaSq
    rw [hdual τ K]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmem : ∀ i : ∀ τ, P τ, (ten fun τ => bK τ (i τ)) ∈ VV K lam := fun i =>
    Submodule.subset_span ⟨_, fun τ => hbK τ (i τ), rfl⟩
  have hv0 : (v : Pol K ι n) ∈ Submodule.span K (Set.range fun i : ∀ τ, P τ => ten fun τ => bK τ (i τ)) := by
    have h2 : (v : Pol K ι n) ∈ tensorLat K K fun τ => nablaSq K n (lam τ) := v.2
    rw [← hKspan] at h2
    exact h2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv0
  have hveq : v = ∑ i, a i • (⟨_, hmem i⟩ : VV K lam) := by
    apply Subtype.ext
    rw [← ha]
    simp
  have hΦi : ∀ i, mulMap (PadicAlgCl l) n lamW (Φ ⟨_, hmem i⟩) = ten fun τ => u τ (i τ) := fun i => by
    obtain ⟨y, hy, hyΦ⟩ := hΦ (fun τ => bK τ (i τ)) ⟨_, hmem i⟩ (fun τ => hbK τ (i τ)) rfl
    rw [hyΦ, mulMap_tprod]
    congr 1
    funext τ
    rw [hy, liftPol, map_map_int]
  have hΦv : mulMap (PadicAlgCl l) n lamW (Φ v) = ∑ i, e0 (a i) • ten fun τ => u τ (i τ) := by
    rw [hveq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul, hΦi]
  obtain ⟨r, hr, hrv⟩ := latD_coords lamW F hF u (fun τ x0 hx0 => by
    rw [res_eq hS τ, GlobalTheory.T.mem_weylLattice_add_iff_det_pow_mul] at hx0
    obtain ⟨g, hg, rfl⟩ := hx0
    rw [hspan τ F.O] at hg
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F.O).1 hg
    refine ⟨d, ?_⟩
    rw [map_mul, map_pow, map_detPol, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [u, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_map_int]
    ring) hv
  have hra : ∀ i, e0 (a i) = r i :=
    (Fintype.linearIndependent_iffₛ.1 huind) (fun i => e0 (a i)) r (hΦv.symm.trans hrv)
  rw [← ha]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨s, hs, t, hst⟩ := (GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place K l w e0 hw (a i)).1 (hra i ▸ hr i)
  refine smul_mem_locP w _ _ _ s t hs hst (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
  refine ⟨MvPolynomial.map (Int.castRingHom (𝓞 K)) (b τ (i τ)), ?_, ?_⟩
  · unfold delSq
    rw [hspan τ (𝓞 K)]
    exact Submodule.subset_span ⟨_, rfl⟩
  · exact map_map_int (algebraMap (𝓞 K) K) _

end GlobalTheory.FrameRead.DelStd
