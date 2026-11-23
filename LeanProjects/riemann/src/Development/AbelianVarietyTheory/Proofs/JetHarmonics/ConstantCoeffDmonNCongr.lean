import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.NabJet
open MvPowerSeries

variable {k : Type} [CommRing k] {d n : ℕ}

theorem coeff_mul_congr (N : ℕ) (f g E : PS k n d)
    (h : ∀ a : Fin n × Fin d →₀ ℕ, a.degree ≤ N → coeff a f = coeff a g)
    (a : Fin n × Fin d →₀ ℕ) (ha : a.degree ≤ N) : coeff a (f * E) = coeff a (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = a.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]

theorem coeff_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (N : ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + 1 → coeff mo f = coeff mo g)
    (mo : Fin n × Fin d →₀ ℕ) (hmo : mo.degree ≤ N) :
    coeff mo (DofN F b v f) = coeff mo (DofN F b v g) := by
  classical
  unfold DofN
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add, Finsupp.degree_single]
  omega

theorem coeff_iterate_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (r : ℕ) :
    ∀ (N : ℕ) (f g : PS k n d),
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo ((DofN F b v)^[r] f) = coeff mo ((DofN F b v)^[r] g) := by
  induction r with
  | zero => intro N f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro N f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih N _ _ (coeff_DofN_congr F b v (N + r) f g h) mo hmo

theorem coeff_foldr_DofN_congr (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by
  induction L with
  | nil => intro N h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro N h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_DofN_congr F (cp l) (u l) (m l) N _ _ (ih (N + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem constantCoeff_DmonN_congr (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) :
    constantCoeff (DmonN F cp u m f) = constantCoeff (DmonN F cp u m g) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  unfold DmonN
  refine coeff_foldr_DofN_congr F cp u m f g _ 0 (fun mo' h' => h mo' ?_) 0 (by simp)
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum, zero_add] at h'

theorem isLinearMap_DofN (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) :
    IsLinearMap k (DofN F b v : PS k n d → PS k n d) := by
  constructor
  · intro f g
    unfold DofN
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  · intro c f
    unfold DofN
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem isLinearMap_iterate {M : Type} [AddCommGroup M] [Module k M] (φ : M → M) (hφ : IsLinearMap k φ) (r : ℕ) :
    IsLinearMap k φ^[r] := by
  induction r with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ r ih =>
    constructor
    · intro f g
      simp only [Function.iterate_succ_apply, hφ.map_add, ih.map_add]
    · intro c f
      simp only [Function.iterate_succ_apply, hφ.map_smul, ih.map_smul]

theorem isLinearMap_DmonN (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) : IsLinearMap k (DmonN F cp u m : PS k n d → PS k n d) := by
  unfold DmonN
  induction (Finset.univ : Finset Ix).toList with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l L ih =>
    have hl := isLinearMap_iterate _ (isLinearMap_DofN F (cp l) (u l)) (m l)
    constructor
    · intro f g
      simp only [List.foldr_cons]
      rw [ih.map_add, hl.map_add]
    · intro c f
      simp only [List.foldr_cons]
      rw [ih.map_smul, hl.map_smul]

theorem constantCoeff_DpolyN_eq (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (P : MvPolynomial Ix k) (f : PS k n d) (S : Finset (Ix →₀ ℕ)) (hS : P.support ⊆ S) :
    constantCoeff (DpolyN F cp u P f) = ∑ m ∈ S, P.coeff m * constantCoeff (DmonN F cp u m f) := by
  unfold DpolyN
  rw [map_sum]
  simp only [map_mul, constantCoeff_C]
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]

end GlobalTheory.PowGerm.NabJet

namespace GlobalTheory.PowGerm
open MvPowerSeries

theorem nabJet : NabJetSt := by
  intro R _ d O _ _ B k _ _ _ h w0 q n Ix _ cp u
  classical
  refine ⟨fun P f g hfg => ?_, fun P J _ c f => ?_, fun f J _ c P => ?_⟩
  · unfold nabValN
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine NabJet.constantCoeff_DmonN_congr _ cp u m _ _ fun mo hmo => ?_
    refine NabJet.coeff_mul_congr P.totalDegree f g _ hfg mo (hmo.trans ?_)
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.degree_apply]
  · unfold nabValN
    simp only [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hl := NabJet.isLinearMap_DmonN (B.FK k) cp u m
    rw [Finset.sum_mul, ← IsLinearMap.mk'_apply hl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, IsLinearMap.mk'_apply, smul_eq_C_mul, map_mul, constantCoeff_C]
    ring
  · unfold nabValN
    set S : Finset (Ix →₀ ℕ) := (∑ j, c j • P j).support ∪ Finset.univ.biUnion fun j => (P j).support with hS
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u _ _ S Finset.subset_union_left]
    have hj : ∀ j, (P j).support ⊆ S := fun j =>
      (Finset.subset_biUnion_of_mem (fun j => (P j).support) (Finset.mem_univ j)).trans Finset.subset_union_right
    simp only [fun j => NabJet.constantCoeff_DpolyN_eq (B.FK k) cp u (P j)
      (f * FB.expS k ((q : k) • ∑ b, ev ![pt k d b] (B.hL k h w0))) S (hj j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]

end GlobalTheory.PowGerm
