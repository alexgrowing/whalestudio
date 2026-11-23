import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityCoverFunctionReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnityStatement

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRefTup

section IdempotentCombination
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

theorem conj_sum_eq (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ}
    {b : Fin m → ℂ} {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {g : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (ha : Expands O κ Φ a f) (hb : Expands O κ Φ b g) (x : GA D (Wc D i)) :
    ∑ k, τ (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) x) =
    ∑ k, τ (b k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (g k : T.toCore.R ((i : ℕ) + 1)) x) := by
  have h0 : Expands O κ (fun _ => 0) (Fin.append a (fun k => -b k)) (Fin.append f g) := by
    intro y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← ha y, ← hb y, add_neg_cancel]
  have h1 := hZ.2 _ _ _ h0 x
  rw [Fin.sum_univ_add] at h1
  simp only [Fin.append_left, Fin.append_right, map_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at h1
  linear_combination (-1 : ℂ) * h1

theorem conjFun_lin (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ Φ' Ψ Ψ' : GA D (Wc D i) → ℂ}
    (h1 : ConjFun O κ τ 1 Φ Φ') (h2 : ConjFun O κ τ 1 Ψ Ψ') (c d : ℂ) :
    ConjFun O κ τ 1 (fun x => c * Φ x + d * Ψ x) (fun x => τ c * Φ' x + τ d * Ψ' x) := by
  obtain ⟨n, a, f, ha⟩ := h1.1
  obtain ⟨m, b, g, hb⟩ := h2.1
  have hs : Expands O κ (fun x => c * Φ x + d * Ψ x) (Fin.append (fun k => c * a k) (fun k => d * b k)) (Fin.append f g) := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ha x, hb x, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, hs⟩, fun N e h he x => ?_⟩
  simp only [one_mul]
  rw [conj_sum_eq O κ τ hZ he hs x, Fin.sum_univ_add, h1.2 _ _ _ ha x, h2.2 _ _ _ hb x]
  simp only [Fin.append_left, Fin.append_right, one_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem conjFun_sum (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) : ∀ (n : ℕ) (α : Fin n → ℂ)
    (Φ Φ' : Fin n → GA D (Wc D i) → ℂ), (∀ k, ConjFun O κ τ 1 (Φ k) (Φ' k)) →
    ConjFun O κ τ 1 (fun g => ∑ k, α k * Φ k g) (fun g => ∑ k, τ (α k) * Φ' k g) := by
  intro n
  induction n with
  | zero => intro α Φ Φ' _; simpa using hZ
  | succ n ih =>
    intro α Φ Φ' hk
    have h := conjFun_lin O κ τ hZ (hk 0) (ih (fun k => α k.succ) (fun k => Φ k.succ) (fun k => Φ' k.succ)
      (fun k => hk k.succ)) (α 0) 1
    simp only [map_one, one_mul] at h
    simpa only [Fin.sum_univ_succ] using h

end IdempotentCombination

set_option maxHeartbeats 1000000 in

theorem conjFun_base_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∀ y y' : (R.HV i A.μ0).H, ConjForm R i τ c A.μ0 A.μ0 y y' → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase c hc
  have h2 := GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hcore hfin hfw hQ i hpins
  obtain ⟨M, hMp, hMl, hMe, hMn, hMc, hMx, hMs⟩ := h2
  have h3 := GlobalTheory.T.exists_rootOfUnity_coverFunction_reference_tuple hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs
  have h4 := GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs h3.choose h3.choose_spec.1 h3.choose_spec.2
  refine ⟨h4.choose, h4.choose_spec.1, fun τ hB y y' hyy => ?_⟩
  have hP := h4.choose_spec.2
  let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  haveI := hMn
  let ta : M.c'.F ≃+* M.c'.F := (τa.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => AlgEquiv.restrictNormal_commutes τa M.c'.F a
  have hct : ConjTup R τ A.μ0 A.μ0 := by
    refine ⟨rfl, fun x => ?_⟩
    have h1 := hcore.lev.xi A.μ0
    rw [hcore.lev.xi_base] at h1
    rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x]
    simp
  have h5 := GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hcore hfw i T0 id M hMp τ ta hta hB c ((hMe c).1 hc) hMx A.μ0 A.μ0 hct y y' hyy
  obtain ⟨n, α, ys, ys', hy, hy', hk⟩ := h5
  have hZ : ConjFun (O i) (κ i) τ 1 (fun _ => 0) (fun _ => 0) := by
    have := hP τ ta hta hB 0 0 (fun h => ⟨0, 0, by simp, by rw [map_zero, map_zero]; rfl, by rw [map_zero, map_zero]; rfl⟩)
    simpa using this
  have hL := conjFun_sum (O i) (κ i) τ hZ n α
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys k) (v₀ i (sg0 D A)) g)
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys' k) (v₀ i (sg0 D A)) g) (fun k => hP τ ta hta hB (ys k) (ys' k) (hk k))
  subst hy hy'
  convert hL using 2 with g g
  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.ConjRefTup
