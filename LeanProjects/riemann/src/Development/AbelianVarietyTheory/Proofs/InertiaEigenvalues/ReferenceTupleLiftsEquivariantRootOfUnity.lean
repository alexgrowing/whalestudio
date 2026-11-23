import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option autoImplicit false

namespace GlobalTheory.ConjRefLift

section Scale

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {c : ℂ} (hc : c ≠ 0)
    {Ψ Ψ' Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ 1 Ψ Ψ') (e : ∀ g, Φ g = c⁻¹ * Ψ g)
    (e' : ∀ g, Φ' g = (τ c)⁻¹ * Ψ' g) : ConjFun O κ τ 1 Φ Φ' := by
  obtain ⟨⟨n, a, f, ha⟩, hall⟩ := h
  have hτc : τ c ≠ 0 := (map_ne_zero τ).2 hc
  refine ⟨⟨n, fun k => c⁻¹ * a k, f, fun g => ?_⟩, fun m b f' hb g => ?_⟩
  · rw [e g, ha g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hb' : Expands O κ Ψ (fun k => c * b k) f' := fun g => by
      have h1 := hb g
      rw [e g] at h1
      have h2 : Ψ g = c * (c⁻¹ * Ψ g) := by field_simp
      rw [h2, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e' g, hall m _ f' hb' g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, one_mul]
    field_simp

theorem conjFun_congr {Tp' : Type} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup) (O' : OMDat T.toCore R i Tp' tup')
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ}
    (hphi : O.phi (T.cE ((i : ℕ) + 1) O.s0) = O'.phi (T.cE ((i : ℕ) + 1) O'.s0)) (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands at h ⊢
  rw [← hphi]
  exact h

end Scale

set_option maxHeartbeats 2000000 in

theorem conjFun_lifts_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs c₀ hc₀ hc₀P
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hC D G Pl0 T0 A T R F κ v₀ hcore hT hio O i hpins
  have hEqO := (hphase hrow0).1
  have elev : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hMl]
  have hEq : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), elev]
    exact hEqO
  obtain ⟨ζ, z, hζ, -, hser⟩ :=
    GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin ⟨fw⟩ hio hQ i hpins hphase T0 id M hMp hMl hMe
  obtain ⟨nζ, hnζ, hζn⟩ := hζ
  obtain ⟨nc, hnc, hcn⟩ := hc₀
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0, hnζ.ne'] at hζn
  have hc0 : ((c₀ : M.c'.F) : ℂ) ≠ 0 := fun h0 => by simp [h0, hnc.ne'] at hcn
  refine ⟨(ζ * (c₀ : ℂ))⁻¹, ⟨nζ * nc, Nat.mul_pos hnζ hnc, ?_⟩, fun τ ta hta hB y y' hyy => ?_⟩
  · rw [inv_pow, mul_pow, pow_mul, hζn, one_pow, mul_comm nζ nc, pow_mul, hcn, one_pow, mul_one, inv_one]
  have hf : Fixes M.c' ta :=
    fixes_of_le (c := T.Q.c) ta fun x hx => Subtype.ext ((hta x).trans (hB.core ⟨x, hx⟩))
  obtain ⟨h, J', hR, -⟩ := (hMp.tuple A.μ0).reps
  choose x x' hxx hx hx' using fun k => hyy (h k)
  have hio' : ∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k)) := fun k =>
    GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB (x k) (x' k) (hxx k)
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hC D G Pl0 T0 A T R F κ v₀ hcore hT i T0 id M hMp A.μ0 x
  obtain ⟨f, hf2⟩ := hex
  have hfc := hf2.1
  have hfs := hf2.2
  have hfsec : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hP' := hc₀P τ ta hta hB hf x x' hio' f hfsec hfs
  have e1 := hser A.μ0 h J' hR y x hx f hfsec hfs
  have e2 := hser A.μ0 h J' hR y' x' hx' _ hP'.1 hP'.2
  dsimp only [id_eq] at e1 e2
  have hCM := GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB hf z f hfc hEq
  have hsm : ∀ (s : M.c'.F) (Fr : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') a b,
      rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (s • Fr)) a b =
        inC M.c' s * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z Fr) a b := by
    intro s Fr a b
    rw [map_smul, map_smulₛₗ]
    rfl
  have hcv : inC M.c' c₀ = (c₀ : ℂ) := rfl
  have htv : inC M.c' (ta c₀) = τ (c₀ : ℂ) := hta c₀
  have hτ0 : τ (c₀ : ℂ) ≠ 0 := (map_ne_zero τ).2 hc0
  refine conjFun_scale (O i) (κ i) τ hc0 (conjFun_congr M (O i) (GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1))) hCM)
    (fun g => ?_) (fun g => ?_)
  · beta_reduce
    rw [mul_assoc, e1 g]
    field_simp
  · beta_reduce
    have hs := hsm ((ta c₀ * c₀⁻¹)⁻¹) (galRul hf f) (M.dict g).1 (M.dict g).2
    rw [mul_assoc, e2 g]
    erw [hs]
    rw [map_inv₀, map_mul, map_inv₀, hcv, htv]
    field_simp

end GlobalTheory.ConjRefLift
