import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatDatumRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureTensorOTransSumLin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ExportSeries (Base Twist PairRep detChar twistBy series)

noncomputable section

namespace GlobalTheory.ConjGen

open GlobalTheory.ConjCombine

section CFAux

variable {X Bt : Type} {φ : Bt → X → ℂ} {τ : ℂ ≃+* ℂ}

theorem cf_one_of {ζ : ℂ} (hζ : ζ ≠ 0) {Φ Φ' : X → ℂ} (h : CF φ τ ζ Φ Φ') :
    CF φ τ 1 Φ (fun g => ζ⁻¹ * Φ' g) := by
  refine ⟨h.1, fun n a F ha g => ?_⟩
  show ζ⁻¹ * Φ' g = _
  rw [h.2 n a F ha g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [one_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]

theorem cf_of_exp {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') (ζ : ℂ) {Φ Φ' : X → ℂ} {n : ℕ} {b : Fin n → ℂ} {F : Fin n → Bt}
    (hb : Exp φ Φ b F) (hb' : Exp φ Φ' (fun k => ζ * τ (b k)) F) : CF φ τ ζ Φ Φ' := by
  refine ⟨⟨n, b, F, hb⟩, fun m a G ha g => ?_⟩
  rw [hb' g]
  have hw := conj_wd h0 ha hb g
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [hw]

theorem cf_comp {ζ : ℂ} (hζ : ζ ≠ 0) {Φ Φ' : X → ℂ} (h : CF φ τ ζ Φ Φ') (r : X → X) (M : Bt → Bt) {χ : ℂ}
    (hχ : τ χ = χ) (hr : ∀ F x, φ F (r x) = χ⁻¹ * φ (M F) x) : CF φ τ ζ (fun x => Φ (r x)) (fun x => Φ' (r x)) := by
  obtain ⟨n, a, F, ha⟩ := h.1
  refine cf_of_exp (cf_one_of hζ h) ζ (b := fun k => χ⁻¹ * a k) (F := fun k => M (F k)) (fun x => ?_) (fun x => ?_)
  · rw [ha (r x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [hr]
    ring
  · rw [h.2 n a F ha (r x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [hr, map_mul, map_inv₀, hχ]
    ring

theorem cf_sum {ζ : ℂ} (hζ : ζ ≠ 0) {Ψ Ψ' : X → ℂ} (h0 : CF φ τ ζ Ψ Ψ') {ι : Type} [Fintype ι] (β : ι → ℂ)
    (Φs Φs' : ι → X → ℂ) (h : ∀ p, CF φ τ ζ (Φs p) (Φs' p)) :
    CF φ τ ζ (fun g => ∑ p, β p * Φs p g) (fun g => ∑ p, τ (β p) * Φs' p g) := by
  let e := (Fintype.equivFin ι).symm
  have hc := conj_comb (cf_one_of hζ h0) (fun j => β (e j)) (fun j => Φs (e j)) (fun j g => ζ⁻¹ * Φs' (e j) g)
    (fun j => cf_one_of hζ (h (e j))) ζ
  have e1 : (fun g => ∑ j, β (e j) * Φs (e j) g) = fun g => ∑ p, β p * Φs p g :=
    funext fun g => Equiv.sum_comp e (fun p => β p * Φs p g)
  have e2 : (fun g => ζ * ∑ j, τ (β (e j)) * (ζ⁻¹ * Φs' (e j) g)) = fun g => ∑ p, τ (β p) * Φs' p g := by
    funext g
    rw [Equiv.sum_comp e (fun p => τ (β p) * (ζ⁻¹ * Φs' p g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_left_comm, ← mul_assoc ζ, mul_inv_cancel₀ hζ, one_mul]
  rw [e1, e2] at hc
  exact hc

theorem cf_smul {ζ : ℂ} (hζ : ζ ≠ 0) {Φ Φ' : X → ℂ} (h : CF φ τ ζ Φ Φ') (d : ℂ) :
    CF φ τ ζ (fun g => d * Φ g) (fun g => τ d * Φ' g) := by
  have := cf_sum hζ h (β := fun _ : Unit => d) (fun _ => Φ) (fun _ => Φ') (fun _ => h)
  simpa using this

end CFAux

section Rt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_mul_right (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) {τ : ℂ ≃+* ℂ} (hτ : FixBase T R i τ)
    (hE : O.EquivAt κ (T.cE ((i : ℕ) + 1) O.s0)) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) {ζ : ℂ} (hζ : ζ ≠ 0)
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O κ τ ζ (fun x => Φ (x * k)) (fun x => Φ' (x * k)) := by
  rw [GlobalTheory.ConjClassSum.conjFun_iff] at h ⊢
  set χ : ℂ := ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) with hχd
  have hχ0 : χ ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ => Units.ne_zero _
  have hτχ : τ χ = χ := by
    rw [hχd, map_prod]
    exact Finset.prod_congr rfl fun PP _ => hτ.chi PP.1 PP.2 _
  refine cf_comp hζ h (fun x => x * k)
    (fun F => ⟨actLev T.toCore.Q.c O.lev2 g (F : T.toCore.R ((i : ℕ) + 1)), (hE g k hk F F.2).1⟩) hτχ fun F x => ?_
  have e := (hE g k hk F F.2).2 x
  change _ = χ⁻¹ * (_ * O.phi _ (actLev T.toCore.Q.c O.lev2 g (F : T.toCore.R ((i : ℕ) + 1))) x)
  rw [e, ← hχd]
  field_simp

end Rt

section Gen

variable {D : D7} {S T : HSp D}

theorem gen_eq_series {B : Base S T} (hB : B.Good) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω ω' : PairRep S T}
    (hω : B.IsWeil 1 ω) (hω' : B.IsWeil ψ.chi ω') (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    B.gen ω ψ h P g = ((detChar S ψ.chi h : Circle) : ℂ) * series B.F ω' (B.vecFlat ψ) h P g := by
  have hf : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat ψ) P) := GlobalTheory.ExportSeries.Base.isThetaFunO_fock_vecAt hB hQ _ P
  have ho : IsWeilDatumO B.F.ψ S T (B.mu * 1) (B.mu * 1 * B.eta⁻¹) ω := hω
  have ho' : IsWeilDatumO B.F.ψ S T (B.mu * 1 * ψ.chi) (B.mu * 1 * B.eta⁻¹ * ψ.chi) ω' := by
    have e1 : B.mu * 1 * ψ.chi = B.mu * ψ.chi := by rw [mul_one]
    have e2 : B.mu * 1 * B.eta⁻¹ * ψ.chi = B.mu * ψ.chi * B.eta⁻¹ := by rw [mul_one, mul_right_comm]
    rw [e1, e2]
    exact hω'
  have key := GlobalTheory.SplitChange.twist_eq ho hψ.isHeckeChar hψ.real ho' (GlobalTheory.ExportSeries.muVal_detChar S hψ.real)
    (GlobalTheory.ExportSeries.muVal_detChar T hψ.real) h g hf
  have hS : ((detChar S ψ.chi h : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [GlobalTheory.ExportSeries.Base.gen, LinearMap.comp_apply, GlobalTheory.ExportSeries.twistBy_apply, GlobalTheory.ExportSeries.series_apply]
  rw [key, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem levJ_eq (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  unfold GlobalTheory.ExportSeries.Base.levJ GlobalTheory.ExportSeries.Base.levS
  rw [hQ]
  rfl

theorem series_weil {B : Base S T} (hB : B.Good) {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {ω ω' : PairRep S T}
    (hω : B.IsWeil ψ.chi ω) (hω' : B.IsWeil ψ.chi ω') (h : GA D S) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat ψ) h P = series B.F ω' (B.vecFlat ψ) h P := by
  funext g
  have hf : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat ψ) P) := GlobalTheory.ExportSeries.Base.isThetaFunO_fock_vecAt hB hQ _ P
  rw [GlobalTheory.ExportSeries.series_apply, GlobalTheory.ExportSeries.series_apply,
    GlobalTheory.WeilUniq.weilDatum_unique D _ hB.frame.vac.1 S T _ _ ω ω' hω hω' (h, g) _ hf]

end Gen

section Sum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem isThetaFunO_flat {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good) (hBo : BaseOf R i B)
    {ψ : Twist D Circle} {t : T0} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) (ht : IsTupOf R B ψ t) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsFlatVec R i t f) : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) f := by
  rw [GlobalTheory.FlatVecSum.eq_vecFlat_princ hBo ht hC.lev hB hψ hQ hf]
  exact GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
    (GlobalTheory.ExportSeries.Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ _) hB.frame.vac.2.theta

theorem series_vecFlat_eq_sum {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hBo : BaseOf R i B) [Fintype B.G.P.H] (k : B.G.P.H → GA D (Wc D i))
    (hk : ∀ p, Lev.IsLevelLift (Wc D i) B.F.βT B.G.levT p.1 (k p)) {ψ : Twist D Circle} {t : T0} (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ht : IsTupOf R B ψ t) {f : WO (Vc D i) (Wc D i) → ℂ} (hf : IsFlatVec R i t f)
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)) :
    series B.F (R.ωP i t) (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) w) g =
      ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * ser R i t f u h w (g * k p) := by
  have hω : B.IsWeil ψ.chi (R.ωP i t) := hBo.isWeil hC.thP.ωP ht
  have ho : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) (B.mu * ψ.chi) (B.mu * ψ.chi * B.eta⁻¹) (R.ωP i t) := hω
  have hθ := hB.frame.vac.2.inf
  have hstd : IsStdChar D B.F.ψ (-1) := hB.frame.vac.1
  have hft := isThetaFunO_flat hC hB hBo hψ hQ ht hf
  have hv := ((GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A Ks R F hC i B hB hBo).2.2 k hk).2 ψ t f hψ hQ ht hf
  set P := R.ioP i (PiTensorProduct.tprod ℂ u) w with hP
  have hmove : ∀ p, (R.ωP i t) (1, k p) (B.F.fock f P) = B.F.fock ((R.ωP i t) (1, k p) f) P := fun p => by
    have hkf : k p ∈ GfC (Wc D i) := (hk p).1
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) ho hθ (fun _ => 1) (fun _ => 1)
      (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT 1 (k p)
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite B.F.θ τ (one_mem (GfC (Vc D i)))])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hkf])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite B.F.θ τ (one_mem (GfC (Vc D i))), Matrix.one_mul])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hkf]) _ hft P).2
  have hsum := (GlobalTheory.SingleDatum.pureTensorO_finsetSum hstd hθ (fun _ => 1) (fun τ => (B.F.BS τ).val) B.F.sT B.F.BT
    Finset.univ (fun p => (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) (fun p => (R.ωP i t) (1, k p) f)
    (fun p => ho.om_pres _ f hft) P).2
  rw [GlobalTheory.ExportSeries.series_apply, hv]
  change (R.ωP i t) (h, g) (B.F.fock (∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • (R.ωP i t) (1, k p) f) P) 0 = _
  rw [show B.F.fock (∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • (R.ωP i t) (1, k p) f) P =
      ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) • B.F.fock ((R.ωP i t) (1, k p) f) P from hsum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hmove p, ← hBo.series_eq_ser t f u (h) w, GlobalTheory.ExportSeries.series_apply, ← Module.End.mul_apply, ← map_mul,
    Prod.mk_mul_mk, mul_one]

end Sum

set_option maxHeartbeats 4000000 in

theorem conj_gen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV →
    GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
    PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c →
    ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
    ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ ω : PairRep (Vc D i) (Wc D i), B.IsWeil 1 ω →
    ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → FixDat B τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧
    ∀ (ψ ψ' : Twist D Circle) (t t' : T0), ψ.Good → ψ'.Good → B.admitted ψ.Q → B.admitted ψ'.Q → IsTupOf R B ψ t → IsTupOf R B ψ' t' →
    ConjChar τ ψ ψ' → ∃ s : (AE D)ˣ, (∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' →
      ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ))
        (ph i • B.gen ω ψ h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)))
        (ph i • B.gen ω ψ' h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x')))) ∧
    ∀ ω₁ ω₁' : PairRep (Vc D i) (Wc D i), B.IsWeil ψ.chi ω₁ → B.IsWeil ψ'.chi ω₁' →
    ∀ {I : Type} [Fintype I] (hs : I → GA D (Vc D i)), (∀ j, hs j ∈ GfC (Vc D i)) →
    ∀ Fm Fm' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank,
    (∀ j, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧
      Fm (GlobalTheory.ExportSeries.finPt (Vc D i) (hs j)) = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧
      Fm' (GlobalTheory.ExportSeries.finPt (Vc D i) (hs j)) = R.ioP i (PiTensorProduct.tprod ℂ u) (c x')) →
    ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ))
      (ph i • B.classSum ω₁ ψ hs Fm) (ph i • B.classSum ω₁' ψ' hs Fm') := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hT0 hFW hio hQG i hOP hPT c hc u hu B hB hBo ω hω τ hτ hfix
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hE : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  obtain ⟨ζ0, hζ0, hgb⟩ := GlobalTheory.T.conjugate_thetaSeries_flatDatum_rootOfUnity hCI D G Pl0 T0 A T R F κ v₀ O ph hnV hC hT0 ⟨fw⟩ hio hQG i hOP hPT c hc u hu τ hτ
  refine ⟨ζ0, hζ0, fun ψ ψ' t t' hψ hψ' hQ hQ' ht ht' hcc => ?_⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t).1
  obtain ⟨f', hf'⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t').1
  obtain ⟨s, hs⟩ := hgb t t' (conjTup_of R ht ht' hcc hfix) f f' hf hf'
  set ζ := ζ0 * ((R.xi t' s : Circle) : ℂ) with hζd
  have hζ : ζ ≠ 0 := by
    obtain ⟨n, hn, hpow⟩ := hζ0
    refine mul_ne_zero (fun h0 => ?_) (Circle.coe_ne_zero _)
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  obtain ⟨hfin, ⟨k, hk⟩, hsum⟩ := GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A _ R F hC i B hB hBo
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  obtain ⟨hk0, -⟩ := hsum k fun p => (hk p).1
  choose g0 hg0 using hk0
  have hlift : ∀ p, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm (g0 p))) (k p) := fun p => by
    exact (congrArg (fun z => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) z (k p))
      (R.eG.apply_symm_apply (g0 p))).mpr (hg0 p)
  have hrt : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∀ p, ConjFun (O i) (κ i) τ ζ
      (fun g => ph i * ser R i t f u h (c x) (g * k p)) (fun g => ph i * ser R i t' f' u h (c x') (g * k p)) :=
    fun h hh x x' hx p => conjFun_mul_right (O i) (κ i) hτ hE (hlift p) hζ (hs h hh x x' hx)
  have hcp : ∀ p, τ ((((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) = (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) := fun p => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix.2.1 p]
  obtain ⟨h₀, x₀, hh₀, hx₀⟩ : ∃ (h₀ : GA D (Vc D i)) (x₀ : VsV D i ℂ), h₀ ∈ GfC (Vc D i) ∧ ConjVec i τ x₀ x₀ := by
    refine ⟨1, 0, one_mem _, ?_⟩
    unfold ConjVec
    simp
  have hCF0 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hs h₀ hh₀ x₀ x₀ hx₀)
  refine ⟨s, fun h hh x x' hx => ?_, fun ω₁ ω₁' hω₁ hω₁' I _ hs' hfs Fm Fm' hFm => ?_⟩
  · set dS : ℂ := ((detChar (Vc D i) ψ.chi h : Circle) : ℂ) with hdS
    set dS' : ℂ := ((detChar (Vc D i) ψ'.chi h : Circle) : ℂ) with hdS'
    have e1 : (ph i • B.gen ω ψ h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) =
        fun g => ∑ p, (dS * (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t f u h (c x) (g * k p)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, gen_eq_series hB hψ hQ hω (hBo.isWeil hC.thP.ωP ht),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : (ph i • B.gen ω ψ' h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) =
        fun g => ∑ p, τ (dS * (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t' f' u h (c x') (g * k p)) := by
      have hd : τ dS = dS' := (hcc.2 _).symm
      funext g
      rw [Pi.smul_apply, smul_eq_mul, gen_eq_series hB hψ' hQ' hω (hBo.isWeil hC.thP.ωP ht'),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, hd, hcp]
      ring
    rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
    exact cf_sum hζ hCF0 _ _ _ fun p => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hrt h hh x x' hx p)
  · choose x x' hx hFx hFx' using hFm
    have hJ : B.levJ ψ' = B.levJ ψ := levJ_eq B hcc.1
    set n : I → ℂ := fun j => ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (B.levJ ψ)
      (GlobalTheory.ExportSeries.finPt (Vc D i) (hs' j))) : ℕ) : ℂ) with hn
    have e1 : (ph i • B.classSum ω₁ ψ hs' Fm) = fun g => ∑ q : I × B.G.P.H,
        ((n q.1)⁻¹ * (((B.G.P.chi q.2)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t f u (hs' q.1) (c (x q.1)) (g * k q.2)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ExportSeries.Base.classSum_apply, Fintype.sum_prod_type, Finset.sum_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hFx j, series_weil hB hQ hω₁ (hBo.isWeil hC.thP.ωP ht),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : (ph i • B.classSum ω₁' ψ' hs' Fm') = fun g => ∑ q : I × B.G.P.H,
        τ ((n q.1)⁻¹ * (((B.G.P.chi q.2)⁻¹ : ℂˣ) : ℂ)) * (ph i * ser R i t' f' u (hs' q.1) (c (x' q.1)) (g * k q.2)) := by
      funext g
      rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ExportSeries.Base.classSum_apply, Fintype.sum_prod_type, Finset.sum_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hFx' j, series_weil hB hQ' hω₁' (hBo.isWeil hC.thP.ωP ht'),
        series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum, Finset.mul_sum, hJ]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, map_inv₀, map_natCast, hcp]
      ring
    rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
    exact cf_sum hζ hCF0 _ _ _ fun q => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1
      (hrt (hs' q.1) (hfs q.1) (x q.1) (x' q.1) (hx q.1) q.2)

end GlobalTheory.ConjGen
