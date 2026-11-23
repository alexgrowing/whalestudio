import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

noncomputable section

namespace GlobalTheory.Mem.PlaceVal

section General

open Formalism.L2.DIV Formalism.BasicNotions Formalism.BasicNotions.TH

theorem exists_ext_pol {K K' I W : Type} [Field K] [Field K'] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ} (ι : K →+* K')
    (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) (U : Submodule K (MvPolynomial I K)) (c : U →ₛₗ[σ] W) :
    ∃ c' : MvPolynomial I K' →ₛₗ[σ'] W, ∀ v : U, c' (MvPolynomial.map ι (v : MvPolynomial I K)) = c v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let _ : Module K' W := Module.compHom W σ'
  let f : MvPolynomial I K' →ₗ[K'] W :=
    (MvPolynomial.basisMonomials I K').constr K' fun m => c (π (MvPolynomial.monomial m 1))
  have hf : ∀ m, f (MvPolynomial.monomial m 1) = c (π (MvPolynomial.monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials I K').constr_basis K' (fun m => c (π (MvPolynomial.monomial m 1))) m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have key : ∀ p : MvPolynomial I K, f (MvPolynomial.map ι p) = c (π p) := fun p => by
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.monomial m (1 : K') := by
        rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e1, f.map_smul, hf, e2, π.map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun a p => f.map_smul a p }, fun v => (key v).trans ?_⟩
  exact congrArg c (LinearMap.congr_fun hπ v)

theorem exists_ext_VV {K K' I W : Type} [Field K] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (ι : K →+* K') (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) {n : ℕ} (lam : I → DomWeight n) (c : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c v := by
  obtain ⟨c', hc⟩ := exists_ext_pol ι σ' hσ (VV K lam) c
  exact ⟨c'.comp (VV K' lam).subtype, fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, hc v⟩⟩

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem exists_coef_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ _ i K' _ jL σ' hσ
  obtain ⟨gramR, c0R, c0L, hT⟩ := hR.fam.tie
  obtain ⟨c0', hc⟩ := exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal⟩

end GlobalTheory.Mem.PlaceVal
