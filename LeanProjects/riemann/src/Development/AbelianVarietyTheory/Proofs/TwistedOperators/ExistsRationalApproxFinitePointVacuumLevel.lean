import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinApprox

variable {D : D7}

def finRat (D : D7) : D.host.E →+ AE D := TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 1)

theorem finRat_apply (a : D.host.E) : finRat D a = pairA D.host.F 0 1 ⊗ₜ[D.host.F] a := rfl

theorem finRat_eq (a : D.host.E) : incA D a - pairA D.host.F 1 0 ⊗ₜ[D.host.F] a = finRat D a := by
  have h1 : (1 : AF D.host.F) = pairA D.host.F 1 0 + pairA D.host.F 0 1 :=
    Prod.ext (add_zero (1 : Ainf D.host.F)).symm (zero_add (1 : Af D.host.F)).symm
  rw [finRat_apply]
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] a - _ = _
  rw [h1, TensorProduct.add_tmul, add_sub_cancel_left]

private theorem infPart_tmul' (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem infPart_finRat (a : D.host.E) : infPart D (finRat D a) = 0 := by
  rw [finRat_apply, infPart_tmul']
  have h0 : fstA D.host.F (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (w : AE D) :
    w = ∑ i, (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr w i ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).sum_repr w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fstA_basis_repr_eq_zero_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) (i : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i) = 0 := by
  have h1 : infPart D z = ∑ j, fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z j) •
      Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E) j := by
    conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [infPart_tmul', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 := congrArg
    (fun v => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr v i) h1
  simp only [hz, map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_sum_self] at h2
  exact h2.symm

private theorem eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) :
    z = ∑ i, pairA D.host.F 0 (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Prod.ext (fstA_basis_repr_eq_zero_of_infPart_eq_zero hz i) rfl

theorem mem_closure_finRat {z : AE D} (hz : infPart D z = 0) : z ∈ closure (Set.range (finRat D)) := by
  have hd : DenseRange (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) =>
      ⇑(algebraMap D.host.F (Af D.host.F))) :=
    DenseRange.piMap fun _ => AdeleCharTwist.denseRange_fin
  have hc : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
    refine continuous_finset_sum _ fun i _ => ?_
    have h1 : Continuous fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
      have he : (fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) =
          fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact Continuous.smul (M := AF D.host.F) (X := AE D) continuous_id continuous_const
    have h2 : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => pairA D.host.F 0 (y i) := by
      show Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => ((0 : Ainf D.host.F), y i)
      exact continuous_const.prodMk (continuous_apply i)
    exact h1.comp h2
  have hm : Set.MapsTo (fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i)
      (Set.range (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) => ⇑(algebraMap D.host.F (Af D.host.F))))
      (Set.range (finRat D)) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨∑ i, q i • Module.finBasis D.host.F D.host.E i, ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRat_apply, ← TensorProduct.smul_tmul]
    congr 1
    exact Prod.ext (smul_zero (q i)) ((Algebra.smul_def (q i) (1 : Af D.host.F)).trans (mul_one _))
  have hz' := map_mem_closure hc (hd fun i => sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) hm
  rw [eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero hz]
  exact hz'

theorem mem_closure_mat {m n : ℕ} {y : Mx D m n} (hy : y.map (infPart D) = 0) :
    y ∈ closure (Set.range fun ℓ : Matrix (Fin m) (Fin n) D.host.E => (ℓ.map (finRat D) : Mx D m n)) := by
  have h1 : ∀ i j, y i j ∈ closure (Set.range (finRat D)) := fun i j =>
    mem_closure_finRat (by simpa using congrFun (congrFun hy i) j)
  have h2 : (y : Fin m → Fin n → AE D) ∈
      closure (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => Set.range (finRat D)) := by
    refine mem_closure_pi.mpr fun i _ => ?_
    refine mem_closure_pi.mpr fun j _ => ?_
    exact h1 i j
  refine closure_mono ?_ h2
  intro x hx
  have hx' : ∀ i j, ∃ a, finRat D a = x i j := fun i j => hx i (Set.mem_univ i) j (Set.mem_univ j)
  choose ℓ hℓ using hx'
  exact ⟨Matrix.of ℓ, by ext i j; exact hℓ i j⟩

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]

private theorem continuous_actO_one {S T : HSp D} (h : GA D T) : Continuous (actO S T 1 h) := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold actO
  fun_prop

theorem exists_approx {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (g : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    ∃ (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), w.map (infPart D) = 0 ∧ heisO ψ S T w f = f ∧
      x = actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) + w := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hy : (actO S T 1 g x).map (infPart D) = 0 := actO_fin 1 g hx
  have hVo : IsOpen {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} :=
    hUo.preimage ((continuous_actO_one (S := S) g⁻¹).comp (continuous_const.sub continuous_id))
  have h0 : actO S T 1 g⁻¹ 0 = 0 := by
    have h00 := GlobalTheory.HeckeVacuum.act_sub g⁻¹ (0 : WO S T) 0
    rwa [sub_self, sub_self] at h00
  have hyV : actO S T 1 g x ∈ {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} := by
    show actO S T 1 g⁻¹ (actO S T 1 g x - actO S T 1 g x) ∈ U
    rw [sub_self, h0]
    exact U.zero_mem
  obtain ⟨_, hvV, ℓ, rfl⟩ := mem_closure_iff.mp (mem_closure_mat (m := T.rank) (n := S.rank) hy) _ hVo hyV
  have hrat : ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ = (ℓ.map (finRat D) : WO S T) := by
    ext i j
    exact finRat_eq (ℓ i j)
  have key : actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) =
      actO S T 1 g⁻¹ (ℓ.map (finRat D)) := congrArg _ hrat
  have hw : (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))).map (infPart D) = 0 := by
    refine actO_fin 1 g⁻¹ ?_
    ext i j
    have hij : infPart D (actO S T 1 g x i j) = 0 := by simpa using congrFun (congrFun hy i) j
    simp [hij, infPart_finRat]
  refine ⟨ℓ, actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D)), hw,
    hU (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))) hvV hw, ?_⟩
  rw [key, GlobalTheory.HeckeVacuum.act_sub, add_sub_cancel, ← GlobalTheory.HeckeVacuum.act_mul, inv_mul_cancel,
    GlobalTheory.HeckeVacuum.act_one]

theorem exists_rat_approx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  intro D G _ _ Pl0 T0 A T _ R _ _ hP i g x hx
  exact exists_approx (hP.vP i A.μ0).1.2.theta g hx

end GlobalTheory.FinApprox
