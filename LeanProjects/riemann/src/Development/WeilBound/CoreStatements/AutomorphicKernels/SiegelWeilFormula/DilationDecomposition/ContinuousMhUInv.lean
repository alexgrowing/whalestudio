import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil.Tb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : SD σ)

abbrev bA : Module.Basis (Fin 2) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) d.bs

abbrev Ix : Type := Fin d.m × Fin d.n × Fin 2

theorem tmul_eq (c : AF F) (k : Fin 2) : c ⊗ₜ[F] d.bs k = c • bA d k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem cmb_eq (c : Ix d → AF F) (i : Fin d.m) (j : Fin d.n) : d.cmb c i j = ∑ k, c (i, j, k) • bA d k := by
  simp only [SD.cmb, tmul_eq]

theorem cmb_crd (Y : Mx F E d.m d.n) : d.cmb (d.crd Y) = Y := by
  funext i j
  rw [cmb_eq]
  exact (bA d).sum_repr (Y i j)

theorem crd_cmb (c : Ix d → AF F) : d.crd (d.cmb c) = c := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((bA d).repr (d.cmb c i j)) k = c (i, j, k)
  rw [cmb_eq]
  exact congrFun ((bA d).repr_sum_self fun k => c (i, j, k)) k

def mh (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) : Matrix (Ix d) (Ix d) (AF F) :=
  fun p q => if p.2.1 = q.2.1 then (bA d).repr (M p.1 q.1 * bA d q.2.2) p.2.2 else 0

theorem crd_mul (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) (Y : Mx F E d.m d.n) :
    d.crd (M * Y) = mh d M *ᵥ d.crd Y := by
  funext p
  obtain ⟨i, j, k⟩ := p
  have hY : ∀ i', Y i' j = ∑ k', d.crd Y (i', j, k') • bA d k' := fun i' => ((bA d).sum_repr (Y i' j)).symm
  show ((bA d).repr ((M * Y) i j)) k = _
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun i' _ => by rw [hY i']]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mh, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [if_true]
  exact Finset.sum_congr rfl fun k' _ => mul_comm _ _

theorem mulVec_ext {A B : Matrix (Ix d) (Ix d) (AF F)} (h : ∀ c, A *ᵥ c = B *ᵥ c) : A = B := by
  ext p q
  have := congrFun (h (Pi.single q 1)) p
  simpa [Matrix.mulVec_single_one] using this

theorem mh_mul (M N : Matrix (Fin d.m) (Fin d.m) (AE F E)) : mh d (M * N) = mh d M * mh d N :=
  mulVec_ext d fun c => by
    conv_lhs => rw [← crd_cmb d c]
    conv_rhs => rw [← crd_cmb d c]
    rw [← crd_mul, ← Matrix.mulVec_mulVec, ← crd_mul, ← crd_mul, Matrix.mul_assoc]

theorem mh_one : mh d 1 = 1 :=
  mulVec_ext d fun c => by
    conv_lhs => rw [← crd_cmb d c]
    rw [← crd_mul, Matrix.one_mul, crd_cmb, Matrix.one_mulVec]

theorem continuous_mh : Continuous (mh d) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [mh]
  split_ifs
  · have hc := (IsModuleTopology.continuous_of_linearMap ((bA d).coord p.2.2)).comp
      ((continuous_id.matrix_elem p.1 q.1).mul (continuous_const (y := bA d q.2.2)))
    exact hc
  · exact continuous_const

def mhU : GL (Fin d.m) (AE F E) →* GL (Ix d) (AF F) :=
  Units.map { toFun := mh d, map_one' := mh_one d, map_mul' := mh_mul d }

theorem continuous_mhU_inv : Continuous fun h : UA σ d.A.J => mhU d ((h : GL (Fin d.m) (AE F E))⁻¹) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun h : UA σ d.A.J => ((h : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine ⟨(continuous_mh d).comp h2, ?_⟩
  simp only [← map_inv, inv_inv]
  exact (continuous_mh d).comp h1

def xi : Matrix (Fin d.m) (Fin d.n) E ≃ (Ix d → F) where
  toFun X p := d.bs.repr (X p.1 p.2.1) p.2.2
  invFun c i j := ∑ k, c (i, j, k) • d.bs k
  left_inv X := by
    funext i j
    exact d.bs.sum_repr (X i j)
  right_inv c := by
    funext p
    obtain ⟨i, j, k⟩ := p
    exact congrFun (d.bs.repr_sum_self fun k => c (i, j, k)) k

theorem crd_incM (X : Matrix (Fin d.m) (Fin d.n) E) : d.crd (incM F X) = PositivityTheory.RgEis.ratV (xi d X) := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((bA d).repr ((1 : AF F) ⊗ₜ[F] X i j)) k = algebraMap F (AF F) (d.bs.repr (X i j) k)
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem bound_cpt (Fn : Mx F E d.m d.n → ℂ) (hF : Fn ∈ d.schM) (Ω : Set (UA σ d.A.J)) (hΩ : IsCompact Ω) :
    ∃ u : (Ix d → F) → ℝ, Summable u ∧ ∀ h ∈ Ω, ∀ X, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ u (xi d X) := by
  have hG : (fun c => Fn (d.cmb c)) ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi F (Ix d) := hF
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hG (hΩ.image (continuous_mhU_inv d))
  refine ⟨u, hu, fun h hh X => ?_⟩
  have e : Fn (mat h⁻¹ * incM F X) =
      Fn (d.cmb (((mhU d ((h : GL (Fin d.m) (AE F E))⁻¹) : GL (Ix d) (AF F)) : Matrix (Ix d) (Ix d) (AF F)) *ᵥ
        PositivityTheory.RgEis.ratV (xi d X))) := by
    rw [← crd_incM, ← cmb_crd d (mat h⁻¹ * incM F X), crd_mul]
    rfl
  rw [e]
  exact hb _ ⟨h, hh, rfl⟩ _

theorem reindex (Fn : Mx F E d.m d.n → ℂ) (γ : UA σ d.A.J) (hγ : γ ∈ ratU σ d.A.J) :
    ∃ e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E, ∀ h X,
      Fn (mat (γ * h)⁻¹ * incM F (e X)) = Fn (mat h⁻¹ * incM F X) := by
  obtain ⟨G, hG⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hinc : ∀ A B : Matrix (Fin d.m) (Fin d.m) E, incM F (A * B) = incM F A * incM F B := fun A B => by
    simp only [incM]; exact Matrix.map_mul
  have hinc' : ∀ (A : Matrix (Fin d.m) (Fin d.m) E) (B : Matrix (Fin d.m) (Fin d.n) E), incM F (A * B) = incM F A * incM F B :=
    fun A B => by simp only [incM]; exact Matrix.map_mul
  have l1 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * ((G : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have l2 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, (G : Matrix (Fin d.m) (Fin d.m) E) * (((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨⟨fun X => (G : Matrix (Fin d.m) (Fin d.m) E) * X, fun X => ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X, l1, l2⟩,
    fun h X => ?_⟩
  congr 1
  have hm : mat (γ * h)⁻¹ = mat h⁻¹ * incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
    have : (((γ : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
        incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
      rw [← hG, ← map_inv]; rfl
    simp only [mat, mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [this]
  simp only [Equiv.coe_fn_mk, hm]
  rw [Matrix.mul_assoc, ← hinc', l1]

theorem cpt (hS : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.ThK.Dbl.Cpt σ d.A.J := by
  have hC := GlobalTheory.ThK.Dbl.cptAll_of PositivityTheory.ThKEst.grpTop_of PositivityTheory.ThKEst.epsOf_of (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl h1) d.ok.aniso
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr h1) d.ok.aniso

end PositivityTheory.SiegelWeilFormula.Kdil.Tb

namespace PositivityTheory.SiegelWeilFormula.Kdil

open Tb in

theorem thetaBdd_of (hS : GlobalTheory.Published.SiegelSetUnitary) : ThetaBdd := by
  intro F E _ _ _ _ _ σ d Fn hF
  obtain ⟨Ω, hΩ, cov⟩ := (cpt d hS).cov
  obtain ⟨u, hu, hb⟩ := bound_cpt d Fn hF Ω hΩ
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h
  obtain ⟨e, he⟩ := reindex d Fn γ hγ
  have key : (fun X => ‖Fn (mat h⁻¹ * incM F X)‖) = (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) ∘ e := by
    funext X
    exact congrArg norm (he h X).symm
  have hs : Summable (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
  refine ⟨?_, ?_⟩
  · rw [key]; exact e.summable_iff.2 hs
  · rw [key]
    show ∑' X, ‖Fn (mat (γ * h)⁻¹ * incM F (e X))‖ ≤ _
    rw [e.tsum_eq (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖)]
    calc ∑' Y, ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖ ≤ ∑' Y, u (xi d Y) :=
          hs.tsum_le_tsum (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
      _ = ∑' ξ, u ξ := (xi d).tsum_eq u

end PositivityTheory.SiegelWeilFormula.Kdil

end
