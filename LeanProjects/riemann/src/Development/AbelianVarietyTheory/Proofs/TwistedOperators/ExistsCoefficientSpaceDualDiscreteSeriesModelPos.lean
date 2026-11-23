import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.DualCoef

theorem exists_contragredient {G X κ : Type} [Group G] [TopologicalSpace G] [AddCommGroup X] [Module ℂ X] [Fintype κ]
    (B : Module.Basis κ ℂ X) (T : G →* Module.End ℂ X)
    (hu : ∀ g p q, B.repr (T g⁻¹ (B p)) q = starRingEnd ℂ (B.repr (T g (B q)) p))
    (hc : ∀ p q, Continuous fun g => B.repr (T g (B q)) p)
    (hi : ∀ U : Submodule ℂ X, (∀ g, ∀ x ∈ U, T g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (ρ : G →* Module.End ℂ (EuclideanSpace ℂ κ)) (e : EuclideanSpace ℂ κ ≃ₗ[ℂ] Module.Dual ℂ X),
      (∀ g w x, e (ρ g w) x = e w (T g⁻¹ x)) ∧ (∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) ∧
      (∀ x, Continuous fun g => ρ g x) ∧
      ∀ U : Submodule ℂ (EuclideanSpace ℂ κ), (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  have : Module.Finite ℂ X := Module.Finite.of_basis B
  let e : EuclideanSpace ℂ κ ≃ₗ[ℂ] Module.Dual ℂ X :=
    (WithLp.linearEquiv 2 ℂ (κ → ℂ)).trans B.dualBasis.equivFun.symm
  have he : ∀ w y, e w y = ∑ p, w p * B.repr y p := by
    intro w y
    simp [e, Module.Basis.equivFun_symm_apply]
  let ρ : G →* Module.End ℂ (EuclideanSpace ℂ κ) :=
    { toFun := fun g => e.symm.toLinearMap ∘ₗ (T g⁻¹).dualMap ∘ₗ e.toLinearMap
      map_one' := by
        ext w : 1
        apply e.injective
        ext y
        simp
      map_mul' := fun g h => by
        ext w : 1
        apply e.injective
        ext y
        simp [mul_inv_rev, Module.End.mul_apply] }
  have hρ : ∀ g w x, e (ρ g w) x = e w (T g⁻¹ x) := by
    intro g w x
    simp [ρ]
  have hcoord : ∀ g w q, (ρ g w) q = ∑ p, w p * starRingEnd ℂ (B.repr (T g (B p)) q) := by
    intro g w q
    have h1 : (ρ g w) q = e (ρ g w) (B q) := by
      rw [he]
      simp [Finsupp.single_apply]
    rw [h1, hρ, he]
    exact Finset.sum_congr rfl fun p _ => by rw [hu]
  have horth : ∀ g p r, ∑ q, B.repr (T g (B p)) q * starRingEnd ℂ (B.repr (T g (B r)) q) =
      if p = r then 1 else 0 := by
    intro g p r
    have h2 : ∀ q, starRingEnd ℂ (B.repr (T g (B r)) q) = B.repr (T g⁻¹ (B q)) r := fun q => (hu g q r).symm
    simp_rw [h2]
    have h3 : ∑ q, B.repr (T g (B p)) q * B.repr (T g⁻¹ (B q)) r =
        B.repr (T g⁻¹ (∑ q, B.repr (T g (B p)) q • B q)) r := by
      rw [map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [h3, B.sum_repr, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      B.repr_self, Finsupp.single_apply]
  refine ⟨ρ, e, hρ, ?_, ?_, ?_⟩
  · intro g x y
    simp only [PiLp.inner_apply, RCLike.inner_apply, hcoord]
    calc ∑ q, (∑ r, y r * starRingEnd ℂ (B.repr (T g (B r)) q)) *
          starRingEnd ℂ (∑ p, x p * starRingEnd ℂ (B.repr (T g (B p)) q))
        = ∑ p, ∑ r, starRingEnd ℂ (x p) * y r *
            ∑ q, B.repr (T g (B p)) q * starRingEnd ℂ (B.repr (T g (B r)) q) := by
          simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          ring
      _ = ∑ p, y p * starRingEnd ℂ (x p) := by
          simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  · intro x
    have hfun : (fun g => ρ g x) = fun g => WithLp.toLp 2 (fun q => ∑ p, x p * starRingEnd ℂ (B.repr (T g (B p)) q)) := by
      funext g
      ext q
      simp [hcoord]
    rw [hfun]
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => ?_)
    exact continuous_finsetSum _ fun p _ => continuous_const.mul (Complex.continuous_conj.comp (hc q p))
  · intro U hU
    let W : Submodule ℂ (Module.Dual ℂ X) := U.map e.toLinearMap
    have hinv : ∀ g, ∀ x ∈ W.dualCoannihilator, T g x ∈ W.dualCoannihilator := by
      intro g x hx
      rw [Submodule.mem_dualCoannihilator] at hx ⊢
      rintro φ ⟨w, hw, rfl⟩
      have hw' : ρ g⁻¹ w ∈ U := hU g⁻¹ ⟨w, hw, rfl⟩
      have := hx (e (ρ g⁻¹ w)) ⟨_, hw', rfl⟩
      rw [hρ, inv_inv] at this
      exact this
    have hUW : U = W.comap e.toLinearMap := (Submodule.comap_map_eq_of_injective e.injective U).symm
    rcases hi _ hinv with h | h
    · right
      have hW : W = ⊤ := by
        rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), h, Submodule.dualAnnihilator_bot]
      rw [hUW, hW, Submodule.comap_top]
    · left
      have hW : W = ⊥ := by
        rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), h, Submodule.dualAnnihilator_top]
      rw [hUW, hW, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr e.injective

def tensRep {G ι : Type} [Group G] {H : ι → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (r : ∀ i, G →* Module.End ℂ (H i)) : G →* Module.End ℂ (⨂[ℂ] i, H i) where
  toFun g := PiTensorProduct.map fun i => r i g
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem tensRep_apply {G ι : Type} [Group G] {H : ι → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (r : ∀ i, G →* Module.End ℂ (H i)) (g : G) : tensRep r g = PiTensorProduct.map fun i => r i g := rfl

theorem exists_contragredient_tensor {G ι : Type} [Group G] [TopologicalSpace G] [Fintype ι] {H : ι → Type}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)]
    (r : ∀ i, G →* Module.End ℂ (H i)) (hu : ∀ i g v, ‖r i g v‖ = ‖v‖) (hc : ∀ i v, Continuous fun g => r i g v)
    (hi : ∀ U : Submodule ℂ (⨂[ℂ] i, H i), (∀ g, ∀ x ∈ U, tensRep r g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (κ : Type) (_ : Fintype κ) (ρ : G →* Module.End ℂ (EuclideanSpace ℂ κ))
      (e : EuclideanSpace ℂ κ ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, H i)),
      (∀ g w x, e (ρ g w) x = e w (tensRep r g⁻¹ x)) ∧ (∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) ∧
      (∀ x, Continuous fun g => ρ g x) ∧
      ∀ U : Submodule ℂ (EuclideanSpace ℂ κ), (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  let b : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (H i))) ℂ (H i) := fun i => stdOrthonormalBasis ℂ (H i)
  let B : Module.Basis (∀ i, Fin (Module.finrank ℂ (H i))) ℂ (⨂[ℂ] i, H i) :=
    Basis.piTensorProduct fun i => (b i).toBasis
  have hrepr : ∀ (x : ∀ i, H i) p, B.repr (PiTensorProduct.tprod ℂ x) p = ∏ i, inner ℂ (b i (p i)) (x i) := by
    intro x p
    simp only [B, Basis.piTensorProduct_repr_tprod_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    exact Finset.prod_congr rfl fun i _ => (b i).repr_apply_apply (x i) (p i)
  have hB : ∀ p, B p = PiTensorProduct.tprod ℂ fun i => b i (p i) := by
    intro p
    simp [B]
  have hT : ∀ g (x : ∀ i, H i), tensRep r g (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => r i g (x i) := by
    intro g x
    rw [tensRep_apply, PiTensorProduct.map_tprod]
  have hinner : ∀ i g (v w : H i), inner ℂ (r i g v) (r i g w) = inner ℂ v w := by
    intro i g
    exact (LinearMap.norm_map_iff_inner_map_map (r i g)).mp (hu i g)
  have hback : ∀ i g (v : H i), r i g (r i g⁻¹ v) = v := by
    intro i g v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have huB : ∀ g p q, B.repr (tensRep r g⁻¹ (B p)) q = starRingEnd ℂ (B.repr (tensRep r g (B q)) p) := by
    intro g p q
    rw [hB, hB, hT, hT, hrepr, hrepr, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hinner i g (b i (q i)), hback, inner_conj_symm]
  have hcB : ∀ p q, Continuous fun g => B.repr (tensRep r g (B q)) p := by
    intro p q
    simp_rw [hB, hT, hrepr]
    exact continuous_finsetProd _ fun i _ => continuous_const.inner (hc i _)
  obtain ⟨ρ, e, h1, h2, h3, h4⟩ := exists_contragredient B (tensRep r) huB hcB hi
  exact ⟨_, inferInstance, ρ, e, h1, h2, h3, h4⟩

theorem nontrivial_dual_tensor {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    [∀ i, Nontrivial (H i)] : Nontrivial (Module.Dual ℂ (⨂[ℂ] i, H i)) := by
  classical
  have hv : ∀ i, ∃ v : H i, v ≠ 0 := fun i => exists_ne 0
  choose v hv using hv
  have hf : ∀ i, ∃ f : Module.Dual ℂ (H i), f (v i) ≠ 0 := by
    intro i
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).mp h)
  choose f hf using hf
  let m : MultilinearMap ℂ H ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  let φ : Module.Dual ℂ (⨂[ℂ] i, H i) := PiTensorProduct.lift m
  refine ⟨⟨φ, 0, fun h => ?_⟩⟩
  have hz := LinearMap.congr_fun h (PiTensorProduct.tprod ℂ v)
  have hprod : φ (PiTensorProduct.tprod ℂ v) = ∏ i, f i (v i) := by
    simp [φ, m]
  rw [hprod, LinearMap.zero_apply] at hz
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hf i) hz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem frame_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have hJ : Formalism.REAL.Jm (M.ε τ) = ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ := by
    rw [← M.fr_gram τ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc ((M.fr τ)⁻¹)ᴴ * (gᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by
        rw [M.fr_gram τ, hg', hJ]

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  obtain ⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -⟩ := M.ds τ
  rw [DSModel.rep, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
  exact h1

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.H τ) :
    M.rep τ (g * g') v = M.rep τ g (M.rep τ g' v) := by
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hm : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  obtain ⟨-, -, ⟨⟨-, hmul⟩, -, -⟩, -⟩ := M.ds τ
  rw [DSModel.rep, DSModel.rep, DSModel.rep, hm, hmul _ (frame_mem M τ hg) _ (frame_mem M τ hg'),
    ContinuousLinearMap.comp_apply]

def locRep (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) (hs : M.sm τ = ⊤) :
    GA D V →* Module.End ℂ (M.sm τ) where
  toFun h := (M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) h) : M.H τ →ₗ[ℂ] M.H τ).restrict
    fun _ _ => hs ▸ Submodule.mem_top
  map_one' := by
    ext v
    simp [GlobalTheory.PointAtPlaceHom.infMat_one, rep_one]
  map_mul' g h := by
    ext v
    simp [GlobalTheory.PointAtPlaceHom.infMat_mul, rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V h τ)]

theorem coe_locRep (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) (hs : M.sm τ = ⊤) (h : GA D V) (v : M.sm τ) :
    (locRep hθ M τ hs h v : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) h) v := rfl

theorem locRep_of_one (hθ : IsInfFam θ) (M : DSModel V S) (τ : D.what₂.Tau) (hs : M.sm τ = ⊤) {h : GA D V}
    (hh : infMat D.sp.cm.sig V.gram (θ τ) h = 1) : locRep hθ M τ hs h = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [coe_locRep, hh, rep_one, one_apply_eq_self, LinearMap.id_apply]

theorem infMat_of_fin (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {h : GA D V} (hh : h ∈ GfC V) :
    infMat D.sp.cm.sig V.gram φ h = 1 := by
  have h1 : infHom V h = 1 := hh
  have h2 : ((infHom V h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [h1, Units.val_one]
  unfold infMat
  simp only [infHom, matHom, Formalism.UG.bc] at h2
  have h3 := congrArg (fun m => Matrix.map m φ) h2
  rw [Matrix.map_one _ (map_zero φ) (map_one φ)] at h3
  exact h3

theorem exists_dual_coef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∃ (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), c.Is ∧ IsDualPair θ M c pr ∧ Function.Surjective pr := by
  intro D θ V S M hθ hall
  classical
  have hfsi := AllPlus.finite_smooth_irreducible D V S M hall
  have hs : ∀ τ, M.sm τ = ⊤ := fun τ => (hfsi τ).2.1
  have : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (hfsi τ).1
  let r : ∀ τ, GA D V →* Module.End ℂ (M.sm τ) := fun τ => locRep hθ M τ (hs τ)
  have hr : ∀ τ g (v : M.sm τ), (r τ g v : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) g) v :=
    fun τ g v => coe_locRep hθ M τ (hs τ) g v
  have hid : ∀ τ k, infMat D.sp.cm.sig V.gram (θ τ) k = 1 → r τ k = LinearMap.id :=
    fun τ k hk => locRep_of_one hθ M τ (hs τ) hk
  have hu : ∀ τ g (v : M.sm τ), ‖r τ g v‖ = ‖v‖ := by
    intro τ g v
    obtain ⟨-, -, ⟨-, hn, -⟩, -⟩ := M.ds τ
    show ‖(r τ g v : M.H τ)‖ = ‖(v : M.H τ)‖
    rw [hr]
    exact hn _ (frame_mem M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)) v
  have hc : ∀ τ (v : M.sm τ), Continuous fun g => r τ g v := by
    intro τ v
    obtain ⟨-, -, ⟨-, -, hcont⟩, -⟩ := M.ds τ
    have hm : Continuous fun g : GA D V => M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (M.fr τ)⁻¹ :=
      (continuous_const.mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).mul continuous_const
    have hv : Continuous fun g : GA D V => M.σ τ (M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) g * (M.fr τ)⁻¹) v :=
      (hcont (v : M.H τ)).comp_continuous hm
        fun g => frame_mem M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
    refine continuous_induced_rng.2 ?_
    convert hv using 1
    funext g
    exact hr τ g v
  have hat : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ τ', τ' ≠ τ → r τ' (atTau θ V τ g) = LinearMap.id :=
    fun τ g hg τ' hne => hid τ' _ ((GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.2 τ' hne)
  have hsingle : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), (fun τ' => r τ' (atTau θ V τ g)) =
      Function.update (fun τ' => (LinearMap.id : Module.End ℂ (M.sm τ'))) τ (r τ (atTau θ V τ g)) := by
    intro τ g hg
    funext τ'
    by_cases h : τ' = τ
    · subst h
      rw [Function.update_self]
    · rw [Function.update_of_ne h, hat τ g hg τ' h]
  have hi : ∀ U : Submodule ℂ (⨂[ℂ] τ, M.sm τ), (∀ g, ∀ x ∈ U, tensRep r g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let σ' : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (M.sm τ) :=
      fun τ u => r τ (atTau θ V τ (unfr M τ u))
    have hσ' : ∀ τ u (x : M.sm τ), (σ' τ u x : M.H τ) = M.σ τ u x := by
      intro τ u x
      show (r τ _ x : M.H τ) = _
      rw [hr, (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (hall.unfr_mem τ u)).2.1, rep_unfr]
    refine GlobalTheory.DefLift.piTensor_irreducible σ' ?_ U ?_
    · intro τ U' hU'
      rcases (hfsi τ).2.2 (U'.map (M.sm τ).subtype) (by
          rintro u _ ⟨x, hx, rfl⟩
          exact ⟨σ' τ u x, hU' u x hx, hσ' τ u x⟩) with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : M.H τ) ∈ U'.map (M.sm τ).subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [Submodule.eq_top_iff']
        intro x
        obtain ⟨y, hy, hxy⟩ := (show (x : M.H τ) ∈ U'.map (M.sm τ).subtype by rw [h]; trivial)
        rwa [Subtype.ext hxy] at hy
    · intro τ u x hx
      have hg := hall.unfr_mem τ u
      have := hU (atTau θ V τ (unfr M τ u)) x hx
      rwa [tensRep_apply, hsingle τ _ hg] at this
  obtain ⟨κ, _, ρ, e, h1, h2, h3, h4⟩ := exists_contragredient_tensor r hu hc hi
  have hT1 : ∀ k ∈ GfC V, tensRep r k = 1 := by
    intro k hk
    rw [tensRep_apply]
    have : (fun τ => r τ k) = fun τ => (LinearMap.id : Module.End ℂ (M.sm τ)) :=
      funext fun τ => hid τ k (infMat_of_fin (θ τ) hk)
    rw [this, PiTensorProduct.map_id, Module.End.one_eq_id]
  have hnt : ∀ τ, Nontrivial (M.sm τ) := by
    intro τ
    obtain ⟨-, hnt, -⟩ := M.ds τ
    obtain ⟨v, hv⟩ := exists_ne (0 : M.H τ)
    refine nontrivial_of_ne (⟨v, by rw [hs τ]; trivial⟩ : M.sm τ) 0 fun h => hv ?_
    exact congrArg Subtype.val h
  have : Nontrivial (Module.Dual ℂ (⨂[ℂ] τ, M.sm τ)) := nontrivial_dual_tensor
  have : Nontrivial (EuclideanSpace ℂ κ) := e.toEquiv.nontrivial
  let c : CoefA V := { W := EuclideanSpace ℂ κ, ρ := ρ }
  refine ⟨c, e.toLinearMap, ⟨?_, h2, h3, inferInstance, h4⟩, ⟨?_, ?_⟩, e.surjective⟩
  · intro k hk
    refine LinearMap.ext fun w => e.injective (LinearMap.ext fun x => ?_)
    show e (ρ k w) x = e w x
    rw [h1, hT1 _ (inv_mem hk), Module.End.one_apply]
  · intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : EuclideanSpace ℂ κ)
    exact hw (e.injective ((LinearMap.congr_fun h w).trans (map_zero e).symm))
  · intro τ g hg w v u huv
    have hspec := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
    have hupd : Function.update v τ u = fun τ' => r τ' (atTau θ V τ g) (v τ') := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact Subtype.ext (by rw [hr, hspec.2.1, huv])
      · rw [Function.update_of_ne h, hat τ g hg τ' h, LinearMap.id_apply]
    show e (ρ (atTau θ V τ g) w) _ = e w _
    rw [h1, hupd, ← PiTensorProduct.map_tprod, ← tensRep_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]

end GlobalTheory.DualCoef

end
