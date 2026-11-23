import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelDualPairCasimirApplyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasimirNumberIdentityDualPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestLeastDegreeMirror
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypesJointHarmonicShapeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegreeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialKFiniteBothMembersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointIntertwinerDiscreteSeriesDescendsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairingStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg
open TensorProduct

noncomputable section
namespace GlobalTheory.ThetaUnique

section General
variable {p q : ℕ}

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) : GKMod p q where
  V := M.V ⧸ N
  act :=
    { toFun := fun Z => N.mapQ N (M.act Z) fun y hy => hN Z y hy
      map_add' := fun Y Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp }
  lie := fun Y Z => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    have := LinearMap.congr_fun (M.lie Y Z) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.sub_apply, Module.End.mul_apply, this, Submodule.Quotient.mk_sub]
  kfin := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hv, hst⟩ := M.kfin v
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hv, ?_⟩
    rintro Z hZ _ ⟨w, hw, rfl⟩
    exact ⟨M.act Z w, hst Z hZ w hw, rfl⟩
  wts := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    refine Submodule.iSup_induction _ (motive := fun v => N.mkQ v ∈ _) (M.wts v) ?_ (by simp) ?_
    · intro μ x hx
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
      intro a
      show N.mkQ (M.act (Eab a a) x) = _
      rw [hx a, map_smul]
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem map_hwSub {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ W}
    (g : V →ₗ[ℂ] W) (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, hv.1, map_smul]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_casimir {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ W}
    (g : V →ₗ[ℂ] W) (hg : ∀ Z v, g (a Z v) = b Z (g v)) (v : V) :
    g (casimir a v) = casimir b (g v) := by
  simp [casimir, LinearMap.sum_apply, map_sum, hg]

theorem eq_zero_of_contract {z : V ⊗[ℂ] W}
    (h : ∀ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (LinearMap.lTensor V φ z) = 0) : z = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisRight_apply, h]
  simp

theorem eq_tmul_of_contract {z : V ⊗[ℂ] W} {L : Submodule ℂ V} (hL : Module.finrank ℂ L = 1)
    {v : V} (hv : v ∈ L) (ψ : V →ₗ[ℂ] ℂ) (hψ : ψ v = 1)
    (h : ∀ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (LinearMap.lTensor V φ z) ∈ L) :
    z = v ⊗ₜ TensorProduct.lid ℂ W (LinearMap.rTensor W ψ z) := by
  have hv0 : (⟨v, hv⟩ : L) ≠ 0 := by
    intro h0
    have : v = 0 := congrArg Subtype.val h0
    simp [this] at hψ
  rw [← sub_eq_zero]
  refine eq_zero_of_contract fun φ => ?_
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0).1 hL ⟨_, h φ⟩
  have hc' : c • v = TensorProduct.rid ℂ V (LinearMap.lTensor V φ z) := congrArg Subtype.val hc
  have key : ∀ z : V ⊗[ℂ] W, ψ (TensorProduct.rid ℂ V (LinearMap.lTensor V φ z)) =
      φ (TensorProduct.lid ℂ W (LinearMap.rTensor W ψ z)) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 := key z
  rw [← hc', map_smul, hψ] at h2
  rw [map_sub, map_sub, ← hc']
  simp [← h2]

theorem rid_lTensor_map (φ : W →ₗ[ℂ] ℂ) (A : Module.End ℂ V) (z : V ⊗[ℂ] W) :
    TensorProduct.rid ℂ V (LinearMap.lTensor V φ (TensorProduct.map A LinearMap.id z)) =
      A (TensorProduct.rid ℂ V (LinearMap.lTensor V φ z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lid_rTensor_map (ψ : V →ₗ[ℂ] ℂ) (B : Module.End ℂ W) (z : V ⊗[ℂ] W) :
    TensorProduct.lid ℂ W (LinearMap.rTensor W ψ (TensorProduct.map LinearMap.id B z)) =
      B (TensorProduct.lid ℂ W (LinearMap.rTensor W ψ z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end General

section Core
variable {p q r s : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V} {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V}

theorem image_eq_tmul (M₁ : GKMod p q) (M₂ : GKMod r s) {Λ : Ix p q → ℚ} {Λ' : Ix r s → ℚ}
    (h1 : Module.finrank ℂ (hwSub M₁.act Λ) = 1) {v : M₁.V} (hv : IsHW M₁.act Λ v) {c κ : ℂ}
    (hc : casimir M₁.act v = c • v) {Φ : V} (hΦ₁ : Φ ∈ hwSub a₁ Λ) (hΦ₂ : Φ ∈ hwSub a₂ Λ')
    (hcas : casimir a₂ Φ = casimir a₁ Φ - κ • Φ) (f : V →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (hf₁ : ∀ Z, f ∘ₗ a₁ Z = TensorProduct.map (M₁.act Z) LinearMap.id ∘ₗ f)
    (hf₂ : ∀ Z, f ∘ₗ a₂ Z = TensorProduct.map LinearMap.id (M₂.act Z) ∘ₗ f) :
    ∃ u ∈ hwSub M₂.act Λ', f Φ = v ⊗ₜ u ∧ casimir M₂.act u = (c - κ) • u := by
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hv.1
  let g : V →ₗ[ℂ] M₂.V := (TensorProduct.lid ℂ M₂.V).toLinearMap ∘ₗ LinearMap.rTensor M₂.V ψ ∘ₗ f
  have hg : ∀ Z w, g (a₂ Z w) = M₂.act Z (g w) := fun Z w => by
    have := LinearMap.congr_fun (hf₂ Z) w
    simp only [LinearMap.comp_apply] at this
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, lid_rTensor_map]
  have hfΦ : f Φ = v ⊗ₜ g Φ := by
    refine eq_tmul_of_contract h1 hv.2 ψ hψ fun φ => ?_
    refine map_hwSub (a := a₁)
      ((TensorProduct.rid ℂ M₁.V).toLinearMap ∘ₗ LinearMap.lTensor M₁.V φ ∘ₗ f) (fun Z w => ?_) hΦ₁
    have := LinearMap.congr_fun (hf₁ Z) w
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, this, rid_lTensor_map]
  refine ⟨g Φ, map_hwSub g hg hΦ₂, hfΦ, ?_⟩
  have h3 : f (casimir a₁ Φ) = c • f Φ := by
    rw [map_casimir (b := (LinearMap.rTensorHom M₂.V).comp M₁.act) f
      (fun Z w => LinearMap.congr_fun (hf₁ Z) w), hfΦ, TensorProduct.smul_tmul', ← hc]
    simp [casimir, LinearMap.sum_apply, TensorProduct.sum_tmul, -Fintype.sum_sum_type]
  have h4 : g (casimir a₁ Φ) = c • g Φ := by
    simp only [g, LinearMap.comp_apply, h3, map_smul]
  rw [← map_casimir g hg, hcas, map_sub, h4, map_smul, sub_smul]

theorem range_eq (M₁ : GKMod p q) (hI : IrrGK M₁) (M₂ B : GKMod r s) (hB : IrrGK B) {Φ : V}
    (key : ∀ (M : GKMod r s) (f : V →ₗ[ℂ] M₁.V ⊗[ℂ] M.V),
      (∀ Z, f ∘ₗ a₁ Z = TensorProduct.map (M₁.act Z) LinearMap.id ∘ₗ f) →
      (∀ Z, f ∘ₗ a₂ Z = TensorProduct.map LinearMap.id (M.act Z) ∘ₗ f) → f Φ = 0 → f = 0)
    (f : V →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (hf₁ : ∀ Z, f ∘ₗ a₁ Z = TensorProduct.map (M₁.act Z) LinearMap.id ∘ₗ f)
    (hf₂ : ∀ Z, f ∘ₗ a₂ Z = TensorProduct.map LinearMap.id (M₂.act Z) ∘ₗ f)
    (e : B.V →ₗ[ℂ] M₂.V) (he : ∀ Z x, e (B.act Z x) = M₂.act Z (e x))
    {v : M₁.V} (hv : v ≠ 0) {v' : B.V} (hv' : v' ≠ 0) (hΦ : f Φ = v ⊗ₜ e v') :
    LinearMap.range f =
      LinearMap.range (TensorProduct.map LinearMap.id (LinearMap.range e).subtype) := by
  have hN : ∀ Z, ∀ y ∈ LinearMap.range e, M₂.act Z y ∈ LinearMap.range e := by
    rintro Z _ ⟨x, rfl⟩; exact ⟨_, he Z x⟩
  apply le_antisymm
  · have h0 := key (quotMod M₂ _ hN) (LinearMap.lTensor M₁.V (LinearMap.range e).mkQ ∘ₗ f)
      (fun Z => by
        rw [LinearMap.comp_assoc, hf₁, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
        congr 1
        ext x y; rfl)
      (fun Z => by
        rw [LinearMap.comp_assoc, hf₂, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
        congr 1
        ext x y; rfl)
      (by
        have : (LinearMap.range e).mkQ (e v') = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self e v')
        rw [LinearMap.comp_apply, hΦ]
        change (v ⊗ₜ[ℂ] (LinearMap.range e).mkQ (e v')) = 0
        rw [this, TensorProduct.tmul_zero])
    rintro _ ⟨P, rfl⟩
    have h1 : f P ∈ LinearMap.ker (LinearMap.lTensor M₁.V (LinearMap.range e).mkQ) :=
      LinearMap.congr_fun h0 P
    rw [lTensor_mkQ] at h1
    exact h1
  · have s1 : ∀ x : M₁.V, x ⊗ₜ[ℂ] e v' ∈ LinearMap.range f := by
      rcases hI.2 ((LinearMap.range f).comap ((TensorProduct.mk ℂ M₁.V M₂.V).flip (e v')))
        (by
          rintro Z x ⟨P, hP⟩
          refine ⟨a₁ Z P, ?_⟩
          have := LinearMap.congr_fun (hf₁ Z) P
          simp only [LinearMap.comp_apply] at this
          rw [this, hP]; simp) with h | h
      · exact absurd ((Submodule.eq_bot_iff _).1 h v ⟨Φ, hΦ⟩) hv
      · intro x; exact (Submodule.eq_top_iff'.1 h x :)
    have s2 : ∀ (x : M₁.V) (y : B.V), x ⊗ₜ[ℂ] e y ∈ LinearMap.range f := by
      intro x
      rcases hB.2 ((LinearMap.range f).comap (TensorProduct.mk ℂ M₁.V M₂.V x ∘ₗ e))
        (by
          rintro Z y ⟨P, hP⟩
          refine ⟨a₂ Z P, ?_⟩
          have := LinearMap.congr_fun (hf₂ Z) P
          simp only [LinearMap.comp_apply] at this
          rw [this, hP]; simp [he]) with h | h
      · exact absurd ((Submodule.eq_bot_iff _).1 h v' (s1 x)) hv'
      · intro y; exact (Submodule.eq_top_iff'.1 h y :)
    rintro _ ⟨z, rfl⟩
    induction z with
    | zero => simp
    | tmul x y => obtain ⟨_, y, rfl⟩ := y; exact s2 x y
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

end Core

theorem exists_intw {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (D : DSRep T1) (D' : DSRep T2) (hA : AdmGK D.HK)
    (Tm : D.U.H →L[ℂ] D'.U.H →L[ℂ] F.H)
    (hT : ∀ g h x y, F.π (g, h) (Tm x y) = Tm (D.U.π g x) (D'.U.π h y))
    (Φ : Pol p q r s) (x₀ : D.U.H) (y₀ : D'.U.H) (h0 : inner ℂ (Tm x₀ y₀) (F.ι Φ) ≠ 0) :
    ∃ f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ D.HK.V D'.HK.V, Intw D.HK D'.HK f ∧ f Φ ≠ 0 := by
  obtain ⟨-, hd1, hd2⟩ := GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F
  have hK := GlobalTheory.T.fock_polynomial_kFinite_both_members p q r s T0 T1 T2 F (GlobalTheory.T.fock_Kset_preserves_homogeneous_degree p q r s T0 T1 T2 F)
  have h1 := fun y : D'.U.H => GlobalTheory.T.adjoint_intertwiner_discreteSeries_descends p q T1 D F.H (F.π.comp (MonoidHom.inl _ _))
    (fun g x => F.isom _ x) (Tm.flip y)
    (fun g x => by simpa using hT g 1 x y) _ F.ι (fockAct1 p q r s) (fun P => (hK P).1) hd1
  have h2 := fun x : D.U.H => GlobalTheory.T.adjoint_intertwiner_discreteSeries_descends r s T2 D' F.H (F.π.comp (MonoidHom.inr _ _))
    (fun g x => F.isom _ x) (Tm x)
    (fun g y => by simpa using hT 1 g x y) _ F.ι (fockAct2 p q r s) (fun P => (hK P).2) hd2
  choose φ hφ hφ' using h1
  choose ψ hψ hψ' using h2
  have hlie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  obtain ⟨f, hf0, hf1, hf2⟩ := GlobalTheory.T.exists_linearMap_tensor_of_pairing _ _ _ _ _ D.ι D'.ι D.ι_inj D'.ι_inj φ ψ
    (fun x y P => by rw [hφ, hψ]; rfl) (fun P => by
      obtain ⟨W, hW, hP, hst⟩ := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 P).1
      obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q D.HK hA _ (fockAct1 p q r s) (fun Y Z _ _ => hlie Y Z) W hW hst
        (fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).2)
      exact ⟨E, hE, fun y => hE' (φ y) (fun Z _ v => hφ' y Z v) P hP⟩)
  refine ⟨f, ⟨fun Z => hf1 _ _ fun y P => hφ' y Z P, fun Z => hf2 _ _ fun x P => hψ' x Z P⟩, fun h => h0 ?_⟩
  have := hφ y₀ Φ x₀
  rw [hf0 Φ h y₀] at this
  simpa using this.symm

section Swap
variable {V A B : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

theorem comm_left {f : V →ₗ[ℂ] A ⊗[ℂ] B} {c : Module.End ℂ V} {a : Module.End ℂ A}
    (h : f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) :
    ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) ∘ₗ c =
      TensorProduct.map LinearMap.id a ∘ₗ (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f := by
  rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  congr 1
  ext x y; rfl

theorem comm_right {f : V →ₗ[ℂ] A ⊗[ℂ] B} {c : Module.End ℂ V} {b : Module.End ℂ B}
    (h : f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) :
    ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) ∘ₗ c =
      TensorProduct.map b LinearMap.id ∘ₗ (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f := by
  rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  congr 1
  ext x y; rfl

theorem range_comm {f : V →ₗ[ℂ] A ⊗[ℂ] B} (N : Submodule ℂ A)
    (h : LinearMap.range ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) =
      LinearMap.range (TensorProduct.map LinearMap.id N.subtype)) :
    LinearMap.range f = LinearMap.range (TensorProduct.map N.subtype LinearMap.id) := by
  have h1 : f = (TensorProduct.comm ℂ B A).toLinearMap ∘ₗ
      ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) := by
    ext v; simp
  have h2 : (TensorProduct.comm ℂ B A).toLinearMap ∘ₗ TensorProduct.map LinearMap.id N.subtype =
      TensorProduct.map N.subtype LinearMap.id ∘ₗ (TensorProduct.comm ℂ B N).toLinearMap := by
    ext x y; rfl
  rw [h1, LinearMap.range_comp, h, ← LinearMap.range_comp, h2, LinearEquiv.range_comp]

end Swap

theorem Intw.sub_smul {p q r s : ℕ} {M₁ : GKMod p q} {M₂ : GKMod r s}
    {f g : Pol p q r s →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V} (hf : Intw M₁ M₂ f) (hg : Intw M₁ M₂ g) (c : ℂ) :
    Intw M₁ M₂ (f - c • g) := by
  refine ⟨fun Z => ?_, fun Z => ?_⟩
  · rw [LinearMap.sub_comp, LinearMap.smul_comp, hf.1, hg.1, LinearMap.comp_sub, LinearMap.comp_smul]
  · rw [LinearMap.sub_comp, LinearMap.smul_comp, hf.2, hg.2, LinearMap.comp_sub, LinearMap.comp_smul]

theorem exists_isHW {p q : ℕ} (M : GKMod p q) {Λ : Ix p q → ℚ}
    (h : Module.finrank ℂ (hwSub M.act Λ) = 1) : ∃ v, IsHW M.act Λ v := by
  obtain ⟨v, hv, -⟩ := finrank_eq_one_iff'.1 h
  exact ⟨v, fun h0 => hv (Subtype.ext h0), v.2⟩

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {p q : ℕ} (hn : 1 ≤ p + q) (lam : Ix p q → ℚ) :
    AdmGK (X.ds p q lam).HK ∧ IrrGK (X.ds p q lam).HK :=
  ((h5 p q hn).1 (X.ds p q lam).U ⟨(X.ds p q lam).nontriv, (X.ds p q lam).irred⟩).2.2 _ (X.ds p q lam).ι
    ⟨(X.ds p q lam).ι_inj, (X.ds p q lam).ι_range, (X.ds p q lam).der⟩

theorem jointHW_shape (X : ProvA) (h2 : admH2 X) {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ}
    {P : Pol p q r s} (hJ : P ∈ jointHarm p q r s) (h : IsHW (fockAct1 p q r s) μ P)
    (h' : IsHW (fockAct2 p q r s) μ' P) : JointShape p q r s μ μ' := by
  by_contra hs
  have := ((h2 p q r s).2.2.2.2.1 μ μ').2 hs
  exact h.1 ((Submodule.eq_bot_iff _).1 this P ⟨⟨h.2, h'.2⟩, Submodule.subset_span hJ⟩)

theorem jointHW_line (X : ProvA) (h2 : admH2 X) {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ}
    {P Φ : Pol p q r s} (hJ : P ∈ jointHarm p q r s) (h : IsHW (fockAct1 p q r s) μ P)
    (h' : IsHW (fockAct2 p q r s) μ' P) (hΦ : JointHW (X.fock p q r s) μ μ' Φ) :
    ∃ c : ℂ, P = c • Φ := by
  have h1 := ((h2 p q r s).2.2.2.2.1 μ μ').1 (jointHW_shape X h2 hJ h h')
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    ⟨Φ, ⟨hΦ.2.1.2, hΦ.2.2.1.2⟩, Submodule.subset_span hΦ.1⟩
    (fun h0 => hΦ.2.1.1 (congrArg Subtype.val h0))).1 h1 ⟨P, ⟨h.2, h'.2⟩, Submodule.subset_span hJ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem general (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X) (h7 : admQ7) (h8 : admQ8)
    {p q r s : ℕ} (hn : 1 ≤ p + q) (hM : 1 ≤ r + s) {lam : Ix p q → ℚ} {lam' : Ix r s → ℚ}
    (hp : IsParam lam) (hp' : IsParam lam') (hg : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    (hg' : GapGt lam' (((r + s : ℕ) : ℝ) ^ 3))
    (hs : JointShape p q r s (blattner lam) (blattner lam'))
    (hfl : ∀ μ v, IsHW (X.ds p q lam).HK.act μ v →
      degW (cPair r s) (blattner lam) ≤ degW (cPair r s) μ)
    (hfl' : ∀ μ v, IsHW (X.ds r s lam').HK.act μ v →
      degW (cPair p q) (blattner lam') ≤ degW (cPair p q) μ)
    (hnum : normSq lam' - rhoSq (r + s) = normSq lam - rhoSq (p + q) -
      ((p + q : ℕ) : ℚ) * ((r + s : ℕ) : ℚ) * (((r + s : ℕ) : ℚ) - ((p + q : ℕ) : ℚ)) / 4)
    (hi : ARi X lam lam') (hii : ARii X lam lam') :
    ARiiiUp X lam lam' ∧ ARiiiDown X lam lam' ∧ ARiiiLine X lam lam' := by
  obtain ⟨hA, hI⟩ := discrete_series_gk_admissible_irreducible X h5 hn lam
  obtain ⟨hA', hI'⟩ := discrete_series_gk_admissible_irreducible X h5 hM lam'
  obtain ⟨hr, hc, -⟩ := hD p q lam hp
  obtain ⟨hr', hc', -⟩ := hD r s lam' hp'
  obtain ⟨v, hv⟩ := exists_isHW _ hr
  obtain ⟨v', hv'⟩ := exists_isHW _ hr'
  obtain ⟨Φ₀, hΦ₀⟩ := hi.1
  have hnumC : ((normSq lam' - rhoSq (r + s) : ℚ) : ℂ) = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) -
      ((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ)) / 4 := by
    rw [hnum]; push_cast; ring
  have keyU : ∀ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ →
      ∀ (M : GKMod r s) (f : Pol p q r s →ₗ[ℂ] (X.ds p q lam).HK.V ⊗[ℂ] M.V),
        Intw (X.ds p q lam).HK M f → f Φ = 0 → f = 0 := by
    intro Φ hΦ M f hf h0
    by_contra hne
    obtain ⟨⟨μ', P, hJ, hP, hP', hfP⟩, -⟩ := GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub p q r s _ M f hI hA hf hne _ ⟨v, hv⟩ hfl
    have := (GlobalTheory.T.jointShape_unique_and_degW_eq p q r s _ _ _ _ (jointHW_shape X h2 hJ hP hP') hs).1.1 rfl
    subst this
    obtain ⟨c, rfl⟩ := jointHW_line X h2 hJ hP hP' hΦ
    exact hfP (by rw [map_smul, h0, smul_zero])
  have keyD : ∀ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ →
      ∀ (M : GKMod p q) (f : Pol p q r s →ₗ[ℂ] M.V ⊗[ℂ] (X.ds r s lam').HK.V),
        Intw M (X.ds r s lam').HK f → f Φ = 0 → f = 0 := by
    intro Φ hΦ M f hf h0
    by_contra hne
    obtain ⟨⟨μ, P, hJ, hP, hP', hfP⟩, -⟩ := GlobalTheory.T.fock_minimal_KType_second_member p q r s M _ f hI' hA' hf hne _ ⟨v', hv'⟩ hfl'
    have := (GlobalTheory.T.jointShape_unique_and_degW_eq p q r s _ _ _ _ (jointHW_shape X h2 hJ hP hP') hs).1.2 rfl
    subst this
    obtain ⟨c, rfl⟩ := jointHW_line X h2 hJ hP hP' hΦ
    exact hfP (by rw [map_smul, h0, smul_zero])
  refine ⟨fun MM f hf hne => ⟨?_, fun Φ hΦ => ⟨fun h0 => hne (keyU Φ hΦ _ f hf h0), fun f' hf' h => ?_⟩⟩,
    fun MM f hf hne => ⟨?_, fun Φ hΦ => ⟨fun h0 => hne (keyD Φ hΦ _ f hf h0), fun f' hf' h => ?_⟩⟩, ?_⟩
  · obtain ⟨u, hu, hfu, hcu⟩ := image_eq_tmul (a₁ := fockAct1 p q r s) (a₂ := fockAct2 p q r s) _ MM.M hr hv
      (hc v) hΦ₀.2.1.2 hΦ₀.2.2.1.2 (GlobalTheory.T.fockModel_dualPair_casimir_apply p q r s Φ₀) f hf.1 hf.2
    have hu0 : u ≠ 0 := fun h0 => hne (keyU Φ₀ hΦ₀ _ f hf (by rw [hfu, h0, TensorProduct.tmul_zero]))
    obtain ⟨B, hB⟩ := GlobalTheory.T.exists_unitary_harishChandra_discreteSeries r s _ (X.ds r s lam')
    have hU := GlobalTheory.T.exists_injective_intertwiner_of_lowest_type h7 h8 r s lam' hp' hg' MM B u
    rw [hB] at hU
    obtain ⟨e, he, hev, hea⟩ := hU v' ⟨hu0, hu⟩ hv' (by rw [hcu, hnumC]) (hc' v') hI'
    refine ⟨LinearMap.range e, ?_, LinearEquiv.ofInjective e he, fun Z x => hea Z x, ?_⟩
    · rintro Z _ ⟨x, rfl⟩; exact ⟨_, hea Z x⟩
    · exact range_eq (a₁ := fockAct1 p q r s) (a₂ := fockAct2 p q r s) _ hI MM.M _ hI'
        (fun M f h1 h2 => keyU Φ₀ hΦ₀ M f ⟨h1, h2⟩) f hf.1 hf.2 e hea hv.1 hv'.1 (by rw [hev, hfu])
  · have := keyU Φ hΦ _ _ (Intw.sub_smul hf' hf 1) (by simp [h])
    simpa [sub_eq_zero] using this
  · have hf1 := fun Z => comm_left (hf.1 Z)
    have hf2 := fun Z => comm_right (hf.2 Z)
    have hcas := GlobalTheory.T.fockModel_dualPair_casimir_apply p q r s Φ₀
    obtain ⟨u, hu, hfu, hcu⟩ := image_eq_tmul (a₁ := fockAct2 p q r s) (a₂ := fockAct1 p q r s)
      (κ := -(((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ)) / 4))
      _ MM.M hr' hv' (hc' v') hΦ₀.2.2.1.2 hΦ₀.2.1.2 (by rw [hcas, neg_smul]; abel) _ hf2 hf1
    have hu0 : u ≠ 0 := fun h0 => hne (keyD Φ₀ hΦ₀ _ f hf (by
      rw [h0, TensorProduct.tmul_zero] at hfu
      exact (TensorProduct.comm ℂ _ _).map_eq_zero_iff.1 hfu))
    obtain ⟨B, hB⟩ := GlobalTheory.T.exists_unitary_harishChandra_discreteSeries p q _ (X.ds p q lam)
    have hU := GlobalTheory.T.exists_injective_intertwiner_of_lowest_type h7 h8 p q lam hp hg MM B u
    rw [hB] at hU
    obtain ⟨e, he, hev, hea⟩ := hU v ⟨hu0, hu⟩ hv (by rw [hcu, hnumC]; congr 1; ring) (hc v) hI
    refine ⟨LinearMap.range e, ?_, LinearEquiv.ofInjective e he, fun Z x => hea Z x, ?_⟩
    · rintro Z _ ⟨x, rfl⟩; exact ⟨_, hea Z x⟩
    · refine range_comm _ (range_eq (a₁ := fockAct2 p q r s) (a₂ := fockAct1 p q r s) _ hI' MM.M _ hI
        (fun M g h1 h2 h0 => ?_) _ hf2 hf1 e hea hv'.1 hv.1 (by rw [hev, hfu]))
      have := keyD Φ₀ hΦ₀ M _ ⟨fun Z => comm_right (h2 Z), fun Z => comm_left (h1 Z)⟩ (by simp [h0])
      exact LinearMap.ext fun P =>
        (TensorProduct.comm ℂ _ _).map_eq_zero_iff.1 (LinearMap.congr_fun this P)
  · have := keyD Φ hΦ _ _ (Intw.sub_smul hf' hf 1) (by simp [h])
    simpa [sub_eq_zero] using this
  · obtain ⟨Tm, -, hT, x₀, y₀, h0⟩ := hii Φ₀ hΦ₀
    obtain ⟨f₀, hf₀, hne⟩ := exists_intw _ _ _ hA Tm hT Φ₀ x₀ y₀ h0
    refine ⟨f₀, hf₀, fun h => hne (by simp [h]), fun f hf => ?_⟩
    obtain ⟨u₀, hu₀, hfu₀, -⟩ := image_eq_tmul (a₁ := fockAct1 p q r s) (a₂ := fockAct2 p q r s) _ _ hr hv
      (hc v) hΦ₀.2.1.2 hΦ₀.2.2.1.2 (GlobalTheory.T.fockModel_dualPair_casimir_apply p q r s Φ₀) f₀ hf₀.1 hf₀.2
    obtain ⟨u, hu, hfu, -⟩ := image_eq_tmul (a₁ := fockAct1 p q r s) (a₂ := fockAct2 p q r s) _ _ hr hv
      (hc v) hΦ₀.2.1.2 hΦ₀.2.2.1.2 (GlobalTheory.T.fockModel_dualPair_casimir_apply p q r s Φ₀) f hf.1 hf.2
    have hu0 : u₀ ≠ 0 := fun h => hne (by rw [hfu₀, h, TensorProduct.tmul_zero])
    obtain ⟨c, hcu⟩ := (finrank_eq_one_iff_of_nonzero' ⟨u₀, hu₀⟩
      (fun h => hu0 (congrArg Subtype.val h))).1 hr' ⟨u, hu⟩
    have hcu' : c • u₀ = u := congrArg Subtype.val hcu
    refine ⟨c, sub_eq_zero.1 (keyU Φ₀ hΦ₀ _ _ (Intw.sub_smul hf hf₀ c) ?_)⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hfu, hfu₀, ← hcu', TensorProduct.tmul_smul, sub_self]

theorem gapGt_mono {p q : ℕ} {lam : Ix p q → ℚ} {m n : ℕ} (h : GapGt lam ((n : ℝ) ^ 3)) (hmn : m ≤ n) :
    GapGt lam ((m : ℝ) ^ 3) := fun a b hab =>
  lt_of_le_of_lt (by gcongr) (h a b hab)

theorem theta_unique : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 →
    ArchimedeanRallisFirst X → ArchimedeanRallisSecond X → ArchimedeanRallisUpDownLine X := by
  intro X _ h2 hD h5 h7 h8 h1 hii
  refine ⟨fun t al be ga de h => ?_, fun t al be ga de h => ?_⟩
  · obtain ⟨⟨hp, hp', -⟩, hs, -⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de h.1
    obtain ⟨hf, hf'⟩ := GlobalTheory.LeastDegree.lowest_least_degree X hD t al be ga de h.1
    have ht := h.1.1
    have hn := h.1.2.1
    refine general X h2 hD h5 h7 h8 (by omega) (by omega) hp hp' (gapGt_mono h.2.1 (by omega))
      (gapGt_mono h.2.2.1 (by omega)) hs hf hf' ?_ (h1.1 _ _ _ _ _ h) (hii.1 _ _ _ _ _ h)
    have := (GlobalTheory.T.casimir_number_identity_dualPair t al be ga de h.1).1
    rw [show al.length + de.length + t + (ga.length + be.length) =
        al.length + be.length + ga.length + de.length + t by omega,
      show al.length + be.length + (ga.length + de.length) =
        al.length + be.length + ga.length + de.length by omega, this]
    push_cast; ring
  · obtain ⟨⟨hp, -, hp'⟩, -, hs⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de h.1
    obtain ⟨hf, hf'⟩ := GlobalTheory.LeastDegree.lowest_least_degree_mirror X hD t al be ga de h.1
    have ht := h.1.1
    have hn := h.1.2.1
    refine general X h2 hD h5 h7 h8 (by omega) (by omega) hp hp' (gapGt_mono h.2.1 (by omega))
      (gapGt_mono h.2.2.1 (by omega)) hs hf hf' ?_ (h1.2 _ _ _ _ _ h) (hii.2 _ _ _ _ _ h)
    obtain ⟨h3, h4⟩ := GlobalTheory.T.casimir_number_identity_dualPair t al be ga de h.1
    rw [show al.length + de.length + (ga.length + be.length + t) =
        al.length + be.length + ga.length + de.length + t by omega,
      show al.length + be.length + (ga.length + de.length) =
        al.length + be.length + ga.length + de.length by omega, h4, h3]
    push_cast; ring

end GlobalTheory.ThetaUnique
