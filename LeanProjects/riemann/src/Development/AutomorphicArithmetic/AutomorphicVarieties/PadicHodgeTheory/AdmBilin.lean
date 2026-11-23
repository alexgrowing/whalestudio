import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInjStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.AdmBilin

variable {G Q : Type} (F : Type) {B : Type} [Field Q] [Field F] [CommRing B] [Algebra Q F] [Algebra Q B] [Algebra F B]
  [IsScalarTower Q F B] (a : G → B →ₐ[Q] B) (ha : ∀ g (c : F), a g (algebraMap F B c) = algebraMap F B c)
  {V V' W : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V'] [AddCommGroup W] [Module Q W]

private def sig (ρ : G → V →ₗ[Q] V) (g : G) : B ⊗[Q] V →ₗ[Q] B ⊗[Q] V :=
  TensorProduct.map (a g).toLinearMap (ρ g)

private theorem sig_tmul (ρ : G → V →ₗ[Q] V) (g : G) (b : B) (v : V) :
    sig a ρ g (b ⊗ₜ[Q] v) = a g b ⊗ₜ[Q] ρ g v := rfl

private theorem sig_smul (ρ : G → V →ₗ[Q] V) (g : G) (b : B) (w : B ⊗[Q] V) :
    sig a ρ g (b • w) = a g b • sig a ρ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [sig_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private def DD (ρ : G → V →ₗ[Q] V) : Submodule F (B ⊗[Q] V) where
  carrier := {w | ∀ g, sig a ρ g w = w}
  zero_mem' := fun g => map_zero _
  add_mem' := fun hx hy g => by rw [map_add, hx g, hy g]
  smul_mem' := fun c x hx g => by rw [← algebraMap_smul B, sig_smul, ha, hx g]

private theorem finrank_swap (ρ : G → V →ₗ[Q] V) (D : Submodule Q (V ⊗[Q] B))
    (hD : ∀ x, x ∈ D ↔ ∀ g, TensorProduct.map (ρ g) (a g).toLinearMap x = x) :
    finrank Q ↥D = finrank Q F * finrank F ↥(DD F a ha ρ) := by
  have hc : ∀ g w, TensorProduct.comm Q B V (sig a ρ g w) =
      TensorProduct.map (ρ g) (a g).toLinearMap (TensorProduct.comm Q B V w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [sig_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let e : ↥(DD F a ha ρ) ≃ₗ[Q] ↥D :=
    { toFun := fun x => ⟨TensorProduct.comm Q B V x, (hD _).2 fun g => by rw [← hc, x.2 g]⟩
      invFun := fun y => ⟨(TensorProduct.comm Q B V).symm y, fun g => by
        apply (TensorProduct.comm Q B V).injective
        rw [hc, LinearEquiv.apply_symm_apply, (hD _).1 y.2 g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Q B V) c _)
      left_inv := fun x => Subtype.ext ((TensorProduct.comm Q B V).symm_apply_apply _)
      right_inv := fun y => Subtype.ext ((TensorProduct.comm Q B V).apply_symm_apply _) }
  rw [Module.finrank_mul_finrank, e.finrank_eq]

private theorem span_bilin (ρ : G → V →ₗ[Q] V) (ρ' : G → V' →ₗ[Q] V') (π : G → W →ₗ[Q] W)
    (b : V →ₗ[Q] V' →ₗ[Q] W) (hb : ∀ g x y, b (ρ g x) (ρ' g y) = π g (b x y))
    (hs : Submodule.span Q (Set.range fun p : V × V' => b p.1 p.2) = ⊤)
    (h : Submodule.span B (DD F a ha ρ : Set (B ⊗[Q] V)) = ⊤)
    (h' : Submodule.span B (DD F a ha ρ' : Set (B ⊗[Q] V')) = ⊤) :
    Submodule.span B (DD F a ha π : Set (B ⊗[Q] W)) = ⊤ := by
  let m : B ⊗[Q] V →ₗ[B] B ⊗[Q] V' →ₗ[B] B ⊗[Q] W :=
    (TensorProduct.mk B (B ⊗[Q] V) (B ⊗[Q] V')).compr₂
      ((TensorProduct.lift b).baseChange B ∘ₗ (AlgebraTensorModule.distribBaseChange Q B V V').symm.toLinearMap)
  have hm : ∀ c c' v v', m (c ⊗ₜ v) (c' ⊗ₜ v') = (c * c') ⊗ₜ b v v' := by
    intro c c' v v'
    simp [m]
  have hG : ∀ g x y, sig a π g (m x y) = m (sig a ρ g x) (sig a ρ' g y) := by
    intro g x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul c v =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' => simp only [map_add, hx, hx']
      | tmul c' v' => simp only [sig_tmul, hm, map_mul, hb]
  set S := Submodule.span B (DD F a ha π : Set (B ⊗[Q] W))
  have key : ∀ x y, m x y ∈ S := by
    intro x y
    have h1 : Submodule.map₂ m (Submodule.span B (DD F a ha ρ : Set (B ⊗[Q] V)))
        (Submodule.span B (DD F a ha ρ' : Set (B ⊗[Q] V'))) ≤ S := by
      rw [Submodule.map₂_span_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩ g
      rw [hG, hx g, hy g]
    exact h1 (Submodule.apply_mem_map₂ m (h ▸ Submodule.mem_top) (h' ▸ Submodule.mem_top))
  refine GlobalTheory.RegularRing.eq_top_of_tmul _ fun c w => ?_
  have hw : w ∈ Submodule.span Q (Set.range fun p : V × V' => b p.1 p.2) := hs ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    have := key (c ⊗ₜ p.1) (1 ⊗ₜ p.2)
    rwa [hm, mul_one] at this
  | zero => simp
  | add x y _ _ hx hy => rw [tmul_add]; exact S.add_mem hx hy
  | smul q x _ hx => rw [tmul_smul, ← algebraMap_smul B]; exact S.smul_mem _ hx

variable [IsDomain B]
  (hf : ∀ b b' : B, b ≠ 0 → (∀ g, b * a g b' = a g b * b') → ∃ c : F, b' = algebraMap F B c * b)
  (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : Q, a g b = algebraMap Q B x * b) → IsUnit b)

include hf in
private theorem indepB (ρ : G → V →ₗ[Q] V) {ι : Type} (d : ι → ↥(DD F a ha ρ))
    (hd : LinearIndependent F d) : LinearIndependent B fun i => (d i : B ⊗[Q] V) := by
  have h1 : LinearIndependent F fun i => (d i : B ⊗[Q] V) :=
    hd.map' (DD F a ha ρ).subtype (DD F a ha ρ).ker_subtype
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact GlobalTheory.RegularRing.linearIndepOn_of_invariant (fun g b => a g b) (fun g => (sig a ρ g).toAddMonoidHom)
    (sig_smul a ρ) hf _ (fun g i => (d i).2 g) s (h1.linearIndepOn _)

include hf in
private theorem finite_le [FiniteDimensional Q V] (ρ : G → V →ₗ[Q] V) :
    Module.Finite F ↥(DD F a ha ρ) ∧ finrank F ↥(DD F a ha ρ) ≤ finrank Q V := by
  have hr : Module.rank F ↥(DD F a ha ρ) ≤ finrank Q V := by
    refine rank_le fun s hs => ?_
    simpa using LinearIndependent.fintype_card_le_finrank (indepB F a ha hf ρ _ hs)
  haveI : Module.Finite F ↥(DD F a ha ρ) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0
  exact ⟨inferInstance, finrank_le_of_rank_le hr⟩

include hu in
private theorem span_eq_top_of_invariant [FiniteDimensional Q V] (ρ : G → V →ₗ[Q] V)
    (d : Fin (finrank Q V) → B ⊗[Q] V) (hd : ∀ g i, sig a ρ g (d i) = d i)
    (hi : LinearIndependent B d) : Submodule.span B (Set.range d) = ⊤ := by
  classical
  let v := Module.finBasis Q V
  let e := Algebra.TensorProduct.basis B v
  let A := e.toMatrix d
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext i
    refine Fintype.linearIndependent_iff.1 hi c ?_ i
    apply e.repr.injective
    ext j
    have := congrFun hc0 j
    simp only [Matrix.mulVec, dotProduct, A, Basis.toMatrix_apply, Pi.zero_apply] at this
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hrep : ∀ g (w : B ⊗[Q] V) k, e.repr (sig a ρ g w) k =
      ∑ j, algebraMap Q B (v.repr (ρ g (v j)) k) * a g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    simp only [map_sum, sig_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  have hdet : IsUnit A.det := by
    refine hu _ hA fun g => ?_
    let M : Matrix (Fin (finrank Q V)) (Fin (finrank Q V)) Q := fun k j => v.repr (ρ g (v j)) k
    have h1 : A = (algebraMap Q B).mapMatrix M * (a g : B →+* B).mapMatrix A := by
      ext k i
      rw [Matrix.mul_apply]
      change e.repr (d i) k = _
      conv_lhs => rw [← hd g i, hrep]
      rfl
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det] at h2
    have h3 : M.det ≠ 0 := fun h => hA (by rw [h2, h, map_zero, zero_mul])
    refine ⟨M.det⁻¹, ?_⟩
    conv_rhs => rw [h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h3, map_one, one_mul]
    rfl
  exact ((Basis.is_basis_iff_det e).2 hdet).2

include hf hu in
private theorem admissible_iff_span_top [FiniteDimensional Q V] (ρ : G → V →ₗ[Q] V) :
    finrank F ↥(DD F a ha ρ) = finrank Q V ↔ Submodule.span B (DD F a ha ρ : Set (B ⊗[Q] V)) = ⊤ := by
  obtain ⟨h1, h2⟩ := finite_le F a ha hf ρ
  constructor
  · intro h
    let e := Module.finBasisOfFinrankEq F _ h
    rw [eq_top_iff, ← span_eq_top_of_invariant a hu ρ (fun i => e i)
      (fun g i => (e i).2 g) (indepB F a ha hf ρ e e.linearIndependent)]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact (e i).2
  · intro h
    refine le_antisymm h2 ?_
    have hs : Function.Surjective ((DD F a ha ρ).subtype.liftBaseChange B) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, Submodule.range_subtype, h]
    simpa using LinearMap.finrank_le_finrank_of_surjective hs

include ha hf hu in
private theorem admissible_bilinear_image [FiniteDimensional Q F] [FiniteDimensional Q V] [FiniteDimensional Q V']
    [FiniteDimensional Q W] (ρ : G → V →ₗ[Q] V) (ρ' : G → V' →ₗ[Q] V') (π : G → W →ₗ[Q] W)
    (b : V →ₗ[Q] V' →ₗ[Q] W) (hb : ∀ g x y, b (ρ g x) (ρ' g y) = π g (b x y))
    (hs : Submodule.span Q (Set.range fun p : V × V' => b p.1 p.2) = ⊤)
    (D : Submodule Q (V ⊗[Q] B)) (hD : ∀ x, x ∈ D ↔ ∀ g, TensorProduct.map (ρ g) (a g).toLinearMap x = x)
    (D' : Submodule Q (V' ⊗[Q] B)) (hD' : ∀ x, x ∈ D' ↔ ∀ g, TensorProduct.map (ρ' g) (a g).toLinearMap x = x)
    (E : Submodule Q (W ⊗[Q] B)) (hE : ∀ x, x ∈ E ↔ ∀ g, TensorProduct.map (π g) (a g).toLinearMap x = x)
    (h : finrank Q ↥D = finrank Q F * finrank Q V) (h' : finrank Q ↥D' = finrank Q F * finrank Q V') :
    finrank Q ↥E = finrank Q F * finrank Q W := by
  have h0 : 0 < finrank Q F := finrank_pos
  rw [finrank_swap F a ha ρ D hD] at h
  rw [finrank_swap F a ha ρ' D' hD'] at h'
  rw [finrank_swap F a ha π E hE, (admissible_iff_span_top F a ha hf hu π).2 (span_bilin F a ha ρ ρ' π b hb hs
    ((admissible_iff_span_top F a ha hf hu ρ).1 (Nat.eq_of_mul_eq_mul_left h0 h))
    ((admissible_iff_span_top F a ha hf hu ρ').1 (Nat.eq_of_mul_eq_mul_left h0 h')))]

end UpperTheory.V.Loc.AdmBilin

end

theorem UpperTheory.V.Loc.admissible_of_bilinear_openSubgroup_galois :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] W, (∀ g x y, b (ρ g x) (ρ' g y) = π g (b x y)) → Submodule.span ℚ_[l] (Set.range fun p : V × V' => b p.1 p.2) = ⊤ → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hs
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := UpperTheory.V.Loc.openField φ hφ
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l (PP l) (AIP l) T
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have eB : ∀ g z, (PP l).actQ (φ g) z = ((PP l).PD K).actB (e g) z := fun g z => by
    rw [hφe, (PP l).PD_actB]
  have eD : ∀ g z, (PP l).actQdR (φ g) z = ((PP l).PD K).actdR (e g) z := fun g z => by
    rw [hφe, (PP l).PD_actdR]
  have := ((PP l).PD K).finK₀
  have := ((PP l).PD K).finK
  have hF : IsField (Bdr l) := GlobalTheory.RegularRing.isField_of_tied T
  constructor
  · intro h h'
    have : IsDomain (Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T K
    unfold IsCr at h h' ⊢
    rw [hK0] at h h' ⊢
    refine AdmBilin.admissible_bilinear_image ↥(K0 K) (fun g => ((PP l).actQ (φ g) : Bcr l →ₐ[ℚ_[l]] Bcr l)) (fun g c => ?_)
      (fun x y hx hxy => ?_) (fun x hx hxy => ?_) (resCoef ℚ_[l] ρ) (resCoef ℚ_[l] ρ') (resCoef ℚ_[l] π) b hb hs
      _ (fun x => ?_) _ (fun x => ?_) _ (fun x => ?_) h h'
    · exact (eB g _).trans (AlgEquiv.commutes _ c)
    · refine GlobalTheory.RegularRing.fracInv hfit (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C) K x y hx fun g => ?_
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← eB, ← eB]
      exact hxy g
    · refine GlobalTheory.RegularRing.lineUnit hfit (GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)) K x hx fun g => ?_
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← eB]
      exact hxy g
    all_goals
      simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rfl
  · intro h h'
    have : IsDomain (Bdr l) := hF.isDomain
    unfold IsDr at h h' ⊢
    rw [hK] at h h' ⊢
    refine AdmBilin.admissible_bilinear_image ↥K.1 (fun g => ((PP l).actQdR (φ g) : Bdr l →ₐ[ℚ_[l]] Bdr l)) (fun g c => ?_)
      (fun x y hx hxy => ?_) (fun x hx _ => ?_) (resCoef ℚ_[l] ρ) (resCoef ℚ_[l] ρ') (resCoef ℚ_[l] π) b hb hs
      _ (fun x => ?_) _ (fun x => ?_) _ (fun x => ?_) h h'
    · exact (eD g _).trans (AlgEquiv.commutes _ c)
    · refine GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF x y hx fun g => ?_
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← eD, ← eD]
      exact hxy g
    · obtain ⟨u, hu⟩ := hF.mul_inv_cancel hx
      exact IsUnit.of_mul_eq_one u hu
    all_goals
      simp only [Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rfl
