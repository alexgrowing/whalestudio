import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSum

open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

section Linear

variable {F : Type} [Field F] {ι : Type} [Fintype ι] {W : ι → Type} {W' : Type} [∀ i, AddCommGroup (W i)]
  [AddCommGroup W'] [∀ i, Module F (W i)] [Module F W']

theorem finrank_eq_sum (E : W' ≃ₗ[F] (∀ i, W i)) (S' : Submodule F W') (S : ∀ i, Submodule F (W i))
    [∀ i, FiniteDimensional F ↥(S i)] (h : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S i) :
    finrank F ↥S' = ∑ i, finrank F ↥(S i) := by
  let e : ↥S' ≃ₗ[F] (∀ i, ↥(S i)) :=
    { toFun := fun x i => ⟨E x i, (h x).1 x.2 i⟩
      invFun := fun y => ⟨E.symm fun i => (y i : W i), (h _).2 fun i => by simp⟩
      map_add' := fun x y => by funext i; apply Subtype.ext; simp
      map_smul' := fun c x => by funext i; apply Subtype.ext; simp
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun y => by funext i; apply Subtype.ext; simp }
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end Linear

section Tensor

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL] {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module LL (V i)] [∀ i, Module Qp (V i)]
  [∀ i, IsScalarTower Qp LL (V i)]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  (E : V' ≃ₗ[LL] (∀ i, V i))

def tensComp (C : Type) [AddCommGroup C] [Module Qp C] :
    V' ⊗[Qp] C ≃ₗ[LL] (∀ i, V i ⊗[Qp] C) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i => AlgebraTensorModule.map (LinearMap.proj i ∘ₗ E.toLinearMap) LinearMap.id)
    (∑ i, AlgebraTensorModule.map (E.symm.toLinearMap ∘ₗ LinearMap.single LL V i)
      LinearMap.id ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.pi_ext' fun j => ?_
      refine AlgebraTensorModule.ext fun v c => ?_
      funext i
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.single_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h])
    (by
      refine AlgebraTensorModule.ext fun v c => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.proj_apply, LinearMap.pi_apply, AlgebraTensorModule.map_tmul,
        LinearMap.single_apply, LinearEquiv.coe_coe]
      rw [← sum_tmul, ← map_sum, Finset.univ_sum_single, E.symm_apply_apply])

@[simp] theorem tensComp_tmul {C : Type} [AddCommGroup C] [Module Qp C] (v : V') (c : C) (i : ι) :
    tensComp E C (v ⊗ₜ[Qp] c) i = E v i ⊗ₜ[Qp] c := rfl

theorem tensComp_map {C D : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D]
    (φ' : V' →ₗ[LL] V') (φ : ∀ i, V i →ₗ[LL] V i) (h : ∀ x i, E (φ' x) i = φ i (E x i)) (ψ : C →ₗ[Qp] D)
    (x : V' ⊗[Qp] C) (i : ι) :
    tensComp E D (AlgebraTensorModule.map φ' ψ x) i =
      AlgebraTensorModule.map (φ i) ψ (tensComp E C x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [h]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

end Tensor

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module LL (V i)] [∀ i, Module Qp (V i)]
    [∀ i, IsScalarTower Qp LL (V i)]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : ∀ i, Representation LL G (V i)} {ρ' : Representation LL G V'} {E : V' ≃ₗ[LL] (∀ i, V i)}
    (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dcris_iff (x : V' ⊗[Qp] B) : x ∈ Dcris PD ρ' ↔ ∀ i, tensComp E B x i ∈ Dcris PD (ρ i) := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (tensComp E B).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  rw [actVB, tensComp_map E _ _ (hE g)]
  rfl

theorem mem_DdR_iff (x : V' ⊗[Qp] BdR) : x ∈ DdR PD ρ' ↔ ∀ i, tensComp E BdR x i ∈ DdR PD (ρ i) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (tensComp E BdR).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  rw [actVdR, tensComp_map E _ _ (hE g)]
  rfl

theorem mem_FildR_iff (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V' ⊗[Qp] BdR) :
    x ∈ FildR PD ρ' τ a ↔ ∀ i, tensComp E BdR x i ∈ FildR PD (ρ i) τ a := by
  simp only [FildR, DdRE, Submodule.mem_inf, forall_and]
  refine and_congr (and_congr (mem_DdR_iff PD hE x) ?_) ?_
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
    rw [forall_comm]
    refine forall_congr' fun c => ?_
    rw [← (tensComp E BdR).injective.eq_iff, funext_iff, map_smul]
    refine forall_congr' fun i => ?_
    rw [mulVdR, tensComp_map E _ (fun _ => LinearMap.id) (fun _ _ => rfl)]
    rfl
  · constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨_, (tensComp_map E _ (fun _ => LinearMap.id) (fun _ _ => rfl) _ y i).symm⟩
    · intro h
      choose y hy using h
      refine ⟨(tensComp E _).symm y, (tensComp E BdR).injective ?_⟩
      funext i
      rw [tensComp_map E _ (fun _ => LinearMap.id) (fun _ _ => rfl), LinearEquiv.apply_symm_apply, hy]

theorem isCrys_sum [∀ i, FiniteDimensional LL (V i)] (h : ∀ i, IsCrys PD (ρ i)) : IsCrys PD ρ' := by
  have hK : FiniteDimensional Qp K₀ := by
    have := PD.finK
    exact Module.Finite.of_injective (IsScalarTower.toAlgHom Qp K₀ K).toLinearMap (algebraMap K₀ K).injective
  have : ∀ i, FiniteDimensional LL ↥(Dcris PD (ρ i)) := fun i => by
    rcases subsingleton_or_nontrivial (V i) with hs | hs
    · infer_instance
    · exact Module.finite_of_finrank_pos (h i ▸ Nat.mul_pos finrank_pos finrank_pos)
  unfold IsCrys at h ⊢
  rw [finrank_eq_sum (tensComp E B) _ _ (mem_Dcris_iff PD hE), E.finrank_eq, Module.finrank_pi_fintype,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

theorem finrank_DdR_sum [∀ i, FiniteDimensional LL ↥(DdR PD (ρ i))] :
    finrank LL ↥(DdR PD ρ') = ∑ i, finrank LL ↥(DdR PD (ρ i)) :=
  finrank_eq_sum (tensComp E BdR) _ _ (mem_DdR_iff PD hE)

theorem multV_sum [∀ i, FiniteDimensional LL ↥(DdR PD (ρ i))] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ' τ a = ∑ i, multV PD (ρ i) τ a := by
  have h := fun b =>
    haveI := fun i => GlobalTheory.Pst.finiteDimensional_filDR PD (ρ i) τ b
    finrank_eq_sum (tensComp E BdR) _ _ (mem_FildR_iff PD hE τ b)
  simp only [multV, h, Finset.sum_sub_distrib, Nat.cast_sum]

end Period

section Block

open Matrix

variable {Γ : Type} [Group Γ] {ι : Type} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {n : ℕ}
  (e : (Σ j, Fin (a j)) ≃ Fin n)

def blockHom (k : Type) [CommRing k] : (∀ j, Matrix (Fin (a j)) (Fin (a j)) k) →+* Matrix (Fin n) (Fin n) k :=
  (Matrix.reindexAlgEquiv k k e).toRingEquiv.toRingHom.comp (Matrix.blockDiagonal'RingHom (fun j => Fin (a j)) k)

def blockRep {k : Type} [CommRing k] (r : ∀ j, Γ →* GL (Fin (a j)) k) : Γ →* GL (Fin n) k :=
  MonoidHom.toHomUnits ((blockHom e k).toMonoidHom.comp (MonoidHom.pi fun j => (Units.coeHom _).comp (r j)))

variable {k : Type} [CommRing k] (r : ∀ j, Γ →* GL (Fin (a j)) k)

theorem blockRep_val (g : Γ) : (blockRep e r g).val = reindex e e (blockDiagonal' fun j => (r j g).val) := rfl

theorem charpoly_blockRep (g : Γ) : (blockRep e r g).val.charpoly = ∏ j, (r j g).val.charpoly := by
  rw [blockRep_val, charpoly_reindex]
  simp only [charpoly]
  rw [← GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  congr 1
  ext ⟨i, x⟩ ⟨j, y⟩ : 2
  by_cases h : i = j
  · subst h
    simp [charmatrix_apply, blockDiagonal'_apply_eq, diagonal_apply]
  · rw [charmatrix_apply_ne _ _ _ (fun h' => h (congrArg Sigma.fst h')), blockDiagonal'_apply_ne _ _ _ h,
      blockDiagonal'_apply_ne _ _ _ h]
    simp

theorem continuous_blockRep [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace k]
    (h : ∀ j, Continuous (r j)) : Continuous (blockRep e r) := by
  have hv : Continuous fun g => (blockRep e r g).val :=
    (Continuous.matrix_blockDiagonal' (continuous_pi fun j => Units.continuous_val.comp (h j))).matrix_submatrix _ _
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [← map_inv]
  exact hv.comp continuous_inv

theorem mapRep_blockRep {k' : Type} [CommRing k'] (f : k →+* k') :
    Formalism.MainNotions.N.mapRep f (blockRep e r) = blockRep e fun j => Formalism.MainNotions.N.mapRep f (r j) := by
  refine MonoidHom.ext fun g => Units.ext ?_
  change (reindex e e (blockDiagonal' fun j => (r j g).val)).map f =
    reindex e e (blockDiagonal' fun j => (r j g).val.map f)
  rw [← blockDiagonal'_map _ _ (map_zero f)]
  rfl

variable (k) in

def vecComp : (Fin n → k) ≃ₗ[k] (∀ j, Fin (a j) → k) :=
  (LinearEquiv.funCongrLeft k k e).trans (LinearEquiv.piCurry k fun _ _ => k)

theorem vecComp_mulVec (g : Γ) (x : Fin n → k) (i : ι) :
    vecComp e k ((blockRep e r g).val *ᵥ x) i = (r i g).val *ᵥ vecComp e k x i := by
  funext y
  change ((blockRep e r g).val *ᵥ x) (e ⟨i, y⟩) = ∑ z, (r i g).val y z * x (e ⟨i, z⟩)
  rw [blockRep_val, mulVec, dotProduct, ← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [blockDiagonal'_apply_ne _ _ _ (Ne.symm hj)]
  · simp

end Block

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst
open Formalism.MainNotions.N (mapRep)

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O)
  {ι : Type} [Fintype ι] [DecidableEq ι] {a : ι → ℕ} {n : ℕ} (e : (Σ j, Fin (a j)) ≃ Fin n)
  {r : ∀ j, ↥Gw →* GL (Fin (a j)) (Om l)}

omit [DecidableEq ι] in

theorem exists_common_model (h : ∀ j, ∃ L r', IsModel Bw (r j) L r') (L₀ : FinExt l) :
    ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧ ∃ r' : ∀ j, ↥Gw →* GL (Fin (a j)) ↥L.1,
      ∀ j, IsModel Bw (r j) L (r' j) := by
  choose L r' hr using h
  have := fun j => (L j).2
  let M : FinExt l := supExt (supExt L₀ Bw.LL)
    ⟨⨆ j, (L j).1, IntermediateField.finiteDimensional_iSup_of_finite⟩
  have hl : ∀ j, (L j).1 ≤ M.1 := fun j => (le_iSup (fun j => (L j).1) j).trans le_sup_right
  exact ⟨M, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, _, fun j => (hr j).enlarge (hl j)⟩

theorem isModel_blockRep {L : FinExt l} (hL : Bw.LL.1 ≤ L.1) {r' : ∀ j, ↥Gw →* GL (Fin (a j)) ↥L.1}
    (h : ∀ j, IsModel Bw (r j) L (r' j)) : IsModel Bw (blockRep e r) L (blockRep e r') :=
  ⟨hL, by rw [mapRep_blockRep]; exact congrArg _ (funext fun j => (h j).2)⟩

theorem vecComp_repE {L : FinExt l} (r' : ∀ j, ↥Gw →* GL (Fin (a j)) ↥L.1) (g : ↥(GK Bw.Kw))
    (x : Fin n → ↥L.1) (i : ι) :
    vecComp e _ (Bw.repE L (blockRep e r') g x) i = Bw.repE L (r' i) g (vecComp e _ x i) :=
  vecComp_mulVec e r' (Bw.e.symm g) x i

theorem isCrysAt_blockRep (h : ∀ j, IsCrysAt P Bw (r j)) : IsCrysAt P Bw (blockRep e r) := by
  obtain ⟨L, -, hL, r', hr⟩ := exists_common_model Bw (fun j => (h j).imp fun _ h => h.imp fun _ h => h.1) Bw.LL
  exact ⟨L, _, isModel_blockRep Bw e hL hr,
    isCrys_sum _ (vecComp_repE Bw e r') fun j => ((hr j).isCrysAt_iff P).1 (h j)⟩

theorem isJumpsAt_blockRep {τ : E →+* Om l} {L₀ : FinExt l} {τ₀ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L₀.1}
    (hτ : IsInduced Bw τ τ₀) {J : ι → Multiset ℤ} (h : ∀ j, IsJumpsAt P Bw (r j) τ (J j)) :
    IsJumpsAt P Bw (blockRep e r) τ (∑ j, J j) := by
  obtain ⟨L, h₀, hL, r', hr⟩ := exists_common_model Bw (fun j => (h j).imp fun _ h => h.imp fun _ h => h.1) L₀
  have hd : ∀ j, Bw.IsdRE P L (r' j) := fun j => ((hr j).isdRAt_iff P).1
    ((h j).imp fun _ h => h.imp fun _ h => ⟨h.1, h.2.1⟩)
  have hf := fun j => finiteDimensional_DdR _ _ (hd j)
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion h₀).comp τ₀) := hτ
  have hn : n = ∑ j, a j := by simpa using (Fintype.card_congr e).symm
  refine ⟨L, _, isModel_blockRep Bw e hL hr, ?_, _, hτ', fun m => ?_⟩
  · rw [LocBridge.IsdRE, finrank_DdR_sum _ (vecComp_repE Bw e r'), hn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hd j
  · rw [LocBridge.multE, multV_sum _ (vecComp_repE Bw e r'), Multiset.count_sum', Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => (h j).count_eq P (hr j) hτ' m

end Local

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

theorem exists_sum (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ)
    [Fact l.Prime] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (a : ι' → ℕ) (n : ℕ) (hn : ∑ j, a j = n)
    (r : ∀ j, G E Ω →* GL (Fin (a j)) (Qbar l)) (hr : ∀ j, Continuous (r j)) :
    ∃ R : G E Ω →* GL (Fin n) (Qbar l), Continuous R ∧
      (∀ J : ι' → (E →+* Qbar l) → Multiset ℤ, (∀ j, GlobalTheory.ExpFrame.CrysWith (r j) (J j)) →
        GlobalTheory.ExpFrame.CrysWith R (fun τ => ∑ j, J j τ)) ∧
      ∀ g, (R g).val.charpoly = ∏ j, (r j g).val.charpoly := by
  let e : (Σ j, Fin (a j)) ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hn)
  refine ⟨blockRep e r, continuous_blockRep e r hr, fun J hJ => ⟨continuous_blockRep e r hr, ?_⟩,
    charpoly_blockRep e r⟩
  intro P AI hT w A hA O _ _ _ Bw hB
  have h := fun j => (hJ j).2 P AI hT w A hA O Bw hB
  exact ⟨isCrysAt_blockRep P Bw e fun j => (h j).1,
    fun τ LL' τ' hτ => isJumpsAt_blockRep P Bw e hτ fun j => (h j).2 τ LL' τ' hτ⟩

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices →
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι' : Type) [Fintype ι'] [DecidableEq ι'] (a : ι' → ℕ) (n : ℕ), ∑ j, a j = n →
    ∀ (r : ∀ j, G E Ω →* GL (Fin (a j)) (Qbar l)), (∀ j, Continuous (r j)) →
    ∃ R : G E Ω →* GL (Fin n) (Qbar l), Continuous R ∧
      (∀ J : ι' → (E →+* Qbar l) → Multiset ℤ, (∀ j, GlobalTheory.ExpFrame.CrysWith (r j) (J j)) →
        GlobalTheory.ExpFrame.CrysWith R (fun τ => ∑ j, J j τ)) ∧
      ∀ g, (R g).val.charpoly = ∏ j, (r j g).val.charpoly :=
  fun _ => exists_sum

end GlobalTheory.BlockSum
