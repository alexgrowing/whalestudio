import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CoeffBC

section General

variable {L L' : Type} [Field L] [Field L'] [Algebra L L'] {ι : Type} [Fintype ι] [DecidableEq ι]
  {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L' M'] [Module L M']
  {N N' : Type} [AddCommGroup N] [Module L N] [AddCommGroup N'] [Module L' N'] [Module L N']

def IsCoord (u : ι → L') (J : M →ₗ[L] M') (π : ι → M' →ₗ[L] M) : Prop :=
  (∀ x, ∑ k, u k • J (π k x) = x) ∧ ∀ k l m, π k (u l • J m) = if k = l then m else 0

def Rel (π : ι → M' →ₗ[L] M) (S : Submodule L M) (S' : Submodule L' M') : Prop :=
  ∀ x, x ∈ S' ↔ ∀ k, π k x ∈ S

theorem exists_isCoord [IsScalarTower L L' M'] (u : Basis ι L L') (J : M →ₗ[L] M')
    (h : IsBaseChange L' J) : ∃ π : ι → M' →ₗ[L] M, IsCoord u J π := by
  let π : ι → M' →ₗ[L] M := fun k =>
    (TensorProduct.lid L M).toLinearMap ∘ₗ LinearMap.rTensor M (u.coord k) ∘ₗ
      (h.equiv.symm.toLinearMap.restrictScalars L)
  have hπ : ∀ k (s : L') (m : M), π k (s • J m) = u.repr s k • m := by
    intro k s m
    have : h.equiv.symm (s • J m) = s ⊗ₜ[L] m := by
      rw [LinearEquiv.symm_apply_eq, h.equiv_tmul]
    simp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, this]
    simp
  refine ⟨π, fun x => ?_, fun k l m => ?_⟩
  · obtain ⟨y, rfl⟩ := h.equiv.surjective x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [h.equiv_tmul]
      simp only [hπ, map_smul]
      conv_rhs => rw [← u.sum_repr s, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, smul_comm]
    | add a b ha hb =>
      simp only [map_add, smul_add, Finset.sum_add_distrib, ha, hb]
  · rw [hπ, u.repr_self, Finsupp.single_apply]
    by_cases hk : k = l
    · simp [hk]
    · simp [hk, Ne.symm hk]

variable {u : ι → L'} {J : M →ₗ[L] M'} {π : ι → M' →ₗ[L] M}
  {JN : N →ₗ[L] N'} {πN : ι → N' →ₗ[L] N}

theorem IsCoord.sum (h : IsCoord u J π) (m : ι → M) (k : ι) :
    π k (∑ l, u l • J (m l)) = m k := by
  simp [map_sum, h.2]

theorem IsCoord.comm (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) (k : ι) (x : N') :
    π k (f' x) = f (πN k x) := by
  conv_lhs => rw [← hN.1 x]
  simp only [map_sum f', map_smul, hf]
  exact h.sum _ k

theorem IsCoord.rel_ker (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel πN (LinearMap.ker f) (LinearMap.ker f') := by
  intro x
  simp only [LinearMap.mem_ker, ← h.comm hN f f' hf]
  refine ⟨fun hx k => by simp [hx], fun hx => ?_⟩
  rw [← h.1 (f' x)]
  simp [hx]

theorem IsCoord.rel_range (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel π (LinearMap.range f) (LinearMap.range f') := by
  intro x
  constructor
  · rintro ⟨y, rfl⟩ k
    exact ⟨_, (h.comm hN f f' hf k y).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨∑ k, u k • JN (y k), ?_⟩
    simp only [map_sum, map_smul, hf, hy]
    exact h.1 x

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.inf {S T : Submodule L M} {S' T' : Submodule L' M'} (h : Rel π S S')
    (h' : Rel π T T') : Rel π (S ⊓ T) (S' ⊓ T') := by
  intro x
  simp only [Submodule.mem_inf, h x, h' x, forall_and]

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.iInf {κ : Type} {S : κ → Submodule L M} {S' : κ → Submodule L' M'}
    (h : ∀ i, Rel π (S i) (S' i)) : Rel π (⨅ i, S i) (⨅ i, S' i) := by
  intro x
  simp only [Submodule.mem_iInf, fun i => h i x]
  exact forall_comm

theorem IsCoord.nonempty_equiv [IsScalarTower L L' M'] (h : IsCoord u J π) {S : Submodule L M}
    {S' : Submodule L' M'} (hS : Rel π S S') : Nonempty (S' ≃ₗ[L] (ι → S)) := by
  let F : S' →ₗ[L] (ι → S) := LinearMap.pi fun k =>
    LinearMap.codRestrict S (π k ∘ₗ (S'.subtype.restrictScalars L))
      (fun x => (hS x.1).1 x.2 k)
  have hF : ∀ x k, (F x k : M) = π k x := fun _ _ => rfl
  refine ⟨LinearEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    rw [← h.1 x, ← h.1 y]
    simp only [← hF, hxy]
  · intro m
    refine ⟨⟨∑ l, u l • J (m l), (hS _).2 fun k => ?_⟩, ?_⟩
    · rw [h.sum (fun l => (m l : M))]; exact (m k).2
    · funext k
      apply Subtype.ext
      rw [hF]
      exact h.sum (fun l => (m l : M)) k

theorem IsCoord.finrank_eq [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    finrank L' S' = finrank L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  have h1 : finrank L L' * finrank L' S' = finrank L S' := Module.finrank_mul_finrank L L' S'
  have h2 : finrank L (ι → S) = Fintype.card ι * finrank L S := by
    simp [Module.finrank, rank_fun_eq_lift_mul]
  rw [e.finrank_eq, h2, ← Module.finrank_eq_card_basis u] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem IsCoord.finite_iff [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    Module.Finite L' S' ↔ Module.Finite L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  obtain ⟨k⟩ := u.index_nonempty
  constructor
  · intro _
    haveI : Module.Finite L S' := Module.Finite.trans L' S'
    haveI : Module.Finite L (ι → S) := Module.Finite.equiv e
    exact Module.Finite.of_surjective (LinearMap.proj k : (ι → S) →ₗ[L] S)
      (LinearMap.proj_surjective k)
  · intro _
    haveI : Module.Finite L S' := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite L L' S'

theorem IsCoord.tensor {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    (h : IsCoord u J π) (C : Type) [AddCommGroup C] [Module Q C] :
    IsCoord u (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C))
      (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : C →ₗ[Q] C)) := by
  constructor
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, h.1]
    | add a b ha hb => simp only [map_add, smul_add, Finset.sum_add_distrib, ha, hb]
  · intro k l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul', h.2]
      split_ifs <;> simp
    | add a b ha hb =>
      simp only [map_add, smul_add, ha, hb]
      split_ifs <;> simp

theorem map_comm {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    {C D : Type} [AddCommGroup C] [Module Q C] [AddCommGroup D] [Module Q D]
    (f : M →ₗ[L] M) (f' : M' →ₗ[L'] M') (hf : ∀ m, f' (J m) = J (f m)) (φ : C →ₗ[Q] D)
    (y : M ⊗[Q] C) :
    AlgebraTensorModule.map f' φ (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C) y) =
      AlgebraTensorModule.map J (LinearMap.id : D →ₗ[Q] D) (AlgebraTensorModule.map f φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp [hf]
  | add a b ha hb => simp only [map_add, ha, hb]

end General

theorem finrank_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ _ _ _ V V' _ _ _ _ _ _ _ _ _ _ ρ ρ' j hj hρ
  classical
  haveI : IsScalarTower Qp LL V' := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul LL' (algebraMap Qp LL r) x, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  let u := Module.finBasis LL LL'
  obtain ⟨π, h⟩ := exists_isCoord u j hj
  have hB := h.tensor (Q := Qp) B
  have hR := h.tensor (Q := Qp) BdR
  have r0 : Rel π (H0V ρ) (H0V ρ') :=
    Rel.iInf fun g => h.rel_ker h _ _ fun y => by simp [hρ]
  have rc : Rel _ (Dcris PD ρ) (Dcris PD ρ') :=
    Rel.iInf fun g => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVB]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rd : Rel _ (DdR PD ρ) (DdR PD ρ') :=
    Rel.iInf fun g => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVdR]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rf : ∀ a : ℤ,
      Rel (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : BdR →ₗ[Qp] BdR))
        (FilV PD (LL := LL) (V := V) a) (FilV PD (LL := LL') (V := V') a) := by
    intro a
    have hF := h.tensor (Q := Qp) ↥((PD.Fil a).restrictScalars Qp)
    refine hR.rel_range hF
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype)
      (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
        ((PD.Fil a).restrictScalars Qp).subtype) fun y => ?_
    exact map_comm (J := j) LinearMap.id LinearMap.id (fun _ => rfl)
      ((PD.Fil a).restrictScalars Qp).subtype y
  have re : ∀ τ : K →ₐ[Qp] LL,
      Rel _ (DdRE PD ρ τ) (DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rd.inf (Rel.iInf fun c => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVdR,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  have rl : ∀ τ : K₀ →ₐ[Qp] LL,
      Rel _ (DcrisL PD ρ τ) (DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rc.inf (Rel.iInf fun c => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVB,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  refine ⟨?_, h.finrank_eq r0, ⟨hB.finrank_eq rc, hB.finite_iff rc⟩,
    ⟨hR.finrank_eq rd, hR.finite_iff rd⟩, fun a => hR.finrank_eq (rd.inf (rf a)),
    fun τ => hB.finrank_eq (rl τ),
    fun τ => ⟨hR.finrank_eq (re τ), fun a => hR.finrank_eq ((re τ).inf (rf a))⟩⟩
  have := h.finrank_eq (S := ⊤) (S' := ⊤) (fun x => by simp)
  simpa using this

end GlobalTheory.CoeffBC
