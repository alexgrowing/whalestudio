import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem mulR_mem_DdR (ρ : Representation LL G V) (c : K) {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) :
    mulR Qp F LL V (algebraMap K F c) x ∈ DdR PD ρ := by
  rw [mem_DdR] at hx ⊢
  intro g
  rw [← sm_one_tmul, act_sm, hx]
  simp

theorem ext_mulR (f : V →ₗ[LL] V') (b : F) (x : V ⊗[Qp] F) :
    ext Qp F f (mulR Qp F LL V b x) = mulR Qp F LL V' b (ext Qp F f x) := by
  rw [← sm_one_tmul, ext_sm, sm_one_tmul]

theorem ext_mem_FildR (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FildR PD ρ τ a) : ext Qp F f x ∈ FildR PD ρ' τ a := by
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨(mem_DdR PD _ _).2 fun g => ?_, fun c => ?_⟩, ext_mem_FilV PD f hx.2⟩
  · rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx.1.1]
  · rw [← ext_mulR, ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul]

theorem ext_ext_of_leftInverse (f : V →ₗ[LL] V') (s : V' →ₗ[LL] V) (hs : ∀ v, s (f v) = v) (x : V ⊗[Qp] F) :
    ext Qp F s (ext Qp F f x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [hs]

theorem ext_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) : Function.Injective (ext Qp F f) := by
  obtain ⟨s, hs⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  exact Function.LeftInverse.injective (ext_ext_of_leftInverse f s (LinearMap.congr_fun hs))

theorem mem_FildR_of_ext (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hi : Function.Injective f) (τ : K →ₐ[Qp] LL) {a : ℤ}
    {x : V ⊗[Qp] F} (hx : ext Qp F f x ∈ FildR PD ρ' τ a) : x ∈ FildR PD ρ τ a := by
  obtain ⟨s, hs⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨(mem_DdR PD _ _).2 fun g => ext_injective f hi ?_,
    fun c => ext_injective f hi ?_⟩, ?_⟩
  · rw [← act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx.1.1]
  · rw [ext_mulR, ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul]
  · rw [← ext_ext_of_leftInverse f s (LinearMap.congr_fun hs) x]
    exact ext_mem_FilV PD s hx.2

theorem ext_eq_rTensor (f : V →ₗ[LL] V') (x : V ⊗[Qp] F) :
    ext Qp F f x = (f.restrictScalars Qp).rTensor F x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp

theorem ext_exact (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (ext Qp F f) (ext Qp F g) := by
  intro y
  have := rTensor_exact F (f := f.restrictScalars Qp) (g := g.restrictScalars Qp) h hg y
  simpa only [Set.mem_range, ext_eq_rTensor] using this

theorem exists_ext_mem_FilV (g : V →ₗ[LL] V') (hg : Function.Surjective g) {a : ℤ} {y : V' ⊗[Qp] F}
    (hy : y ∈ FilV PD (LL := LL) (V := V') a) : ∃ x ∈ FilV PD (LL := LL) (V := V) a, ext Qp F g x = y := by
  refine FilV_induction PD (p := fun y => ∃ x ∈ FilV PD (LL := LL) (V := V) a, ext Qp F g x = y)
    ⟨0, Submodule.zero_mem _, map_zero _⟩ (fun w b hb => ?_) ?_ hy
  · obtain ⟨v, rfl⟩ := hg w
    exact ⟨v ⊗ₜ b, tmul_mem_FilV PD v hb, by simp⟩
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    exact ⟨x + x', Submodule.add_mem _ hx hx', map_add _ _ _⟩

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DcrisL (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧ ∀ c : K₀, mulR Qp B LL V (algebraMap K₀ B c) x = τ c • x := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, mulVB]

theorem mulR_mem_Dcris (ρ : Representation LL G V) (c : K₀) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    mulR Qp B LL V (algebraMap K₀ B c) x ∈ Dcris PD ρ := by
  rw [mem_Dcris] at hx ⊢
  intro g
  have : ∀ x, actVB PD ρ g (mulR Qp B LL V (algebraMap K₀ B c) x) =
      mulR Qp B LL V (algebraMap K₀ B c) (actVB PD ρ g x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [this, hx]

theorem ιV_mem_DdR (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by
  have key : ∀ g y, actVdR PD ρ g (ιV PD (LL := LL) (V := V) y) = ιV PD (LL := LL) (V := V) (actVB PD ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, ιV, PD.ι_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [mem_Dcris] at hx
  rw [mem_DdR]
  intro g
  rw [key, hx]

theorem ιV_mulR (b : B) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulR Qp B LL V b x) = mulR Qp F LL V (PD.ι b) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add a b ha hb => simp only [map_add, ha, hb]

def TensInj : Prop := ∀ (m : ℕ) (c : Fin m → K), LinearIndependent K₀ c → ∀ b : Fin m → B,
  ∑ i, algebraMap K F (c i) * PD.ι (b i) = 0 → ∀ i, b i = 0

variable {PD} in
theorem TensInj.tensor (h : TensInj PD) (m : ℕ) (c : Fin m → K) (hc : LinearIndependent K₀ c)
    (x : Fin m → V ⊗[Qp] B)
    (hx : ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) = 0) (i : Fin m) :
    x i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  have key : ∀ (a : F) (y : V ⊗[Qp] B) j, TensorProduct.equivFinsuppOfBasisLeft (N := F) b
      (mulR Qp F LL V a (ιV PD (LL := LL) (V := V) y)) j =
        a * PD.ι (TensorProduct.equivFinsuppOfBasisLeft (N := B) b y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
        (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
      simp [ιV, hsm]
    | add a b ha hb => simp only [map_add, ha, hb, Finsupp.add_apply, mul_add]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  have := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft (N := F) b z j) hx
  simp only [map_sum, Finsupp.finset_sum_apply, key, map_zero, Finsupp.zero_apply] at this
  simpa using h m c hc _ this i

theorem isDR_of_isCrys (h : TensInj PD) (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V) (hc : IsCrys PD ρ) :
    IsDR PD ρ ∧ ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) := by
  have := PD.finK
  have : FiniteDimensional K₀ K := FiniteDimensional.right Qp K₀ K
  let c := Module.finBasis K₀ K
  let Θ₀ : (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) →ₗ[LL] V ⊗[Qp] F :=
    ∑ i, mulR Qp F LL V (algebraMap K F (c i)) ∘ₗ ιV PD (LL := LL) (V := V) ∘ₗ (Dcris PD ρ).subtype ∘ₗ
      LinearMap.proj i
  have hΘ₀ : ∀ x, Θ₀ x = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) :=
    fun x => by simp [Θ₀, LinearMap.sum_apply]
  let Θ := Θ₀.codRestrict (DdR PD ρ) fun x => by
    rw [hΘ₀]
    exact Submodule.sum_mem _ fun i _ => mulR_mem_DdR PD ρ _ (ιV_mem_DdR PD ρ (x i).2)
  have hi : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Subtype.ext (h.tensor (LL := LL) _ c c.linearIndependent (fun i => (x i : V ⊗[Qp] B))
      ((hΘ₀ x).symm.trans (congrArg Subtype.val hx)) i)
  have := Module.Finite.of_injective Θ hi
  have : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective (LinearMap.proj (R := LL) (φ := fun _ => ↥(Dcris PD ρ))
      (⟨0, finrank_pos⟩ : Fin (finrank K₀ K))) (Function.surjective_eval _)
  have h1 : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hc,
      ← Module.finrank_mul_finrank Qp K₀ K]
    ring
  have h2 := LinearMap.finrank_le_finrank_of_injective hi
  have h3 : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (h1 ▸ h2)
  refine ⟨h3, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h1.trans h3.symm)).1 hi ⟨y, hy⟩
  exact ⟨_, c, fun i => x i, fun i => (x i).2, (congrArg Subtype.val hx).symm.trans (hΘ₀ x)⟩

variable [FiniteDimensional Qp K] [CharZero Qp]

theorem sub_sm_idem_mem (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {y : V ⊗[Qp] F} (hy : y ∈ DdR PD ρ) :
    y - sm Qp F LL V (idem F τ) y ∈ Submodule.span LL
      {z | ∃ (c : K), ∃ y ∈ DdR PD ρ, z = mulR Qp F LL V (algebraMap K F c) y - τ c • y} := by
  obtain ⟨n, a, c, h, h1⟩ := idem_repr F τ
  have : y - sm Qp F LL V (idem F τ) y =
      ∑ i, (-a i) • (mulR Qp F LL V (algebraMap K F (c i)) y - τ (c i) • y) := by
    rw [h, map_sum, LinearMap.sum_apply]
    simp only [sm_tmul_left, smul_sub, smul_smul, neg_smul, neg_mul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_smul, h1, one_smul]
    abel
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c i, y, hy, rfl⟩)

theorem exists_component_equiv (h : TensInj PD) (ρ : Representation LL G V)
    (hs : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)))
    (τ : K →ₐ[Qp] LL) (τ₀ : K₀ →ₐ[Qp] LL) (hτ : ∀ c, τ₀ c = τ (algebraMap K₀ K c)) :
    ∃ e : ↥(DcrisL PD ρ τ₀) ≃ₗ[LL] ↥(DdRE PD ρ τ), ∀ x : ↥(DcrisL PD ρ τ₀),
      (e x : V ⊗[Qp] F) = sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) x) := by
  have := PD.finK₀
  have : FiniteDimensional K₀ K := FiniteDimensional.right Qp K₀ K
  let Θ : ↥(DcrisL PD ρ τ₀) →ₗ[LL] ↥(DdRE PD ρ τ) :=
    (sm Qp F LL V (idem F τ) ∘ₗ ιV PD (LL := LL) (V := V) ∘ₗ (DcrisL PD ρ τ₀).subtype).codRestrict _
      fun x => sm_idem_mem_DdRE PD ρ τ (ιV_mem_DdR PD ρ x.2.1)
  have hιc : ∀ c : K₀, PD.ι (algebraMap K₀ B c) = algebraMap K F (algebraMap K₀ K c) := fun c => by
    rw [PD.ι.commutes, IsScalarTower.algebraMap_apply K₀ K F]
  have hcomm : ∀ (c : K) (z : V ⊗[Qp] F), sm Qp F LL V (idem F τ) (mulR Qp F LL V (algebraMap K F c) z) =
      τ c • sm Qp F LL V (idem F τ) z := fun c z => by
    rw [← sm_one_tmul, sm_comm, sm_one_tmul, mulR_sm_idem]
  refine ⟨LinearEquiv.ofBijective Θ ⟨?_, ?_⟩, fun x => rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    have h0 : sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) x) = 0 := congrArg Subtype.val h0
    let β := Module.finBasis K₀ K
    obtain ⟨n, a, c, he, h1⟩ := idem_repr F τ
    have e1 : ∀ c : K, mulR Qp F LL V (algebraMap K F c) (ιV PD (LL := LL) (V := V) x) =
        ∑ i, τ₀ (β.repr c i) • mulR Qp F LL V (algebraMap K F (β i)) (ιV PD (LL := LL) (V := V) x) := by
      intro c
      conv_lhs => rw [← β.sum_repr c, map_sum, ← sm_one_tmul, tmul_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sm_one_tmul, Algebra.smul_def, map_mul, mul_comm, ← mulR_mulR, ← hιc, ← ιV_mulR,
        ((mem_DcrisL PD ρ τ₀ x).1 hx).2, map_smul, map_smul]
    have e2 : ∀ c : K, τ c = ∑ i, τ₀ (β.repr c i) * τ (β i) := by
      intro c
      conv_lhs => rw [← β.sum_repr c, map_sum]
      simp only [Algebra.smul_def, map_mul, hτ]
    have e3 := h.tensor (LL := LL) _ β β.linearIndependent (fun i => (∑ j, a j * τ₀ (β.repr (c j) i)) • x) (by
      rw [he, map_sum, LinearMap.sum_apply] at h0
      simp only [sm_tmul_left, e1 (c _), Finset.smul_sum, smul_smul] at h0
      rw [Finset.sum_comm] at h0
      simpa only [map_smul, ← Finset.sum_smul] using h0)
    have e4 : ∑ i, τ (β i) * ∑ j, a j * τ₀ (β.repr (c j) i) = 1 := by
      rw [← h1]
      simp only [e2 (c _), Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    apply Subtype.ext
    change x = 0
    rw [← one_smul LL x, ← e4, Finset.sum_smul]
    exact Finset.sum_eq_zero fun i _ => by rw [mul_smul, e3, smul_zero]
  · rintro ⟨y, hy⟩
    obtain ⟨m, c, x, hx, hy'⟩ := hs y hy.1
    obtain ⟨n, a, u, he, h1⟩ := idem_repr B τ₀
    have e0 : ∀ z, sm Qp B LL V (idem B τ₀) z = ∑ j, a j • mulR Qp B LL V (algebraMap K₀ B (u j)) z := by
      intro z
      rw [he, map_sum, LinearMap.sum_apply]
      simp only [sm_tmul_left]
    have e1 : ∀ i, sm Qp B LL V (idem B τ₀) (x i) ∈ DcrisL PD ρ τ₀ := fun i => by
      refine (mem_DcrisL PD ρ τ₀ _).2 ⟨?_, fun c => mulR_sm_idem τ₀ c _⟩
      rw [e0]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mulR_mem_Dcris PD ρ _ (hx i))
    have e2 : ∀ z, sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) (sm Qp B LL V (idem B τ₀) z)) =
        sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) z) := by
      intro z
      rw [e0, map_sum, map_sum]
      simp only [map_smul, ιV_mulR, hιc, hcomm, smul_smul, ← hτ, ← Finset.sum_smul, h1, one_smul]
    refine ⟨∑ i, τ (c i) • ⟨_, e1 i⟩, Subtype.ext ?_⟩
    change _ = y
    rw [← sm_idem_of_mem_DdRE PD ρ τ hy, hy', map_sum, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, map_smul, Submodule.coe_smul, ← e2]
    rfl

end GlobalTheory.DRFil
