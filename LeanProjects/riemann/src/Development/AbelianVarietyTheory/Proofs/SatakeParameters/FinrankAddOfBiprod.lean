import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.SumJumps

theorem finrank_add_of_biprod {L M M₁ M₂ : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup M₁] [Module L M₁] [AddCommGroup M₂] [Module L M₂]
    (p₁ : M →ₗ[L] M₁) (p₂ : M →ₗ[L] M₂) (i₁ : M₁ →ₗ[L] M) (i₂ : M₂ →ₗ[L] M)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0)
    (h21 : ∀ x, p₂ (i₁ x) = 0) (h : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L M) (S₁ : Submodule L M₁) (S₂ : Submodule L M₂)
    [Module.Finite L S₁] [Module.Finite L S₂]
    (a₁ : ∀ x ∈ S, p₁ x ∈ S₁) (a₂ : ∀ x ∈ S, p₂ x ∈ S₂) (b₁ : ∀ x ∈ S₁, i₁ x ∈ S)
    (b₂ : ∀ x ∈ S₂, i₂ x ∈ S) : finrank L S = finrank L S₁ + finrank L S₂ := by
  rw [← Module.finrank_prod]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective
    ((p₁.restrict a₁).prod (p₂.restrict a₂)) ⟨?_, ?_⟩)
  · intro x y hxy
    have e1 : p₁ x = p₁ y := congrArg (fun z : S₁ × S₂ => (z.1 : M₁)) hxy
    have e2 : p₂ x = p₂ y := congrArg (fun z : S₁ × S₂ => (z.2 : M₂)) hxy
    apply Subtype.ext
    rw [← h x, ← h y, e1, e2]
  · rintro ⟨x, y⟩
    refine ⟨⟨i₁ x + i₂ y, S.add_mem (b₁ _ x.2) (b₂ _ y.2)⟩, ?_⟩
    ext
    · simp [h11, h12]
    · simp [h21, h22]

section Funct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

def ext1 (Qp : Type) [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (C : Type) [AddCommGroup C] [Module Qp C] (f : V →ₗ[LL] V') :
    V ⊗[Qp] C →ₗ[LL] V' ⊗[Qp] C :=
  AlgebraTensorModule.map f LinearMap.id

theorem ext1_comm {C C' : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup C'] [Module Qp C']
    (f : V →ₗ[LL] V') (r : V →ₗ[LL] V) (r' : V' →ₗ[LL] V') (hf : ∀ v, f (r v) = r' (f v))
    (u : C →ₗ[Qp] C') (x : V ⊗[Qp] C) :
    AlgebraTensorModule.map r' u (ext1 Qp C f x) = ext1 Qp C' f (AlgebraTensorModule.map r u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1, hf]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ext1_comp_ext1 {C : Type} [AddCommGroup C] [Module Qp C]
    (f : V →ₗ[LL] V') (f' : V' →ₗ[LL] V'') (x : V ⊗[Qp] C) :
    ext1 Qp C f' (ext1 Qp C f x) = ext1 Qp C (f' ∘ₗ f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ext1_id {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [ext1]

theorem ext1_zero {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem ext1_add {C : Type} [AddCommGroup C] [Module Qp C] (f f' : V →ₗ[LL] V') (x : V ⊗[Qp] C) :
    ext1 Qp C f x + ext1 Qp C f' x = ext1 Qp C (f + f') x := by
  simp [ext1, AlgebraTensorModule.map_add_left]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext1 Qp B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVB at this ⊢
  rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem fildR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext1 Qp BdR f x ∈ FildR PD ρ' τ a := by
  intro x hx
  simp only [FildR, DdRE, DdR, FilV, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero,
    LinearMap.mem_range] at hx ⊢
  obtain ⟨⟨h1, h2⟩, y, hy⟩ := hx
  refine ⟨⟨fun g => ?_, fun c => ?_⟩, ext1 Qp _ f y, ?_⟩
  · have := h1 g
    unfold actVdR at this ⊢
    rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]
  · have := h2 c
    unfold mulVdR at this ⊢
    rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), this, map_smul]
  · rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), hy]

theorem finrank_add_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] (V' × V''))
    (S : Submodule LL (V ⊗[Qp] C)) (S₁ : Submodule LL (V' ⊗[Qp] C)) (S₂ : Submodule LL (V'' ⊗[Qp] C))
    [Module.Finite LL S₁] [Module.Finite LL S₂]
    (a₁ : ∀ x ∈ S, ext1 Qp C (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₁)
    (a₂ : ∀ x ∈ S, ext1 Qp C (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') x ∈ S)
    (b₂ : ∀ x ∈ S₂, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') x ∈ S) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_add_of_biprod _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1, ext1_comp_ext1, ext1_add]
    convert ext1_id (LL := LL) x
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      ← map_add]
    apply e.injective
    simp

variable {ρ'' : Representation LL G V''}

theorem equivariant_inl_inr_of_prod_equiv (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2)) :
    (∀ g v, (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ' g ((LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ'' g ((LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') (ρ' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') (ρ'' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') v)) := by
  refine ⟨fun g v => by simp [he], fun g v => by simp [he], fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    rw [he]; simp
  · apply e.injective
    rw [he]; simp

theorem finrank_dcris_add (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2))
    [Module.Finite LL (Dcris PD ρ')] [Module.Finite LL (Dcris PD ρ'')] :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') + finrank LL (Dcris PD ρ'') := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant_inl_inr_of_prod_equiv e he
  exact finrank_add_tensor e _ _ _ (dcris_map PD _ h1) (dcris_map PD _ h2) (dcris_map PD _ h3)
    (dcris_map PD _ h4)

theorem finite_fildR [Module.Finite LL (DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Module.Finite LL (FildR PD ρ τ a) :=
  Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) (inf_le_left.trans inf_le_left)

theorem multV_add (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2))
    [Module.Finite LL (DdR PD ρ')] [Module.Finite LL (DdR PD ρ'')] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a + multV PD ρ'' τ a := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant_inl_inr_of_prod_equiv e he
  have key : ∀ b, finrank LL (FildR PD ρ τ b) =
      finrank LL (FildR PD ρ' τ b) + finrank LL (FildR PD ρ'' τ b) := fun b => by
    haveI := finite_fildR PD (ρ := ρ') τ b
    haveI := finite_fildR PD (ρ := ρ'') τ b
    exact finrank_add_tensor e _ _ _ (fildR_map PD _ h1 τ b) (fildR_map PD _ h2 τ b)
      (fildR_map PD _ h3 τ b) (fildR_map PD _ h4 τ b)
  simp only [multV, key]
  push_cast
  ring

end Funct

theorem tateDual_summand : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], Formalism.MainNotions.LocalSituation.fontCore PD → TateDualRule PD → GoodO (Qp := Qp) LL O → ∀ (A W Bk T : GRep G Qp LL O) (e : A.V ≃ₗ[LL] (W.V × Bk.V)) (Pr : W.V →ₗ[LL] T.V →ₗ[LL] LL) (τ : K →ₐ[Qp] LL) (J J' : Multiset ℤ), (∀ g v, e (A.ρ g v) = (W.ρ g (e v).1, Bk.ρ g (e v).2)) → IsCrys PD A.ρ → (∀ a, multV PD A.ρ τ a = ((J + J').count a : ℕ)) → (∀ a, multV PD Bk.ρ τ a = (J'.count a : ℕ)) → IsDual1 PD W.ρ T.ρ Pr → IsCrys PD T.ρ ∧ ∀ a, multV PD T.ρ τ a = ((J.map fun u => -u - 1).count a : ℕ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hT hO A W Bk T e Pr
    τ J J' he hA mA mB hD
  obtain ⟨⟨fW, lW⟩, ⟨gW, -⟩, -⟩ := hF LL O hO W
  obtain ⟨⟨fB, lB⟩, ⟨gB, -⟩, -⟩ := hF LL O hO Bk
  have hW : IsCrys PD W.ρ := by
    have h1 := finrank_dcris_add PD e he
    have h2 : finrank LL A.V = finrank LL W.V + finrank LL Bk.V := by
      rw [e.finrank_eq, Module.finrank_prod]
    unfold IsCrys at hA ⊢
    rw [h1, h2, mul_add] at hA
    omega
  obtain ⟨c, m⟩ := hT LL O hO W T Pr hW hD
  refine ⟨c, fun a => ?_⟩
  have hinj : Function.Injective fun u : ℤ => -u - 1 := fun x y h => by
    simp only at h; omega
  have ha : a = -(-a - 1) - 1 := by ring
  have h3 := multV_add PD e he τ (-a - 1)
  rw [mA, mB, Multiset.count_add] at h3
  rw [ha, m τ, Multiset.count_map_eq_count' _ _ hinj]
  push_cast at h3
  omega

end GlobalTheory.HTW.SumJumps
