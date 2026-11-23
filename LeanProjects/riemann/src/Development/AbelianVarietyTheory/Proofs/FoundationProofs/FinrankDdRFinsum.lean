import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing

noncomputable section

namespace GlobalTheory.DeRhamSplit

open Module TensorProduct

section General

variable {F K L M : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  [AddCommGroup M] [Module L M] [Module F M] [IsScalarTower F L M]

def evalEmb (F K L : Type) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] :
    L ⊗[F] K →ₐ[L] ((K →ₐ[F] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (AlgHom.pi fun τ => τ) fun _ _ => .all _ _

theorem evalEmb_tmul (a : L) (c : K) (τ : K →ₐ[F] L) :
    evalEmb F K L (a ⊗ₜ c) τ = a * τ c := by
  simp [evalEmb, Algebra.ofId_apply]

theorem evalEmb_bijective [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) : Function.Bijective (evalEmb F K L) := by
  have hli : LinearIndependent L (fun τ : K →ₐ[F] L => (τ : K → L)) := by
    have h := (linearIndependent_monoidHom K L).comp (fun τ : K →ₐ[F] L => (τ : K →* L))
      (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    exact h
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have hsurj : Function.Surjective (evalEmb F K L).toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨1 ⊗ₜ c, ?_⟩
    funext τ
    simp [evalEmb_tmul, flip]
  have hfin : finrank L (L ⊗[F] K) = finrank L ((K →ₐ[F] L) → L) := by
    simp [hcard]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj, hsurj⟩

theorem finrank_eq_sum [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) (m : K →ₐ[F] Module.End L M)
    (W : Submodule L M) [FiniteDimensional L W] (hW : ∀ c, ∀ x ∈ W, m c x ∈ W) :
    finrank L W = ∑ τ : K →ₐ[F] L,
      finrank L ↥(W ⊓ ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)) := by
  classical
  have hcomm : ∀ (a : L) (c : K), Commute (Algebra.ofId L (Module.End L M) a) (m c) :=
    fun a c => Algebra.commutes a (m c)
  let Ψ : L ⊗[F] K →ₐ[L] Module.End L M :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) m hcomm
  have hΨ : ∀ a c x, Ψ (a ⊗ₜ c) x = a • m c x := by
    intro a c x
    change (Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ c) : Module.End L M) x = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp [Algebra.ofId_apply]
  let Φ := AlgEquiv.ofBijective _ (evalEmb_bijective hcard)
  let e : (K →ₐ[F] L) → L ⊗[F] K := fun τ => Φ.symm (Pi.single τ 1)
  have he : ∀ τ, evalEmb F K L (e τ) = Pi.single τ 1 := fun τ => Φ.apply_symm_apply _
  let E : (K →ₐ[F] L) → Submodule L M := fun τ => ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)
  have hE : ∀ τ x, x ∈ E τ ↔ ∀ c, m c x = τ c • x := by
    intro τ x
    simp [E, Submodule.mem_iInf, sub_eq_zero]
  have hΨW : ∀ z, ∀ x ∈ W, Ψ z x ∈ W := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact W.smul_mem _ (hW c x hx)
    | add y z hy hz => rw [map_add]; exact W.add_mem hy hz
  have hΨE : ∀ σ, ∀ x ∈ E σ, ∀ z, Ψ z x = evalEmb F K L z σ • x := by
    intro σ x hx z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, evalEmb_tmul, (hE σ x).1 hx, mul_smul]
    | add y z hy hz => simp [map_add, hy, hz, add_smul]
  have hsum : ∑ τ, e τ = 1 := by
    apply (evalEmb_bijective hcard).1
    rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : L))
  have hmul : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := by
    intro τ c
    apply (evalEmb_bijective hcard).1
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [evalEmb_tmul]
    · simp [Pi.single_eq_of_ne h]
  have hpE : ∀ τ x, Ψ (e τ) x ∈ E τ := by
    intro τ x
    rw [hE]
    intro c
    have := congrArg (fun z => Ψ z x) (hmul τ c)
    simpa [map_mul, map_smul, hΨ] using this
  let f : W →ₗ[L] (∀ τ, ↥(W ⊓ E τ)) := LinearMap.pi fun τ =>
    LinearMap.codRestrict _ ((Ψ (e τ)) ∘ₗ W.subtype) fun x => ⟨hΨW _ _ x.2, hpE τ _⟩
  have hf : ∀ x τ, (f x τ : M) = Ψ (e τ) x := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : (x : M) = ∑ τ, Ψ (e τ) x := by
        rw [← LinearMap.sum_apply, ← map_sum, hsum, map_one]; rfl
      apply Subtype.ext
      rw [h1]
      simp [← hf, hx]
    · intro y
      refine ⟨⟨∑ σ, (y σ : M), W.sum_mem fun σ _ => (y σ).2.1⟩, ?_⟩
      funext τ
      apply Subtype.ext
      rw [hf, map_sum, Finset.sum_eq_single τ]
      · rw [hΨE τ _ (y τ).2.2, he]; simp
      · intro σ _ h
        rw [hΨE σ _ (y σ).2.2, he]; simp [Pi.single_eq_of_ne h]
      · simp
  have : ∀ τ, FiniteDimensional L ↥(W ⊓ E τ) := fun τ =>
    Submodule.finiteDimensional_of_le inf_le_left
  rw [(LinearEquiv.ofBijective f hbij).finrank_eq, Module.finrank_pi_fintype]

end General

section Period

open Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (b : BdR) :
    mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c (v ⊗ₜ[Qp] b) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * b) := by
  simp [mulVdR]

def mulHom (Qp K BdR LL V : Type) [Field Qp] [Field K] [Algebra Qp K] [CommRing BdR]
    [Algebra Qp BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [Field LL] [Algebra Qp LL]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) where
  toFun c := mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c
  map_one' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_mul' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, mul_assoc]
  map_zero' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_add' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, add_mul, tmul_add]
  commutes' a := by
    apply AlgebraTensorModule.ext
    intro v b
    rw [mulVdR_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul]
    simp [Algebra.algebraMap_eq_smul_one]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR_tmul]
  | add y z hy hz => simp [map_add, hy, hz]

theorem mul_mem_DdR (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx]

theorem mul_mem_FilV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR_tmul, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

theorem finrank_DdR [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  refine ⟨finrank_eq_sum hcard (mulHom Qp K BdR LL V) _ (mul_mem_DdR PD ρ), ?_⟩
  have : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [finrank_eq_sum hcard (mulHom Qp K BdR LL V) (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨mul_mem_DdR PD ρ c x hx.1, mul_mem_FilV PD a c x hx.2⟩)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [inf_right_comm]
  rfl

theorem finrank_DdR_finsum [FiniteDimensional Qp K] (hcard : Nat.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  rw [Nat.card_eq_fintype_card] at hcard
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact finrank_DdR PD ρ hcard a

end Period

open Formalism.BasicNotions in
theorem card_emb {l : ℕ} [Fact l.Prime] (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have := K.2
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective (fun τ => LL.1.val.comp τ) ⟨?_, ?_⟩
  · intro a b hab
    ext x
    exact DFunLike.congr_fun hab x
  · intro τ
    exact ⟨τ.codRestrict LL.1.toSubalgebra (h τ), by ext x; rfl⟩

open Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations in
theorem finrank_DdR_local {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) {m : ℕ} (hm : 0 < m)
    (ρ : Representation ↥LL.1 ↥(Loc.GK K) (Fin m → ↥LL.1))
    (hρ : finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = finrank ℚ_[l] ↥K.1 * m) (a : ℤ) :
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) a) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hpos : 0 < finrank ↥LL.1 ↥(DdR (P.PD K) ρ) := by
    rw [hρ]
    exact Nat.mul_pos Module.finrank_pos hm
  have hD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) := FiniteDimensional.of_finrank_pos hpos
  have hc := card_emb _ _ h
  exact finrank_DdR_finsum (P.PD K) ρ hc a

end GlobalTheory.DeRhamSplit
