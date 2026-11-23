import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

noncomputable section

namespace GlobalTheory.NL.CompD

theorem exists_proj {F K L M : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [AddCommGroup M] [Module F M]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) (α : L →ₐ[F] Module.End F M)
    (β : K →ₐ[F] Module.End F M) (hc : ∀ a c, Commute (α a) (β c)) :
    ∃ e : (K →ₐ[F] L) → Module.End F M, (∀ x, ∑ σ, e σ x = x) ∧
      (∀ σ c x, β c (e σ x) = α (σ c) (e σ x)) ∧ (∀ σ c x, e σ (β c x) = β c (e σ x)) ∧
      (∀ σ a x, e σ (α a x) = α a (e σ x)) ∧
      ∀ N : AddSubgroup M, (∀ a, ∀ x ∈ N, α a x ∈ N) → (∀ c, ∀ x ∈ N, β c x ∈ N) →
        ∀ σ, ∀ x ∈ N, e σ x ∈ N := by
  classical
  let Ψ : L ⊗[F] K →ₐ[F] Module.End F M := Algebra.TensorProduct.lift α β hc
  have hΨ : ∀ a c, Ψ (a ⊗ₜ c) = α a * β c := fun a c => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hb := GlobalTheory.DeRhamSplit.evalEmb_bijective hcard
  let Φ := AlgEquiv.ofBijective _ hb
  let e : (K →ₐ[F] L) → L ⊗[F] K := fun τ => Φ.symm (Pi.single τ 1)
  have he : ∀ τ, GlobalTheory.DeRhamSplit.evalEmb F K L (e τ) = Pi.single τ 1 := fun τ => Φ.apply_symm_apply _
  have hsum : ∑ τ, e τ = 1 := by
    apply hb.1
    rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : L))
  have hmul : ∀ τ c, (1 ⊗ₜ c) * e τ = (τ c ⊗ₜ 1) * e τ := by
    intro τ c
    apply hb.1
    rw [map_mul, map_mul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [GlobalTheory.DeRhamSplit.evalEmb_tmul]
    · simp [Pi.single_eq_of_ne h]
  have h1 : ∀ c, β c = Ψ (1 ⊗ₜ c) := fun c => by rw [hΨ, map_one, one_mul]
  have h2 : ∀ a, α a = Ψ (a ⊗ₜ 1) := fun c => by rw [hΨ, map_one, mul_one]
  refine ⟨fun σ => Ψ (e σ), fun x => ?_, fun σ c x => ?_, fun σ c x => ?_, fun σ c x => ?_,
    fun N hα hβ σ x hx => ?_⟩
  · rw [← LinearMap.sum_apply, ← map_sum, hsum, map_one]; rfl
  · rw [h1, h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hmul]
  · rw [h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · rw [h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · change Ψ (e σ) x ∈ N
    generalize e σ = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact hα _ _ (hβ _ _ hx)
    | add y z hy hz => rw [map_add]; exact N.add_mem hy hz

theorem indep_of_span {L R D : Type} [Field L] [CommRing R] (ι : L → R) [AddCommGroup D] [Module L D]
    [FiniteDimensional L D] {n : ℕ} (hn : finrank L D = n) (A : D →+ (Fin n → R))
    (hA : ∀ c x, A (c • x) = ι c • A x) (hspan : Submodule.span R (Set.range A) = ⊤)
    {r : ℕ} (d : Fin r → D) (hd : LinearIndependent L d) : LinearIndependent R fun a => A (d a) := by
  classical
  let Bs := Basis.extend hd.linearIndepOn_id
  haveI : Fintype (hd.linearIndepOn_id.extend (Set.subset_univ _)) := FiniteDimensional.fintypeBasisIndex Bs
  have hcard := (finrank_eq_card_basis Bs).symm.trans hn
  let q := Fintype.equivFinOfCardEq hcard
  have hsurj : Function.Surjective (Fintype.linearCombination R fun s => A (Bs s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨fun s => ι (Bs.repr x s), ?_⟩
    conv_rhs => rw [← Bs.sum_repr x]
    simp only [Fintype.linearCombination_apply, map_sum, hA]
  have hinj := OrzechProperty.injective_of_surjective_of_injective
    (LinearEquiv.funCongrLeft R R q.symm).toLinearMap _ (LinearEquiv.injective _) hsurj
  have hli : LinearIndependent R fun s => A (Bs s) := linearIndependent_iff_injective_fintypeLinearCombination.2 hinj
  have := hli.comp (fun a => ⟨d a, hd.linearIndepOn_id.subset_extend _ ⟨a, rfl⟩⟩)
    (fun a b hab => hd.injective (congrArg Subtype.val hab))
  convert this using 1
  funext a
  simp [Bs]

section Tens

variable {Qp LL V : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V] [Module LL V]
  [Module Qp V] [IsScalarTower Qp LL V] {R : Type} [CommRing R] [Algebra Qp R]

variable (Qp LL V) in

def mu (b : R) : V ⊗[Qp] R →ₗ[LL] V ⊗[Qp] R :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

theorem mu_tmul (b c : R) (v : V) : mu Qp LL V b (v ⊗ₜ c) = v ⊗ₜ (b * c) := rfl

variable (Qp V R) in

def muHom : R →ₐ[Qp] Module.End Qp (V ⊗[Qp] R) :=
  (Module.End.lTensorAlgHom Qp R V).comp (Algebra.lmul Qp R)

variable (LL) in
theorem muHom_apply (b : R) (x : V ⊗[Qp] R) : muHom Qp V R b x = mu Qp LL V b x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem mu_mu (b c : R) (x : V ⊗[Qp] R) : mu Qp LL V b (mu Qp LL V c x) = mu Qp LL V (b * c) x := by
  simp only [← muHom_apply, map_mul, Module.End.mul_apply]

theorem mu_one (x : V ⊗[Qp] R) : mu Qp LL V (1 : R) x = x := by
  simp only [← muHom_apply, map_one, Module.End.one_apply]

theorem mu_sub (b c : R) (x : V ⊗[Qp] R) : mu Qp LL V (b - c) x = mu Qp LL V b x - mu Qp LL V c x := by
  simp only [← muHom_apply, map_sub, LinearMap.sub_apply]

theorem exists_sum {K : Type} [Field K] [Algebra Qp K] [Algebra K R] [IsScalarTower Qp K R]
    [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (N : Submodule LL (V ⊗[Qp] R)) (hN : ∀ c : K, ∀ x ∈ N, mu Qp LL V (algebraMap K R c) x ∈ N)
    (x : V ⊗[Qp] R) (hx : x ∈ N) : ∃ y : (K →ₐ[Qp] LL) → V ⊗[Qp] R, ∑ σ, y σ = x ∧
      ∀ σ, y σ ∈ N ∧ ∀ c : K, mu Qp LL V (algebraMap K R c) (y σ) = σ c • y σ := by
  obtain ⟨e, h1, h2, -, -, h5⟩ := exists_proj hcard (Algebra.lsmul Qp Qp (V ⊗[Qp] R) : LL →ₐ[Qp] _)
    ((muHom Qp V R).comp (IsScalarTower.toAlgHom Qp K R)) (fun a c => by
      refine LinearMap.ext fun x => ?_
      simp [muHom_apply LL])
  refine ⟨fun σ => e σ x, h1 x, fun σ => ⟨h5 N.toAddSubgroup (fun a x hx => N.smul_mem a hx)
    (fun c x hx => ?_) σ x hx, fun c => ?_⟩⟩
  · simpa [muHom_apply LL] using hN c x hx
  · simpa [muHom_apply LL] using h2 σ c x

def coords {n : ℕ} (v : Basis (Fin n) LL V) (ι : LL →ₐ[Qp] R) : V ⊗[Qp] R →ₗ[Qp] (Fin n → R) :=
  LinearMap.pi fun j => TensorProduct.lift
    ((LinearMap.mul Qp R) ∘ₗ ι.toLinearMap ∘ₗ (v.coord j).restrictScalars Qp)

theorem coords_tmul {n : ℕ} (v : Basis (Fin n) LL V) (ι : LL →ₐ[Qp] R) (x : V) (b : R) (j : Fin n) :
    coords v ι (x ⊗ₜ b) j = ι (v.repr x j) * b := rfl

theorem coords_smul {n : ℕ} (v : Basis (Fin n) LL V) (ι : LL →ₐ[Qp] R) (c : LL) (x : V ⊗[Qp] R) :
    coords v ι (c • x) = ι c • coords v ι x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => funext j; simp [smul_tmul', coords_tmul, mul_assoc]
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]

theorem coords_mu {n : ℕ} (v : Basis (Fin n) LL V) (ι : LL →ₐ[Qp] R) (c : R) (x : V ⊗[Qp] R) :
    coords v ι (mu Qp LL V c x) = c • coords v ι x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => funext j; simp [mu_tmul, coords_tmul, mul_left_comm]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, smul_add]

theorem coords_surj {n : ℕ} (v : Basis (Fin n) LL V) (ι : LL →ₐ[Qp] R) :
    Function.Surjective (coords v ι) := by
  intro f
  refine ⟨∑ j, v j ⊗ₜ f j, ?_⟩
  funext j
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · simp [coords_tmul]
  · intro k _ hk
    simp [coords_tmul, Finsupp.single_apply, hk]
  · simp

end Tens

section Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)

theorem mem_Dcris (x : T.V ⊗[Qp] B) : x ∈ Dcris PD T.ρ ↔ ∀ g, actVB PD T.ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR (x : T.V ⊗[Qp] BdR) : x ∈ DdR PD T.ρ ↔ ∀ g, actVdR PD T.ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DcrisL (τ : K₀ →ₐ[Qp] LL) (x : T.V ⊗[Qp] B) : x ∈ DcrisL PD T.ρ τ ↔
    x ∈ Dcris PD T.ρ ∧ ∀ c, mu Qp LL T.V (algebraMap K₀ B c) x = τ c • x := by
  simp [DcrisL, Submodule.mem_iInf, sub_eq_zero, mulVB, mu]

theorem mem_DdRE (τ : K →ₐ[Qp] LL) (x : T.V ⊗[Qp] BdR) : x ∈ DdRE PD T.ρ τ ↔
    x ∈ DdR PD T.ρ ∧ ∀ c, mu Qp LL T.V (algebraMap K BdR c) x = τ c • x := by
  simp [DdRE, Submodule.mem_iInf, sub_eq_zero, mulVdR, mu]

theorem iota_mem (x : T.V ⊗[Qp] B) (hx : x ∈ Dcris PD T.ρ) :
    ιV PD (LL := LL) (V := T.V) x ∈ DdR PD T.ρ := by
  rw [mem_DdR]
  intro g
  conv_rhs => rw [← (mem_Dcris PD T x).1 hx g]
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [ιV, actVdR, actVB, PD.ι_comm]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem iota_mu (c : K₀) (x : T.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T.V) (mu Qp LL T.V (algebraMap K₀ B c) x) =
      mu Qp LL T.V (algebraMap K BdR (algebraMap K₀ K c)) (ιV PD (LL := LL) (V := T.V) x) := by
  rw [← IsScalarTower.algebraMap_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [ιV, mu_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mu_mem_Dcris (c : K₀) (x : T.V ⊗[Qp] B) (hx : x ∈ Dcris PD T.ρ) :
    mu Qp LL T.V (algebraMap K₀ B c) x ∈ Dcris PD T.ρ := by
  rw [mem_Dcris]
  intro g
  conv_rhs => rw [← (mem_Dcris PD T x).1 hx g]
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [actVB, mu_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

abbrev others (τ : K →ₐ[Qp] LL) : Submodule LL (T.V ⊗[Qp] BdR) :=
  ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

theorem others_le_compKer (τ : K →ₐ[Qp] LL) (ι : LL →ₐ[Qp] BdR)
    (hι : ∀ c, ι (τ c) = algebraMap K BdR c) : others PD T τ ≤ compKer T ι := by
  refine iSup₂_le fun τ' hτ' y hy => ?_
  obtain ⟨c, hc⟩ : ∃ c, τ c - τ' c ≠ 0 := by
    by_contra h
    push Not at h
    exact hτ' (AlgHom.ext fun c => (sub_eq_zero.1 (h c)).symm)
  rw [← Submodule.smul_mem_iff _ hc, sub_smul, ← ((mem_DdRE PD T τ' y).1 hy).2 c, ← hι]
  exact Submodule.subset_span ⟨τ c, y, rfl⟩

theorem mu_mem_others (τ : K →ₐ[Qp] LL) (c : K) :
    ∀ y ∈ others PD T τ, mu Qp LL T.V (algebraMap K BdR c) y ∈ others PD T τ := by
  have : others PD T τ ≤ (others PD T τ).comap (mu Qp LL T.V (algebraMap K BdR c)) := by
    refine iSup₂_le fun τ' hτ' y hy => ?_
    rw [Submodule.mem_comap, ((mem_DdRE PD T τ' y).1 hy).2 c]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem τ' (Submodule.mem_iSup_of_mem hτ' hy))
  exact this

theorem exists_part [FiniteDimensional Qp K] (hc : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K) (τ : K →ₐ[Qp] LL)
    (N : Submodule LL (T.V ⊗[Qp] BdR)) (hle : N ≤ DdR PD T.ρ)
    (hN : ∀ c : K, ∀ x ∈ N, mu Qp LL T.V (algebraMap K BdR c) x ∈ N)
    (x : T.V ⊗[Qp] BdR) (hx : x ∈ N) :
    ∃ y ∈ N, y ∈ DdRE PD T.ρ τ ∧ x - y ∈ others PD T τ := by
  classical
  obtain ⟨y, h1, h2⟩ := exists_sum hc N hN x hx
  have h3 : ∀ σ, y σ ∈ DdRE PD T.ρ σ := fun σ => (mem_DdRE PD T σ _).2 ⟨hle (h2 σ).1, (h2 σ).2⟩
  refine ⟨y τ, (h2 τ).1, h3 τ, ?_⟩
  rw [← h1, ← Finset.sum_erase_eq_sub (Finset.mem_univ τ)]
  exact Submodule.sum_mem _ fun σ hσ => Submodule.mem_iSup_of_mem σ
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hσ) (h3 σ))

theorem mu_iota_mem [FiniteDimensional Qp K] [FiniteDimensional Qp K₀]
    (hc : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K) (hc0 : Fintype.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀)
    (τ : K →ₐ[Qp] LL) (k : K) (d : T.V ⊗[Qp] B) (hd : d ∈ Dcris PD T.ρ) :
    mu Qp LL T.V (algebraMap K BdR k) (ιV PD (LL := LL) (V := T.V) d) ∈
      (DcrisL PD T.ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map (ιV PD (LL := LL) (V := T.V)) ⊔
        others PD T τ := by
  obtain ⟨y, h1, h2⟩ := exists_sum hc0 _ (mu_mem_Dcris PD T) d hd
  rw [← h1, map_sum, map_sum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  let N : Submodule LL (T.V ⊗[Qp] BdR) := DdR PD T.ρ ⊓ ⨅ c : K₀,
    LinearMap.ker (mu Qp LL T.V (algebraMap K BdR (algebraMap K₀ K c)) - σ c • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ x ∈ DdR PD T.ρ ∧
      ∀ c, mu Qp LL T.V (algebraMap K BdR (algebraMap K₀ K c)) x = σ c • x := by
    simp [N, Submodule.mem_iInf, sub_eq_zero]
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_part PD T hc τ N inf_le_left (fun c x hx => by
      rw [hN] at hx ⊢
      refine ⟨GlobalTheory.DeRhamSplit.mul_mem_DdR PD T.ρ c x hx.1, fun c' => ?_⟩
      rw [mu_mu, mul_comm, ← mu_mu, hx.2, map_smul])
    (ιV PD (LL := LL) (V := T.V) (y σ)) (by
      rw [hN]
      exact ⟨iota_mem PD T _ (h2 σ).1, fun c => by rw [← iota_mu, (h2 σ).2, map_smul]⟩)
  by_cases hσ : σ = τ.comp (IsScalarTower.toAlgHom Qp K₀ K)
  · have e : mu Qp LL T.V (algebraMap K BdR k) (ιV PD (LL := LL) (V := T.V) (y σ)) =
        τ k • ιV PD (LL := LL) (V := T.V) (y σ) +
          (mu Qp LL T.V (algebraMap K BdR k) (ιV PD (LL := LL) (V := T.V) (y σ) - z) -
            τ k • (ιV PD (LL := LL) (V := T.V) (y σ) - z)) := by
      rw [map_sub, ((mem_DdRE PD T τ z).1 hz2).2 k, smul_sub]
      abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_map_of_mem ?_))
      (Submodule.sub_mem _ (mu_mem_others PD T τ k _ hz3) (Submodule.smul_mem _ _ hz3))
    rw [← hσ, mem_DcrisL]
    exact h2 σ
  · obtain ⟨c, hc⟩ : ∃ c, σ c - τ (algebraMap K₀ K c) ≠ 0 := by
      by_contra h
      push Not at h
      exact hσ (AlgHom.ext fun c => sub_eq_zero.1 (h c))
    have hz : z = 0 := by
      rw [← smul_eq_zero_iff_right hc, sub_smul, ← ((hN z).1 hz1).2 c, ((mem_DdRE PD T τ z).1 hz2).2, sub_self]
    rw [hz, sub_zero] at hz3
    exact Submodule.mem_sup_right (mu_mem_others PD T τ k _ hz3)

theorem coords_ker {n : ℕ} (v : Basis (Fin n) LL T.V) (ι : LL →ₐ[Qp] BdR) (x : T.V ⊗[Qp] BdR)
    (hx : x ∈ compKer T ι) : coords v ι x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, y, rfl⟩ := hx
    rw [map_sub, coords_smul]
    exact sub_eq_zero.2 (coords_mu v ι (ι c) y).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coords_smul, hx, smul_zero]

theorem indep (τ : K →ₐ[Qp] LL) (ι : LL →ₐ[Qp] BdR) (hι : ∀ c, ι (τ c) = algebraMap K BdR c)
    (D : Submodule LL (T.V ⊗[Qp] B)) [FiniteDimensional LL D] (hD : finrank LL D = finrank LL T.V)
    (hle : DdR PD T.ρ ≤ D.map (ιV PD (LL := LL) (V := T.V)) ⊔ others PD T τ)
    (hspan : ∀ y : T.V ⊗[Qp] BdR, ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → T.V ⊗[Qp] BdR),
      (∀ i, d i ∈ DdR PD T.ρ) ∧ y = ∑ i, mu Qp LL T.V (b i) (d i))
    (r : ℕ) (d : Fin r → T.V ⊗[Qp] B) (b : Fin r → BdR) (hd : ∀ a, d a ∈ D)
    (hli : LinearIndependent LL d)
    (h : ∑ a, mulVR T (b a) (ιV PD (LL := LL) (V := T.V) (d a)) ∈ compKer T ι) (a : Fin r) : b a = 0 := by
  let v := Module.finBasis LL T.V
  let A : D →+ (Fin (finrank LL T.V) → BdR) := (coords v ι).toAddMonoidHom.comp
    ((ιV PD (LL := LL) (V := T.V)) ∘ₗ D.subtype).toAddMonoidHom
  have hA : ∀ x : D, A x = coords v ι (ιV PD (LL := LL) (V := T.V) x) := fun _ => rfl
  have hl := indep_of_span ι hD A (fun c x => by rw [hA, hA, Submodule.coe_smul, map_smul, coords_smul])
    (by
      rw [eq_top_iff]
      intro f _
      obtain ⟨y, rfl⟩ := coords_surj v ι f
      obtain ⟨m, b, w, hw, rfl⟩ := hspan y
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [coords_mu]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨_, ⟨x, hx, rfl⟩, u, hu, e⟩ := Submodule.mem_sup.1 (hle (hw i))
      rw [← e, map_add, coords_ker T v ι u (others_le_compKer PD T τ ι hι hu), add_zero]
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    (fun a => ⟨d a, hd a⟩) (LinearIndependent.of_comp D.subtype hli)
  refine Fintype.linearIndependent_iff.1 hl b ?_ a
  have := coords_ker T v ι _ h
  rw [map_sum] at this
  rw [← this]
  exact Finset.sum_congr rfl fun a _ => (coords_mu v ι _ _).symm

theorem act_compKer (g : G) (ι ι' : LL →ₐ[Qp] BdR) (h : ∀ c, PD.actdR g (ι c) = ι' c)
    (x : T.V ⊗[Qp] BdR) (hx : x ∈ compKer T ι) : actVdR PD T.ρ g x ∈ compKer T ι' := by
  have : compKer T ι ≤ (compKer T ι').comap (actVdR PD T.ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, y, rfl⟩
    refine Submodule.subset_span ⟨c, actVdR PD T.ρ g y, ?_⟩
    rw [map_sub, map_smul]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, mulVR, h]
    | add y z hy hz => simp only [map_add, hy, hz]
  exact this hx

theorem act_FilV (g : G) (a : ℤ) (x : T.V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := T.V) a) :
    actVdR PD T.ρ g x ∈ FilV PD (LL := LL) (V := T.V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨T.ρ g v ⊗ₜ ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

theorem mu_FilV (a : ℤ) (c : BdR) (hc : ∀ b ∈ PD.Fil a, c * b ∈ PD.Fil a) (x : T.V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := T.V) a) :
    mu Qp LL T.V c x ∈ FilV PD (LL := LL) (V := T.V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨c * b.1, hc _ b.2⟩, rfl⟩
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

theorem mem_FilV_of_comp {E : Type} [Field E] [Algebra Qp E] [Algebra K E] [Algebra E BdR]
    [IsScalarTower Qp E BdR] [IsScalarTower K E BdR] [FiniteDimensional Qp LL]
    (hE : Fintype.card (LL →ₐ[Qp] E) = finrank Qp LL) (τ : K →ₐ[Qp] LL) (ι : LL →ₐ[Qp] BdR) (a : ℤ)
    (hFil : ∀ c : E, ∀ b ∈ PD.Fil a, algebraMap E BdR c * b ∈ PD.Fil a)
    (htr : ∀ σ : LL →ₐ[Qp] E, (∀ k, σ (τ k) = algebraMap K E k) →
      ∃ g, ∀ c, PD.actdR g (ι c) = algebraMap E BdR (σ c))
    (y : T.V ⊗[Qp] BdR) (hy : y ∈ DdRE PD T.ρ τ)
    (h : y ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a) : y ∈ FilV PD (LL := LL) (V := T.V) a := by
  obtain ⟨e, h1, h2, h3, h4, h5⟩ := exists_proj hE
    ((muHom Qp T.V BdR).comp (IsScalarTower.toAlgHom Qp E BdR))
    (Algebra.lsmul Qp Qp (T.V ⊗[Qp] BdR) : LL →ₐ[Qp] _) (fun a c => by
      refine LinearMap.ext fun x => ?_
      simp [muHom_apply LL])
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, muHom_apply LL, Algebra.lsmul_apply] at h2 h3 h4 h5
  obtain ⟨hy1, hy2⟩ := (mem_DdRE PD T τ y).1 hy
  rw [← h1 y]
  refine Submodule.sum_mem _ fun σ _ => ?_
  by_cases hσ : ∀ k, σ (τ k) = algebraMap K E k
  · obtain ⟨g, hg⟩ := htr σ hσ
    obtain ⟨u, hu, w, hw, e1⟩ := Submodule.mem_sup.1 h
    have hu' := act_compKer PD T g ι ((IsScalarTower.toAlgHom Qp E BdR).comp σ) hg u hu
    have hk : ∀ x ∈ compKer T ((IsScalarTower.toAlgHom Qp E BdR).comp σ), e σ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, y, rfl⟩ := hx
        rw [map_sub, h3, h2]
        exact sub_eq_zero.2 (h4 σ (σ c) y).symm
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [h3, hx, smul_zero]
    rw [← (mem_DdR PD T y).1 hy1 g, ← e1, map_add, map_add, hk _ hu', zero_add]
    exact h5 (FilV PD (LL := LL) (V := T.V) a).toAddSubgroup
      (fun c x hx => mu_FilV PD T a _ (hFil c) x hx) (fun c x hx => Submodule.smul_mem _ c hx) σ _
      (act_FilV PD T g a w hw)
  · push Not at hσ
    obtain ⟨k, hk⟩ := hσ
    have h6 : mu Qp LL T.V (algebraMap E BdR (σ (τ k) - algebraMap K E k)) (e σ y) = 0 := by
      rw [map_sub, mu_sub, ← h2, ← h4, ← IsScalarTower.algebraMap_apply, hy2, h3, sub_self]
    have h7 : e σ y = 0 := by
      rw [← mu_one (LL := LL) (e σ y), ← map_one (algebraMap E BdR), ← inv_mul_cancel₀ (sub_ne_zero.2 hk),
        map_mul, ← mu_mu, h6, map_zero]
    rw [h7]
    exact Submodule.zero_mem _

theorem filAt_iff [FiniteDimensional Qp K] (hc : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (τ : K →ₐ[Qp] LL) (ι : LL →ₐ[Qp] BdR) (hι : ∀ c, ι (τ c) = algebraMap K BdR c) (a : ℤ)
    (hkey : ∀ y ∈ DdRE PD T.ρ τ, y ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a →
      y ∈ FilV PD (LL := LL) (V := T.V) a) (τ₀ : K₀ →ₐ[Qp] LL) (d : T.V ⊗[Qp] B)
    (hd : d ∈ DcrisL PD T.ρ τ₀) : ιV PD (LL := LL) (V := T.V) d ∈ FilAt PD T τ a ↔
      ιV PD (LL := LL) (V := T.V) d ∈ compKer T ι ⊔ FilV PD (LL := LL) (V := T.V) a := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · exact (sup_le (le_sup_of_le_right inf_le_right)
      (le_sup_of_le_left (others_le_compKer _ T τ ι hι)) : FilAt _ T τ a ≤ _) hf
  · obtain ⟨y, -, hy1, hy2⟩ := exists_part PD T hc τ _ le_rfl
      (GlobalTheory.DeRhamSplit.mul_mem_DdR _ T.ρ) _ (iota_mem _ T d hd.1)
    have hy3 := hkey y hy1 (by
      rw [← sub_sub_cancel (ιV PD (LL := LL) (V := T.V) d) y]
      exact Submodule.sub_mem _ hf (Submodule.mem_sup_left (others_le_compKer _ T τ ι hι hy2)))
    rw [← add_sub_cancel y (ιV PD (LL := LL) (V := T.V) d)]
    exact Submodule.add_mem_sup ⟨hy1, hy3⟩ hy2

theorem exists_lift (τ : K →ₐ[Qp] LL) (D : Submodule LL (T.V ⊗[Qp] B))
    (hle : DdR PD T.ρ ≤ D.map (ιV PD (LL := LL) (V := T.V)) ⊔ others PD T τ) :
    ∀ w ∈ DdRE PD T.ρ τ, ∃ d ∈ D, ιV PD (LL := LL) (V := T.V) d - w ∈ others PD T τ := by
  intro w hw
  obtain ⟨_, ⟨d, hd, rfl⟩, u, hu, e⟩ := Submodule.mem_sup.1 (hle hw.1)
  refine ⟨d, hd, ?_⟩
  rw [← e, sub_add_cancel_left]
  exact Submodule.neg_mem _ hu

omit [TopologicalSpace G] in
theorem finite_DcrisL {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) (h : IsCrys PD ρ) (τ₀ : K₀ →ₐ[Qp] LL) :
    FiniteDimensional LL ↥(DcrisL PD ρ τ₀) :=
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ h
  Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left

end Period

theorem exists_factor {F L E R : Type} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    [FiniteDimensional F L] [CommRing R] [IsDomain R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]
    (hE : Fintype.card (L →ₐ[F] E) = finrank F L) (ι : L →ₐ[F] R) :
    ∃ σ : L →ₐ[F] E, ∀ c, ι c = algebraMap E R (σ c) := by
  obtain ⟨e, h1, h2, -⟩ := exists_proj hE ((Algebra.lmul F R).comp (IsScalarTower.toAlgHom F E R))
    ((Algebra.lmul F R).comp ι) (fun a c => (Commute.all (algebraMap E R a) (ι c)).map (Algebra.lmul F R))
  obtain ⟨σ, hσ⟩ : ∃ σ, e σ 1 ≠ 0 := by
    by_contra h
    push Not at h
    have := h1 1
    simp [h] at this
  exact ⟨σ, fun c => mul_right_cancel₀ hσ (by simpa using h2 σ c 1)⟩

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem om_mul_mem_Fil (K : FinExt l) (a : ℤ) (c : Om l) (b : P.R.BdR) (hb : b ∈ (P.PD K).Fil a) :
    algebraMap (Om l) P.R.BdR c * b ∈ (P.PD K).Fil a := by
  obtain ⟨K', hK'⟩ : ∃ K' : FinExt l, c ∈ K'.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {c},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)⟩,
    IntermediateField.mem_adjoin_simple_self _ c⟩
  have h1 : b ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, P.PD_Fil K' K]; exact hb
  have h2 := ((P.PD K').Fil a).smul_mem ⟨c, hK'⟩ h1
  rw [← SetLike.mem_coe, P.PD_Fil K' K, Algebra.smul_def] at h2
  exact h2

theorem exists_conj (K LL : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (σ₀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l)
    (h₀ : ∀ k, σ₀ (τ k) = (k : Om l)) (h : ∀ k, σ (τ k) = (k : Om l)) :
    ∃ g : ↥(GK K), ∀ c, (g : GQ l) (σ₀ c) = σ c := by
  obtain ⟨g₀, hg₀⟩ := Points.exists_aut LL.1 σ₀
  obtain ⟨g, hg⟩ := Points.exists_aut LL.1 σ
  have key : ∀ c, (g₀.symm.trans g) (σ₀ c) = σ c := fun c => by
    rw [AlgEquiv.trans_apply, ← hg₀, AlgEquiv.symm_apply_apply, hg]
  refine ⟨⟨g₀.symm.trans g, fun k => ?_⟩, key⟩
  have := key (τ k)
  rw [h₀, h] at this
  exact this

theorem mem_FilV_local [IsDomain P.R.BdR] (K LL : FinExt l) (T : Lt K LL) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (hι : ∀ c, ι (τ c) = algebraMap ↥K.1 P.R.BdR c) (a : ℤ)
    (y : T.V ⊗[ℚ_[l]] P.R.BdR) (hy : y ∈ DdRE (P.PD K) T.ρ τ)
    (h : y ∈ compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a) :
    y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hE := AlgHom.card ℚ_[l] ↥LL.1 (Om l)
  obtain ⟨σ₀, hσ₀⟩ := exists_factor hE ι
  refine mem_FilV_of_comp (P.PD K) T hE τ ι a (om_mul_mem_Fil _ K a) (fun σ hσ => ?_) y hy h
  obtain ⟨g, hg⟩ := exists_conj K LL τ σ₀ σ (fun k => (algebraMap (Om l) P.R.BdR).injective
    (by rw [← hσ₀, hι]; rfl)) hσ
  exact ⟨g, fun c => by rw [P.PD_actdR, hσ₀, P.actQdR_Om, hg]⟩

variable {P} in

theorem ddR_le {AI : LocAinf l P} (ht : LocTied l P AI) (K LL : FinExt l) (T : Lt K LL)
    (hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (hc0 : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K)) (hT : IsCrys (P.PD K) T.ρ)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    DdR (P.PD K) T.ρ ≤ (DcrisL (P.PD K) T.ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map
      (ιV (P.PD K) (LL := ↥LL.1) (V := T.V)) ⊔ others (P.PD K) T τ := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  rw [Nat.card_eq_fintype_card] at hc hc0
  intro y hy
  obtain ⟨m, c, d, hd, rfl⟩ := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ ht K LL T.V T.ρ hT).2 y hy
  exact Submodule.sum_mem _ fun j _ => mu_iota_mem (P.PD K) T hc hc0 τ (c j) (d j) (hd j)

variable {P} in

theorem component_tied {AI : LocAinf l P} (ht : LocTied l P AI) (K LL : FinExt l) (T : Lt K LL)
    (hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (hc0 : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K)) (hT : IsCrys (P.PD K) T.ρ)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (hι : ∀ c, ι (τ c) = algebraMap ↥K.1 P.R.BdR c) (τ₀ : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = τ₀) :
    (∀ (r : ℕ) (d : Fin r → T.V ⊗[ℚ_[l]] P.R.B) (b : Fin r → P.R.BdR), (∀ a, d a ∈ DcrisL (P.PD K) T.ρ τ₀) →
      LinearIndependent ↥LL.1 d →
      ∑ a, mulVR T (b a) (ιV (P.PD K) (LL := ↥LL.1) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0) ∧
    (∀ d ∈ DcrisL (P.PD K) T.ρ τ₀, ∀ a : ℤ,
      ιV (P.PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt (P.PD K) T τ a ↔
      ιV (P.PD K) (LL := ↥LL.1) (V := T.V) d ∈ compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a) ∧
    (∀ w ∈ DdRE (P.PD K) T.ρ τ, ∃ d ∈ DcrisL (P.PD K) T.ρ τ₀,
      ιV (P.PD K) (LL := ↥LL.1) (V := T.V) d - w ∈ others (P.PD K) T τ) ∧
    finrank ↥LL.1 ↥(DcrisL (P.PD K) T.ρ τ₀) = finrank ↥LL.1 T.V := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hdim := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _ ht K LL T.V T.ρ).1 hc0 hT τ₀
  have hle := ddR_le ht K LL T hc hc0 hT τ
  rw [hτ] at hle
  rw [Nat.card_eq_fintype_card] at hc
  have hspan := GlobalTheory.Per.DeRhamSpan.tied_deRham_span l _ _ ht K LL T.V T.ρ
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ ht K LL T.V T.ρ hT).1
  haveI := finite_DcrisL (P.PD K) T.ρ hT τ₀
  haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied ht).isDomain
  exact ⟨indep (P.PD K) T τ ι hι _ hdim hle hspan,
    fun d hd a => filAt_iff (P.PD K) T hc τ ι hι a (mem_FilV_local P K LL T τ ι hι a) τ₀ d hd,
    exists_lift (P.PD K) T τ _ hle, hdim⟩

end Local

set_option maxHeartbeats 1000000 in

theorem component : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i → (∀ (r : ℕ) (d : Fin r → T.V ⊗[ℚ_[l]] (D.loc l).R.B) (b : Fin r → (D.loc l).R.BdR), (∀ a, d a ∈ Di (HW l) h T i) → LinearIndependent ↥LL.1 d → ∑ a, mulVR T (b a) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0) ∧ (∀ d ∈ Di (HW l) h T i, ∀ a : ℤ, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ↔ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) a) ∧ (∀ w ∈ DdRE ((D.loc l).PD K) T.ρ τ, ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') ∧ Module.finrank ↥LL.1 ↥(Di (HW l) h T i) = Module.finrank ↥LL.1 T.V := by
  intro D HW l _ K s LL h W T hT i ζ τ ι hC hτ
  obtain ⟨-, -, -, hc, hc0⟩ := Points.points D HW l K s LL h
  exact component_tied (D.locT l) K LL T hc hc0 hT τ ι hC.2.2 _ hτ

end GlobalTheory.NL.CompD
