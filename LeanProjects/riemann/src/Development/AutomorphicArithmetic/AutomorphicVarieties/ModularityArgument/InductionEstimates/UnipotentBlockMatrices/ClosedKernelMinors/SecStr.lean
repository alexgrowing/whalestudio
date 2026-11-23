import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmissibleCuspFormsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem secStr_side {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (μ₂ : Measure (G1 K 2))
    [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)) (D : TypeDat K n) (hτ : CuspIrr μ₂ τ) (ι : G1 K 2 →* G1 K n)
    (hι : Continuous ι) (hιK : ∀ x ∈ KG K 2, ι x ∈ KG K n) (hK : IsCompact (KG K n : Set (G1 K n))) :
    ∃ E : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E ∧ (∀ φ ∈ E, Rd τ φ) ∧
      ∀ f : G1 K n → ℂ, Continuous f → D.Fix f → ∀ g, ∀ k ∈ KG K n,
        (∃ v ∈ τ, Reps μ₂ v fun m => f (g * ι m * k)) → (fun m => f (g * ι m * k)) ∈ E := by
  classical
  obtain ⟨-, hUK, 𝒜, hfd, hA, hfix⟩ := typeFin D
  obtain ⟨O, hO, hOU⟩ := D.isOpen
  have hmem : ∀ g ∈ KG K n, g ∈ D.U ↔ (g : AdelicGLn.AdelicGL K n) ∈ O := fun g hg =>
    ⟨fun h => ((hOU g).1 h).1, fun h => (hOU g).2 ⟨h, hg⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun k : KG K n => {y : G1 K n | (((k : G1 K n)⁻¹ * y : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O})
    (fun k => hO.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id)))
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by
      have := (hmem 1 (one_mem _)).1 (one_mem _)
      simpa using this⟩)
  let c : KG K n → G1 K 2 →* G1 K n := fun k => (MulAut.conj ((k : G1 K n)⁻¹)).toMonoidHom.comp ι
  have hc : ∀ k x, c k x = (k : G1 K n)⁻¹ * ι x * k := fun k x => by simp [c]
  have hcc : ∀ k, Continuous (c k) := fun k => by
    have : (c k : G1 K 2 → G1 K n) = fun x => (k : G1 K n)⁻¹ * ι x * k := funext (hc k)
    rw [this]
    exact (continuous_const.mul hι).mul continuous_const
  let U : Subgroup (G1 K 2) := KG K 2 ⊓ ⨅ j : t, D.U.comap (c j)
  have hU : ∀ x, x ∈ U ↔ x ∈ KG K 2 ∧ ∀ j : t, c j x ∈ D.U := fun x => by
    simp only [U, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  let d : t → U → D.U := fun j x => ⟨c j x, ((hU x).1 x.2).2 j⟩
  have hd : ∀ j, Continuous (d j) := fun j => ((hcc j).comp continuous_subtype_val).subtype_mk _
  have hdm : ∀ j x y, d j (x * y) = d j x * d j y := fun j x y => Subtype.ext (map_mul (c j) _ _)
  let ℬ : Submodule ℂ (U → ℂ) := ⨆ j : t, 𝒜.map (LinearMap.funLeft ℂ ℂ (d j))
  have hin : ∀ j, ∀ a ∈ 𝒜, (fun x => a (d j x)) ∈ ℬ := fun j a ha =>
    Submodule.mem_iSup_of_mem j ⟨a, ha, rfl⟩
  have hcK : ∀ j : KG K n, ∀ x ∈ KG K 2, c j x ∈ KG K n := fun j x hx => by
    rw [hc]
    exact mul_mem (mul_mem (inv_mem j.2) (hιK x hx)) j.2
  obtain ⟨E, hE, hR, hP⟩ := adm μ₂ τ hτ U inf_le_left
    ⟨⋂ j : t, {x | ((c j x : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O},
      isOpen_iInter_of_finite fun j => hO.preimage (continuous_subtype_val.comp (hcc j)), fun x hx => by
        rw [hU, Set.mem_iInter]
        exact ⟨fun h j => (hmem _ (hcK j x hx)).1 (h.2 j), fun h => ⟨hx, fun j => (hmem _ (hcK j x hx)).2 (h j)⟩⟩⟩
    ℬ inferInstance (fun a ha => by
      refine Submodule.iSup_induction _ (motive := fun a : U → ℂ => Continuous a ∧ ∀ u : U, (fun x => a (x * u)) ∈ ℬ) ha ?_ ?_ ?_
      · rintro j _ ⟨b, hb, rfl⟩
        refine ⟨(hA b hb).1.comp (hd j), fun u => ?_⟩
        have := hin j _ ((hA b hb).2 (d j u))
        simpa only [LinearMap.funLeft_apply, hdm] using this
      · exact ⟨continuous_zero, fun _ => zero_mem _⟩
      · exact fun a b ha hb => ⟨ha.1.add hb.1, fun u => add_mem (ha.2 u) (hb.2 u)⟩)
  refine ⟨E, hE, hR, fun f hf hD g k hk hrep => hP _ (hf.comp ((continuous_const.mul hι).mul continuous_const)) hrep fun m => ?_⟩
  obtain ⟨j, hj, hjk⟩ := Set.mem_iUnion₂.1 (ht hk)
  have hu : (j : G1 K n)⁻¹ * k ∈ D.U := (hmem _ (mul_mem (inv_mem j.2) hk)).2 hjk
  have h := hin ⟨j, hj⟩ _ ((hA _ (hfix f hf hD (g * ι m * j))).2 ⟨_, hu⟩)
  convert h using 3 with x
  change _ = g * ι m * j * (c j x * ((j : G1 K n)⁻¹ * k))
  rw [hc, map_mul]
  group

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secStr :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
      ∃ E₁ E₂ : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E₁ ∧ FiniteDimensional ℂ E₂ ∧ (∀ φ ∈ E₁, Rd τ₁ φ) ∧ (∀ φ ∈ E₂, Rd τ₂ φ) ∧
        ∀ f : G1 K (2 + 2) → ℂ, Continuous f → D.Fix f → Slices τ₁ τ₂ f → ∀ k ∈ KG K (2 + 2),
          (∀ m₂, (fun m₁ => f (lv m₁ m₂ 0 * k)) ∈ E₁) ∧ ∀ m₁, (fun m₂ => f (lv m₁ m₂ 0 * k)) ∈ E₂ := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂
  obtain ⟨-, hmul, -, hcont, -, -, -, -, -, -, hK, hcpt⟩ := @blkLaws K _ _
  obtain ⟨ι₁, d₁⟩ : ∃ ι : G1 K 2 →* G1 K (2 + 2), ∀ m, ι m = lv m 1 0 :=
    ⟨MonoidHom.mk' (fun m => lv m 1 0) fun a b => by rw [hmul, mul_one, add_zero], fun _ => rfl⟩
  obtain ⟨ι₂, d₂⟩ : ∃ ι : G1 K 2 →* G1 K (2 + 2), ∀ m, ι m = lv 1 m 0 :=
    ⟨MonoidHom.mk' (fun m => lv 1 m 0) fun a b => by rw [hmul, mul_one, add_zero], fun _ => rfl⟩
  have c₁ : Continuous ι₁ := by
    have h : Continuous fun m : G1 K 2 => ((m, 1, 0) : G1 K 2 × G1 K 2 × ℝ) := continuous_id.prodMk continuous_const
    exact (hcont.comp' h).congr fun m => (d₁ m).symm
  have c₂ : Continuous ι₂ := by
    have h : Continuous fun m : G1 K 2 => ((1, m, 0) : G1 K 2 × G1 K 2 × ℝ) :=
      continuous_const.prodMk (continuous_id.prodMk continuous_const)
    exact (hcont.comp' h).congr fun m => (d₂ m).symm
  have e₁ : ∀ m₁ m₂, lv m₁ m₂ 0 = lv 1 m₂ 0 * ι₁ m₁ := fun m₁ m₂ => by
    rw [d₁, hmul, mul_one, one_mul, add_zero]
  have e₂ : ∀ m₁ m₂, lv m₁ m₂ 0 = lv m₁ 1 0 * ι₂ m₂ := fun m₁ m₂ => by
    rw [d₂, hmul, mul_one, one_mul, add_zero]
  obtain ⟨E₁, f₁, r₁, p₁⟩ := secStr_side μ₂ τ₁ D h₁ ι₁ c₁ (fun x hx => by rw [d₁]; exact hK x hx 1 (one_mem _)) (hcpt _).1
  obtain ⟨E₂, f₂, r₂, p₂⟩ := secStr_side μ₂ τ₂ D h₂ ι₂ c₂ (fun x hx => by rw [d₂]; exact hK 1 (one_mem _) x hx) (hcpt _).1
  refine ⟨E₁, E₂, f₁, f₂, r₁, r₂, fun f hf hD hS k hk => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · have h := (hS k).1 m₂
    have e : (fun m₁ => f (lv m₁ m₂ 0 * k)) = fun m₁ => f (lv 1 m₂ 0 * ι₁ m₁ * k) := funext fun m₁ => by rw [← e₁]
    rw [e] at h ⊢
    exact p₁ f hf hD _ k hk h
  · have h := (hS k).2 m₁
    have e : (fun m₂ => f (lv m₁ m₂ 0 * k)) = fun m₂ => f (lv m₁ 1 0 * ι₂ m₂ * k) := funext fun m₂ => by rw [← e₂]
    rw [e] at h ⊢
    exact p₂ f hf hD _ k hk h
