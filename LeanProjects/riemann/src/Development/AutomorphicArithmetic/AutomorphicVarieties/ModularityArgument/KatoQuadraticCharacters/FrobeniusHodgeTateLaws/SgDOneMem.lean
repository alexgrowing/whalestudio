import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement

open UpperTheory.V.Z.Kato.Joint
open Formalism.ConjugateSelfDual GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

variable {l : ℕ} [Fact l.Prime]

private theorem norm_zl (c : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

private theorem nadd {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem nmul {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ r) : ‖x * y‖ ≤ r := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

private theorem nappr (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - algebraMap ℤ_[l] (Qbar l) c‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hz
  simp only [map_mul, map_pow, map_natCast, map_sub] at h
  rw [norm_sub_rev, ← h]
  exact nmul (by rw [norm_zl]; exact z.norm_le_one) le_rfl

private theorem extend {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (r : ℝ) (f : M → ℕ → Qbar l)
    (hf : ∀ b ∈ B, ∀ b' ∈ B, ∀ c c' : ℤ_[l], ∀ i,
      ‖f (c • b + c' • b') i - (algebraMap ℤ_[l] (Qbar l) c * f b i + algebraMap ℤ_[l] (Qbar l) c' * f b' i)‖ ≤ r) :
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] M) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ B, ∀ i, ‖Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i - f b i‖ ≤ r := by
  classical
  let e := Module.Free.chooseBasis ℤ_[l] B
  let g : B →ₗ[ℤ_[l]] (ℕ → Qbar l) := e.constr ℤ_[l] (fun k => f (e k))
  have h0 : ∀ i, ‖f 0 i‖ ≤ r := fun i => by simpa using hf 0 B.zero_mem 0 B.zero_mem 0 0 i
  have hr : 0 ≤ r := (norm_nonneg _).trans (h0 0)
  have hg : ∀ b : B, ∀ i, ‖g b i - f b i‖ ≤ r := by
    intro b i
    have hb : b ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa [g] using hr
    | zero => simpa using h0 i
    | add x y _ _ hx hy =>
      have h := hf x x.2 y y.2 1 1 i
      simp only [one_smul, map_one, one_mul] at h
      rw [← norm_neg] at h
      have := nadd (nadd hx hy) h
      convert this using 2
      simp only [map_add, Pi.add_apply, Submodule.coe_add]
      ring
    | smul c x _ hx =>
      have h := hf x x.2 0 B.zero_mem c 0 i
      simp only [zero_smul, add_zero, map_zero, zero_mul] at h
      rw [← norm_neg] at h
      have := nadd (nmul (x := algebraMap ℤ_[l] (Qbar l) c) (by rw [norm_zl]; exact c.norm_le_one) hx) h
      convert this using 2
      simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def]
      ring
  haveI : Module.IsTorsionFree ℤ_[l] (Qbar l) := by
    refine (Module.isTorsionFree_iff_algebraMap_injective).2 ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have := norm_zl a
    rw [ha, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  haveI : Module.Flat ℤ_[l] (Qbar l) := inferInstance
  have hinj : Function.Injective (B.subtype.baseChange (Qbar l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Qbar l) B.subtype B.injective_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange (Qbar l))
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(g.liftBaseChange (Qbar l)) ∘ₗ s, fun b hb i => ?_⟩
  have h1 : s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B) :=
    LinearMap.congr_fun hs ((1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B))
  simpa [h1] using hg ⟨b, hb⟩ i

private theorem sgD_one_mem {N : ℕ} (hN : N ≠ 0) : sgD N l 1 ∈ Gam N l := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (l := l) (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  refine ⟨?_, h1⟩
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)

private theorem act_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gam N l) {b : X.Fn l} (hb : b ∈ X.B N l w) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

open UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt in
theorem UpperTheory.V.Z.Kato.Joint.thLin :
    UpperTheory.V.Z.Kato.Joint.ThLin := by
  intro l _ Ω _ _ _ ε X A N w j hS n
  obtain ⟨hA, h2, hlN, h5, hw, hj⟩ := hS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN).symm
  have hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩
  haveI := (GlobalTheory.T.kummerBettiModule_free_finite ε X ε.injective hhol N l w h2 h5 hcop hw).1
  have hth : ∀ b ∈ X.B N l w, IsThB X A N l n b (thN X A N l n 1 b) := by
    intro b hb
    have h := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol h2 hlN h5 hA n w 1 hw (Nat.coprime_one_left N) b hb).1
    rwa [act_fix X (sgD_one_mem (by omega)) hb] at h
  have hint : ∀ b ∈ X.B N l w, ∀ i, ‖th X A N j n b i‖ ≤ 1 := by
    intro b hb i
    obtain ⟨f, -, -, -, h, -⟩ := hth b hb
    exact hj _ (h _)
  refine extend (X.B N l w) ‖((l : ℕ) : Qbar l) ^ n‖ (th X A N j n) ?_
  intro b hb b' hb' c c' i
  have hm : c • b + c' • b' ∈ X.B N l w := add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hb')
  obtain ⟨z, hz, h⟩ := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol h2 hlN h5 hA n w hw _ hm _ _ (hth _ hm)
    (GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w b b' hb hb' c c' _ _ (hth b hb) (hth b' hb')) ((i : ℚ) / ((1 : ℕ) : ℚ))
  have h1 := congrArg j h
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_sub, map_add, map_mul, map_pow,
    map_natCast] at h1
  have h3 : ‖j z * ((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := nmul (hj z hz) le_rfl
  have := nadd (nadd h3 (nmul (hint b hb i) (nappr n c))) (nmul (hint b' hb' i) (nappr n c'))
  convert this using 2
  simp only [th, seqN]
  linear_combination h1
