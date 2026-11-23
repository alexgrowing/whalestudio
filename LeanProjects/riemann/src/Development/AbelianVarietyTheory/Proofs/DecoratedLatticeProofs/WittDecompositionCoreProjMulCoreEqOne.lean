import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def dualC (𝔟 : FI D) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {c | ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range}
  add_mem' := fun {x y} hx hy b hb => by
    rw [mul_add]; exact add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [mul_zero]; exact zero_mem _
  smul_mem' := fun r x hx b hb => by
    obtain ⟨o, ho⟩ := hx b hb
    refine ⟨r * o, ?_⟩
    rw [map_mul, ho, Algebra.smul_def]; ring

theorem mem_dualC {𝔟 : FI D} {c : D.host.E} :
    c ∈ dualC 𝔟 ↔ ∀ b ∈ 𝔟, star b * c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

def crd {m : ℕ} (q : Matrix (Fin m) (Fin S.rank) D.host.E) : (Fin S.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin m → D.host.E) :=
  (Matrix.mulVecLin q).restrictScalars (𝓞 D.host.E)

def splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) : Lat S :=
  (⨅ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).comap ((LinearMap.proj i).comp (crd d.qX))) ⊓
    L₀.comap (crd d.q0) ⊓ ⨅ i : Fin ρ, (dualC (𝔟 i)).comap ((LinearMap.proj i).comp (crd d.qY))

theorem mem_splitL (d : HypDec S S₀ ρ) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (y : Fin S.rank → D.host.E) :
    y ∈ splitL d L₀ 𝔟 ↔ (∀ i : Fin ρ, (d.qX *ᵥ y) i ∈ 𝔟 i) ∧ d.q0 *ᵥ y ∈ L₀ ∧ ∀ i : Fin ρ, (d.qY *ᵥ y) i ∈ dualC (𝔟 i) := by
  simp only [splitL, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.proj_apply]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

variable (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pX_jX)
theorem qX_i₀ : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
theorem qX_e' : d.qX * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_jY)
theorem qY_e : d.qY * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_jX)
theorem qY_i₀ : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)
theorem qY_e' : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
theorem wittDecomposition_coreProj_mul_e_eq_zero : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
theorem wittDecomposition_coreProj_mul_core_eq_one : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
theorem wittZeroProjection_mul_dualBasis_eq_zero : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)

theorem gram_eq : S.gram = d.qYᴴ * d.qX + d.q0ᴴ * (S₀.gram * d.q0) + d.qXᴴ * d.qY := by
  apply rat_injective
  rw [rat_add, rat_add, rat_mul, rat_mul, rat_mul, rat_mul, rat_conjTranspose, rat_conjTranspose, rat_conjTranspose]
  exact d.gA_eq

theorem rat_mulVec_gen {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_mem_latV {S' : HSp D} (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat S'}
    (hM : ∀ x ∈ L, M *ᵥ x ∈ L') (P : Pl D → Prop) {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [rat_mulVec_gen]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

variable {d} {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem e_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ 𝔟 i) : d.e *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e, Matrix.one_mulVec]; exact hw i
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_e_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e, Matrix.zero_mulVec]; exact zero_mem _

theorem i₀_mem {x : Fin S₀.rank → D.host.E} (hx : x ∈ L₀) : d.i₀ *ᵥ x ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_i₀, Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]; exact hx
  · rw [Matrix.mulVec_mulVec, qY_i₀, Matrix.zero_mulVec]; exact zero_mem _

theorem e'_mem {w : Fin ρ → D.host.E} (hw : ∀ i : Fin ρ, w i ∈ dualC (𝔟 i)) : d.e' *ᵥ w ∈ splitL d L₀ 𝔟 := by
  refine (mem_splitL d L₀ 𝔟 _).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mulVec_mulVec, qX_e', Matrix.zero_mulVec]
    show (0 : D.host.E) ∈ (𝔟 i : Submodule (𝓞 D.host.E) D.host.E); exact zero_mem _
  · rw [Matrix.mulVec_mulVec, wittZeroProjection_mul_dualBasis_eq_zero, Matrix.zero_mulVec]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, qY_e', Matrix.one_mulVec]; exact hw i

theorem single_mem_of_mem {I : ℕ → Submodule (𝓞 D.host.E) D.host.E} (i : Fin ρ) {a : D.host.E} (ha : a ∈ I i) (j : Fin ρ) :
    (Pi.single i a : Fin ρ → D.host.E) j ∈ I j := by
  by_cases h : j = i
  · subst h; rw [Pi.single_eq_same]; exact ha
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

def colProj {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    Matrix (Fin S.rank) (Fin m) D.host.E := Matrix.of fun k l => f k i * q i l

theorem colProj_mulVec {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (x : Fin m → D.host.E) : colProj q f i *ᵥ x = f *ᵥ Pi.single i ((q *ᵥ x) i) := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]

theorem colMul_rat {m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ)
    (y : Fin m → AE D) : colMul (rat f) i ((rat q *ᵥ y) i) = rat (colProj q f i) *ᵥ y := by
  funext k
  simp only [colMul, colProj, rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem colMul_eq_mulVec {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : colMul x i a = x *ᵥ Pi.single i a := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_comm]

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) : x *ᵥ w = ∑ i, colMul x i (w i) := by
  funext k
  simp only [colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

variable (d L₀ 𝔟)

theorem monoAt_splitL (v : Pl D) : MonoAt d (splitL d L₀ 𝔟) L₀ v := by
  have hX : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qX d.e i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i
      (((mem_splitL d L₀ 𝔟 x).1 hx).1 i))
  have hY : ∀ i : Fin ρ, ∀ x ∈ splitL d L₀ 𝔟, colProj d.qY d.e' i *ᵥ x ∈ splitL d L₀ 𝔟 := fun i x hx => by
    rw [colProj_mulVec]
    exact e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i (((mem_splitL d L₀ 𝔟 x).1 hx).2.2 i))
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 (fun x hx => ((mem_splitL d L₀ 𝔟 x).1 hx).2.1) _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ (fun x hx => i₀_mem hx) _ h2

theorem line_splitL (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jX i a ∈ latV S (splitL d L₀ 𝔟) (· = v) ↔ a ∈ idV (𝔟 i) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (splitL d L₀ 𝔟) (· = v), (d.pX *ᵥ y) i ∈ idV (𝔟 i) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qX *ᵥ _) i ∈ _
        rw [rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact ((mem_splitL d L₀ 𝔟 x).1 hx).1 i
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [colMul_eq_mulVec, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jX i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [colMul_eq_mulVec]
        change rat d.e *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb), rfl⟩
    | zero =>
      have : colMul d.jX i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jX i (z + z') = colMul d.jX i z + colMul d.jX i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jX i (-z) = -colMul d.jX i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.SeeSaw.SplitLat

end
