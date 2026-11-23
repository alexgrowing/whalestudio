import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UnitaryEmbeddingGroup

variable {D : D7}

theorem antiDiagonalEpsilonGramMatrix_mul_self {K : Type} [Field K] (c : ℕ) (ε : K) :
    antiDiagonalSignGramMatrix c ε * antiDiagonalSignGramMatrix c ε = Matrix.diagonal (fun p : Fin c => if p.1 + p.1 + 1 = c then ε * ε else 1) := by
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single p.rev]
  · have hp := p.2; have hq := q.2
    simp only [antiDiagonalSignGramMatrix, Matrix.diagonal_apply, Fin.val_rev, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring
  · intro r _ hr
    have : ¬ p.1 + r.1 + 1 = c := fun e => hr (Fin.ext (by rw [Fin.val_rev]; omega))
    simp [antiDiagonalSignGramMatrix, this]
  · simp

theorem antiDiagonalEpsilonGramMatrix_det_ne_zero {K : Type} [Field K] {c : ℕ} {ε : K} (hε : ε ≠ 0) : (antiDiagonalSignGramMatrix c ε).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (antiDiagonalEpsilonGramMatrix_mul_self c ε)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_diagonal] at this
  exact Finset.prod_ne_zero_iff.2 (fun p _ => by split_ifs <;> simp [hε]) this.symm

theorem incA_inj : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem map_inj {m n : ℕ} : Function.Injective (fun M : Matrix (Fin m) (Fin n) D.host.E => M.map (incA D)) :=
  fun _ _ e => Matrix.ext fun i j => incA_inj (congrFun (congrFun e i) j)

theorem mt_inv_mul (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  show (matHom V g⁻¹).1 * (matHom V g).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  show (matHom V g).1 * (matHom V g⁻¹).1 = 1
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mem_GfC_iff (V : HSp D) (g : GA D V) : g ∈ GfC V ↔
    (matHom V g).1.map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
  show infHom V g = 1 ↔ _
  exact Units.ext_iff

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔
    (matHom V g).1.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
  show finHom V g = 1 ↔ _
  exact Units.ext_iff

section Dec

variable {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)

def rM : Matrix (Fin c) (Fin B.rank) D.host.E :=
  (antiDiagonalSignGramMatrix c ε)⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram)

theorem perp' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram * frameMat B A d.ι = 0 := by
  have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) d.perp
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT, ← Matrix.mul_assoc] at this
  rw [this]; ext i j; simp [Formalism.UG.cT]

theorem qM_a : GlobalTheory.UnitaryEmbeddingProperties.qM d * d.a = 0 := by
  rw [GlobalTheory.UnitaryEmbeddingProperties.qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem rM_P : rM d * frameMat B A d.ι = 0 := by
  rw [rM, Matrix.mul_assoc, perp', Matrix.mul_zero]

theorem rM_a (hε : ε ≠ 0) : rM d * d.a = 1 := by
  rw [rM, Matrix.mul_assoc, d.gram, Matrix.nonsing_inv_mul _ (antiDiagonalEpsilonGramMatrix_det_ne_zero hε).isUnit]

theorem decomp (hε : ε ≠ 0) : frameMat B A d.ι * GlobalTheory.UnitaryEmbeddingProperties.qM d + d.a * rM d = 1 := by
  have h : Matrix.fromRows (GlobalTheory.UnitaryEmbeddingProperties.qM d) (rM d) * Matrix.fromCols (frameMat B A d.ι) d.a = 1 := by
    rw [Matrix.fromRows_mul_fromCols, GlobalTheory.UnitaryEmbeddingProperties.qM_mul, qM_a, rM_P, rM_a d hε, Matrix.fromBlocks_one]
  rw [← Matrix.fromCols_mul_fromRows]
  exact (Matrix.mul_eq_one_comm_of_equiv ((finCongr d.rank.symm).trans finSumFinEquiv.symm)).2 h

end Dec

end GlobalTheory.UnitaryEmbeddingGroup

namespace GlobalTheory.UnitaryEmbeddingGroup

variable {D : D7}

local infixl:70 " ⋆ₘ " => HMul.hMul

theorem unit_gen {R : Type} [CommRing R] (σ : R →+* R) {n r : ℕ} (J : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin r) R) (X : Matrix (Fin r) (Fin r) R) (g : Matrix (Fin n) (Fin n) R) (hPX : P * X = g * P)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT σ X * (Formalism.UG.cT σ P * J * P) * X = Formalism.UG.cT σ P * J * P := by
  calc Formalism.UG.cT σ X * (Formalism.UG.cT σ P * J * P) * X = Formalism.UG.cT σ (P * X) * J * (P * X) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ g * J * g) * P := by rw [hPX, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]

section Ad

variable {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)

theorem matA_eq (h : GA D A) : (matHom A h).1 =
    (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) ⋆ₘ (matHom B (stabilizerEmbedding d h)).1 ⋆ₘ (frameMat B A d.ι).map (incA D) := by
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, Matrix.mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P _ _ (GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map _ d),
    ← Matrix.mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map, Matrix.one_mul]

theorem map_eq_one_iff {R : Type} [CommRing R] (π : AE D →+* R) (h : GA D A) :
    (matHom A h).1.map π = 1 ↔ (matHom B (stabilizerEmbedding d h)).1.map π = 1 := by
  refine ⟨GlobalTheory.RealType.Emb_map_eq_one d π, fun e => ?_⟩
  rw [matA_eq d h, Matrix.map_mul, Matrix.map_mul, e, Matrix.mul_one, ← Matrix.map_mul,
    GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map, Matrix.map_one _ (map_zero π) (map_one π)]

theorem unitaryEmbedding_injective : Function.Injective (stabilizerEmbedding d) := fun h h' e =>
  GlobalTheory.AutFunCounterexample.GA_ext A (by rw [matA_eq d h, matA_eq d h', e])

theorem mem_rational_of_embedding_rational (h : GA D A) (hg : stabilizerEmbedding d h ∈ GQ B) : h ∈ GQ A := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hg
  set P := frameMat B A d.ι
  set Q := GlobalTheory.UnitaryEmbeddingProperties.qM d
  have e0 : matHom B (stabilizerEmbedding d h) = Formalism.UG.bc (incA D) γE := e.symm
  have e1 : (matHom B (stabilizerEmbedding d h)).1 = γE.val.map (incA D) := by
    rw [e0]; rfl
  have e2 : (matHom B (stabilizerEmbedding d h⁻¹)).1 = (γE⁻¹).val.map (incA D) := by
    have i1 : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ := map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) h
    rw [i1, map_inv, e0, ← map_inv]; rfl
  have hA1 : (Q ⋆ₘ γE.val ⋆ₘ P).map (incA D) = (matHom A h).1 := by
    rw [matA_eq d h, e1, Matrix.map_mul, Matrix.map_mul]
  have hA2 : (Q ⋆ₘ (γE⁻¹).val ⋆ₘ P).map (incA D) = (matHom A h⁻¹).1 := by
    rw [matA_eq d h⁻¹, e2, Matrix.map_mul, Matrix.map_mul]
  let M : GL (Fin A.rank) D.host.E := ⟨Q ⋆ₘ γE.val ⋆ₘ P, Q ⋆ₘ (γE⁻¹).val ⋆ₘ P,
    map_inj (by
      show (Q ⋆ₘ γE.val ⋆ₘ P ⋆ₘ (Q ⋆ₘ (γE⁻¹).val ⋆ₘ P)).map (incA D) =
        (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D)
      rw [Matrix.map_mul, hA1, hA2, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]),
    map_inj (by
      show (Q ⋆ₘ (γE⁻¹).val ⋆ₘ P ⋆ₘ (Q ⋆ₘ γE.val ⋆ₘ P)).map (incA D) =
        (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D)
      rw [Matrix.map_mul, hA1, hA2, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)])⟩
  have hu : M ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) A.gram := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Q ⋆ₘ γE.val ⋆ₘ P) * A.gram * (Q ⋆ₘ γE.val ⋆ₘ P) = A.gram
    apply map_inj
    show (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Q ⋆ₘ γE.val ⋆ₘ P) * A.gram * (Q ⋆ₘ γE.val ⋆ₘ P)).map (incA D) =
      A.gram.map (incA D)
    rw [Matrix.map_mul, Matrix.map_mul, ← GlobalTheory.AutFunCounterexample.cT_map_gen, hA1]
    exact h.2
  refine Subgroup.mem_subgroupOf.2 ⟨M, hu, Units.ext ?_⟩
  exact hA1

theorem unitaryEmbedding_fixes_vectors (h : GA D A) : mt B (stabilizerEmbedding d h) ⋆ₘ d.a.map (incA D) = d.a.map (incA D) := by
  obtain ⟨-, a2⟩ := (embRel_iff d h _).2 rfl
  ext i j
  exact congr_fun (a2 (fun k => d.a k j) (by funext k; exact congr_fun (congr_fun d.perp k) j)) i

theorem fix_adj (g : GA D B) (hg : mt B g ⋆ₘ d.a.map (incA D) = d.a.map (incA D)) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a ⋆ₘ B.gram).map (incA D) ⋆ₘ mt B g =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a ⋆ₘ B.gram).map (incA D) := by
  have hU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt B g) * B.gram.map (incA D) * mt B g =
      B.gram.map (incA D) := g.2
  rw [Matrix.map_mul, ← GlobalTheory.AutFunCounterexample.cT_map_gen]
  conv_lhs => rw [← hg]
  rw [Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (mt B g), hU]

variable (hε : ε ≠ 0)
include hε

theorem fix_P (g : GA D B) (hg : mt B g ⋆ₘ d.a.map (incA D) = d.a.map (incA D)) :
    mt B g ⋆ₘ (frameMat B A d.ι).map (incA D) = (frameMat B A d.ι).map (incA D) ⋆ₘ
      ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) ⋆ₘ mt B g ⋆ₘ (frameMat B A d.ι).map (incA D)) := by
  have hdec : (frameMat B A d.ι).map (incA D) ⋆ₘ (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) +
      d.a.map (incA D) ⋆ₘ (rM d).map (incA D) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _), decomp d hε,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h0 : (rM d).map (incA D) ⋆ₘ mt B g ⋆ₘ (frameMat B A d.ι).map (incA D) = 0 := by
    rw [rM, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (mt B g), fix_adj d g hg,
      ← Matrix.map_mul, perp', Matrix.map_zero _ (map_zero _), Matrix.mul_zero]
  calc mt B g ⋆ₘ (frameMat B A d.ι).map (incA D) = ((frameMat B A d.ι).map (incA D) ⋆ₘ (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) +
        d.a.map (incA D) ⋆ₘ (rM d).map (incA D)) ⋆ₘ (mt B g ⋆ₘ (frameMat B A d.ι).map (incA D)) := by
        rw [hdec, Matrix.one_mul]
    _ = (frameMat B A d.ι).map (incA D) ⋆ₘ ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) ⋆ₘ mt B g ⋆ₘ (frameMat B A d.ι).map (incA D)) +
        d.a.map (incA D) ⋆ₘ ((rM d).map (incA D) ⋆ₘ mt B g ⋆ₘ (frameMat B A d.ι).map (incA D)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
    _ = _ := by rw [h0, Matrix.mul_zero, add_zero]

theorem fix_ker (g : GA D B) (hg : mt B g ⋆ₘ d.a.map (incA D) = d.a.map (incA D)) (x : Fin B.rank → D.host.E)
    (hx : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) ⋆ₘ B.gram) *ᵥ x = 0) :
    mt B g *ᵥ (fun i => incA D (x i)) = fun i => incA D (x i) := by
  have hq : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ x = 0 := by
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hxa : d.a *ᵥ (rM d *ᵥ x) = x := by
    have := congrArg (· *ᵥ x) (decomp d hε)
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hq, Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] at this
    exact this
  have hm : (fun i => incA D (x i)) = d.a.map (incA D) *ᵥ (fun i => incA D ((rM d *ᵥ x) i)) := by
    conv_lhs => rw [← hxa]
    funext i; exact RingHom.map_mulVec (incA D) d.a _ i
  rw [hm, Matrix.mulVec_mulVec, hg]

theorem mem_range_of_fix (g : GA D B) (hg : mt B g ⋆ₘ d.a.map (incA D) = d.a.map (incA D)) : ∃ h, stabilizerEmbedding d h = g := by
  set P' := (frameMat B A d.ι).map (incA D)
  set Q' := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D)
  have hg' : mt B g⁻¹ ⋆ₘ d.a.map (incA D) = d.a.map (incA D) := by
    conv_lhs => rw [← hg, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have e1 : mt B g ⋆ₘ P' = P' ⋆ₘ (Q' ⋆ₘ mt B g ⋆ₘ P') := fix_P d hε g hg
  have e2 : mt B g⁻¹ ⋆ₘ P' = P' ⋆ₘ (Q' ⋆ₘ mt B g⁻¹ ⋆ₘ P') := fix_P d hε g⁻¹ hg'
  have hQP : Q' ⋆ₘ P' = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map _ d
  have hXY : Q' ⋆ₘ mt B g ⋆ₘ P' ⋆ₘ (Q' ⋆ₘ mt B g⁻¹ ⋆ₘ P') = 1 := by
    rw [Matrix.mul_assoc (Q' ⋆ₘ mt B g), ← e2, ← Matrix.mul_assoc, Matrix.mul_assoc Q', mt_mul_inv, Matrix.mul_one, hQP]
  have hYX : Q' ⋆ₘ mt B g⁻¹ ⋆ₘ P' ⋆ₘ (Q' ⋆ₘ mt B g ⋆ₘ P') = 1 := by
    rw [Matrix.mul_assoc (Q' ⋆ₘ mt B g⁻¹), ← e1, ← Matrix.mul_assoc, Matrix.mul_assoc Q', mt_inv_mul, Matrix.mul_one, hQP]
  have hJA : A.gram.map (incA D) = Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) P' ⋆ₘ B.gram.map (incA D) ⋆ₘ P' := by
    rw [← GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom, Matrix.map_mul, Matrix.map_mul, GlobalTheory.AutFunCounterexample.cT_map_gen]
  have hU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt B g) * B.gram.map (incA D) * mt B g =
      B.gram.map (incA D) := g.2
  have hX : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Q' ⋆ₘ mt B g ⋆ₘ P') * A.gram.map (incA D) * (Q' ⋆ₘ mt B g ⋆ₘ P') =
      A.gram.map (incA D) := by
    rw [hJA]
    exact unit_gen _ _ _ _ _ e1.symm hU
  let hm : GA D A := ⟨⟨Q' ⋆ₘ mt B g ⋆ₘ P', Q' ⋆ₘ mt B g⁻¹ ⋆ₘ P', hXY, hYX⟩, hX⟩
  have hrel : EmbRel B A d.ι g hm := ⟨e1, fun x hx => fix_ker d hε g hg x hx⟩
  exact ⟨hm, ((embRel_iff d hm g).1 hrel).symm⟩

end Ad

end GlobalTheory.UnitaryEmbeddingGroup

namespace GlobalTheory.UnitaryEmbeddingGroup

theorem unitaryEmbedding_hom_properties : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (c : ℕ) (ε : D.host.E), ε ≠ 0 →
    ∀ d : HermitianOrthogonalExtensionData A B c ε, ∃ ι : GA D A →* GA D B, (∀ h, ι h = stabilizerEmbedding d h) ∧ Continuous ι ∧ Function.Injective ι ∧
      (∀ h, ι h ∈ GQ B ↔ h ∈ GQ A) ∧ (∀ h, ι h ∈ GfC B ↔ h ∈ GfC A) ∧ (∀ h, ι h ∈ GinfC B ↔ h ∈ GinfC A) ∧
      (∀ g, g ∈ ι.range ↔ HMul.hMul (mt B g) (d.a.map (incA D)) = d.a.map (incA D)) ∧
      (∀ h, HMul.hMul (mt B (ι h)) ((frameMat B A d.ι).map (incA D)) = HMul.hMul ((frameMat B A d.ι).map (incA D)) (mt A h)) ∧
      ∀ τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∃ k' ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), ι (atTau θ A τ k) = atTau θ B τ k' := by
  intro D θ hθ A B c ε hε d
  refine ⟨MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d), fun h => rfl, GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d,
    unitaryEmbedding_injective d, fun h => ⟨mem_rational_of_embedding_rational d h, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d h⟩, fun h => ?_, fun h => ?_,
    fun g => ⟨?_, fun hg => ?_⟩, fun h => ((embRel_iff d h _).2 rfl).1, ?_⟩
  · show stabilizerEmbedding d h ∈ GfC B ↔ h ∈ GfC A
    rw [mem_GfC_iff, mem_GfC_iff, map_eq_one_iff d]
  · show stabilizerEmbedding d h ∈ GinfC B ↔ h ∈ GinfC A
    rw [mem_GinfC_iff, mem_GinfC_iff, map_eq_one_iff d]
  · rintro ⟨h, rfl⟩
    exact unitaryEmbedding_fixes_vectors d h
  · obtain ⟨h, e⟩ := mem_range_of_fix d hε g hg
    exact ⟨h, e⟩
  · intro τ k hk
    have hx := GlobalTheory.PointAtPlaceHom.atTau_spec hθ A τ hk
    have hk' := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ B (stabilizerEmbedding d (atTau θ A τ k)) τ
    refine ⟨_, hk', ?_⟩
    have hy : IsAtTau θ B τ (infMat D.sp.cm.sig B.gram (θ τ) (stabilizerEmbedding d (atTau θ A τ k))) (stabilizerEmbedding d (atTau θ A τ k)) := by
      refine ⟨GlobalTheory.RealType.Emb_mem_inf d hx.1, rfl, fun τ' hτ' => ?_⟩
      have h2 := hx.2.2 τ' hτ'
      rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at h2 ⊢
      exact GlobalTheory.RealType.Emb_map_eq_one d _ h2
    exact (GlobalTheory.PointAtPlace.existsUnique_isAtTau B τ θ hθ _ hk').unique hy (GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hk')

end GlobalTheory.UnitaryEmbeddingGroup
