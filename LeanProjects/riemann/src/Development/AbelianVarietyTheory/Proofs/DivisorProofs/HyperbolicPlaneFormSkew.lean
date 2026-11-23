import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivative
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraRepDerivationMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationsCommuteDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineIsLineOfPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalEnvelopingLineDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementCommutesTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandGeneratorMemQuantumDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreGeneratedByGelfandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeBlockConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBlockTriangularNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def derEnd {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : Module.End ℂ (SmG σ J) where
  toFun f := ⟨lineDer γ f.1, isSm_lineDer f.2 hγ⟩
  map_add' f f' := Subtype.ext (lineDer_add f.2 f'.2 hγ)
  map_smul' a f := Subtype.ext (lineDer_smul a f.1 γ)

theorem exists_isDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ D, IsDer σ J τ D := by
  classical
  let ρ : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (SmG σ J) := fun Z =>
    if hZ : ∃ γ, IsLineOf σ J τ Z γ then derEnd (hZ.choose_spec.isRealLine h) else 0
  have hρ : ∀ Z γ, IsLineOf σ J τ Z γ → ∀ f : SmG σ J, (ρ Z f).1 = lineDer γ f.1 := fun Z γ hγ f => by
    have hZ : ∃ γ, IsLineOf σ J τ Z γ := ⟨γ, hγ⟩
    simp only [ρ, dif_pos hZ]
    rw [hγ.unique h hZ.choose_spec]; rfl
  obtain ⟨D, h1, h2⟩ := GlobalTheory.T.lie_algebra_rep_derivation_matrix n (J.map τ.1) (conjTranspose_map h hJ τ.1) (isUnit_det_map hJ τ.1) _ ρ
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X + X') h hJ (by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hX', add_zero])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.add_apply, Submodule.coe_add, hρ _ _ hγ, hρ _ _ hδ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).1 hε)
    (fun c X hX => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, hρ _ _ hγ, hρ _ _ (hγ.smul c)]
      funext g
      have hd := ((differentiable_of_isSm f.2 (hγ.isRealLine h) g) (0 * c)).hasDerivAt.scomp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).mul_const c)
      have := hd.deriv
      simp only [zero_mul, one_mul] at this
      simpa [lineDer, Function.comp_def] using this)
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X * X' - X' * X) h hJ (by
        have e1 := eq_neg_of_add_eq_zero_left hX
        have e2 := eq_neg_of_add_eq_zero_left hX'
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
          Matrix.mul_assoc, e1, e2, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2,
          Matrix.mul_sub]
        simp [Matrix.mul_assoc])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply, hρ _ _ hγ, hρ _ _ hδ,
        hρ _ _ hδ, hρ _ _ hγ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).2 hε)
  exact ⟨D, h1, fun Z γ hγ f => by rw [h2 Z (hγ.skew h)]; exact hρ Z γ hγ f⟩

theorem glRel_frame {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B)
    (hD : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ}
    (hRQ : R * Q = 1) : GlRel fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R) := by
  intro a b c d
  have e : ∀ a b c d : Fin m, Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
      if b = c then Q * Matrix.single a d (1 : ℂ) * R else 0 := fun a b c d => by
    have : Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
        Q * (Matrix.single a b (1 : ℂ) * (R * Q) * Matrix.single c d 1) * R := by simp only [Matrix.mul_assoc]
    rw [this, hRQ, Matrix.mul_one]
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp
  rw [← hD, e, e, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem eq_sum_frame {m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hQR : Q * R = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) : X = ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) := by
  have e : ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) =
      Q * (∑ a, ∑ b, Matrix.single a b ((R * X * Q) a b)) * R := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, ← Matrix.matrix_eq_sum_single]
  simp only [← Matrix.mul_assoc, hQR, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQR, Matrix.mul_one]

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

theorem gelfA_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (k : ℕ) : gelfA X k ∈ S := by
  unfold gelfA
  refine S.sum_mem fun π _ => S.list_prod_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  exact hS _ _

theorem finite_of_gelf (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)) (hD : ∀ w, IsDer σ J (τ w) (D w))
    (v : SmG σ J) (hv : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ {x | ∃ a ∈ Algebra.adjoin ℂ
      (Set.range (gelfA fun a b => D w (Matrix.single a b 1))), x = a v})) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z v.1}) := by
  classical
  let X : InfinitePlace F → Fin n → Fin n → Module.End ℂ (SmG σ J) := fun w a b => D w (Matrix.single a b 1)
  have hG : ∀ w, GlRel (X w) := fun w => by
    simpa using glRel_frame (D w) (hD w).1 (Q := 1) (R := 1) (Matrix.mul_one _)
  have hc : ∀ w w', w ≠ w' → ∀ a b c d, X w a b * X w' c d = X w' c d * X w a b := fun w w' hne a b c d =>
    GlobalTheory.T.derivations_commute_distinct_places F E σ h n J hJ w (τ w) (D w) (hD w) w' (τ w') (D w') (hD w') hne _ _
  obtain ⟨W, hW, hvW, hs⟩ := GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable (SmG σ J) (InfinitePlace F)
    (fun w => Algebra.adjoin ℂ (Set.range (gelfA (X w)))) (fun w w' hne a ha b hb => by
      have h1 : ∀ c d, a * X w' c d = X w' c d * a := fun c d => by
        have : Algebra.adjoin ℂ (Set.range (gelfA (X w))) ≤ Subalgebra.centralizer ℂ {X w' c d} := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨k, rfl⟩
          exact gelfA_mem _ _ (fun a b => by rintro _ rfl; exact (hc w w' hne a b c d).symm) k
        exact (this ha _ rfl).symm
      have : Algebra.adjoin ℂ (Set.range (gelfA (X w'))) ≤ Subalgebra.centralizer ℂ {a} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨k, rfl⟩
        exact gelfA_mem _ _ (fun c d => by rintro _ rfl; exact h1 c d) k
      exact this hb _ rfl) v hv
  let A := Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × Fin n × Fin n => X p.1 p.2.1 p.2.2)
  have hDA : ∀ w Z, D w Z ∈ A := fun w Z => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum]
    refine A.sum_mem fun a _ => A.sum_mem fun b _ => ?_
    rw [← mul_one (Z a b), ← smul_eq_mul, ← Matrix.smul_single, map_smul]
    exact A.smul_mem (Algebra.subset_adjoin ⟨(w, a, b), rfl⟩) _
  have hword : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ u ∈ A, ∀ f : SmG σ J, l.foldr lineDer f.1 = (u f).1 := fun l => by
    induction l with
    | nil => exact fun _ => ⟨1, A.one_mem, fun f => rfl⟩
    | cons γ l ih =>
      intro hl
      obtain ⟨u, hu, e⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      obtain ⟨w, Z, hZ⟩ := GlobalTheory.T.real_line_is_line_of_place F E σ h n J hJ τ γ (hl γ List.mem_cons_self)
      exact ⟨D w Z * u, A.mul_mem (hDA w Z) hu, fun f => by
        rw [List.foldr_cons, e, Module.End.mul_apply, (hD w).2 Z γ hZ]⟩
  refine Submodule.finiteDimensional_of_le (S₂ := W.map (SmG σ J).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  choose! u hu he using fun l (hl : l ∈ z.support) => hword l (hz.1 l hl)
  let U := ∑ l ∈ z.support, z l • u l
  have hU : ∀ f : SmG σ J, dop z f.1 = (U f).1 := fun f => by
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    funext g
    simp only [dop, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← he l hl]
  have hline : ∀ w Z γ, IsLineOf σ J (τ w) Z γ → D w Z * U = U * D w Z := fun w Z γ hγ =>
    LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, Module.End.mul_apply, (hD w).2 Z γ hγ, ← hU, ← hU, (hD w).2 Z γ hγ]
      exact GlobalTheory.UAut.CentralComm.lineDer_dop_comm F E σ n J z hz f.1 f.2 γ (hγ.isRealLine h))
  have hmem := GlobalTheory.T.centre_generated_by_gelfand GlobalTheory.T.relativeCentre' _ _ n X hG hc U (A.sum_mem fun l hl => A.smul_mem (hu l hl) _) fun w a b => by
    obtain ⟨γ₁, γ₂, h1, h2, e⟩ := exists_lines h hJ (τ w) (Matrix.single a b 1)
    change D w _ * U = U * D w _
    rw [e, map_add, map_smul (D w) Complex.I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hline w _ _ h1,
      hline w _ _ h2]
  have key : ∀ a ∈ Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × ℕ => gelfA (X p.1) p.2), ∀ x ∈ W, a x ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hs p.1 _ (Algebra.subset_adjoin ⟨p.2, rfl⟩)
    | algebraMap r => intro x hx; exact W.smul_mem r hx
    | add x y _ _ hx hy => intro f hf; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; exact hx _ (hy f hf)
  exact ⟨U v, key U hmem v hvW, (hU v).symm⟩

end General

theorem frame_unit_apply {n m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hRQ : R * Q = 1)
    (p q : Fin m) : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = Matrix.single p q 1 := by
  have : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = R * Q * Matrix.single p q (1 : ℂ) * (R * Q) := by
    simp only [Matrix.mul_assoc]
  rw [this, hRQ, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.LeviHC

end
