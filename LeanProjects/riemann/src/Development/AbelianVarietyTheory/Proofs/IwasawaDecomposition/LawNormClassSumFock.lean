import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

theorem classSum_gram_posDef (s : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hpos : ∀ w, w ≠ 0 → 0 < B w w) (hsym : ∀ w w', star (B w w') = B w' w)
    (ψ : C.V → W) (hψ : ∀ x, ψ x = 0 → x = 0) (hs : ∀ x y, s (C.pair x y) = B (ψ x) (ψ y)) :
    (C.H.map s).PosDef := by
  classical
  have hnn : ∀ w, 0 ≤ B w w := fun w => by
    by_cases h : w = 0
    · simp [h]
    · exact (hpos w h).le
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℂ))⁻¹ := fun c => inv_pos.2 (by exact_mod_cast C.wt_pos c)
  have hc : ∀ f g : C.Cl → C.V, s (C.csum f g) = ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ (f c)) (ψ (g c)) := by
    intro f g
    simp only [CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, hs]
  have hsemi : (C.H.map s).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, star_sum, star_mul', hsym,
        star_inv₀, star_natCast]
    · intro x
      have e : star x ⬝ᵥ (C.H.map s) *ᵥ x = ∑ c, ((C.wt c : ℂ))⁻¹ *
          B (∑ i, x i • ψ ((C.basis i : C.Cl → C.V) c)) (∑ j, x j • ψ ((C.basis j : C.Cl → C.V) c)) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, map_sum, LinearMap.sum_apply,
          LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
          starRingEnd_apply, RingHom.id_apply]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)
  rw [hsemi.posDef_iff_det_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : C.csum (C.I v) (C.I v) = 0 := by
    rw [C.csum_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ j, C.H i j * v j = 0 := congrFun hv0 i
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, mul_zero]
  have h2 := hc (C.I v) (C.I v)
  rw [h1, map_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)] at h2
  apply hv
  apply C.I_injective
  rw [map_zero]
  funext c
  refine hψ _ ?_
  by_contra hne
  exact (mul_pos (hw c) (hpos _ hne)).ne' (h2 c (Finset.mem_univ c))

theorem majAt_stdFrame_classSum (v : InfinitePlace K) (hv : ∀ a, v.embedding (star a) = starRingEnd ℂ (v.embedding a))
    (hH : (C.H.map v.embedding).PosDef) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y = v.embedding (C.csum x.1 y.1) := by
  have hI : ∀ z : C.Forms, C.I (C.basis.equivFun z) = z.1 := fun z => by simp [CSD.I_apply]
  have h1 : Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin C.dim)) (stdFrame C.H) v (C.basis.equivFun x) (C.basis.equivFun y) := by
    have h2 : ∀ z : C.Forms, Formalism.HermitianLatticesTheory.vecAt C.basis v z =
        Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin C.dim)) v (C.basis.equivFun z) := by
      intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h2]
  have hm : metOf (stdFrame C.H v) = C.H.map v.embedding := (frameOfSpec _ _ hH).2
  rw [h1, majAt_eq, hm, ← hI x, ← hI y, C.csum_sum]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, hv, Finset.mul_sum, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

end ClassSum

section Pair

variable {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ}

theorem map_pairVr_one (emb : ι → E →+* K) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (hs : ∀ a, s (star a) = starRingEnd ℂ (s a)) (F F' : VV K lam) :
    s (pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) F F') = nfL lam (MvPolynomial.map s F.1) (MvPolynomial.map s F'.1) := by
  have h := pairVr_nfAll emb (1 : Matrix (Fin n) (Fin n) E) lam s (stdFrC (embAt s emb))
    (fun τ => by simp [stdFrC, gramC]) F F' (fun m => hs _)
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (stdFrC (n := n) (embAt s emb)).1 = AlgHom.id ℂ _ := blockAct_one
  rw [h, e, nfL_apply]
  simp [stdFrC]

end Pair

theorem GStep.lawNorm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h [Fintype S.Cl], S.LawNorm emb σ lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF _ h inst x
  have hv : ∀ a, (InfinitePlace.mk σ).embedding (star a) = starRingEnd ℂ ((InfinitePlace.mk σ).embedding a) := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e, hF.sig_star]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hF.sig_star]
  have hre : ∀ a, ((InfinitePlace.mk σ).embedding a).re = (σ a).re := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have hH : ((S.csd emb lam h).H.map (InfinitePlace.mk σ).embedding).PosDef :=
    classSum_gram_posDef (S.csd emb lam h) _ (nfL lam) (ps_nfL_pos lam) (ps_nfL_symm lam)
      (fun F : VV K lam => MvPolynomial.map (InfinitePlace.mk σ).embedding F.1)
      (fun F hF0 => Subtype.ext (MvPolynomial.map_injective _ (RingHom.injective _) (hF0.trans (map_zero _).symm)))
      (fun F F' => map_pairVr_one emb lam _ hv F F')
  have h1 := majAt_stdFrame_classSum (S.csd emb lam h) (InfinitePlace.mk σ) hv hH x x
  refine (congrArg Complex.re h1).trans ?_
  rw [hre]
  congr 1
  have hi : inst = (S.csd emb lam h).finCl := Subsingleton.elim _ _
  subst hi
  unfold CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have h2 : (S.csd emb lam h).wt c = Nat.card (S.Stab c) := (@Nat.card_eq_fintype_card _ (_)).symm
  rw [h2]
  congr 1
  exact (ipFr_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (fr0 emb σ n) (fun τ => by simp [fr0, stdFrC, gramC]) _ _
    (fun m => hF.sig_star _)).symm

end GlobalTheory.Mem.Col2
