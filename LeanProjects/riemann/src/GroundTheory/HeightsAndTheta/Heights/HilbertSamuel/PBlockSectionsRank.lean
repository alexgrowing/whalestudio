import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockSectionsRank

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

def blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : (Σ k, ι k) → MvPolynomial (Ix (Fin r)) ℤ :=
  fun p => if h : p.1 = k₀ then ∑ j, C (N (h ▸ p.2) j) * X j else 0

theorem blockSubst_block (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (i : ι k₀) :
    blockSubst k₀ N ⟨k₀, i⟩ = ∑ j, C (N i j) * X j := by
  simp [blockSubst]

theorem isHomogeneous_blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (p : Σ k, ι k) :
    (blockSubst k₀ N p).IsHomogeneous 1 := by
  unfold blockSubst
  split_ifs
  · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℤ j).C_mul _
  · exact isHomogeneous_zero _ _ _

def fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : MRing ι →ₐ[ℤ] MvPolynomial (Ix (Fin r)) ℤ :=
  bind₁ (blockSubst k₀ N)

def blockLin (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) : Ix (Fin r) → MRing ι :=
  fun j => ∑ i, C (M j i) * X ⟨k₀, i⟩

def back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) : MvPolynomial (Ix (Fin r)) ℤ →ₐ[ℤ] MRing ι :=
  bind₁ (blockLin k₀ M)

theorem fst_eq_of_mem_support {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    {c : (Σ k, ι k) →₀ ℕ} (hc : coeff c f ≠ 0) {p : Σ k, ι k} (hp : p ∈ c.support) : p.1 = k₀ := by
  by_contra hne
  have h := hf c (mem_support_iff.mpr hc) p.1
  rw [blockDeg, if_neg hne, Finset.sum_eq_zero_iff] at h
  exact (Finsupp.mem_support_iff.mp hp) (h p.2 (Finset.mem_univ _))

theorem isHomogeneous_of_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    f.IsHomogeneous n := by
  intro c hc
  have h := hf c (mem_support_iff.mpr hc)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  simp only [Pi.one_apply, smul_eq_mul, mul_one, h, blockDeg, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem isHomogeneous_fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) {f : MRing ι} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) : (fwd k₀ N f).IsHomogeneous n := by
  have := (isHomogeneous_of_blockDeg hf).aeval (blockSubst k₀ N) (isHomogeneous_blockSubst k₀ N)
  rw [one_mul, aeval_eq_bind₁] at this
  exact this

def wB : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_wB (c : (Σ k, ι k) →₀ ℕ) : Finsupp.weight wB c = fun k => ∑ i, c ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k (fun k' _ hk' => ?_) (by simp)]
  · simp [wB]
  · simp [wB, Ne.symm hk']

theorem isMultiHomog_iff_wB (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous wB f a := by
  constructor
  · intro h c hc
    rw [weight_wB]
    funext k
    exact h c (mem_support_iff.mpr hc) k
  · intro h c hc k
    have := h (mem_support_iff.mp hc)
    rw [weight_wB] at this
    exact congrFun this k

theorem isMultiHomog_back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) {g : MvPolynomial (Ix (Fin r)) ℤ} {n : ℕ}
    (hg : g.IsHomogeneous n) : IsMultiHomog (back k₀ M g) (blockDeg k₀ n) := by
  have hbf : ∀ j, IsWeightedHomogeneous wB (blockLin k₀ M j) (Pi.single k₀ 1) := fun j =>
    IsWeightedHomogeneous.sum _ _ _ fun i _ => (isWeightedHomogeneous_X ℤ wB (⟨k₀, i⟩ : Σ k, ι k)).C_mul _
  rw [isMultiHomog_iff_wB, show blockDeg k₀ n = n • Pi.single k₀ 1 by
    funext k; by_cases hk : k = k₀ <;> simp [blockDeg, hk]]
  rw [back, ← aeval_eq_bind₁, aeval_def]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [← zero_add (n • Pi.single k₀ 1)]
  apply IsWeightedHomogeneous.mul (by rw [MvPolynomial.algebraMap_eq]; exact isWeightedHomogeneous_C _ _)
  rw [Finsupp.mem_support_iff] at hd
  have hn : ∑ j ∈ d.support, d j = n := by
    have := hg hd
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  have hp := IsWeightedHomogeneous.prod d.support (fun j => blockLin k₀ M j ^ d j)
    (fun j => d j • Pi.single k₀ 1) fun j _ => (hbf j).pow (d j)
  rw [← Finset.sum_smul, hn] at hp
  exact hp

end Forms

section Values

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}
  {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix (Fin r)) (ι k₀) ℤ}
  {N : Matrix (ι k₀) (Ix (Fin r)) ℤ} {x : Ix (Fin r) → Ω}

theorem aeval_back (h : IsBlockImage y k₀ M N x) (g : MvPolynomial (Ix (Fin r)) ℤ) :
    aeval y (back k₀ M g) = aeval x g := by
  have hx : (fun j => aeval y (blockLin k₀ M j)) = x := funext fun j => by simp [blockLin, h.1 j]
  rw [back, aeval_bind₁, hx]

theorem aeval_fwd (h : IsBlockImage y k₀ M N x) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    aeval x (fwd k₀ N f) = aeval y f := by
  rw [fwd, aeval_bind₁, aeval_def, aeval_def]
  refine eval₂_congr _ _ _ fun {p} {c} hp hc => ?_
  obtain ⟨k, i⟩ := p
  have hk : k = k₀ := fst_eq_of_mem_support hf hc hp
  subst hk
  rw [blockSubst_block, h.2 i]
  simp

theorem secM_eq (h : IsBlockImage y k₀ M N x) (n : ℕ) :
    secM y (blockDeg k₀ n) = (sec ℤ x n).toAddSubgroup := by
  unfold secM
  congr 1
  have hset : {s | ∃ g : MRing ι, IsMultiHomog g (blockDeg k₀ n) ∧ aeval y g = s} =
      ((sec ℤ x n : Submodule ℤ Ω) : Set Ω) := by
    ext s
    simp only [Set.mem_ofPred_eq, sec, Submodule.map_coe, Set.mem_image, SetLike.mem_coe,
      mem_homogeneousSubmodule, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨fwd k₀ N g, isHomogeneous_fwd k₀ N hg, aeval_fwd h hg⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨back k₀ M g, isMultiHomog_back k₀ M hg, aeval_back h g⟩
  rw [hset, Submodule.span_eq]

end Values

theorem exists_blockBasis {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) :
    ∃ (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
      IsBlockImage y k₀ M N x ∧ LinearIndependent ℤ x := by
  set W : Submodule ℤ Ω := Submodule.span ℤ (Set.range fun i : ι k₀ => y ⟨k₀, i⟩) with hW
  have : Module.Finite ℤ W := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  set b := (Module.Free.chooseBasis ℤ W).reindex (Fintype.equivFin _) with hb
  have hc : ∀ j, ∃ c : ι k₀ → ℤ, ∑ i, c i • y ⟨k₀, i⟩ = (b j : Ω) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).2
  choose c hc using hc
  refine ⟨_, fun j i => c j.2 i, fun i j => b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2,
    fun j => (b j.2 : Ω), ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · show (b j.2 : Ω) = ∑ i, (c j.2 i : Ω) * y ⟨k₀, i⟩
    rw [← hc j.2]
    simp [zsmul_eq_mul]
  · have h2 := congrArg Subtype.val (b.sum_repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show y ⟨k₀, i⟩ = ∑ j : Ix (Fin _),
      ((b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2 : ℤ) : Ω) * (b j.2 : Ω)
    conv_lhs => rw [← h2]
    simp [Fintype.sum_sigma, zsmul_eq_mul]
  · have h1 := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    refine h1.comp (fun j : Ix (Fin _) => j.2) ?_
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, a'⟩ h
    cases h
    rfl

end BlockSectionsRank

open BlockSectionsRank in

theorem BlockSectionsRank.proof (hRank : RankOfSections.Statement) (hGF : GenericFibre.Statement)
    (hSR : SectionsRank.Statement) (hArith : BlockImageArith.Statement) (hDeg : BlockImageGenDeg.Statement) :
    BlockSectionsRank.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ hD hY hB
  obtain ⟨r, M, N, x, hx, hind⟩ := exists_blockBasis y k₀
  have hX : IsArithVar (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (D + 1) := hArith D K ι Ω y k₀ r M N x hY hB hx hind
  obtain ⟨hprime, hdim⟩ := hGF Ω (Fin r) x D hX
  obtain ⟨C, hC⟩ := hRank (Fin r) _ D hprime hdim
  have hdeg := hDeg D K ι Ω (Fin r) y k₀ M N x hY hB hx
  refine ⟨C, fun n => ?_⟩
  have hrank : (Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ) =
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Fin r))
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) := by
    rw [hSR Ω (Fin r) x n, secM_eq hx n]
    rfl
  have hpow : ((n : ℝ) + 1) ^ ((D : ℝ) - 1) = ((n : ℝ) + 1) ^ (D - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hD, Nat.cast_one]
  have hgd : (genDeg (mCoordIdeal y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) : ℝ) =
      (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) := by
    rw [← hdeg]
    unfold genDeg
    congr!
  have := hC n
  rw [hpow] at this
  rw [hrank, hgd]
  exact this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
