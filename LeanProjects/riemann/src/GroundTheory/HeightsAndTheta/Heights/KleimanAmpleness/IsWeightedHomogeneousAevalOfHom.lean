import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight gradedPiece hilbFn)

noncomputable section

section General

theorem isWeightedHomogeneous_aeval_of_hom {σ τ M M' R : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid M'] {w : σ → M} {w' : τ → M'} (L : M →+ M')
    (g : σ → MvPolynomial τ R) (hg : ∀ v, IsWeightedHomogeneous w' (g v) (L (w v)))
    {p : MvPolynomial σ R} {m : M} (hp : IsWeightedHomogeneous w p m) :
    IsWeightedHomogeneous w' (aeval g p) (L m) := by
  rw [p.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hdm : Finsupp.weight w d = m := hp (mem_support_iff.mp hd)
  rw [aeval_monomial, algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  have : L m = ∑ v ∈ d.support, d v • L (w v) := by
    rw [← hdm, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [this]
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hg v).pow _

theorem prod_X_pow_mul_C_pow {A σ : Type*} [CommRing A] (s : Finset σ) (t d : σ → ℕ) (b : σ → A)
    (a : A) :
    Polynomial.C a * ∏ x ∈ s, (Polynomial.X ^ t x * Polynomial.C (b x)) ^ d x =
      Polynomial.X ^ (∑ x ∈ s, d x * t x) *
        (Polynomial.C a * ∏ x ∈ s, Polynomial.C (b x) ^ d x) := by
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm (t _) (d _)]
  ring

end General

variable {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)

section Flat

variable (R : Type*) [CommRing R]

def segreFlatVal : (Σ k, segreIdx ι k) → MRing ι R
  | ⟨Sum.inl _, c⟩ => ∏ k, X ⟨k, c k⟩
  | ⟨Sum.inr k, i⟩ => X ⟨k, i⟩

def segreFlat : MRing (segreIdx ι) R →ₐ[R] MRing ι R :=
  aeval (segreFlatVal ι R)

def segreTDeg : (Σ k, segreIdx ι k) → ℕ
  | ⟨Sum.inl _, _⟩ => 1
  | ⟨Sum.inr _, _⟩ => 0

variable {ι R}

omit [Fintype K] in
theorem segreTDeg_eq (v : Σ k, segreIdx ι k) :
    segreTDeg ι v = blockWeight (segreIdx ι) v (Sum.inl ()) := by
  rcases v with ⟨_ | k, c⟩ <;> simp [segreTDeg, blockWeight]

omit [Fintype K] in
theorem weight_segreTDeg (d : (Σ k, segreIdx ι k) →₀ ℕ) :
    Finsupp.weight (segreTDeg ι) d = Finsupp.weight (blockWeight (segreIdx ι)) d (Sum.inl ()) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, segreTDeg_eq]

omit [DecidableEq K] in
theorem segreLiftVal_eq_X_pow_mul_C (W : Ideal (MRing ι R)) (v : Σ k, segreIdx ι k) :
    segreLiftVal ι R W v =
      Polynomial.X ^ segreTDeg ι v * Polynomial.C (Ideal.Quotient.mk W (segreFlatVal ι R v)) := by
  rcases v with ⟨_ | k, c⟩ <;> simp [segreLiftVal, segreTDeg, segreFlatVal]

omit [DecidableEq K] in
theorem segreLiftMap_monomial_eq_X_pow (W : Ideal (MRing ι R)) (d : (Σ k, segreIdx ι k) →₀ ℕ) (r : R) :
    segreLiftMap ι R W (monomial d r) = Polynomial.X ^ Finsupp.weight (segreTDeg ι) d *
      Polynomial.C (Ideal.Quotient.mk W (segreFlat ι R (monomial d r))) := by
  simp only [segreLiftMap, segreFlat, aeval_monomial, segreLiftVal_eq_X_pow_mul_C, Finsupp.prod,
    Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod, map_pow, smul_eq_mul,
    Polynomial.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  exact prod_X_pow_mul_C_pow _ _ _ _ _

omit [DecidableEq K] in

theorem segreLiftMap_of_homog (W : Ideal (MRing ι R)) {f : MRing (segreIdx ι) R} {m₀ : ℕ}
    (hf : IsWeightedHomogeneous (segreTDeg ι) f m₀) :
    segreLiftMap ι R W f =
      Polynomial.X ^ m₀ * Polynomial.C (Ideal.Quotient.mk W (segreFlat ι R f)) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [segreLiftMap_monomial_eq_X_pow, hf (mem_support_iff.mp hd)]

omit [Fintype K] in

theorem isWeightedHomogeneous_segreTDeg {f : MRing (segreIdx ι) R} {M : Unit ⊕ K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (segreIdx ι)) f M) :
    IsWeightedHomogeneous (segreTDeg ι) f (M (Sum.inl ())) := fun d hd => by
  rw [weight_segreTDeg, hf hd]

theorem mem_segreLift_iff (W : Ideal (MRing ι R)) {f : MRing (segreIdx ι) R} {M : Unit ⊕ K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (segreIdx ι)) f M) :
    f ∈ segreLift ι R W ↔ segreFlat ι R f ∈ W := by
  rw [segreLift, RingHom.mem_ker,
    segreLiftMap_of_homog W (isWeightedHomogeneous_segreTDeg hf), Polynomial.X_pow_mul,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.monomial_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

def segreDegMap : (Unit ⊕ K → ℕ) →+ (K → ℕ) where
  toFun M k := M (Sum.inr k) + M (Sum.inl ())
  map_zero' := by funext k; simp
  map_add' M N := by funext k; simp only [Pi.add_apply]; ring

theorem isWeightedHomogeneous_segreFlat {f : MRing (segreIdx ι) R} {M : Unit ⊕ K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight (segreIdx ι)) f M) :
    IsWeightedHomogeneous (blockWeight ι) (segreFlat ι R f) (segreDegMap M) := by
  refine isWeightedHomogeneous_aeval_of_hom segreDegMap _ (fun v => ?_) hf
  rcases v with ⟨_ | k, c⟩
  · have : segreDegMap (blockWeight (segreIdx ι) ⟨Sum.inl (), c⟩) = ∑ k, blockWeight ι ⟨k, c k⟩ := by
      funext k'
      simp [segreDegMap, blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact IsWeightedHomogeneous.prod _ _ _ fun k _ => isWeightedHomogeneous_X _ _ _
  · have : segreDegMap (blockWeight (segreIdx ι) ⟨Sum.inr k, c⟩) = blockWeight ι ⟨k, c⟩ := by
      funext k'
      simp [segreDegMap, blockWeight, Pi.single_apply]
    rw [this]
    exact isWeightedHomogeneous_X _ _ _

omit [DecidableEq K] in

theorem segreFlat_segreIncl (p : MRing ι R) : segreFlat ι R (segreIncl ι R p) = p := by
  have : (segreFlatVal ι R ∘ fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)) = X := by
    funext v; rfl
  rw [segreFlat, segreIncl, aeval_rename, this, aeval_X_left_apply]

omit [Fintype K] in

theorem isWeightedHomogeneous_segreIncl {p : MRing ι R} {m : K → ℕ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p m) :
    IsWeightedHomogeneous (blockWeight (segreIdx ι)) (segreIncl ι R p) (Sum.elim (fun _ => 0) m) := by
  let L : (K → ℕ) →+ (Unit ⊕ K → ℕ) :=
    { toFun := fun m => Sum.elim (fun _ => 0) m
      map_zero' := by funext j; rcases j with _ | k <;> rfl
      map_add' := fun a b => by funext j; rcases j with _ | k <;> simp }
  have key : ∀ v : Σ k, ι k, IsWeightedHomogeneous (blockWeight (segreIdx ι))
      (X (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k) : MRing (segreIdx ι) R) (L (blockWeight ι v)) := by
    intro v
    have : L (blockWeight ι v) = blockWeight (segreIdx ι) ⟨Sum.inr v.1, v.2⟩ := by
      funext j
      rcases j with _ | k <;> simp [L, blockWeight, Pi.single_apply]
    rw [this]
    exact isWeightedHomogeneous_X _ _ _
  have hI : segreIncl ι R p = aeval (fun v : Σ k, ι k =>
      (X (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k) : MRing (segreIdx ι) R)) p := by
    rw [segreIncl, ← aeval_X_left_apply (rename _ p), aeval_rename]
    rfl
  rw [hI]
  exact isWeightedHomogeneous_aeval_of_hom L _ key hp

theorem exists_segreFlat_eq_monomial (m₀ : ℕ) : ∀ (m : K → ℕ) (e : (Σ k, ι k) →₀ ℕ),
    Finsupp.weight (blockWeight ι) e = m + (fun _ => m₀) →
    ∃ g : MRing (segreIdx ι) R,
      IsWeightedHomogeneous (blockWeight (segreIdx ι)) g (Sum.elim (fun _ => m₀) m) ∧
      segreFlat ι R g = monomial e 1 := by
  induction m₀ with
  | zero =>
    intro m e he
    refine ⟨segreIncl ι R (monomial e 1), isWeightedHomogeneous_segreIncl ?_,
      segreFlat_segreIncl _⟩
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [he]; funext k; simp)
  | succ m₀ ih =>
    intro m e he
    classical
    have hk : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := by
      intro k
      have h1 : Finsupp.weight (blockWeight ι) e k ≠ 0 := by rw [he]; simp
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
      obtain ⟨⟨k', i⟩, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      simp only [Pi.smul_apply, blockWeight, Pi.single_apply, smul_eq_mul] at hne
      split_ifs at hne with hkk
      · subst hkk
        exact ⟨i, by simpa using hne⟩
      · simp at hne
    choose c hc using hk
    set s : (Σ k, ι k) →₀ ℕ := ∑ k, Finsupp.single ⟨k, c k⟩ 1 with hs
    have hse : s ≤ e := by
      intro v
      obtain ⟨k', i⟩ := v
      rw [hs, Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single k']
      · rw [Finsupp.single_apply]
        split_ifs with h
        · rw [← h]
          exact Nat.one_le_iff_ne_zero.mpr (hc k')
        · exact Nat.zero_le _
      · intro k _ hk
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hk (congrArg Sigma.fst h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hws : Finsupp.weight (blockWeight ι) s = fun _ => 1 := by
      funext k'
      rw [hs, map_sum, Finset.sum_apply]
      simp [Finsupp.weight_single, blockWeight, Pi.single_apply]
    have he' : Finsupp.weight (blockWeight ι) (e - s) = m + fun _ => m₀ := by
      have h2 := congrArg (Finsupp.weight (blockWeight ι)) (tsub_add_cancel_of_le hse)
      rw [map_add, he, hws] at h2
      funext k
      have := congrFun h2 k
      simp only [Pi.add_apply] at this ⊢
      omega
    obtain ⟨g, hg, hge⟩ := ih m (e - s) he'
    refine ⟨segreY c * g, ?_, ?_⟩
    · have hd : Sum.elim (fun _ => m₀ + 1) m =
          blockWeight (segreIdx ι) ⟨Sum.inl (), c⟩ + Sum.elim (fun _ => m₀) m := by
        funext j
        rcases j with _ | k <;> simp [blockWeight, add_comm]
      rw [hd]
      exact (isWeightedHomogeneous_X R (blockWeight (segreIdx ι)) _).mul hg
    · have hX : segreFlat ι R (segreY c) = monomial s 1 := by
        rw [segreY, segreFlat, aeval_X, hs, monomial_sum_one]
        rfl
      rw [map_mul, hge, hX, monomial_mul, one_mul, add_tsub_cancel_of_le hse]

end Flat

section Field

variable (F : Type*) [Field F]

variable {ι}

theorem map_segreFlat_homog (m₀ : ℕ) (m : K → ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (segreIdx ι)) (Sum.elim (fun _ => m₀) m)).map
        (segreFlat ι F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (m + fun _ => m₀) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have hd : m + (fun _ => m₀) = segreDegMap (Sum.elim (fun _ => m₀) m) := by
      funext k
      simp [segreDegMap]
    rw [mem_weightedHomogeneousSubmodule, hd]
    exact isWeightedHomogeneous_segreFlat hg
  · intro f hf
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    obtain ⟨g, hg, hge⟩ := exists_segreFlat_eq_monomial (R := F) m₀ m e (hf (mem_support_iff.mp he))
    refine ⟨coeff e f • g, Submodule.smul_mem _ _ hg, ?_⟩
    simp [hge, smul_monomial]

theorem finrank_gradedPiece_segreLift (W : Ideal (MRing ι F)) (m₀ : ℕ) (m : K → ℕ) :
    Module.finrank F (gradedPiece (segreLift ι F W) (Sum.elim (fun _ => m₀) m)) =
      Module.finrank F (gradedPiece W (m + fun _ => m₀)) := by
  set H := weightedHomogeneousSubmodule F (blockWeight (segreIdx ι)) (Sum.elim (fun _ => m₀) m)
  let L₁ := (Ideal.Quotient.mkₐ F (segreLift ι F W)).toLinearMap ∘ₗ H.subtype
  let L₂ := (Ideal.Quotient.mkₐ F W).toLinearMap ∘ₗ (segreFlat ι F).toLinearMap ∘ₗ H.subtype
  have h₁ : LinearMap.range L₁ = gradedPiece (segreLift ι F W) (Sum.elim (fun _ => m₀) m) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have h₂ : LinearMap.range L₂ = gradedPiece W (m + fun _ => m₀) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype, map_segreFlat_homog]
    rfl
  have hk : LinearMap.ker L₁ = LinearMap.ker L₂ := by
    ext ⟨g, hg⟩
    simp only [LinearMap.mem_ker, L₁, L₂, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_segreLift_iff W hg
  rw [← h₁, ← h₂]
  exact ((L₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    L₂.quotKerEquivRange).finrank_eq

theorem hilbFn_segreLift (W : Ideal (MRing ι F)) (M : Unit ⊕ K → ℤ) (hM : ∀ j, 0 ≤ M j) :
    hilbFn (segreLift ι F W) M = hilbFn W (fun k => M (Sum.inr k) + M (Sum.inl ())) := by
  have h1 : (fun j => (M j).toNat) =
      Sum.elim (fun _ => (M (Sum.inl ())).toNat) (fun k => (M (Sum.inr k)).toNat) := by
    funext j
    rcases j with _ | k <;> rfl
  have h2 : (fun k => (M (Sum.inr k) + M (Sum.inl ())).toNat) =
      (fun k => (M (Sum.inr k)).toNat) + fun _ => (M (Sum.inl ())).toNat := by
    funext k
    exact Int.toNat_add (hM _) (hM _)
  unfold hilbFn
  rw [if_pos hM, if_pos (fun k => add_nonneg (hM _) (hM _)), h1, h2, finrank_gradedPiece_segreLift]

end Field

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
