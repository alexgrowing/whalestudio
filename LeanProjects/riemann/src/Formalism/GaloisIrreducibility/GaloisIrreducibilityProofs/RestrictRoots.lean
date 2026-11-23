import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open Module Polynomial

section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma rr_charpoly_compl (φ : Module.End K V) (P Q : Submodule K V) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by
  have hconj : (Submodule.prodEquivOfIsCompl P Q hPQ).symm.conj φ = (φ.restrict hP).prodMap (φ.restrict hQ) := by
    apply LinearMap.ext
    rintro ⟨p, q⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [map_add φ, ← LinearMap.restrict_coe_apply φ hP p, ← LinearMap.restrict_coe_apply φ hQ q,
      map_add, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp
  rw [← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl P Q hPQ).symm φ, hconj, LinearMap.charpoly_prodMap]

lemma rr_roots_of_nilp (B : Module.End K V) (c : K) (h : IsNilpotent (B - c • 1)) :
    B.charpoly.roots = Multiset.replicate (finrank K V) c := by
  have h1 := (LinearMap.isNilpotent_iff_charpoly _).mp h
  rw [LinearMap.charpoly_sub_smul] at h1
  have h2 : B.charpoly = (Polynomial.X - Polynomial.C c) ^ finrank K V := by
    have h3 := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C c)) h1
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, Polynomial.pow_comp] at h3
    exact h3
  rw [h2, Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]

end SlopeTestRemainingChoices

lemma rr_nilp_pow {R : Type} [Ring R] {K : Type} [Field K] [Algebra K R] (a : R) (c : K)
    (h : IsNilpotent (a - algebraMap K R c)) (q : ℕ) :
    IsNilpotent (a ^ q - algebraMap K R (c ^ q)) := by
  have hc : Commute a (algebraMap K R c) := (Algebra.commutes c a).symm
  rw [map_pow, ← hc.geom_sum₂_mul]
  refine Commute.isNilpotent_mul_left ?_ h
  refine Commute.sum_left _ _ _ fun i _ => ?_
  exact (((Commute.refl a).sub_right hc).pow_left i).mul_left
    ((hc.symm.sub_right (Commute.refl _)).pow_left _)

private lemma coe_restrict_pow_apply' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (k : ℕ) (x : S) :
    (((A.restrict hS) ^ k) x : V) = (A ^ k) x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.restrict_coe_apply, ihk]

lemma rr_roots_pow {K : Type} [Field K] [IsAlgClosed K] (q : ℕ) : ∀ (n : ℕ) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    finrank K V = n → ∀ (A : Module.End K V),
      (A ^ q).charpoly.roots = A.charpoly.roots.map (· ^ q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn A
  have hinv : ∀ (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (hSq : ∀ x ∈ S, (A ^ q) x ∈ S),
      (A ^ q).restrict hSq = (A.restrict hS) ^ q := by
    intro S hS hSq
    ext x
    rw [LinearMap.restrict_coe_apply, coe_restrict_pow_apply']
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    have hnil : ∀ B : Module.End K V, B.charpoly = 1 := by
      intro B
      have hB : IsNilpotent B := ⟨1, LinearMap.ext fun x => Subsingleton.elim _ _⟩
      rw [(LinearMap.isNilpotent_iff_charpoly B).mp hB, hn, hn0, pow_zero]
    simp [hnil]
  · haveI : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
    obtain ⟨f, hf⟩ : ∃ f : Module.End K V, f = A - μ • 1 := ⟨_, rfl⟩
    obtain ⟨N0, hN0⟩ :=
      Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
    have hPQ := hN0 (N0 + 1) (Nat.le_succ _)

    have hcomm : ∀ g : Module.End K V, Commute g f →
        (∀ x ∈ LinearMap.ker (f ^ (N0 + 1)), g x ∈ LinearMap.ker (f ^ (N0 + 1))) ∧ (∀ x ∈ LinearMap.range (f ^ (N0 + 1)), g x ∈ LinearMap.range (f ^ (N0 + 1))) := by
      intro g hg
      have hgN := (hg.pow_right (N0 + 1)).eq
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [LinearMap.mem_ker] at hx ⊢
        rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply, hx, map_zero]
      · obtain ⟨y, rfl⟩ := hx
        exact ⟨g y, by rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply]⟩
    have hAf : Commute A f := by
      rw [hf]
      exact (Commute.refl A).sub_right ((Commute.one_right A).smul_right μ)
    obtain ⟨hP, hQ⟩ := hcomm A hAf
    obtain ⟨hPq, hQq⟩ := hcomm (A ^ q) (hAf.pow_left q)
    by_cases hQb : LinearMap.range (f ^ (N0 + 1)) = ⊥
    ·
      have hPt : LinearMap.ker (f ^ (N0 + 1)) = ⊤ := by
        have h := hPQ.sup_eq_top
        rwa [hQb, sup_bot_eq] at h
      have hnil : IsNilpotent f := ⟨N0 + 1, LinearMap.ker_eq_top.mp hPt⟩
      rw [hf] at hnil
      have hnilq : IsNilpotent (A ^ q - (μ ^ q) • 1) := by
        have h := rr_nilp_pow A μ (by rw [Algebra.algebraMap_eq_smul_one]; exact hnil) q
        rwa [Algebra.algebraMap_eq_smul_one] at h
      rw [rr_roots_of_nilp A μ hnil, rr_roots_of_nilp (A ^ q) (μ ^ q) hnilq, Multiset.map_replicate]
    ·
      have hPb : LinearMap.ker (f ^ (N0 + 1)) ≠ ⊥ := by
        intro hPb
        obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
        apply hv.2
        have hfv : f v = 0 := by
          rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
            hv.apply_eq_smul, sub_self]
        have hvP : v ∈ LinearMap.ker (f ^ (N0 + 1)) := by
          rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hfv, map_zero]
        rw [hPb] at hvP
        exact (Submodule.mem_bot K).mp hvP
      have hdim := Submodule.finrank_add_eq_of_isCompl hPQ
      have hP0 : finrank K (LinearMap.ker (f ^ (N0 + 1))) ≠ 0 := fun h => hPb (Submodule.finrank_eq_zero.mp h)
      have hQ0 : finrank K (LinearMap.range (f ^ (N0 + 1))) ≠ 0 := fun h => hQb (Submodule.finrank_eq_zero.mp h)
      have ihP := ih _ (by omega) (LinearMap.ker (f ^ (N0 + 1))) rfl (A.restrict hP)
      have ihQ := ih _ (by omega) (LinearMap.range (f ^ (N0 + 1))) rfl (A.restrict hQ)
      have hne : ∀ (S : Submodule K V) (B : Module.End K S), B.charpoly ≠ 0 :=
        fun S B => (LinearMap.charpoly_monic B).ne_zero
      rw [rr_charpoly_compl (A ^ q) _ _ hPQ hPq hQq, rr_charpoly_compl A _ _ hPQ hP hQ,
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        hinv _ hP hPq, hinv _ hQ hQq, ihP, ihQ, Multiset.map_add]

private lemma charpoly_restrict_dvd_charpoly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W) :
    (τ.restrict hτ).charpoly ∣ τ.charpoly := by
  classical
  obtain ⟨Q, hWQ⟩ := Submodule.exists_isCompl W
  obtain ⟨e, he⟩ : ∃ e : (W × Q) ≃ₗ[K] V, e = Submodule.prodEquivOfIsCompl W Q hWQ := ⟨_, rfl⟩
  have he1 : ∀ x : W, e.symm (x : V) = (x, 0) := fun x => by
    rw [he]; exact Submodule.prodEquivOfIsCompl_symm_apply_left W Q hWQ x
  have he2 : ∀ x : W, e (x, 0) = (x : V) := fun x => by
    rw [← he1 x, LinearEquiv.apply_symm_apply]
  have bW := Module.finBasis K W
  have bQ := Module.finBasis K Q
  have key : ∀ j, (e.symm.conj τ) ((bW.prod bQ) (Sum.inl j)) = ((τ.restrict hτ) (bW j), 0) := by
    intro j
    have hb : (bW.prod bQ) (Sum.inl j) = (bW j, 0) := by simp [Module.Basis.prod_apply]
    rw [hb, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, he2, ← LinearMap.restrict_coe_apply τ hτ, he1]
  have h21 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h11 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₁₁ =
      LinearMap.toMatrix bW bW (τ.restrict hτ) := by
    ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inl]
  rw [← LinearEquiv.charpoly_conj e.symm τ, ← LinearMap.charpoly_toMatrix (e.symm.conj τ) (bW.prod bQ),
    ← LinearMap.charpoly_toMatrix (τ.restrict hτ) bW,
    ← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)),
    h21, h11, Matrix.charpoly_fromBlocks_zero₂₁]
  exact dvd_mul_right _ _

theorem restrict_roots_to_subfield : RestrictRoots := by
  unfold RestrictRoots
  intro K V _ _ _ _ _ τ F q hF W hτ hFW
  have hFW' : ∀ v ∈ W, (F : V →ₗ[K] V) v ∈ W := hFW
  have hinj : Function.Injective ((F : V →ₗ[K] V).restrict hFW') := by
    intro x y hxy
    apply Subtype.ext
    apply F.injective
    have h := congrArg Subtype.val hxy
    simpa only [LinearMap.restrict_coe_apply, LinearEquiv.coe_coe] using h
  have hbij : Function.Bijective ((F : V →ₗ[K] V).restrict hFW') :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  obtain ⟨eW, heW⟩ : ∃ eW : W ≃ₗ[K] W, ∀ x, eW x = ((F : V →ₗ[K] V).restrict hFW') x :=
    ⟨LinearEquiv.ofBijective _ hbij, fun x => rfl⟩
  have hconj : eW.conj (τ.restrict hτ) = (τ.restrict hτ) ^ q := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eW.surjective x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only [heW, LinearMap.restrict_coe_apply, coe_restrict_pow_apply', LinearEquiv.coe_coe]
    exact hF y
  constructor
  · exact Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic τ).ne_zero
      (charpoly_restrict_dvd_charpoly τ W hτ)
  · have h1 := rr_roots_pow q (finrank K W) W rfl (τ.restrict hτ)
    rw [← hconj, LinearEquiv.charpoly_conj] at h1
    exact h1.symm

end Formalism.GaloisIrreducibility
