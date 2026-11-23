import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSymm

section Split

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def chernRootsOver : MvPolynomial (ι × ℕ) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R x.2)

variable {m} [DecidableEq ι] (τ₀ : ι)

def rootSplit : Root m ≃ Fin (m τ₀) ⊕ Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) :=
  GlobalTheory.InnerAutomorphism.sigmaSplit (fun τ => Fin (m τ)) τ₀

def splitEquiv : MvPolynomial (Root m) R ≃ₐ[R]
    MvPolynomial (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :=
  (renameEquiv R (rootSplit τ₀)).trans (sumAlgEquiv R _ _)

theorem splitEquiv_X_self (i : Fin (m τ₀)) :
    splitEquiv R τ₀ (X (⟨τ₀, i⟩ : Root m)) = X i := by
  have e : rootSplit τ₀ (⟨τ₀, i⟩ : Root m) = Sum.inl i := GlobalTheory.InnerAutomorphism.sigmaSplit_self (fun τ => Fin (m τ)) τ₀ i
  simp [splitEquiv, e]

theorem splitEquiv_X_ne {τ : ι} (h : τ ≠ τ₀) (i : Fin (m τ)) :
    splitEquiv R τ₀ (X (⟨τ, i⟩ : Root m)) = C (X ⟨⟨τ, h⟩, i⟩) := by
  have e : rootSplit τ₀ (⟨τ, i⟩ : Root m) = Sum.inr ⟨⟨τ, h⟩, i⟩ := GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne (fun τ => Fin (m τ)) h i
  simp [splitEquiv, e]

theorem splitEquiv_symm_X (i : Fin (m τ₀)) :
    (splitEquiv R τ₀).symm (X i) = X (⟨τ₀, i⟩ : Root m) := by
  rw [AlgEquiv.symm_apply_eq, splitEquiv_X_self]

theorem splitEquiv_symm_C (c : MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :
    (splitEquiv R τ₀).symm (C c) = rename (fun y => (⟨y.1.1, y.2⟩ : Root m)) c := by
  rw [AlgEquiv.symm_apply_eq]
  induction c using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C]
    change _ = splitEquiv R τ₀ (algebraMap R _ r)
    rw [AlgEquiv.commutes]; rfl
  | add p q hp hq => simp [map_add, ← hp, ← hq]
  | mul_X p y hp =>
    simp only [map_mul, rename_X]
    rw [← hp, splitEquiv_X_ne R τ₀ y.1.2]

theorem splitEquiv_symm_esymm (j : ℕ) :
    (splitEquiv R τ₀).symm (esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) j) =
      chernRootsOver R m (X (τ₀, j)) := by
  simp [chernRootsOver, esymm, map_sum, map_prod, splitEquiv_symm_X]

theorem splitEquiv_rename_update (σ : Equiv.Perm (Fin (m τ₀))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)) S) = rename σ (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)))) =
      ((rename σ).restrictScalars R).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, Function.update_of_ne h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem splitEquiv_rename_rest (w' : ∀ τ : {τ // τ ≠ τ₀}, Equiv.Perm (Fin (m τ.1))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)) S) =
      MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)))) =
      (mapAlgHom (rename (Equiv.sigmaCongrRight w'))).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem rename_chernRootsOver (T : MvPolynomial ({τ // τ ≠ τ₀} × ℕ) R) :
    rename (fun y : Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) => (⟨y.1.1, y.2⟩ : Root m))
      (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1) T) =
      chernRootsOver R m (rename (Prod.map Subtype.val id) T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [chernRootsOver]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    congr 1
    simp [chernRootsOver, rename_rename]
    rfl

end Split

theorem mem_range_chernRootsOver (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ) (S : MvPolynomial (Root m) R),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    S ∈ (chernRootsOver R m).range := by
  induction n with
  | zero =>
    intro ι _ _ hc R _ m S _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [eq_C_of_isEmpty S]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro ι _ _ hc R _ m S hS
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    let f : Fin (m τ₀) → MvPolynomial (Fin (m τ₀)) R' := fun i => esymm (Fin (m τ₀)) R' (↑i + 1)
    have hsym : splitEquiv R τ₀ S ∈ symmetricSubalgebra (Fin (m τ₀)) R' := by
      rw [mem_symmetricSubalgebra]
      intro σ
      rw [← splitEquiv_rename_update, hS]
    obtain ⟨T, hT⟩ := esymmAlgHom_fin_surjective R' (m := m τ₀) (n := m τ₀) le_rfl ⟨_, hsym⟩
    have hT' : aeval f T = splitEquiv R τ₀ S := by
      rw [← esymmAlgHom_apply, hT]
    have hcoef : ∀ d, coeff d T ∈ (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1)).range := by
      intro d
      apply ih _ hc' R
      intro w'
      have hinv : MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom T = T := by
        apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
        apply Subtype.ext
        rw [esymmAlgHom_apply, esymmAlgHom_apply]
        change aeval f _ = aeval f T
        rw [hT', ← hS (fun τ => if h : τ = τ₀ then 1 else w' ⟨τ, h⟩), splitEquiv_rename_rest, ← hT',
          aeval_def, aeval_def, algebraMap_eq, eval₂_map, eval₂_comp_left, map_comp_C]
        congr 1
        funext i
        exact (map_esymm _ _ _ _).symm
      have := congrArg (coeff d) hinv
      rwa [coeff_map] at this
    let k : MvPolynomial (Fin (m τ₀)) R' →+* MvPolynomial (Root m) R :=
      (splitEquiv R τ₀).symm.toRingEquiv.toRingHom
    have hSE : S = k (eval₂ C f T) := by
      change S = (splitEquiv R τ₀).symm _
      rw [← algebraMap_eq, ← aeval_def, hT', AlgEquiv.symm_apply_apply]
    have key : k (eval₂ C f T) = eval₂ (k.comp C) (k ∘ f) T := eval₂_comp_left k C f T
    rw [hSE, key, eval₂_eq]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · obtain ⟨Tc, hTc⟩ := (AlgHom.mem_range _).mp (hcoef d)
      rw [RingHom.comp_apply, ← hTc]
      change (splitEquiv R τ₀).symm (C _) ∈ _
      rw [splitEquiv_symm_C, rename_chernRootsOver]
      exact AlgHom.mem_range_self _ _
    · change (splitEquiv R τ₀).symm (esymm _ _ _) ∈ _
      rw [splitEquiv_symm_esymm]
      exact AlgHom.mem_range_self _ _

theorem exists_chernRoots_eq_of_blockSymmetric : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  intro ι _ m S hS
  classical
  obtain ⟨R, hR⟩ := (AlgHom.mem_range _).mp (mem_range_chernRootsOver _ ι rfl ℝ m S hS)
  exact ⟨R, hR⟩

end GlobalTheory.BlockSymm
