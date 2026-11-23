import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section Transport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem bc_mem_range_intL_of (φ : K →+* K) (hφ : ∀ x ∈ intL K, φ x ∈ intL K) {n : ℕ}
    (x : GL (Fin n) K) (hx : x ∈ (bc (n := Fin n) (intL K).subtype).range) :
    bc (n := Fin n) φ x ∈ (bc (n := Fin n) (intL K).subtype).range := by
  obtain ⟨M, rfl⟩ := hx
  refine ⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩
  apply Units.ext
  ext i j
  simp [bc]

theorem guMap_symm_comp (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) {n : ℕ} (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [guMap_val]

theorem mem_KU_iff_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} (y : GU σ n) :
    y ∈ KU σ n ↔ guMap g hg n y ∈ KU σ' n := by
  have hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K := by
    intro x hx
    rw [hint]
    simpa using hx
  simp only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩
  · rintro ⟨-, h⟩
    refine ⟨y.2, ?_⟩
    have := bc_mem_range_intL_of (g.symm : K →+* K) hs _ h
    convert this using 1
    apply Units.ext
    ext i j
    simp [bc, guMap_val]

end Transport

open Classical in

theorem satU_guMap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : GU σ n ≃* GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have he : ∀ y, e y = guMap g hg n y := fun _ => rfl
  let E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      change a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n
      rw [← map_inv, ← map_mul, he]
      exact mem_KU_iff_guMap g hg hint _)
  unfold SatU
  refine finsum_congr (fun a => ?_)
  congr 1
  set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'
  have hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y := by
    intro y k
    simp only [hF']
    have hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔
        (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      constructor
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩
        have h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp [Matrix.mul_assoc]
        rw [h1, hy]
        simp [Matrix.mul_assoc]
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩
        simp only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]
    have hh : h' (y * k) = h' y := by
      have := hbi 1 k y
      simpa using this
    simp only [hc, hh]
  have hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out) := by
    intro x
    have hx : E x = QuotientGroup.mk (guMap g hg n x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)
    rw [hx, hk, hinv]
  calc (∑ᶠ x : GU σ n ⧸ KU σ n, if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((k : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        then h' (guMap g hg n x.out) else 0)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, F' (E x).out := by
        refine finsum_congr (fun x => ?_)
        rw [hmk, hF']
        simp only [hcond a x.out]
    _ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)

end GlobalTheory.SatInd
