import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

open GlobalTheory.TopStep
open GlobalTheory.Mem.Col2.PtExist (mat)

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_dep_eq_exp (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : ∃ N : ℕ, dep P c = WithZero.exp (-(N : ℤ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, dep P c = WithZero.exp m := ⟨_, (WithZero.exp_log (dep_ne_zero c)).symm⟩
  have h1 : m ≤ 0 := by
    have := dep_le_one (P := P) c
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  refine ⟨(-m).toNat, ?_⟩
  rw [hm, Int.toNat_of_nonneg (by omega), neg_neg]

variable [StarRing E]

theorem sm_of_lqPrinc {P : HeightOneSpectrum (𝓞 E)} {N c : ℕ} (hd : dep P c = WithZero.exp (-(N : ℤ))) {g : Sp E n ≃ₗ[E] Sp E n}
    (h : lqPrinc P N g) : Sm Valued.v (dep P c) (ratM P g - 1) := by
  intro i j
  have e : (ratM P g - 1) i j = algebraMap E (P.adicCompletion E) ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) := by
    have e1 : mat g i j = LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) i j := by
      rw [LinearMap.toMatrix'_apply]
      rfl
    simp only [Matrix.sub_apply, map_sub, ratM, Matrix.map_apply, e1, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, valued_algebraMap, hd]
  exact h i j

end Loc

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TC

theorem levQ_top_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  intro B X I a
  choose N hN using fun P : I.Q a => exists_dep_eq_exp P.1 (topDep B.R (I.cst a).M + 1)
  refine ⟨N, fun P => (hN P).le, fun P g hg => ?_⟩
  have hk : g ∈ GlobalTheory.TopStep.prinCong (B.R.N B.R.m) P.1 (topDep B.R (I.cst a).M + 1) := mem_prinCong_of_sm g (sm_of_lqPrinc (hN P) hg)
  have e : (I.Tp a).levQ B.R.m = levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) := topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  rw [e]
  exact ⟨prinCong_le_levCong _ _ _ hk, levCong_lam_prinCong _ _ _ hk⟩

end GlobalTheory.Mem.Col2.TC

end
