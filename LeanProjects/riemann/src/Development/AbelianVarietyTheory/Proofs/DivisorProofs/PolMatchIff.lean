import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

theorem I'_sum {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {ι : Type} (s : Finset ι) (Ψ : ι → (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hΨ : ∀ j ∈ s, Ψ j ∈ schA F (Fin a' × Fin (a + a'))) (hc : ∀ j ∈ s, G.M'.Conv om' (Ψ j)) (h : UA σ G.W.J) :
    G.M'.I om' (∑ j ∈ s, Ψ j) h = ∑ j ∈ s, G.M'.I om' (Ψ j) h := by
  have e : ∀ g, theta om' (∑ j ∈ s, Ψ j) g h = ∑ j ∈ s, theta om' (Ψ j) g h := by
    intro g
    simp only [theta, map_sum]
    have hm : ∀ j ∈ s, om' (g, h) (Ψ j) ∈ schA F (Fin a' × Fin (a + a')) :=
      fun j hj => hT.weil'.isUSplitting.pres _ _ (hΨ j hj)
    induction s using Finset.induction_on with
    | empty => simp [thetaSum]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        thetaSum_add F (hm k (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ fun j hj => hm j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hΨ j (Finset.mem_insert_of_mem hj)) (fun j hj => hc j (Finset.mem_insert_of_mem hj))
          (fun j hj => hm j (Finset.mem_insert_of_mem hj))]
  simp only [Model.I, e]
  exact integral_finset_sum s fun j hj => hc j hj h

end GlobalTheory.ThK.PolynomialMatching
