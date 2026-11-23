import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem semilinear_matrix_comm {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] {r : ℕ}
    (σ τ : A →+* A) (f g : D →+ D) (hf : ∀ a x, f (a • x) = σ a • f x)
    (hg : ∀ a x, g (a • x) = τ a • g x) (hc : ∀ x, f (g x) = g (f x))
    (b : Fin r → D) (hb : LinearIndependent A b) (e : A) (P Q : Fin r → Fin r → A)
    (hQ : ∀ k, g (b k) = ∑ m, Q m k • b m) (hP : ∀ k, e • f (b k) = ∑ m, P m k • b m)
    (p k : Fin r) :
    e * ∑ m, Q p m * τ (P m k) = τ e * ∑ m, P p m * σ (Q m k) := by
  have h1 : τ e • g (f (b k)) = ∑ p, (∑ m, Q p m * τ (P m k)) • b p := by
    rw [← hg, hP, map_sum]
    simp only [hg, hQ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : e • f (g (b k)) = ∑ p, (∑ m, P p m * σ (Q m k)) • b p := by
    rw [hQ, map_sum, Finset.smul_sum]
    simp only [hf, smul_comm e, hP, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h3 : ∑ p, (e * ∑ m, Q p m * τ (P m k)) • b p
      = ∑ p, (τ e * ∑ m, P p m * σ (Q m k)) • b p := by
    simp only [mul_smul, ← Finset.smul_sum]
    rw [← h1, ← h2, hc, smul_comm]
  exact (Fintype.linearIndependent_iffₛ.1 hb) _ _ h3 p

theorem matrices_comm : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ (M : ℕ) (Φ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧), (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (Φ i m k) : LetA O n) • (b m : W.DD T)) → ∀ i, R.E ^ M • (Gm i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (Gm (i - 1)).map R.φ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ _ M Φ Gm hG hΦ i
  obtain ⟨hj, -, hφ, hγ, -⟩ := hF
  have hb : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key := semilinear_matrix_comm (A := LetA O n) (letφ (n := n) W.φ₀).toRingHom
    (letγ (n := n) (W.γ₀ W.gam)).toRingHom (W.φD T).toAddMonoidHom (W.γD T W.gam).toAddMonoidHom
    (fun a x => by
      change W.φD T (a • x) = letφ W.φ₀ a • W.φD T x
      rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul])
    (fun a x => by
      change W.γD T W.gam (a • x) = letγ (W.γ₀ W.gam) a • W.γD T W.gam x
      rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul])
    (fun x => W.φγ_comm T W.gam x) _ hb ((fun _ => j R.E : LetA O n) ^ M)
    (fun m k i => j (Φ i m k)) (fun m k i => j (Gm i m k)) hG hΦ
  ext1 p k
  apply hj
  have h := congrFun (key p k) i
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.pow_apply, map_pow] at h
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow,
    map_sum, hφ, hγ]
  exact h

end GlobalTheory.WachTie
