import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem rho_jM_common_eigvec : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m)
    (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i →
    ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧
      ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  intro p _ G P i τ hτ
  let f : G.Fw i →+* PadicAlgCl p := algebraMap (G.Fw i) (PadicAlgCl p)
  have hf : (fun x : G.Fw i => (x : PadicAlgCl p)) = ⇑f := rfl
  have hfe : f.comp (G.embW i) = G.emb i := by
    ext x; rfl
  let ψ : G.C →+* Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) := f.mapMatrix.comp (G.rho i)
  have hψ : ∀ x, ψ x = (G.rho i x).map (fun x => (x : PadicAlgCl p)) := fun x => rfl
  set M := ψ (P.γ : G.C) with hM
  set lam := τ (AdjoinRoot.root P.pol) with hlam
  have hchar : M.charpoly = P.pol.map (G.emb i) := by
    rw [hM, hψ, hf, Matrix.charpoly_map, charpoly_rho_eq_map_pol, Polynomial.map_map, hfe]
  have heval : Polynomial.eval lam M.charpoly = 0 := by
    rw [hchar, Polynomial.eval_map, ← hτ, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, map_zero]
  rw [Matrix.eval_charpoly] at heval
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 heval
  have hMv : M *ᵥ v = lam • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  refine ⟨v, hv0, fun a => ?_⟩
  rw [← hψ]
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk]
  have key : ∀ g : Polynomial G.F, ψ (Polynomial.aeval (P.γ : G.C) g) *ᵥ v =
      τ (AdjoinRoot.mk P.pol g) • v := by
    intro g
    induction g using Polynomial.induction_on with
    | C c =>
      rw [Polynomial.aeval_C, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply τ, hτ]
      show (f.mapMatrix (G.rho i (algebraMap G.F G.C c))) *ᵥ v = _
      rw [G.rho_F]
      ext j
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map]
      exact Or.inl rfl
    | add g h hg hh =>
      rw [map_add, map_add, Matrix.add_mulVec, hg, hh, map_add, map_add, add_smul]
    | monomial k c hk =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← Matrix.mulVec_mulVec, Polynomial.aeval_X, ← hM, hMv,
        Matrix.mulVec_smul, hk, smul_smul]
      congr 1
      rw [map_mul (AdjoinRoot.mk P.pol) _ Polynomial.X, map_mul τ, AdjoinRoot.mk_X, mul_comm]
  exact key g

end GlobalTheory.StabFin
