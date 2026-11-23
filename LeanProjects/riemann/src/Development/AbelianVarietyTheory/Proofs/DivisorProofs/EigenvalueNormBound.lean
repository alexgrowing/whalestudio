import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueIntegralNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonEigenvectorRhoAdjoinRootEmbeddingStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.StabFin

theorem norm_le_one_at_u : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw a ha τ hτ
  obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
  set τ' : FM P →+* PadicAlgCl p := ((σ.symm : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp τ with hτ'
  have hτ'F : τ'.comp (algebraMap G.F (FM P)) = G.emb i := by
    rw [hτ', RingHom.comp_assoc, hσ]
    ext x; simp
  have hnorm : ‖τ a‖ = ‖τ' a‖ := by
    have : τ a = σ (τ' a) := by simp [hτ']
    rw [this]; exact (spectralNorm_eq_of_equiv σ _).symm
  rw [hnorm]
  obtain ⟨m, hm0, hm⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  obtain ⟨k, hk, hkeq⟩ := hm
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding p G P i τ' hτ'F
  have hjm : jM P (a ^ m) = (((w ^ m : P.cent) : G.Cˣ × ℚˣ).1 : G.C) := by
    rw [map_pow, ha]; rfl
  have key : (z * g) * k * (z * g)⁻¹ = inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) := by
    have e : P.toQr r z (w ^ m) = z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z := rfl
    rw [map_pow] at e
    rw [← hkeq] at e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have e2 : inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) =
        z * (z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z) * z⁻¹ := by group
    rw [e2, ← e]
    group
  have hcomp := congrArg (fun x : Gr G r => ((x.2 i : GL (Fin G.n) (KQ p (G.Fw i) r)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r))) key
  have hk' : k.2 i ∈ Kres p (G.Fw i) G.n r := hk.2 i (Set.mem_univ _)
  have hb := GlobalTheory.T.eigenvalue_integral_norm_bound p (G.Fw i) G.n r (G.rho i (jM P (a ^ m))) ((z * g).2 i) (k.2 i) hk'
    (by rw [hjm]; exact hcomp.symm) v (τ' (a ^ m)) hv0 (hv _)
  rw [map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hb

end GlobalTheory.StabFin
