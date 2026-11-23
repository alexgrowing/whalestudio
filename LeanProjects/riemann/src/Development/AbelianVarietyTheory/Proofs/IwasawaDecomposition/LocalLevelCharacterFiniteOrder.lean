import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.ChainTwFin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem lamExp_of_princ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : ↥H, lam x ^ m = 1 := by
  set L : Subgroup ↥(GLint E n P) := lam.ker.map H.subtype with hL
  have hfin : Finite (↥(GLint E n P) ⧸ L) := tfFinite_of_princ P N hN L fun g hg =>
    ⟨⟨g, (hH g hg).choose⟩, (hH g hg).choose_spec, rfl⟩
  have hLi : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hrel := Subgroup.relIndex_mul_index hLH
  have hsub : L.subgroupOf H = lam.ker := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hki : lam.ker.index ≠ 0 := by
    intro h0
    apply hLi
    rw [← hrel, Subgroup.relIndex, hsub, h0, zero_mul]
  refine ⟨lam.ker.index, Nat.pos_of_ne_zero hki, fun x => ?_⟩
  have := Subgroup.pow_index_mem lam.ker x
  rw [MonoidHom.mem_ker, map_pow] at this
  exact this

theorem qbLoc_chr_exp {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) : ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  obtain ⟨N, hN, hH⟩ := hΘ P
  obtain ⟨m, hm, hx⟩ := lamExp_of_princ P.1 N hN (Θ P).H (Θ P).lam hH
  exact ⟨m, hm, fun k => hx _⟩

end GlobalTheory.Mem.Col2.ChEx
