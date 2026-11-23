import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem rhoT_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (t x : GL (Fin n) (AfE F E)) (hx : rhoP F P x = 1) : rhoT F P t x = 1 := by
  show rhoP F P (MulAut.conj t⁻¹ x) = 1
  rw [MulAut.conj_apply, map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem topChi_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  intro F E K _ _ _ _ _ _ _ n Q σ U t Θ d hd N hdN hΘ
  constructor
  · intro h
    choose m hm0 hm using h
    refine ⟨∏ P : Q, m P, Finset.prod_pos fun P _ => hm0 P, fun x => ?_⟩
    unfold topChi
    rw [MonoidHom.inv_apply, inv_pow, MonoidHom.finset_prod_apply, ← Finset.prod_pow, Finset.prod_eq_one, inv_one]
    intro P _
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ P)
    rw [hc, pow_mul, MonoidHom.comp_apply, ← map_pow, MonoidHom.comp_apply]
    have e : locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x) ^ m P = 1 :=
      hm P _
    rw [e, map_one, one_pow]
  · intro x hx
    unfold topChi
    rw [MonoidHom.inv_apply, MonoidHom.finset_prod_apply, Finset.prod_eq_one, inv_one]
    intro P _
    have e : ((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x = 1 :=
      Subtype.ext (rhoT_eq_one P.1 t x.1 (hx P))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_one, map_one]

end GlobalTheory.Mem.Col2.TopCh

end
