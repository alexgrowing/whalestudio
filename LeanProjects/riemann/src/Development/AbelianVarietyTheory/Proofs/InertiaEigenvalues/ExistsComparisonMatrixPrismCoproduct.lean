import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrixStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_toDisc_eq_of_dvd {l : ℕ} {A : Type} [CommRing A] (u : A) (r : ℝ≥0) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε)
    (h : ∀ j : n × n, ((l : ℕ) : A) ^ k ∣ x j.1 j.2) : ∃ y : Matrix n n A, y.map (toDisc l u r) = ε := by
  choose y hy using h
  refine ⟨Matrix.of fun i j => y (i, j), ?_⟩
  ext i j
  have e := congrFun (congrFun hx i) j
  have e2 : x i j = _ := hy (i, j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, e2, map_mul, map_pow, map_natCast] at e
  exact ((isUnit_l_disc l _ _).pow k).mul_left_cancel e

theorem IsDiscMap.map_eq_smul {l : ℕ} {A A' : Type} [CommRing A] [CommRing A'] {u : A} {u' : A'} {r r' : ℝ≥0}
    {f : A →+* A'} {F : Disc l u r →+* Disc l u' r'} (hF : IsDiscMap f F) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε) :
    (x.map f).map (toDisc l u' r') = ((l : ℕ) : Disc l u' r') ^ k • ε.map F := by
  ext i j
  have e := congrArg F (congrFun (congrFun hx i) j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast] at e ⊢
  rw [← e, hF.ext]

theorem map_mul_map_eq_smul_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (A A' : Matrix (Fin d) (Fin d) R) (e : R) (b : ℕ) (h : A * A' = e ^ b • (1 : Matrix (Fin d) (Fin d) R)) :
    A.map f * A'.map f = f e ^ b • (1 : Matrix (Fin d) (Fin d) S) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem Height.dvd_at_section (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (B : Obj l ↥(OL K)) (f f' : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)) (hε : ht.Rel (BK.hf f X) f f' ε) (k : ℕ)
    (x : Matrix (Fin d) (Fin d) B.A)
    (hx : x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε)
    (g : ↥(GK K)) (σ : Hom B (ainfObj K)) (h1 : σ.comp f = bk.ι) (h2 : σ.comp f' = (ainfHom K g).comp bk.ι)
    (j : Fin d × Fin d) : ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j.1 j.2) := by
  obtain ⟨⟨F, hF⟩, hrel⟩ := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht B (ainfObj K) f f f' bk.ι σ ε hε
  have hr := hrel F hF
  rw [h1, h2] at hr
  exact GlobalTheory.T.pow_dvd_galoisComparison_matrix l K bk d ρ τ s ht hτ hρ g (ε.map F) hr k (x.map σ.f) (hF.map_eq_smul k x ε hx) j.1 j.2

theorem matrix_phi_eq_entries {R : Type} [CommRing R] (φ : R →+* R) (e e' : R) (he : Associated e e') (d a b : ℕ)
    (P Q Q' : Matrix (Fin d) (Fin d) R) (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R))
    (x : Matrix (Fin d) (Fin d) R) (hx : e' ^ a • (P * x.map φ) = e ^ a • (x * Q)) :
    ∃ (h : ℕ) (c : Fin d × Fin d → Fin d × Fin d → R),
      ∀ j : Fin d × Fin d, e ^ h * x j.1 j.2 = ∑ i : Fin d × Fin d, φ (x i.1 i.2) * c i j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation R R (RingHom.id R) φ e e' he d d a a b P Q Q' hQ x hx

theorem Height.exists_rel_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) :
    ∃ ε : Matrix (Fin d) (Fin d) En.Q.A,
      ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  have tb : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have h₁ := GlobalTheory.T.comparisonMatrix_exists_on_disc l K bk d ρ τ s ht En.Q (BK.hf En.inl X) En.inl En.inr
  obtain ⟨εD, hεD⟩ := h₁
  have h₂ := GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb εD hεD
  obtain ⟨k, x, hx⟩ := h₂
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb k x εD hεD hx
  have h₃ := matrix_phi_eq_entries En.Q.D.φ (BK.hf En.inl bk.E) (BK.hf En.inr bk.E)
    (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1 d (ht.a + s.N) ht.b (ht.A.map (BK.hf En.inl))
    (ht.A.map (BK.hf En.inr)) (ht.A'.map (BK.hf En.inr))
    (map_mul_map_eq_smul_one (BK.hf En.inr) _ _ _ _ ht.A_mul) x hφ
  obtain ⟨h, c, hc⟩ := h₃
  have hdiv := GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d × Fin d) c h k (fun j => x j.1 j.2) hc
    (Height.dvd_at_section l K bk d ρ τ s ht hτ hρ En.Q En.inl En.inr εD hεD k x hx)
  have h₄ := map_toDisc_eq_of_dvd (BK.hf En.inl X) bk.ρ₀ k x εD hx hdiv
  obtain ⟨y, hy⟩ := h₄
  subst hy
  exact ⟨y, hεD⟩

end GlobalTheory.BSP
