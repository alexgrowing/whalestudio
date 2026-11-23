import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem toGLm_entry {E : Type} [Field E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n f : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = f (Pi.single j 1) i := by
  simp [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem localComponent_eq_frame {hc : CMData F E} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) :
    rhoP F P.1 g = Formalism.UG.bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (p.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [h.fr P i j, toGLm_entry]

theorem rhoT_eq_iota {hc : CMData F E} {k t y x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : GLG E n SG) (θ : GLQ E n Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x * (k * t)) (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p)) (P : Q) :
    rhoT F P.1 t x = iotaP P.1 ((θ P)⁻¹) := by
  have e0 : rhoT F P.1 t x = (rhoP F P.1 (y * (k * t)))⁻¹ * rhoP F P.1 (y * x * (k * t)) := by
    rw [← map_inv, ← map_mul, show (y * (k * t))⁻¹ * (y * x * (k * t)) = t⁻¹ * (k⁻¹ * (x * k)) * t by group,
      map_mul, map_mul, map_mul, map_mul, map_inv (rhoP F P.1) k, hk P, inv_one, one_mul, mul_one]
    simp [rhoT]
  rw [e0, localComponent_eq_frame h1 P, localComponent_eq_frame h2 P]
  show _ * Formalism.UG.bc _ (toGLm E n ((1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((θ P)⁻¹).1)) = _
  rw [one_mul, map_mul, map_mul, inv_mul_cancel_left]
  rfl

theorem topChi_eq {K : Type} [Field K] (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E))
    (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (x : topU U t Θ d) (θ : Θ.grp) (hx : ∀ P : Q, rhoT F P.1 t x.1 = iotaP P.1 ((θ.1 P)⁻¹)) :
    topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Θ.chr θ) := by
  have hθ : ∀ P : Q, θ.1 P ∈ (Θ P).H := fun P => θ.2 P (Set.mem_univ P)
  have key : ∀ P : Q, locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ =
      ((Θ P).lam ⟨θ.1 P, hθ P⟩)⁻¹ := by
    intro P
    have mem : iotaP P.1 ((θ.1 P)⁻¹) ∈ locLev P.1 (Θ P) (d P) := hx P ▸ rhoT_mem x.2 P
    have e : (⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ : locLev P.1 (Θ P) (d P)) = ⟨iotaP P.1 ((θ.1 P)⁻¹), mem⟩ := Subtype.ext (hx P)
    rw [e, ← map_inv]
    exact qbChr_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P) (hΘ P)
      ((θ.1 P)⁻¹) (inv_mem (hθ P)) mem
  have ec : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, hθ P⟩ := by
    unfold LevQFam.chr piChar
    exact MonoidHom.finsetProd_apply (M := ↥(Subgroup.pi Set.univ fun P : Q => (Θ P).H)) _ _ _
  unfold topChi
  rw [MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ec, map_prod, ← _root_.inv_inj, inv_inv, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  show Units.map (σ : K →* ℂ) (locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩) = _
  rw [key, map_inv]

theorem chi_eq_of_J0 {K : Type} [Field K] [NeZero n] {hc : CMData F E} (Λ : LevFam E K n SG) (σ : K →+* ℂ)
    {U : Subgroup (GL (Fin n) (AfE F E))} (χ : U →* ℂˣ) {k t : GL (Fin n) (AfE F E)} (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : U) (h : Λ.grp) (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ x = Units.map (σ : K →* ℂ) (Λ.chr h) := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine hχ x (t' * ⟨_, hz⟩ * t'⁻¹) h ?_ ?_
  · show t'.1 * ((k * t'.1)⁻¹ * x.1 * (k * t'.1)) * t'.1⁻¹ = _
    group
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 ht', hr, one_mul, inv_one, mul_one]

theorem chr_of_J0 {K : Type} [Field K] [NeZero n] (hc : CMData F E) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E)
    (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p))
    (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  rw [chi_eq_of_J0 Λ σ χ ht hχ ⟨x.1, topU_le _ _ _ _ x.2⟩ h hz hr,
    topChi_eq σ U t Θ d hd N hdN hΘ x θ fun P => rhoT_eq_iota h.1 θ.1 hk h1 h2 P, map_mul]

theorem chi_mul_topChi_moved : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ σ U χ k t y p _ hk ht hχ x h θ h1 h2
  have e : y * (k * t) * ((k * t)⁻¹ * x.1 * (k * t)) = y * x.1 * (k * t) := by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * (k * t)) ((k * t)⁻¹ * x.1 * (k * t)) p
    (((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p) h.1).1 h1 (e ▸ h2)).2 rfl
  exact chr_of_J0 hc Λ Θ d hd N hdN hΘ σ U χ k t y p hk ht hχ x h θ h1 h2 hz hr

end GlobalTheory.Mem.Col2.TopCh

end
