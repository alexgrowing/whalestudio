import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0DecorationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

section FrLev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frDiv_mem_GLint (p p' : DecoF E n ST SG Q) (hN : p.deco.1.N = p'.deco.1.N) (P : Q) :
    (p.fr P)⁻¹ * p'.fr P ∈ GLint E n P.1 := by
  intro v
  have h1 := p.2 P (((p.fr P)⁻¹ * p'.fr P) v)
  have h2 := p'.2 P v
  have e : p.1.2 P (((p.fr P)⁻¹ * p'.fr P) v) = p'.fr P v := by
    show p.fr P ((p.fr P).symm (p'.fr P v)) = p'.fr P v
    exact LinearEquiv.apply_symm_apply _ _
  rw [e] at h1
  rw [← h1, ← h2]
  show p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p'.deco.1.N
  rw [hN]

theorem rhoP_eq_fr {g : GL (Fin n) (AfE F E)} {q : DecoF E n ST SG Q} (hq : IsPtOf hc g q) (P : Q) :
    rhoP F P.1 g = bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (q.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (q.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [hq.fr P i j, qsp_toGLm_apply]

end FrLev

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TopCh

theorem mem_topU_iff : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG E n SG × GLQ E n Q) • p = p') := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ U k t y x p p' hk hkP ht hU hp hp'
  set g := y * (k * t) with hg
  set z := (k * t)⁻¹ * x * (k * t) with hz
  have hgz : y * x * (k * t) = g * z := by rw [hg, hz]; group
  rw [hgz] at hp'
  have step := fun h : GLG E n SG => ((GlobalTheory.T.isPtOf_mul_J0_decoration F E hc n ST SG Q g z p p' h).1 hp hp')
  have htU : t ∈ UAd hc n := principal_le_adelic_unitary hc n ST SG ht
  have hktU : k * t ∈ UAd hc n := mul_mem hk htU
  have hgU : g ∈ UAd hc n := hp.uni
  have hgzU : g * z ∈ UAd hc n := hp'.uni
  have hyU : y ∈ UAd hc n := by
    have e : y = g * (k * t)⁻¹ := by rw [hg]; group
    rw [e]; exact mul_mem hgU (inv_mem hktU)
  have hxU : x ∈ UAd hc n := by
    have e : x = y⁻¹ * (g * z) * (k * t)⁻¹ := by rw [hg, hz]; group
    rw [e]; exact mul_mem (mul_mem (inv_mem hyU) hgzU) (inv_mem hktU)
  have hU' : x ∈ U ↔ z ∈ levU hc n ST SG Λ.grp := by
    rw [hU x hxU]
    have e : k⁻¹ * x * k = t * z * t⁻¹ := by rw [hz]; group
    rw [e]
    have htL : t ∈ levU hc n ST SG Λ.grp := kOne_le_unipotentLevel hc n ST SG _ ht
    constructor
    · intro h
      have h2 := mul_mem (mul_mem (inv_mem htL) h) htL
      have e2 : t⁻¹ * (t * z * t⁻¹) * t = z := by group
      rwa [e2] at h2
    · intro h
      exact mul_mem (mul_mem htL h) (inv_mem htL)
  have hT : ∀ P : Q, rhoT F P.1 t x = rhoP F P.1 z := by
    intro P
    show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 z
    rw [hz]
    simp only [map_mul, map_inv, hkP P, one_mul, inv_inv, _root_.mul_inv_rev, inv_one, mul_one]
  have hZ : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoP F P.1 z = iotaP P.1 ⟨_, frDiv_mem_GLint p p' hN P⟩ := by
    intro hN P
    have e : rhoP F P.1 z = (rhoP F P.1 g)⁻¹ * rhoP F P.1 (g * z) := by
      rw [← map_inv, ← map_mul, inv_mul_cancel_left]
    rw [e, rhoP_eq_fr hp P, rhoP_eq_fr hp' P, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hL : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) ↔ (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := by
    intro hN P
    rw [hT P, hZ hN P]
    exact qbU_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P)
      (hΘ P) _
  have hNs : ∀ h : GLG E n SG, p'.deco = ((1, h) : UF E n × GLG E n SG) • p.deco → p.deco.1.N = p'.deco.1.N := by
    intro h e
    rw [e]
    show p.deco.1.N = Formalism.HermitianLatticesTheory.gmap (1 : Sp E n ≃ₗ[E] Sp E n) p.deco.1.N
    exact (Formalism.L2.Col.gmap_one _).symm
  constructor
  · intro hx
    obtain ⟨hz0, hzr⟩ := (mem_levU hc n ST SG _).1 (hU'.1 hx.1)
    let h : Λ.grp := ⟨(redG hc n ST SG ⟨z, hz0⟩)⁻¹, inv_mem hzr⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG E n SG) • p.deco := (step h.1).1 ⟨hz0, (inv_inv _).symm⟩
    have hN := hNs h.1 hdeco
    have hc' : ∀ P : Q, (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := fun P =>
      (hL hN P).1 (rhoT_mem hx P)
    let θ : Θ.grp := ⟨fun P => (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1))⁻¹, fun P _ => inv_mem (hc' P)⟩
    refine ⟨h, θ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hdeco.symm
    · funext P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) = p'.fr P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((p.fr P)⁻¹ * p'.fr P) = p'.fr P
      rw [one_mul, mul_inv_cancel_left]
  · rintro ⟨h, θ, hθ⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG E n SG) • p.deco := by rw [← hθ]; rfl
    obtain ⟨hz0, hzr⟩ := (step h.1).2 hdeco
    have hN := hNs h.1 hdeco
    refine ⟨hU'.2 ((mem_levU hc n ST SG _).2 ⟨hz0, by rw [hzr]; exact inv_mem h.2⟩), ?_⟩
    refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_comap.2 ((hL hN P).2 ?_)
    have hfr : p'.fr P = p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) := by
      rw [← hθ]
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * _ = _
      rw [one_mul]
    have e : (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) = (θ.1 P)⁻¹ := by
      apply Subtype.ext
      show (p.fr P)⁻¹ * p'.fr P = _
      rw [hfr, inv_mul_cancel_left]
    rw [e]
    exact inv_mem (θ.2 P (Set.mem_univ _))

end GlobalTheory.Mem.Col2.TopCh
