import Formalism.LocalToGlobal.Columns.TwQGrp

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG

section Lev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)

local notation "Kv" => v.adicCompletion F

def qbIota : ↥(GLint E n P) →* GL (Fin n) Kv :=
  (bc φ).comp ((toGLm E n).toMonoidHom.comp (GLint E n P).subtype)

theorem qbIota_apply (g : ↥(GLint E n P)) (i j : Fin n) :
    ((qbIota P φ g : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) i j = φ (((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := rfl

theorem qsp_mem_locP {L : Submodule (𝓞 E) (Sp E n)} {x : Sp E n} :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ L := Iff.rfl

theorem qsp_toGLm_apply (g : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = g (Pi.single j 1) i := by
  show LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) i j = _
  exact LinearMap.toMatrix'_apply _ _ _

theorem qsp_entry_int (g : ↥(GLint E n P)) (i j : Fin n) :
    P.valuation E (((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [qsp_toGLm_apply]
  have h1 : (Pi.single j 1 : Sp E n) ∈ stdAt E n P := by
    refine (qsp_mem_locP P).2 ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    intro l _
    rw [Pi.single_apply]
    show (if l = j then (1 : E) else 0) ∈ (1 : Submodule (𝓞 E) E)
    by_cases h : l = j
    · rw [if_pos h]; exact Submodule.one_le.1 le_rfl
    · rw [if_neg h]; exact zero_mem _
  have h2 : g.1 (Pi.single j 1) ∈ stdAt E n P := (g.2 _).2 h1
  obtain ⟨s, hs, hsx⟩ := (qsp_mem_locP P).1 h2
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hsx i trivial)
  have e : g.1 (Pi.single j 1) i * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    rw [ha]
    show _ = (s • g.1 (Pi.single j 1)) i
    rw [Pi.smul_apply, Algebra.smul_def, mul_comm]
  have h3 := congrArg (P.valuation E) e
  rw [map_mul, (P.valuation_eq_one_iff_notMem (K := E)).2 hs, mul_one] at h3
  rw [h3]; exact P.valuation_le_one a

include hint hPv in
theorem qbIota_int (g : ↥(GLint E n P)) : qbInt ((qbIota P φ g : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) := fun i j => by
  rw [qbIota_apply]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qsp_le_of_val P φ hint hPv _ (qsp_entry_int P g i j))

include hint hPv in
theorem qbIota_int_inv (g : ↥(GLint E n P)) :
    qbInt (((qbIota P φ g)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) := by
  rw [← map_inv]; exact qbIota_int P φ hint hPv g⁻¹

variable (Θ : LevI E K n P) (cm : v.adicCompletion F)

theorem qbU_mul_wit (hI : ∀ g : ↥(GLint E n P), qbInt ((qbIota P φ g : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv))
    (hI' : ∀ g : ↥(GLint E n P), qbInt (((qbIota P φ g)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv))
    {a b : GL (Fin n) Kv} {g1 g2 : ↥(GLint E n P)} (ka : (qbIota P φ g1)⁻¹ * a ∈ qbK cm)
    (kb : (qbIota P φ g2)⁻¹ * b ∈ qbK cm) : (qbIota P φ (g1 * g2))⁻¹ * (a * b) ∈ qbK cm := by
  have h := (qbK cm).mul_mem (qbK_conj ka (hI g2) (hI' g2)) kb
  simp only [map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left] at h ⊢
  exact h

theorem qbU_inv_wit (hI : ∀ g : ↥(GLint E n P), qbInt ((qbIota P φ g : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv))
    (hI' : ∀ g : ↥(GLint E n P), qbInt (((qbIota P φ g)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv))
    {a : GL (Fin n) Kv} {g : ↥(GLint E n P)} (ka : (qbIota P φ g)⁻¹ * a ∈ qbK cm) :
    (qbIota P φ g⁻¹)⁻¹ * a⁻¹ ∈ qbK cm := by
  have h := qbK_conj ((qbK cm).inv_mem ka) (hI' g) (by rw [inv_inv]; exact hI g)
  simp only [map_inv, inv_inv, mul_inv_rev, mul_assoc, mul_inv_cancel, mul_one] at h ⊢
  exact h

include hint hPv in

def qbU : Subgroup (GL (Fin n) Kv) where
  carrier := {k | qbInt (k : Matrix (Fin n) (Fin n) Kv) ∧ qbInt ((k⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) ∧
    ∃ g : ↥(GLint E n P), g ∈ Θ.H ∧ (qbIota P φ g)⁻¹ * k ∈ qbK cm}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, g1, hg1, ka⟩ ⟨hb1, hb2, g2, hg2, kb⟩
    refine ⟨?_, ?_, g1 * g2, Θ.H.mul_mem hg1 hg2, ?_⟩
    · rw [Units.val_mul]; exact qbInt_mul ha1 hb1
    · rw [mul_inv_rev, Units.val_mul]; exact qbInt_mul hb2 ha2
    · exact qbU_mul_wit P φ cm (qbIota_int P φ hint hPv) (qbIota_int_inv P φ hint hPv) ka kb
  one_mem' := ⟨by rw [Units.val_one]; exact qbInt_one, by rw [inv_one, Units.val_one]; exact qbInt_one,
    1, Θ.H.one_mem, by simpa using (qbK cm).one_mem⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, g, hg, ka⟩
    exact ⟨ha2, by rw [inv_inv]; exact ha1, g⁻¹, Θ.H.inv_mem hg, qbU_inv_wit P φ cm (qbIota_int P φ hint hPv) (qbIota_int_inv P φ hint hPv) ka⟩

theorem mem_qbU {k : GL (Fin n) Kv} : k ∈ qbU P φ hint hPv Θ cm ↔ qbInt (k : Matrix (Fin n) (Fin n) Kv) ∧
    qbInt ((k⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) ∧ ∃ g : ↥(GLint E n P), g ∈ Θ.H ∧ (qbIota P φ g)⁻¹ * k ∈ qbK cm := Iff.rfl

variable {N : ℕ} (d : E) (hd : d ≠ 0) (hdN : P.valuation E d ≤ WithZero.exp (-(N : ℤ)))

include hint hPv hd hdN in

theorem qbK_princ {g : ↥(GLint E n P)} (hg : qbIota P φ g ∈ qbK (φ d)) : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) := by
  intro i j
  obtain ⟨z, hz, e⟩ := hg.2.2 i j
  have e1 : (((qbIota P φ g : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) - 1) i j =
      φ ((((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, qbIota_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e1] at e
  have h := qsp_mod P φ hint hPv _ d hd z ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hz) e
  exact le_trans h hdN

variable (hΘ : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ Θ.H, Θ.lam ⟨g, h⟩ = 1)

include hint hPv hd hdN hΘ in

theorem qbU_rat (g : ↥(GLint E n P)) : qbIota P φ g ∈ qbU P φ hint hPv Θ (φ d) ↔ g ∈ Θ.H := by
  constructor
  · rintro ⟨-, -, g0, hg0, k⟩
    have h1 : qbIota P φ (g0⁻¹ * g) ∈ qbK (φ d) := by rw [map_mul, map_inv]; exact k
    obtain ⟨h2, -⟩ := hΘ _ (qbK_princ P φ hint hPv d hd hdN h1)
    have := Θ.H.mul_mem hg0 h2
    rwa [mul_inv_cancel_left] at this
  · intro hg
    exact ⟨qbIota_int P φ hint hPv g, by rw [← map_inv]; exact qbIota_int P φ hint hPv g⁻¹, g, hg, by simpa using (qbK (φ d)).one_mem⟩

include hint hPv hd hdN hΘ in

theorem qbChr_wd {k : GL (Fin n) Kv} {g0 g1 : ↥(GLint E n P)} (h0 : g0 ∈ Θ.H) (h1 : g1 ∈ Θ.H)
    (k0 : (qbIota P φ g0)⁻¹ * k ∈ qbK (φ d)) (k1 : (qbIota P φ g1)⁻¹ * k ∈ qbK (φ d)) : Θ.lam ⟨g0, h0⟩ = Θ.lam ⟨g1, h1⟩ := by
  have hk : qbIota P φ (g0⁻¹ * g1) ∈ qbK (φ d) := by
    have e : qbIota P φ (g0⁻¹ * g1) = ((qbIota P φ g0)⁻¹ * k) * ((qbIota P φ g1)⁻¹ * k)⁻¹ := by
      rw [map_mul, map_inv]; try group
    rw [e]; exact (qbK (φ d)).mul_mem k0 ((qbK (φ d)).inv_mem k1)
  obtain ⟨h2, h3⟩ := hΘ _ (qbK_princ P φ hint hPv d hd hdN hk)
  have e2 : (⟨g1, h1⟩ : Θ.H) = ⟨g0, h0⟩ * ⟨g0⁻¹ * g1, h2⟩ := Subtype.ext (by simp)
  rw [e2, map_mul, h3, mul_one]

def qbWit (k : qbU P φ hint hPv Θ (φ d)) : Θ.H :=
  ⟨Classical.choose k.2.2.2, (Classical.choose_spec k.2.2.2).1⟩

theorem qbWit_spec (k : qbU P φ hint hPv Θ (φ d)) : (qbIota P φ (qbWit P φ hint hPv Θ d k).1)⁻¹ * k.1 ∈ qbK (φ d) :=
  (Classical.choose_spec k.2.2.2).2

def qbChr : qbU P φ hint hPv Θ (φ d) →* Kˣ where
  toFun k := Θ.lam (qbWit P φ hint hPv Θ d k)
  map_one' := by
    have := qbChr_wd P φ hint hPv Θ d hd hdN hΘ (qbWit P φ hint hPv Θ d 1).2 Θ.H.one_mem (qbWit_spec P φ hint hPv Θ d 1)
      (by simpa using (qbK (φ d)).one_mem)
    rw [show (⟨(qbWit P φ hint hPv Θ d 1).1, (qbWit P φ hint hPv Θ d 1).2⟩ : Θ.H) = qbWit P φ hint hPv Θ d 1 from rfl] at this
    rw [this]; exact map_one _
  map_mul' a b := by
    have hw := qbU_mul_wit P φ (φ d) (qbIota_int P φ hint hPv) (qbIota_int_inv P φ hint hPv) (qbWit_spec P φ hint hPv Θ d a) (qbWit_spec P φ hint hPv Θ d b)
    have := qbChr_wd P φ hint hPv Θ d hd hdN hΘ (qbWit P φ hint hPv Θ d (a * b)).2
      (Θ.H.mul_mem (qbWit P φ hint hPv Θ d a).2 (qbWit P φ hint hPv Θ d b).2) (qbWit_spec P φ hint hPv Θ d (a * b)) hw
    rw [show (⟨(qbWit P φ hint hPv Θ d (a * b)).1, (qbWit P φ hint hPv Θ d (a * b)).2⟩ : Θ.H) = qbWit P φ hint hPv Θ d (a * b) from rfl]
      at this
    rw [this, ← map_mul]
    rfl

theorem qbChr_rat (g : ↥(GLint E n P)) (hg : g ∈ Θ.H) (h : qbIota P φ g ∈ qbU P φ hint hPv Θ (φ d)) :
    qbChr P φ hint hPv Θ d hd hdN hΘ ⟨_, h⟩ = Θ.lam ⟨g, hg⟩ :=
  qbChr_wd P φ hint hPv Θ d hd hdN hΘ _ hg (qbWit_spec P φ hint hPv Θ d ⟨_, h⟩) (by simpa using (qbK (φ d)).one_mem)

end Lev

end Formalism.L2.Col
