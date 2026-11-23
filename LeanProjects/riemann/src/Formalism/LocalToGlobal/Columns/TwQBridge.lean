import Formalism.LocalToGlobal.Columns.TwQDense

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Bridge

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)

def qbPi (P : Q) : 𝓞 E := Classical.choose (qsp_exists hc P.1 (hQ P))

theorem qbPi_spec (P : Q) : qbPi hc hQ P ∈ P.1.asIdeal ∧ cO E (qbPi hc hQ P) ∉ P.1.asIdeal ∧
    Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E)) :=
  Classical.choose_spec (qsp_exists hc P.1 (hQ P))

def qbSp (P : Q) : Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P.1) ((qbPi hc hQ P : 𝓞 E) : E) :=
  Classical.choice (qbPi_spec hc hQ P).2.2

def qbN (P : Q) : ℕ := Classical.choose (hΘ P)

theorem qbN_spec (P : Q) : 0 < qbN Θ hΘ P ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 (qbN Θ hΘ P) (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1 :=
  Classical.choose_spec (hΘ P)

abbrev qbD (P : Q) : E := ((qbPi hc hQ P : 𝓞 E) : E) ^ qbN Θ hΘ P

theorem qbPi_ne (P : Q) : qbPi hc hQ P ≠ 0 := fun h => (qbPi_spec hc hQ P).2.1 (by rw [h, map_zero]; exact zero_mem _)

theorem qbD_ne (P : Q) : qbD hc Θ hQ hΘ P ≠ 0 :=
  pow_ne_zero _ (fun h => qbPi_ne hc hQ P (by exact_mod_cast h))

theorem qbD_val (P : Q) : P.1.valuation E (qbD hc Θ hQ hΘ P) ≤ WithZero.exp (-(qbN Θ hΘ P : ℤ)) := by
  have h1 : qbPi hc hQ P ^ qbN Θ hΘ P ∈ P.1.asIdeal ^ qbN Θ hΘ P := Ideal.pow_mem_pow (qbPi_spec hc hQ P).1 _
  have := (P.1.intValuation_le_pow_iff_mem _ _).2 h1
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
  simpa using this

abbrev qbF (P : Q) : E →+* (qv F P.1).adicCompletion F := qbPhi hc P.1 (qbPi hc hQ P) (qbSp hc hQ P)

theorem qbF_int (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) ≤ 1 :=
  phi_integral_valuation_le_one hc P.1 _ (qbSp hc hQ P) r

theorem qbF_P (P : Q) (r : 𝓞 E) : Valued.v (qbF hc hQ P (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.1.asIdeal :=
  qsp_sp_P hc P.1 _ (qbPi_spec hc hQ P).1 (qbPi_spec hc hQ P).2.1 (qbSp hc hQ P) r

theorem qbK_mono {v : HeightOneSpectrum (𝓞 F)} {c w : v.adicCompletion F} (hw : w ∈ v.adicCompletionIntegers F)
    {x : GL (Fin n) (v.adicCompletion F)} (hx : x ∈ qbK (c * w)) : x ∈ qbK c := by
  refine ⟨hx.1, hx.2.1, fun i j => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2.2 i j
  exact ⟨w * z, Subring.mul_mem _ hw hz, by rw [e, mul_assoc]⟩

set_option maxHeartbeats 4000000 in

theorem qbU_dense (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F))
    (hk : qbInt (k : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)))
    (hk' : qbInt ((k⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F))) :
    ∃ g : ↥(GLint E n P.1), (qbIota P.1 (qbF hc hQ P) g)⁻¹ * k ∈
      qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P)) := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  have hD0 : b ^ qbN Θ hΘ P ≠ 0 := pow_ne_zero _ hb0
  have hDv : b ^ qbN Θ hΘ P ∈ (underPl F P.1).asIdeal := Ideal.pow_mem_of_mem _ hbP _ hNpos
  obtain ⟨g, hg⟩ := qsp_dense P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (qsp_sp_F hc P.1 _ (qbSp hc hQ P))
    (qsp_isOver P.1) (b ^ qbN Θ hΘ P) hD0 hDv k hk hk'
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  have hDE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (b ^ qbN Θ hΘ P) =
      qbF hc hQ P (qbD hc Θ hQ hΘ P) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P := by
    rw [map_pow, hbE, mul_pow, map_pow]
  rw [hDE] at hg
  have hw : qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P ∈ ((qv F P.1).adicCompletionIntegers F) :=
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _
  have hg2 := qbK_mono hw hg
  refine ⟨g, hg2.1, hg2.2.1, 1, (Θ P).H.one_mem, ?_⟩
  simpa using hg2

def qbLoc : QLoc hc n Q Θ where
  sp P := (qbSp hc hQ P).φ
  sp_sig P := (qbSp hc hQ P).sig
  sp_alg P := (qbSp hc hQ P).alg
  sp_int P := (qbSp hc hQ P).int
  sp_P P r := qbF_P hc hQ P r
  U P := qbU P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbF hc hQ P (qbD hc Θ hQ hΘ P))
  U_int _ _ hk := hk.1
  U_rat P g := qbU_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g
  U_dense P k hk hk' := qbU_dense hc Θ hQ hΘ P k hk hk'
  chr P := qbChr P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2
  chr_rat P g hg h := qbChr_rat P.1 (qbF hc hQ P) (qbF_int hc hQ P) (qbF_P hc hQ P) (Θ P) (qbD hc Θ hQ hΘ P) (qbD_ne hc Θ hQ hΘ P)
    (qbD_val hc Θ hQ hΘ P) (qbN_spec Θ hΘ P).2 g hg h

end Bridge

end Formalism.L2.Col
