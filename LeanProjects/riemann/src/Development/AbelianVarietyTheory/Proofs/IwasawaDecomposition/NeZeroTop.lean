import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.LocalToGlobal.Columns.TwQLevU
import Formalism.LocalToGlobal.Columns.RecLevelAsm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Formalism.LocalToGlobal.Columns.TiedCls

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TopCh

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

theorem phi_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) ≤ 1 := by

  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_le_one (K := E) (v := P) r

theorem phi_lt (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal := by
  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (v := P) r

def locLev (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) : Subgroup (GL (Fin n) (P.adicCompletion E)) :=
  qbU (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ (algebraMap E (P.adicCompletion E) d)

abbrev iotaP (P : HeightOneSpectrum (𝓞 E)) : ↥(GLint E n P) →* GL (Fin n) (P.adicCompletion E) :=
  qbIota (F := E) P (algebraMap E (P.adicCompletion E))

def locChr (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) (hd : d ≠ 0) {N : ℕ} (hdN : P.valuation E d ≤ WithZero.exp (-(N : ℤ)))
    (hΘ : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ Θ.H, Θ.lam ⟨g, h⟩ = 1) : locLev P Θ d →* Kˣ :=
  qbChr (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ d hd hdN hΘ

end Loc

section Ad

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] {n : ℕ}
  {Q : Finset (HeightOneSpectrum (𝓞 E))}

variable (F) in

abbrev rhoP (P : HeightOneSpectrum (𝓞 E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) := bc (adAt F P)

variable (F) in

def rhoT (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) :=
  (rhoP F P).comp (MulAut.conj t⁻¹).toMonoidHom

def topU (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : Subgroup (GL (Fin n) (AfE F E)) :=
  U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)

theorem topU_le (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : topU U t Θ d ≤ U :=
  inf_le_left

theorem rhoT_mem {U : Subgroup (GL (Fin n) (AfE F E))} {t : GL (Fin n) (AfE F E)} {Θ : LevQFam E K n Q} {d : Q → E}
    {x : GL (Fin n) (AfE F E)} (hx : x ∈ topU U t Θ d) (P : Q) : rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) := by
  have hx' : x ∈ U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t) := hx
  exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hx').2 P)

def topChi (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0)
    (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) :
    topU U t Θ d →* ℂˣ :=
  (∏ P : Q, (Units.map (σ : K →* ℂ)).comp ((locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P)).comp
    (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ fun x => rhoT_mem x.2 P)))⁻¹

end Ad

instance neZero_top (R : Ranks) : NeZero (R.N R.m) := ⟨by have := N_m_succ R; omega⟩

end GlobalTheory.Mem.Col2.TopCh

end
