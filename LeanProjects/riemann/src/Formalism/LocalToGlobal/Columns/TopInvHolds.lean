import Formalism.LocalToGlobal.Columns.RefKEquivOfCpTop

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TI

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xt_eN_single {E : Type} [Field E] {N p : ℕ} (hp : p < N) : Loc.eN E N p = (Pi.single (⟨p, hp⟩ : Fin N) (1 : E) : Fin N → E) := by
  funext l
  unfold Loc.eN
  by_cases h : l = ⟨p, hp⟩
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, if_neg]
    intro h2
    exact h (Fin.ext h2)

theorem topInv_holds (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) : TopInv Ch sel mu cst m2 := by
  intro w hw y z hz
  have hu := ciQ_notMem_sq hX hPr hw
  have hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨k, hk⟩ : ∃ k, cst.B = k + 1 := ⟨cst.B - 1, by have := hc.B_pos; omega⟩
  refine xtPhiTop_congr Ch mu hX hPr hm cst.sharp hw y (y + z) fun p p' hp hp' => ?_
  have hp'' : p' < R.N (m2 + 1) + cOf R (m2 + 1) := by omega
  refine ⟨(qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single ⟨p', hp''⟩ 1) ⟨p, hp⟩),
    (xtIntAt_qpow (qOf w.1) k).mul (hz _ _), ?_⟩
  rw [xtEntB (xt_cOf hm) _ (by omega) hp', xtEntB (xt_cOf hm) _ (by omega) hp', LinearMap.add_apply, Pi.add_apply, xt_eN_single hp'', hk]
  congr 1
  field_simp
  ring

end TI

end Formalism.L2.Col
