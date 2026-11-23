import Formalism.LocalToGlobal.Columns.ChainLawXi
import Formalism.LocalToGlobal.Columns.ChainLawPhi
import Formalism.LocalToGlobal.Columns.ChainLawPhiPf

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Join

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem clPsi_restr {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    LinearMap.funLeft E E (Fin.castAdd c) (clL_ext c κ v) = κ (LinearMap.funLeft E E (Fin.castAdd c) v) := by
  funext l
  show (clL_ext c κ v) (Fin.castAdd c l) = κ (LinearMap.funLeft E E (Fin.castAdd c) v) l
  rw [clL_ext_apply, ciExtM_castAdd,
    show κ (LinearMap.funLeft E E (Fin.castAdd c) v) = κ.toLinearMap (LinearMap.funLeft E E (Fin.castAdd c) v) from rfl,
    ← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, LinearMap.funLeft_apply]

theorem clPsi_atNL {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    atNL E (n + c) n (clL_ext c κ v) = atNL E (n + c) n v := by
  unfold atNL
  split_ifs with h
  · have hc : 0 < c := by omega
    have e : (⟨n, h⟩ : Fin (n + c)) = Fin.natAdd n ⟨0, hc⟩ := rfl
    simp only [LinearMap.proj_apply]
    rw [e, clL_ext_natAdd]
  · rfl

theorem clPsi_joinCol {n' c' n c : ℕ} (κ₀ : Sp E n' ≃ₗ[E] Sp E n') (κ : Sp E n ≃ₗ[E] Sp E n) (x₀ : HomE E n' n) (y' : Sp E n) :
    joinCol (c' := c') (c := c) (κ.symm.toLinearMap ∘ₗ x₀ ∘ₗ κ₀.toLinearMap) (κ.symm y') =
      (clL_ext c κ.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x₀ y' ∘ₗ (clL_ext c' κ₀).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]
  rw [clL_ext_inX, clPsi_restr, clPsi_atNL]
  simp only [map_add, map_smul]

end Join

section Psi

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clPsi_phiHyp (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) :
    PhiGSLawHyp P (qOf P) R.k R.rS R.r R.t (m2 + 1) (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) := by
  obtain ⟨hk0, hr0, hrN0, -⟩ := ranks_frame_inequalities R hm (j := m2) (by omega)
  obtain ⟨hk1, -, hrN1, -⟩ := ranks_frame_inequalities R hm (j := m2 + 1) le_rfl
  exact ⟨ciQ_mem P, ciQ_notMem_sq hX hPr hP, by omega, hk0, hk1, hr0, t_pos R, by simpa using hrN0.symm, hrN1.symm⟩

end Psi

end Formalism.L2.Col
