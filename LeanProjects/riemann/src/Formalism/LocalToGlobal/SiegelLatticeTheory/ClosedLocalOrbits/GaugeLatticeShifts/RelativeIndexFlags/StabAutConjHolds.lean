import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.LoUniConjTranspose

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stabAutConj_holds (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hE : TermEqIff D u u') (hrows : IsRowReps D F0 what₂) : StabAutConjP D u u' F0 what₂ := by
  intro t w F₁ F₂ L₁ U₁ L₂ U₂ h1 h2
  obtain ⟨⟨hp1, hm1⟩, -, hL1, -, -⟩ := h1
  obtain ⟨⟨hp2, hm2⟩, -, hL2, -, -⟩ := h2
  have hrow : IsRowLat D F0 t.lam := hrows.1 t.lam t.mem
  have hrel := (hE F0 t.lam hrow ⟨F₁, hp1⟩ ⟨F₂, hp2⟩).1 (hm1.trans hm2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hrel
  have hfr' : ∀ a, frame F₂ a = (n * m) (frame F₁ a) := fun a => hfr a
  obtain ⟨N, hNu, hNr⟩ := exists_upUni hn
  have hNd : N.det = 1 := det_upUni hNu
  have hNu' : IsUnit N.det := by rw [hNd]; exact isUnit_one
  have hNHd : N.conjTranspose.det = 1 := by rw [Matrix.det_conjTranspose, hNd, star_one]
  obtain ⟨l1, hl1, hl1i⟩ : ∃ l : GLR D, (l : MatR D) = L₁ ∧ ((l⁻¹ : GLR D) : MatR D) = L₁⁻¹ :=
    ⟨unitOf L₁ (det_loUni hL1), rfl, rfl⟩
  obtain ⟨l2, hl2, hl2i⟩ : ∃ l : GLR D, (l : MatR D) = L₂ ∧ ((l⁻¹ : GLR D) : MatR D) = L₂⁻¹ :=
    ⟨unitOf L₂ (det_loUni hL2), rfl, rfl⟩
  obtain ⟨v, hv, hvi⟩ : ∃ l : GLR D, (l : MatR D) = N.conjTranspose ∧
      ((l⁻¹ : GLR D) : MatR D) = (N.conjTranspose)⁻¹ :=
    ⟨unitOf N.conjTranspose hNHd, rfl, rfl⟩
  have hv' : IsLoUni (v : MatR D) := by rw [hv]; exact loUni_conjTranspose hNu
  have hl1' : IsLoUni (l1 : MatR D) := by rw [hl1]; exact hL1
  have hl2' : IsLoUni (l2 : MatR D) := by rw [hl2]; exact hL2
  refine ⟨l2⁻¹ * v⁻¹ * l1, ?_, ?_⟩
  · have m1 : l1 ∈ loGen (D.R.rS + 1) D.host.E := Subgroup.subset_closure hl1'
    have m2 : l2 ∈ loGen (D.R.rS + 1) D.host.E := Subgroup.subset_closure hl2'
    have m3 : v ∈ loGen (D.R.rS + 1) D.host.E := Subgroup.subset_closure hv'
    exact mul_mem (mul_mem (inv_mem m2) (inv_mem m3)) m1
  · unfold stabAut cj
    rw [MonoidHom.map_closure]
    congr 1
    ext a
    constructor
    · rintro ⟨s₂, ⟨hs0, hs2⟩, uu₂, hrep₂, ha₂⟩
      refine ⟨(l2⁻¹ * v⁻¹ * l1)⁻¹ * a * (l2⁻¹ * v⁻¹ * l1), ?_, ?_⟩
      · refine ⟨n⁻¹ * s₂ * n, ⟨?_, ?_⟩, N⁻¹ * uu₂ * N, ?_, ?_⟩
        · exact nlam_mul (nlam_mul (nlam_inv hn) hs0) hn
        · have hc := (nlam_conj (isAutLam_mul _ hn.1 hm.1) hfr' s₂).1 hs2
          have e : n⁻¹ * s₂ * n = m * ((n * m)⁻¹ * s₂ * (n * m)) * m⁻¹ := by group
          rw [e]
          exact nlam_mul (nlam_mul hm hc) (nlam_inv hm)
        · exact repM_mul (repM_mul (repM_inv hNr hNu') hrep₂) hNr
        · rw [← hl2i, ← hl2] at ha₂
          rw [← hl1i, ← hl1, Units.val_mul, Units.val_mul, ha₂, conj_key']
          congr 2
          rw [hv, hvi]
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨a₁, ⟨s₁, ⟨hs0, hs1⟩, uu₁, hrep₁, ha₁⟩, rfl⟩
      refine ⟨n * s₁ * n⁻¹, ⟨?_, ?_⟩, N * uu₁ * N⁻¹, ?_, ?_⟩
      · exact nlam_mul (nlam_mul hn hs0) (nlam_inv hn)
      · refine (nlam_conj (isAutLam_mul _ hn.1 hm.1) hfr' _).2 ?_
        have e : (n * m)⁻¹ * (n * s₁ * n⁻¹) * (n * m) = m⁻¹ * s₁ * m := by group
        rw [e]
        exact nlam_mul (nlam_mul (nlam_inv hm) hs1) hm
      · exact repM_mul (repM_mul hNr hrep₁) (repM_inv hNr hNu')
      · rw [← hl1i, ← hl1] at ha₁
        rw [← hl2i, ← hl2]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [Units.val_mul, Units.val_mul, ha₁, conj_key]
        congr 2
        rw [hv, hvi]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, mul_assoc]

end Formalism.L2.SG.Pf.RelativeIndexFlags
