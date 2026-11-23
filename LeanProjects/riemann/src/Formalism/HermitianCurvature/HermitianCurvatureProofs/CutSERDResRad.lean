import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rdb_glev0_inter_om (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem rdb_ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  simp only [Q.FFl, Q.SmoothLev, Q.LeftEq, Q.RightEq, rdb_glev0_inter_om]

private theorem conjTranspose_mul_H_mul_preserved_of_preserved {n : ℕ} (H a b : Matrix (Fin n) (Fin n) ℂ)
    (ha : a.conjTranspose * H * a = H) (hb : b.conjTranspose * H * b = H) :
    (a * b).conjTranspose * H * (a * b) = H := by
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * H * (a * b)
      = b.conjTranspose * (a.conjTranspose * H * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [ha, hb]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem radial_residue_formula : RDResRad := by
  classical
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD J hJ
  have hz := hD.1.2.1
  have hz' := hD.1.2.2.1
  rw [rdb_ffl_om_eq] at hJ
  obtain ⟨hS, -, -, hE⟩ := hJ
  have huh : ∀ a b : Mx P.k P.r, a ∈ UH (Hpk P.k P.r) → b ∈ UH (Hpk P.k P.r) →
      a * b ∈ UH (Hpk P.k P.r) :=
    fun a b ha hb => conjTranspose_mul_H_mul_preserved_of_preserved _ a b ha hb
  have hcell : ∀ c ∈ OmX P.r, wCell P.k P.r (Fin.last P.r) c ∈ UH (Hpk P.k P.r) := by
    intro c hc
    refine List.prod_induction _ huh ?_ ?_
    · show (1 : Mx P.k P.r).conjTranspose * Hpk P.k P.r * 1 = Hpk P.k P.r
      simp
    · intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact Qx3.weyl_cell_mem_unitary a (hc a)
  have hcomm : ∀ (c : Fin P.r → ℂ) (h : Mx P.k P.r), h ∈ UWset P.k P.r z →
      Commute (wCell P.k P.r (Fin.last P.r) c) h := by
    intro c h hh
    refine Commute.list_prod_left _ _ ?_
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact Qx3.w1_commute_of_mem_Glev a (c a) ⟨hh.1, fun b _ => hh.2.1 b⟩
  have hin : ∀ x ∈ DomR P.k P.r z z',
      wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Glev P.k P.r 0 ∩ OmPlus P.k P.r z z' :=
    fun x hx => ⟨Rad.glev0 (huh _ _ (hcell _ hx.1) hx.2.1.1),
      Rad.wCell_mem_omPlus hz hz' hx.1 hx.2.1 hx.2.2⟩
  let Φ0 : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR P.k P.r z z' then resG P.k P.r (Fin.last P.r) J c g else 0
  have hmem : Φ0 ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact if_neg hx
    · intro x₀ hx₀
      obtain ⟨U, F, hU, hxU, hF, hag⟩ :=
        Rad.sf_resG hS x₀ ⟨hx₀.1, (hin x₀ hx₀).2⟩ hx₀.2.1
      refine ⟨U ∩ (Prod.fst ⁻¹' OmX P.r ∩ Prod.snd ⁻¹' {g | 0 < GGl P.k P.r z z' g}), F,
        hU.inter (((Qx3.isOpen_OmX _).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((Qx5.GGl_continuous _ _ _ _).comp continuous_snd))),
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hF.mono Set.inter_subset_left, ?_⟩
      intro x hx hg
      have hxD : x ∈ DomR P.k P.r z z' := ⟨hx.2.1, hg, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
      rw [if_pos hxD]
      exact hag x hx.1 hg
    · intro x hx h hh h' hh'
      have hx' := Rad.domR_uw hx hh hh'
      show (if (x.1, h * x.2 * h') ∈ DomR P.k P.r z z' then _ else _) =
        π h ∘SL (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) ∘SL π' h'
      rw [if_pos hx', if_pos hx]
      simp only [resG]
      rw [show wCell P.k P.r (Fin.last P.r) x.1 * (h * x.2 * h') =
          h * (wCell P.k P.r (Fin.last P.r) x.1 * x.2) * h' by
        simp only [← mul_assoc, (hcomm x.1 h hh).eq]]
      rw [hE _ (hin x hx) h hh h' hh']
      simp [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨⟨Φ0, hmem⟩, fun x hx => ?_⟩
  show (if (x.1, x.2) ∈ DomR P.k P.r z z' then _ else _) = _
  rw [if_pos hx]

end Formalism.FourierDecayAlt.P.CutSE
