import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOrthOf

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem zv (Z a b : MatR D) (h : a * ZhatOM Z * b = ZhatOM Z) : a * Z * sbs b = Z := by
  rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq] at h
  unfold sbs
  calc a * Z * (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) =
      a * (Z * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [h, Matrix.mul_assoc, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one]

theorem uu'_eq (Z a₁ a₂ V₁ V₂ uu' : MatR D) (hZ : IsUnit Z.det) (ha₁ : IsUnit a₁.det)
    (hV₁ : IsUnit V₁.det) (hV₂ : IsUnit V₂.det)
    (h₁ : a₁ * Z * V₁ = Z) (h₂ : a₂ * Z * V₂ = Z) (hc : a₁⁻¹ * a₂ * Z * uu' = Z) : uu' * V₁ = V₂ := by
  have e2 : a₂ * Z = Z * V₂⁻¹ := by
    calc a₂ * Z = a₂ * Z * V₂ * V₂⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hV₂]
      _ = Z * V₂⁻¹ := by rw [h₂]
  have e3 : a₁⁻¹ * Z = Z * V₁ := by
    calc a₁⁻¹ * Z = a₁⁻¹ * (a₁ * Z * V₁) := by rw [h₁]
      _ = Z * V₁ := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha₁]
  have e4 : Z * (V₁ * V₂⁻¹ * uu') = Z * 1 := by
    rw [Matrix.mul_one]
    calc Z * (V₁ * V₂⁻¹ * uu') = a₁⁻¹ * Z * V₂⁻¹ * uu' := by rw [e3]; simp only [Matrix.mul_assoc]
      _ = a₁⁻¹ * (a₂ * Z) * uu' := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = a₁⁻¹ * a₂ * Z * uu' := by simp only [Matrix.mul_assoc]
      _ = Z := hc
  have e5 : V₁ * V₂⁻¹ * uu' = 1 := by
    have := congrArg (fun M => Z⁻¹ * M) e4
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hZ] using this
  have e6 : uu' = V₂ * V₁⁻¹ := by
    calc uu' = (V₂ * V₁⁻¹) * (V₁ * V₂⁻¹ * uu') := by
          rw [Matrix.mul_assoc V₂, ← Matrix.mul_assoc V₁⁻¹, ← Matrix.mul_assoc V₁⁻¹,
            Matrix.nonsing_inv_mul _ hV₁, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hV₂]
      _ = V₂ * V₁⁻¹ := by rw [e5, Matrix.mul_one]
  rw [e6, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hV₁, Matrix.mul_one]

theorem fib_mpr (γ : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D)
    (hL : IsLoUni L) (hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0) (hZu : IsUnit (Zhat F0 F'.fl).det)
    (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (x₁ x₂ : GLR D) (hx₁ : (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L)
    (hd₁ : LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁) (hd₂ : LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂)
    (hh : x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L) : CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ := by
  obtain ⟨ha₁, hb₁, hZ₁, -, hν₁, -, hν₁f, hm₁f, -, -, hF₁⟩ := hd₁
  obtain ⟨ha₂, hb₂, hZ₂, -, hν₂, -, hν₂f, hm₂f, -, -, hF₂⟩ := hd₂
  obtain ⟨s, ⟨hsF, hsF'⟩, uu, hu, hx⟩ := (mem_stabAut_iff u u' F0 what₂ γ F' L hL hT0 _).1 hh
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  have ha₁d : IsUnit (a₁ : MatR D).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det ha₁]; exact isUnit_one
  have hU₁ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₁
  have hU₂ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₂
  have hV₁ : IsUpUni (sbs b₁) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₁
  have hV₂ : IsUpUni (sbs b₂) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₂
  have hV₁d : IsUnit (sbs b₁).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hV₁]; exact isUnit_one
  have hV₂d : IsUnit (sbs b₂).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hV₂]; exact isUnit_one
  have hU₁d : IsUnit ((a₁ : MatR D).conjTranspose).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU₁]; exact isUnit_one

  have hsF0 := hsF
  obtain ⟨hAut, hf1, hf2⟩ := hsF
  obtain ⟨-, hg1, hg2⟩ := hsF'
  have hiso : ∀ x y, (VS D).hT (s x) (s y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff _ s).1 hAut).1
  obtain ⟨uu0, huu0, hu0⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F0 s hf1 hf2
  have heq : uu = uu0 :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.coef_unique (Formalism.L2.SG.Pf.StabilizerIndexVolumes.frame_indep F0 hT0) (fun b => s (F0.fvec b)) uu uu0 hu hu0
  subst heq
  obtain ⟨uu', -, hu'⟩ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.tri_exists F'.fl s hg1 hg2
  have hZc := Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhat_conj F0 F'.fl s hiso uu uu' hu0 hu'

  have himg := img_quot L _ _ hLd ha₁d x₁ x₂ hx₁ hx₂
  rw [hx] at himg
  have hcanc : uu.conjTranspose = ((a₂ : MatR D).conjTranspose * ((a₁ : MatR D).conjTranspose)⁻¹).conjTranspose := by
    have := congrArg (fun M => L * M * L⁻¹) himg
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLd, Matrix.mul_one] at this
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLd, Matrix.one_mul] using this
  have huu : uu = (a₂ : MatR D).conjTranspose * ((a₁ : MatR D).conjTranspose)⁻¹ := by
    have := congrArg Matrix.conjTranspose hcanc
    simpa only [Matrix.conjTranspose_conjTranspose] using this
  have hcT : uu.conjTranspose = ((a₁ : MatR D))⁻¹ * (a₂ : MatR D) := by
    rw [hcanc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hc : ((a₁ : MatR D))⁻¹ * (a₂ : MatR D) * Zhat F0 F'.fl * uu' = Zhat F0 F'.fl := by
    rw [← hcT]; exact hZc.symm
  have hmove := uu'_eq _ _ _ _ _ uu' hZu ha₁d hV₁d hV₂d (zv _ _ _ hZ₁) (zv _ _ _ hZ₂) hc

  set n : (VS D).V ≃ₗ[D.host.E] (VS D).V := ν₂⁻¹ * s * ν₁ with hn
  have hnN : n ∈ NLam γ.lam (lf D F0) :=
    Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hν₂) hsF0) hν₁
  have hnf := act_mul _ _ _ _ _ (act_mul _ _ _ _ _ (act_inv' _ ν₂ _ hU₂ hν₂f) hu0) hν₁f
  have hone : ((a₂ : MatR D).conjTranspose)⁻¹ * uu * (a₁ : MatR D).conjTranspose = 1 := by
    rw [huu, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hU₁d,
      Matrix.nonsing_inv_mul _ (by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU₂]; exact isUnit_one)]
  rw [hone] at hnf
  have hnf' : ∀ b, n (F0.fvec b) = F0.fvec b := fun b => by
    rw [show F0.fvec b = frame (lf D F0) b from rfl, hnf b, ← act_one]
    rfl
  refine ⟨n, ⟨hnN, fun a => ?_, ?_⟩, fun a => ?_, ?_⟩
  · have := hnf' (Fin.castSucc a); simpa [FlagG.fvec, Fin.snoc_castSucc] using this
  · have := hnf' (Fin.last _); simpa [FlagG.fvec, Fin.snoc_last] using this
  all_goals
    have hsm : ∀ c, s (m₁ (frame F' c)) = m₂ (frame F' c) := fun c => by
      have := act_mul (frame F') s m₁ uu' (sbs b₁) hu' hm₁f c
      rw [hmove] at this
      rw [hm₂f c]
      exact this
    have hnF : ∀ c, n (frame F₁ c) = frame F₂ c := fun c => by
      rw [hF₁ c, hF₂ c]
      show ν₂⁻¹ (s (ν₁ (ν₁⁻¹ (m₁ (frame F' c))))) = _
      rw [show ν₁ (ν₁⁻¹ (m₁ (frame F' c))) = (ν₁ * ν₁⁻¹) (m₁ (frame F' c)) from rfl, mul_inv_cancel]
      show ν₂⁻¹ (s (m₁ (frame F' c))) = _
      rw [hsm c]
  · have := hnF (Fin.castSucc a); simpa [frame, FlagG.fvec, Fin.snoc_castSucc] using this
  · have := hnF (Fin.last _); simpa [frame, FlagG.fvec, Fin.snoc_last] using this

end Formalism.L2.SG.Pf.ZsVolFib

end
