import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOrthOf

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem fib_mp (γ : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D)
    (hL : IsLoUni L) (hGr : IsUnit (Formalism.L2.SG.Pf.StabilizerIndexVolumes.gramOf (Formalism.L2.SG.Pf.StabilizerIndexVolumes.gg F0 F'.fl)).det)
    (hZu : IsUnit (Zhat F0 F'.fl).det)
    (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (x₁ x₂ : GLR D) (hx₁ : (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L)
    (hd₁ : LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁) (hd₂ : LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂)
    (hrel : CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂) : x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L := by
  obtain ⟨ha₁, hb₁, -, -, hν₁, hm₁, hν₁f, hm₁f, -, -, hF₁⟩ := hd₁
  obtain ⟨ha₂, hb₂, -, -, hν₂, hm₂, hν₂f, hm₂f, -, -, hF₂⟩ := hd₂
  obtain ⟨n, ⟨hnN, hne, hnz⟩, hn1e, hn1z⟩ := hrel
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  have ha₁d : IsUnit (a₁ : MatR D).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det ha₁]; exact isUnit_one
  have hU₁ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₁
  have hU₂ := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_conjT ha₂
  have hV₁ : IsUpUni (sbs b₁) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₁
  have hV₂ : IsUpUni (sbs b₂) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_sgn hb₂
  have hnf : ∀ b, n (frame (lf D F0) b) = ∑ c, (1 : MatR D) c b • frame (lf D F0) c := by
    intro b
    rw [← act_one (frame (lf D F0)) b]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · show n (F0.fvec (Fin.last _)) = F0.fvec (Fin.last _)
      simp only [FlagG.fvec, Fin.snoc_last]
      exact hnz
    · show n (F0.fvec (Fin.castSucc a)) = F0.fvec (Fin.castSucc a)
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      exact hne a
  have hnF : ∀ c, n (frame F₁ c) = frame F₂ c := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · show n (F₁.fl.fvec (Fin.last _)) = F₂.fl.fvec (Fin.last _)
      simp only [FlagG.fvec, Fin.snoc_last]
      exact hn1z
    · show n (F₁.fl.fvec (Fin.castSucc a)) = F₂.fl.fvec (Fin.castSucc a)
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      exact hn1e a
  set t : (VS D).V ≃ₗ[D.host.E] (VS D).V := ν₂ * n * ν₁⁻¹ with ht
  have htN : t ∈ NLam γ.lam (lf D F0) :=
    Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_mul hν₂ hnN) (Formalism.L2.SG.Pf.nlamPf_inv hν₁)
  set Uq : MatR D := (a₂ : MatR D).conjTranspose * 1 * ((a₁ : MatR D).conjTranspose)⁻¹ with hUq
  have htf : ∀ b, t (frame (lf D F0) b) = ∑ c, Uq c b • frame (lf D F0) c :=
    act_mul _ _ _ _ _ (act_mul _ _ _ _ _ hν₂f hnf) (act_inv' _ ν₁ _ hU₁ hν₁f)
  have htm : ∀ b, t (m₁ (frame F' b)) = m₂ (frame F' b) := by
    intro b
    show ν₂ (n (ν₁⁻¹ (m₁ (frame F' b)))) = _
    rw [← hF₁ b, hnF b, hF₂ b]
    show (ν₂ * ν₂⁻¹) (m₂ (frame F' b)) = _
    rw [mul_inv_cancel]
    rfl
  have htf' := act_quot (frame F') t m₁ m₂ (sbs b₁) (sbs b₂) hV₁ hm₁f hm₂f htm
  have hiso : ∀ x y, (VS D).hT (t x) (t y) = (VS D).hT x y := ((Formalism.L2.SG.Pf.isAutLam_iff _ t).1 htN.1).1
  have hsX : ∀ x, (∀ i, (VS D).hT (F0.e i) x = 0) → t x - x ∈ Submodule.span D.host.E (Set.range F0.e) :=
    fun x hx => htN.2.2 x (mem_orth_of F0 x hx)
  have hUp : IsUpUni Uq :=
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_mul (Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_mul hU₂ Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_one) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_inv hU₁)
  have hVp : IsUpUni (sbs b₂ * (sbs b₁)⁻¹) := Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_mul hV₂ (Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_inv hV₁)
  obtain ⟨hflag, horth⟩ := Formalism.L2.SG.Pf.ZsVolKey.nlam_of_frames F0 F'.fl hGr hZu t hiso _ _ hUp hVp htf htf' hsX
  have htN' : t ∈ NLam γ.lam F' := ⟨htN.1, fun j x hx => hflag j x hx, fun x hx => horth x (orth_e F'.fl x hx)⟩
  refine Subgroup.subset_closure ⟨t, ⟨htN, htN'⟩, Uq, htf, ?_⟩
  rw [hUq, Matrix.mul_one]
  exact img_quot L _ _ hLd ha₁d x₁ x₂ hx₁ hx₂

end Formalism.L2.SG.Pf.ZsVolFib

end
