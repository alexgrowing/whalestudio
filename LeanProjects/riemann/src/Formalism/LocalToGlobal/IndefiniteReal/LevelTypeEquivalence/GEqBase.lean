import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv.Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Comm

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (matA D V h).map (infPart D) = 1 := by
  rw [GfC, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem psiT_of_mem_GfC' {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) : (matA D V h).map (psiT D τ) = 1 := by
  have h1 := (mem_GfC' h).1 hh
  have h2 : (matA D V h).map (psiT D τ) = ((matA D V h).map (infPart D)).map (thetaC D τ) := by
    rw [Matrix.map_map]
    rfl
  rw [h2, h1]
  first
  | simp
  | exact Matrix.map_one _ (map_zero _) (map_one _)

theorem comm_inf_fin {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' := (mem_GinfC (D := D) (V := V) (h := a)).1 ha
  have hb' := (mem_GfC' b).1 hb
  have hinf : (matA D V a * matA D V b).map (infPart D) = (matA D V b * matA D V a).map (infPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, hb', mul_one, one_mul]
  have hfin : (matA D V a * matA D V b).map (finPart D) = (matA D V b * matA D V a).map (finPart D) := by
    rw [Matrix.map_mul, Matrix.map_mul, ha', mul_one, one_mul]
  have key : matA D V (a * b) = matA D V (b * a) := by
    rw [matA_mul, matA_mul]
    ext i j
    exact ae_ext (D := D) (congrFun (congrFun hinf i) j) (congrFun (congrFun hfin i) j)
  first
  | exact Subtype.ext (Units.ext key)
  | (apply Subtype.ext; apply Units.ext; exact key)
  | (apply Subtype.ext; apply Subtype.ext; apply Units.ext; exact key)

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem atTau_mem (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem oneP_mem (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : oneP θ V τ X t ∈ GinfC V := by
  unfold oneP
  exact atTau_mem θ τ _

theorem prod_oneP_mem {k : ℕ} (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := by
  apply Subgroup.list_prod_mem
  intro x hx
  simp only [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact oneP_mem θ (τs i) (Xs i) (t i)

end Comm

section RTr

variable {D : D7} {V : HSp D} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {κ : GA D V}

theorem rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ f) = rTr V κ (Rder θ V τ X f) := by
  funext g
  simp only [Rder, rTr]
  congr 1
  funext t
  rw [mul_assoc, comm_inf_fin (oneP_mem θ τ X t) hκ, ← mul_assoc]

theorem rderC_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : GA D V → ℂ) :
    RderC θ V τ Z (rTr V κ f) = rTr V κ (RderC θ V τ Z f) := by
  simp only [RderC, rder_rTr θ hκ]
  funext g
  simp only [rTr, Pi.add_apply, Pi.smul_apply]

theorem foldr_comm_rTr (l : List ((GA D V → ℂ) → (GA D V → ℂ)))
    (h : ∀ f ∈ l, ∀ φ, f (rTr V κ φ) = rTr V κ (f φ)) (φ : GA D V → ℂ) :
    l.foldr (fun f acc => f acc) (rTr V κ φ) = rTr V κ (l.foldr (fun f acc => f acc) φ) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun f hf => h f (by simp [hf]))]
    exact h g (by simp) _

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (f : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ f) = rTr V κ (gelf θ V τ k f) := by
  simp only [gelf]
  have hs : ∀ F : (Fin (k + 1) → Fin V.rank) → GA D V → ℂ,
      rTr V κ (Finset.sum Finset.univ F) = Finset.sum Finset.univ (fun i => rTr V κ (F i)) := by
    intro F
    funext g
    simp [rTr, Finset.sum_apply]
  rw [hs]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  apply foldr_comm_rTr
  intro f hf φ
  simp only [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_rTr θ hκ τ _ φ

theorem foldr_rder_rTr (hκ : κ ∈ GfC V) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (rTr V κ φ) = rTr V κ (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact rder_rTr θ hκ p.1 p.2 _

theorem isAutFunSm_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V κ φ) := by
  haveI : IsTopologicalGroup (GA D V) := (ga_facts (D := D) V).1
  obtain ⟨⟨hleft, hlevel, hcont⟩, hsmooth, hzfin, hgrowth⟩ := hφ
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [rTr]
    rw [mul_assoc]
    exact hleft γ hγ (g * κ)
  · obtain ⟨U, hU, hUk⟩ := hlevel
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun x : GA D V => κ⁻¹ * x * κ⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hU.preimage hc
    · intro k hk hkf g
      simp only [rTr]
      have hk' : κ⁻¹ * k * κ ∈ U := by simpa [MulAut.conj_apply] using hk
      have hkf' : κ⁻¹ * k * κ ∈ GfC V := mul_mem (mul_mem (inv_mem hκ) hkf) hκ
      have h1 := hUk _ hk' hkf' (g * κ)
      rw [← h1]
      congr 1
      group
  · exact hcont.comp (continuous_id.mul continuous_const)
  · intro k τs Xs hX g
    simp only [rTr]
    have hc : ∀ t : Fin k → ℝ, g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * κ =
        g * κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod := by
      intro t
      rw [mul_assoc, comm_inf_fin (prod_oneP_mem θ τs Xs t) hκ, ← mul_assoc]
    simp_rw [hc]
    exact hsmooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, hφW, hgel⟩ := hzfin
    let R : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
      { toFun := rTr V κ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine ⟨W.map R, ?_, Submodule.mem_map_of_mem hφW, ?_⟩
    · first
      | (haveI := hW; infer_instance)
      | exact Module.Finite.map W R
    · rintro τ k' _ ⟨f, hf, rfl⟩
      exact ⟨gelf θ V τ k' f, hgel τ k' f hf, (gelf_rTr θ hκ τ k' f).symm⟩
  · obtain ⟨N, hN⟩ := hgrowth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_rder_rTr θ hκ l φ]
    simp only [rTr]
    rw [mul_assoc, comm_inf_fin hg hκ, ← mul_assoc]
    exact hC g hg

theorem isCuspFun_rTr (κ : GA D V) {φ : GA D V → ℂ} (hφ : IsCuspFun V φ) : IsCuspFun V (rTr V κ φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using hφ r C hC μ 𝓕 hμ h𝓕 (g * κ)

end RTr

end Formalism.IndefR.Eqv.Act

end
