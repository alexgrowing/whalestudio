import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

variable {D : D7} {V : HSp D} {n : ℕ}

def RatFrame (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h)

theorem ratF_injective (V : HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, γ₀, h₀, e⟩ h
  have h1 : finHom V γ = 1 := congrArg Subtype.val h
  have h2 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((finHom V γ).1 i j) = inclR (F := D.host.F) (Af D.host.F) (γ₀.1 i j) := by
      have : (matHom V γ).1 i j = inclR (F := D.host.F) (AF D.host.F) (γ₀.1 i j) :=
        (congrArg (fun g : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e).symm
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 i j) = _
      rw [this]
      simp [inclR]
    have hi : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) := by
      haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
      exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    apply hi
    rw [← h3, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  subst h2
  exact Subtype.ext (Subtype.ext (e.symm.trans (map_one _)))

def frameEquiv (P : principalLevelFrame.RowPsi V n) : GAf D.host.E n ≃* Bridge.Gf V :=
  MulEquiv.ofBijective ((finHom V).rangeRestrict.comp P.ψ)
    ⟨fun a b e => P.inj (TopMult.lift_unique (P.into a) (P.into b) e), fun y => by
      obtain ⟨h, hh, e⟩ := TopMult.exists_lift y
      obtain ⟨g, rfl⟩ := P.onto h hh
      exact ⟨g, e⟩⟩

theorem frameEquiv_apply (P : principalLevelFrame.RowPsi V n) (g) : frameEquiv P g = (finHom V).rangeRestrict (P.ψ g) := rfl

theorem RatFrame.iff {P : principalLevelFrame.RowPsi V n} (h : RatFrame P) (g) :
    g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ, Bridge.ratF V γ = frameEquiv P g :=
  (h g).trans ⟨fun ⟨γ, hγ, e⟩ => ⟨⟨γ, hγ⟩, Subtype.ext e⟩, fun ⟨γ, e⟩ => ⟨γ.1, γ.2, congrArg Subtype.val e⟩⟩

theorem comap_le_Umax {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsBaseFrame V β Λ 1)
    (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    (levEnv V β Lv).J.comap (frameEquiv P).toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
  (hP.2 κ).2 ((GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG (Lv := flag1L Lv) ⟨P.into κ, hκ⟩))

section Read

variable {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem weight_match (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    {x₀ : D.what₂.Mt μ j} (h₀ : x₀ ≠ 0) (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (δ : Γ) (hδ : ι δ = φ γ) (v : X.wt.W) :
    e (X.wt.ρ γ v) = ρ δ (e v) := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  let U : Subrepresentation X.wt.ρ := ⟨Submodule.span ℂ (Set.range (X.real x₀)), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => X.wt.ρ g w ∈ Submodule.span ℂ (Set.range (X.real x₀))) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, (hA x₀).1.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := X.wt.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ (X.real_inj ?_)
    rw [map_zero]
    funext g
    have : X.real x₀ g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  have hv : v ∈ Submodule.span ℂ (Set.range (X.real x₀)) := by
    show v ∈ U.toSubmodule
    rw [hU]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun v _ => e (X.wt.ρ γ v) = ρ δ (e v)) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨h, rfl⟩
    have := hFm x₀ δ (φ h) 1
    rw [← (hA x₀).1.1 γ h, hread, hread, map_mul, ← hδ]
    simpa using this
  · simp
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb]
  · intro c a _ ha
    simp only [map_smul, ha]

def pullForm : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ).comp e.toLinearMap).compl₂ e.toLinearMap

theorem pullForm_apply (a b : X.wt.W) : pullForm X e a b = inner ℂ (e a) (e b) := rfl

theorem classSum_of_read {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hrat : ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔ ∃ γ, ι γ = φ h) (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : IsBounded (J.comap φ.toMonoidHom)) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x'))
    (h0 : (∀ x : D.what₂.Mt μ j, x = 0) → ∃ β, IsInvForm X.wt β) : ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := classSum_transport (W := W) ι hι φ hrat J y hy
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := h0 hz
    obtain ⟨T, c', hT, -, -⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  · obtain ⟨x₀, h₀⟩ := not_forall.1 hz
    have hβ : IsInvForm X.wt (pullForm X e) := by
      refine ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => ?_, fun γ a b => ?_⟩
      · rw [pullForm_apply]
        exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))
      · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
        have hw := weight_match X ι φ ρ J χ e Fm hFm hread h₀ γ δ hδ
        exact (congrArg₂ (inner ℂ) (hw a) (hw b)).trans (hρ δ _ _)
    obtain ⟨T, c', hT, hc', hcmp⟩ := classSum_compare hβ hX hN (fun κ h => (hNJ κ h).1) hJ hT'
    have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ (J.comap φ.toMonoidHom) (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
      ⟨(hA x).1, fun κ => funext fun g => e.injective (by
        have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
        show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
        rw [map_smul, hread, hread, map_mul]
        simpa using this)⟩
    refine ⟨_, T, c * c', hβ, hT, mul_pos hc hc', fun x x' => ?_⟩
    rw [hip, ← htr X.wt (pullForm X e) (X.real x) (X.real x') _ _ fun g => by rw [pullForm_apply, hread, hread],
      hcmp _ _ _ _ (hA x) (hA x') (hB x) (hB x')]
    push_cast
    ring

end Read

end GlobalTheory.FormInner

end
