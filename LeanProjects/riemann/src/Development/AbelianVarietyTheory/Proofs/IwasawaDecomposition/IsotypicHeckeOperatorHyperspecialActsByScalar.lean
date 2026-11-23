import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSphericalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoTypScalar

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

local notation3 "L⁺" => maximalRealSubfield L

theorem heckeD_eq_sum_of {v : HeightOneSpectrum (𝓞 L⁺)} {J : Subgroup (GAf L n)}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have tr : ∀ x ∈ D, ∀ y ∈ D, TrivOutside {v} (x⁻¹ * y) := fun x hx y hy =>
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy)
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    have ht := tr γ (h1 γ hγ) _ hc.choose_spec.1
    have hu : γ⁻¹ * hc.choose ∈ Umax L n := (hJ _ ht).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu ht) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hJ _ (tr γ (h1 γ hγ) δ (h1 δ hδ))).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hJ _ (tr γ (h1 γ hγ) x hx)).2 e)⟩)
    · exact absurd (dif_neg h) hc

theorem isoTyp_scalar (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 L⁺)))
    (hyp : NG.HypOutside J χ B) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hsB : s.v ∉ B) (hϖ : IsUnif L s.v ϖ) :
    ∃ c : ℂ, ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → NG.tN J s ϖ k f = c • f := by
  classical
  have tc : ∀ κ : GAf L n, TrivOutside {s.v} κ → TrivOutside Bᶜ κ := fun κ hκ v hv =>
    hκ v fun h => hv (by rw [Set.mem_compl_iff, Set.mem_singleton_iff.1 h]; exact hsB)
  have hJU : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n) := fun κ hκ => (hyp κ (tc κ hκ)).1
  have hfin : ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' tSet L n s ϖ k).Finite :=
    GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level L n (Umax L n) 1 ∅ (fun κ _ => ⟨Iff.rfl, fun _ => MonoidHom.one_apply _⟩) s ϖ k
      (Set.notMem_empty _) hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax L n) _ hfin
  set q : ℂ := ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ with hq
  have hJeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN J s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, heckeD_eq_sum_of hJU (fun x hx => hx.1) hR1 hR2 hf]
  have hUeq : ∀ f : GAf L n → a.W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      NG.tN (Umax L n) s ϖ k f = q • ∑ γ ∈ R, NG.rt L n γ f := fun f hf => by
    rw [NG.tN, GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := s.v) (fun x hx => hx.1) hR1 hR2 hf]
  obtain ⟨c, hc⟩ := GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical L n a S hS s ϖ k hϖ
  have hS0 : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      q • ∑ γ ∈ R, NG.rt L n γ f = c • f := fun f hf hx => (hUeq f hx).symm.trans (hc f hf hx)

  have hiso : ∀ S' : Submodule ℂ (GAf L n → a.W), NG.IsoRep S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    rintro S' ⟨T, hT⟩ f hf hfx
    set g : S := T.symm ⟨f, hf⟩ with hg
    have hTg : ((T g : S') : GAf L n → a.W) = f := by simp [g]
    have hgx : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (g : GAf L n → a.W) = g := by
      intro κ h1 h2
      have e := hT κ g ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ rfl
      rw [hTg, hfx κ h1 h2] at e
      have e2 : T ⟨NG.rt L n κ (g : GAf L n → a.W), hS.1.stable κ _ g.2⟩ = T g := Subtype.ext (e.trans hTg.symm)
      exact congrArg Subtype.val (T.injective e2)
    have key : (c • g : S) = q • ∑ γ ∈ R, (⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_sum]
      exact (hS0 g g.2 hgx).symm
    have hterm : ∀ γ : GAf L n,
        ((T ⟨NG.rt L n γ (g : GAf L n → a.W), hS.1.stable γ _ g.2⟩ : S') : GAf L n → a.W) = NG.rt L n γ f := by
      intro γ
      rw [hT γ g _ rfl, hTg]
    have := congrArg (fun u : S => ((T u : S') : GAf L n → a.W)) key
    simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum, hTg, hterm] at this
    exact this.symm

  have hsum : ∀ t : Finset (Submodule ℂ (GAf L n → a.W)),
      (↑t : Set (Submodule ℂ (GAf L n → a.W))) ⊆ {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'} →
      (∀ h, ∀ f ∈ ⨆ S' ∈ t, S', NG.rt L n h f ∈ ⨆ S' ∈ t, S') ∧
      ∀ f ∈ ⨆ S' ∈ t, S', (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
        q • ∑ γ ∈ R, NG.rt L n γ f = c • f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot]
      refine ⟨fun h f hf => ?_, fun f hf _ => ?_⟩
      · rw [hf, map_zero]
      · simp [hf]
    | insert S₁ t hS₁ ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨hst, hfx⟩ := ih hs.2
      have h1 := hs.1
      rw [Finset.iSup_insert]
      refine ⟨fun h f hf => ?_, fun f hf hfix => ?_⟩
      · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
        rw [map_add]
        exact Submodule.add_mem_sup (h1.1.1.stable h x hx) (hst h y hy)
      · by_cases hd : S₁ ⊓ (⨆ S' ∈ t, S') = ⊥
        · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
          have hxy : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ x = x ∧ NG.rt L n κ y = y := by
            intro κ hκ hκ'
            have e := hfix κ hκ hκ'
            rw [map_add] at e
            have e1 : NG.rt L n κ x - x = y - NG.rt L n κ y := by
              rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
            have hm : NG.rt L n κ x - x ∈ S₁ ⊓ (⨆ S' ∈ t, S') :=
              ⟨S₁.sub_mem (h1.1.1.stable κ x hx) hx, e1 ▸ Submodule.sub_mem _ hy (hst κ y hy)⟩
            rw [hd, Submodule.mem_bot] at hm
            refine ⟨sub_eq_zero.1 hm, ?_⟩
            rw [hm] at e1
            exact (sub_eq_zero.1 e1.symm).symm
          simp only [map_add, Finset.sum_add_distrib, smul_add]
          rw [hiso S₁ h1.2 x hx fun κ h h' => (hxy κ h h').1, hfx y hy fun κ h h' => (hxy κ h h').2]
        · have hsub : NG.IsSubrep a.ρ (S₁ ⊓ (⨆ S' ∈ t, S')) :=
            ⟨inf_le_left.trans h1.1.1.le, fun h f hf => ⟨h1.1.1.stable h f hf.1, hst h f hf.2⟩⟩
          have heq : S₁ ⊓ (⨆ S' ∈ t, S') = S₁ := (h1.1.2.2 _ hsub inf_le_left).resolve_left hd
          have hle : S₁ ≤ ⨆ S' ∈ t, S' := heq ▸ inf_le_right
          exact hfx f ((sup_le hle le_rfl) hf) hfix
  refine ⟨c, fun f hf hT => ?_⟩
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f := by
    intro κ h1 h2
    have hκ : κ ∈ J := (hJU κ h2).2 h1
    have e := hT.2 ⟨κ, hκ⟩
    rw [(hyp κ (tc κ h2)).2 hκ] at e
    simpa using e
  rw [hJeq f hfix]
  unfold NG.isoTyp at hf
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact (hsum t ht).2 f hft hfix

theorem main : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := by
  intro D μ j Mr B _ hyp S hS s ϖ k hsB hϖ _ _
  obtain ⟨c, hc⟩ := isoTyp_scalar Mr.wt Mr.J Mr.χ B hyp S hS s ϖ k hsB hϖ
  refine ⟨c, fun y hy => hc _ (Submodule.mem_comap.1 hy) ?_⟩
  rw [← Mr.real_range]
  exact ⟨y, rfl⟩

end GlobalTheory.IsoTypScalar

end
