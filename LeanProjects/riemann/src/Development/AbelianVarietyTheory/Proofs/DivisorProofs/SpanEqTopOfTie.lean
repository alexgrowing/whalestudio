import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

noncomputable section

namespace GlobalTheory.ConjSpan

section General

open Formalism.IndefR.Bridge Formalism.L2.DIV

theorem span_eq_top {G Γ W W' K V₀ H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Field K] [NumberField K] [StarRing K] [AddCommGroup V₀] [Module K V₀]
    [AddCommGroup H] [Module ℂ H] {ι : Γ →* G} {S : CSD K} {τ σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
    {ρ' : Γ →* Module.End ℂ W'} {J : Subgroup G} {χ χ' : J →* ℂˣ} (P : ClassPres ι S τ ρ J χ)
    (c₀ : V₀ →ₛₗ[τ] W) (c₁ : V₀ →ₛₗ[σ] W') (e : S.V ≃ₗ[K] V₀) (he : ∀ x, P.coef x = c₀ (e x))
    (hspan : Submodule.span ℂ (Set.range c₁) = ⊤)
    (hact : ∀ γ v, ∃ v', c₀ v' = ρ γ (c₀ v) ∧ c₁ v' = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ a : K, τ a = (χ k : ℂ) ∧ σ a = (χ' k : ℂ))
    (E : H →ₗ[ℂ] (G → W')) (hE : Function.Injective E) (hr : LinearMap.range E = AdForms ι ρ' J χ')
    (j : S.Forms → H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ E (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  classical
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [PresBasic.coef_injective P h]
  have hval : ∀ (x : S.Forms) c, E (j x) (P.y c) = c₁ (e ((x : S.Cl → S.V) c)) := by
    intro x c
    obtain ⟨v, h1, h2⟩ := hj x (P.y c)
    rw [ClassPres.extL_apply, PresBasic.ext_y, he] at h1
    rw [h2, hinj h1]
  have hρ : ∀ c (g : S.Gam c) (x : S.V), c₁ (e (S.ρ c g x)) =
      (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) (c₁ (e x)) := by
    intro c g x
    obtain ⟨a, ha, ha'⟩ := hχ (stabK ι (P.stabI c g))
    obtain ⟨v', h1, h2⟩ := hact (P.stabI c g : Γ) (e x)
    have h3 : e (S.ρ c g x) = a • v' := by
      apply hinj
      rw [← he, P.coef_act, map_smulₛₗ, ha, h1, he]
    rw [h3, map_smulₛₗ, ha', h2]
  have hmem : ∀ w, E w ∈ AdForms ι ρ' J χ' := fun w => hr ▸ LinearMap.mem_range_self E w
  have hone : ∀ c (u : W'), ∃ w ∈ Submodule.span ℂ (Set.range j), ∀ c', E w (P.y c') =
      (Pi.single c (∑ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ) u) : S.Cl → W') c' := by
    intro c u
    have hu : u ∈ Submodule.span ℂ (Set.range c₁) := hspan ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      obtain ⟨x, rfl⟩ := e.surjective v
      refine ⟨j (PresBasic.avgForm S c x), Submodule.subset_span ⟨_, rfl⟩, fun c' => ?_⟩
      rw [hval]
      by_cases h : c' = c
      · subst h
        simp only [PresBasic.avgForm, Pi.single_eq_same, map_sum, hρ]
      · simp [PresBasic.avgForm, Pi.single_eq_of_ne h]
    | zero => exact ⟨0, Submodule.zero_mem _, fun c' => by simp⟩
    | add u u' _ _ h h' =>
      obtain ⟨w, hw, h⟩ := h
      obtain ⟨w', hw', h'⟩ := h'
      refine ⟨w + w', Submodule.add_mem _ hw hw', fun c' => ?_⟩
      simp only [map_add, Pi.add_apply, h, h', smul_add, Finset.sum_add_distrib, Pi.single_add]
    | smul a u _ h =>
      obtain ⟨w, hw, h⟩ := h
      refine ⟨a • w, Submodule.smul_mem _ _ hw, fun c' => ?_⟩
      simp only [map_smul, Pi.smul_apply, h, smul_comm _ a, ← Finset.smul_sum, Pi.single_smul]
  rw [eq_top_iff]
  intro w _
  choose f hf hf' using fun c => hone c ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c))
  have key : w = ∑ c, f c := by
    apply hE
    funext g
    obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
    rw [hmem w γ _ k, hmem _ γ _ k]
    congr 2
    rw [map_sum, Finset.sum_apply]
    simp only [hf']
    rw [Finset.sum_eq_single c (fun c' _ hc => Pi.single_eq_of_ne (Ne.symm hc) _) (by simp), Pi.single_eq_same]
    have hg : ∀ g : S.Gam c, (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ' (P.stabI c g : Γ)
        ((Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c)) = (Fintype.card (S.Gam c) : ℂ)⁻¹ • E w (P.y c) := by
      intro g
      have h1 := hmem w (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
      rw [stabK_spec] at h1
      rw [map_smul, smul_comm, ← h1]
    simp only [hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast Fintype.card_ne_zero
  rw [key]
  exact Submodule.sum_mem _ fun c _ => hf c

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem span_eq_top_of_tie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ χ' : J →* ℂˣ} (P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c₀ : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : Bridge.CoefTie V C P lam c₀ pair nab del) (hM : Bridge.CoefMapTie V C c₀ rho)
    {σ : D.what₂.LL →+* ℂ} (c : CoefA V) (c₁ : VV D.what₂.LL lam →ₛₗ[σ] c.W)
    (hact : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, c₁ (rho γE v) = c.ρ (γ : GA D V) (c₁ v))
    (hspan : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL lam a)) = ⊤)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ ((χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ))
    (H : HMod (Bridge.Gf V → c.W)) {ip} (hH : H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ') ip)
    (j : S.Forms → H.H) (hj : ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨e, -, he, -⟩ := hP
  have hspan' : Submodule.span ℂ (Set.range c₁) = ⊤ :=
    eq_top_iff.2 (hspan.ge.trans (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)))
  refine span_eq_top (ρ' := c.coef.ρ) P c₀ c₁ e he hspan' (fun γ v => ?_) hχ H.e hH.1 hH.2.1 j hj
  obtain ⟨γE, h⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  exact ⟨_, hM.1 γ γE h v, hact γ γE h v⟩

set_option maxHeartbeats 1600000 in

theorem span_conjForms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → Submodule.span ℂ (Set.range j) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC
  obtain ⟨χ', hχ, hH⟩ := hC.model
  have h1 := hT.coefL i A.μ0
  have h2 := hT.mapL i
  refine span_eq_top_of_tie (V := Vc D i) (R.B.L i A.μ0).pres h1 h2 c c₁ hC.act hC.span hχ H hH j fun x h => ?_
  have h0 := congrFun (hjV i A.μ0 x) h
  exact (hC.base x h).imp fun v hv => ⟨h0.symm.trans hv.1, hv.2⟩

end GlobalTheory.ConjSpan

end
