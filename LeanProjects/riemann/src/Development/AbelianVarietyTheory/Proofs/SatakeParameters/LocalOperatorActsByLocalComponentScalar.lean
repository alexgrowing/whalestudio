import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorpStatement
import GroundTheory.AutomorphicForms.SmoothRep
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.LocOpAct

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cosetSum_mem_fixed (ρ : Representation ℂ G V) {K N : Subgroup G} [Fintype (K ⧸ N.subgroupOf K)] {v : V}
    (hv : v ∈ GroundTheory.Automorphic.fixedVectors ρ N) :
    GroundTheory.Automorphic.cosetSum ρ K N v ∈ GroundTheory.Automorphic.fixedVectors ρ K := by
  intro k hk
  rw [GroundTheory.Automorphic.cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := GroundTheory.Automorphic.act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out ((⟨k, hk⟩ : K) • q)) (by
      rw [QuotientGroup.out_eq']; conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl)
  simpa using this

theorem opOf_eq (ρ : Representation ℂ G V) (f : G →₀ ℂ) (v : V) :
    GlobalTheory.Cong.opOf ρ f v = (f.sum fun g c => c • ρ g) v := by
  simp [GlobalTheory.Cong.opOf, Finsupp.sum, LinearMap.sum_apply]

theorem opOf_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (τ : Representation ℂ G W) (F : V →ₗ[ℂ] W) (hF : ∀ g v, F (ρ g v) = τ g (F v)) (f : G →₀ ℂ) (v : V) :
    F (GlobalTheory.Cong.opOf ρ f v) = GlobalTheory.Cong.opOf τ f (F v) := by
  simp only [GlobalTheory.Cong.opOf, Finsupp.sum, map_sum, map_smul, hF]

end GlobalTheory.LocOpAct

theorem GlobalTheory.Cong.opOf_locU_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ (Kw : Subgroup (GL (Fin a) (w.adicCompletion E))), IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))) → IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ), (∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) → ∃ f' : UA E a →₀ ℂ, (∀ g ∈ f'.support, g ∈ locU a w ∧ f' g = f (cLoc w g)) ∧ ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) f' φ = z σ • φ := by
  classical
  intro E _ _ _ a w hw Kw hKc hKo f z hf
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw
  let e : locU a w ≃* GL (Fin a) (w.adicCompletion E) :=
    MulEquiv.ofBijective ((cLoc w).comp (locU a w).subtype) hbij
  let j : GL (Fin a) (w.adicCompletion E) →* UA E a := (locU a w).subtype.comp e.symm.toMonoidHom
  let ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (UA E a → ℂ) := (RU E a).comp j
  have hcj : ∀ g, cLoc w (j g) = g := fun g => e.apply_symm_apply g
  have hinj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  haveI : CompactSpace Kw := isCompact_iff_compactSpace.1 hKc
  have hfin : ∀ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) →
      Finite (Kw ⧸ N.subgroupOf Kw) := fun N hN =>
    Subgroup.quotient_finite_of_isOpen _ (by rw [Subgroup.coe_subgroupOf]; exact hN.preimage continuous_subtype_val)
  refine ⟨f.mapDomain j, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact ⟨(e.symm h).2, by rw [Finsupp.mapDomain_apply hinj, hcj]⟩
  · intro U hU σ hσ φ hφU hφK
    have hop : ∀ ψ, opOf (RU E a) (f.mapDomain j) ψ = opOf ρ' f ψ := by
      intro ψ
      simp only [GlobalTheory.Cong.opOf]
      rw [Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b c₁ c₂; simp [add_smul])]
      rfl
    rw [hop]
    have hFint : ∀ (F : {F : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, F v ∈ U) ∧
        ∀ (x : locU a w) v, F (σ.ρ (cLoc w x) v) = RU E a x (F v)}) g v, F.1 (σ.ρ g v) = ρ' g (F.1 v) := by
      intro F g v
      have h := F.2.2 (e.symm g) v
      have h2 : cLoc w ((e.symm g : locU a w) : UA E a) = g := hcj g
      rw [h2] at h
      exact h
    let T : Module.End ℂ (UA E a → ℂ) := (f.sum fun g c => c • ρ' g) - z σ • 1
    have hT : ∀ ψ, T ψ = opOf ρ' f ψ - z σ • ψ := fun ψ => by
      rw [GlobalTheory.LocOpAct.opOf_eq]; rfl
    have key := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hσ φ hφU
    have hC : ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' φ) = 0 := by
      refine Submodule.iSup_induction _ (motive := fun ψ => ∃ N : Subgroup (GL (Fin a) (w.adicCompletion E)),
        IsOpen (N : Set (GL (Fin a) (w.adicCompletion E))) ∧
        ∀ N' : Subgroup (GL (Fin a) (w.adicCompletion E)), IsOpen (N' : Set (GL (Fin a) (w.adicCompletion E))) → N' ≤ N →
          T (GroundTheory.Automorphic.cosetSum ρ' Kw N' ψ) = 0) key ?_ ?_ ?_
      · rintro F _ ⟨v, rfl⟩
        refine ⟨GroundTheory.Automorphic.stabilizerOf σ.ρ v, σ.smooth v, fun N' hN' hle => ?_⟩
        haveI := hfin N' hN'
        haveI := Fintype.ofFinite (Kw ⧸ N'.subgroupOf Kw)
        have hv : v ∈ GroundTheory.Automorphic.fixedVectors σ.ρ N' := fun n hn => hle hn
        have hu := GlobalTheory.LocOpAct.cosetSum_mem_fixed σ.ρ (K := Kw) hv
        have hcs : GroundTheory.Automorphic.cosetSum ρ' Kw N' (F.1 v) = F.1 (GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v) := by
          rw [GroundTheory.Automorphic.cosetSum_apply, GroundTheory.Automorphic.cosetSum_apply, map_sum]
          simp only [hFint]
        have hfix : GroundTheory.Automorphic.cosetSum σ.ρ Kw N' v ∈ GlobalTheory.PRep.fixed σ.ρ Kw := fun k => by
          show σ.ρ k _ = ((1 : Kw →* ℂˣ) k : ℂ) • _
          simp [hu k k.2]
        rw [hcs, hT, ← GlobalTheory.LocOpAct.opOf_map σ.ρ ρ' F.1 (hFint F) f, hf σ _ hfix, map_smul, sub_self]
      · exact ⟨⊤, by simp, fun N' _ _ => by simp⟩
      · rintro x y ⟨N₁, h₁, hx⟩ ⟨N₂, h₂, hy⟩
        refine ⟨N₁ ⊓ N₂, by rw [Subgroup.coe_inf]; exact h₁.inter h₂, fun N' hN' hle => ?_⟩
        rw [map_add, map_add, hx N' hN' (hle.trans inf_le_left), hy N' hN' (hle.trans inf_le_right), add_zero]
    obtain ⟨N, hN, hNφ⟩ := hC
    haveI := hfin N hN
    haveI := Fintype.ofFinite (Kw ⧸ N.subgroupOf Kw)
    have hφ : φ ∈ GroundTheory.Automorphic.fixedVectors ρ' Kw := fun k hk => by
      have := hφK (j k) (e.symm k).2 (by rw [hcj]; exact hk)
      exact this
    have h0 := hNφ N hN le_rfl
    rw [GroundTheory.Automorphic.cosetSum_of_mem ρ' hφ, map_smul] at h0
    have hne : (Fintype.card (Kw ⧸ N.subgroupOf Kw) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [smul_eq_zero] at h0
    have h1 := h0.resolve_left hne
    rw [hT, sub_eq_zero] at h1
    exact h1
