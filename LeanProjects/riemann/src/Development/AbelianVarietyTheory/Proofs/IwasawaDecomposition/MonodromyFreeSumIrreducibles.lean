import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStableIsCompl

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_irr_list (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V), finrank ℂ V = n → a.N = 0 →
    ∃ L : List (WD h), (∀ z ∈ L, IsIrrWD z) ∧ WD.mk a = sumList L := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hN
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · refine ⟨[], by simp, ?_⟩
    show WD.mk a = WD.mk (WDRep.diag h (ι := Fin 0) fun i => i.elim0)
    exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [hn]), fun _ _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _⟩
  · haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
    have hP : ∃ d, ∃ Q : Submodule ℂ V, (∀ σ, ∀ v ∈ Q, a.ρ σ v ∈ Q) ∧ Q ≠ ⊥ ∧ finrank ℂ Q = d :=
      ⟨_, ⊤, fun _ _ _ => trivial, top_ne_bot, rfl⟩
    obtain ⟨Q, hQs, hQ0, hQd⟩ := Nat.find_spec hP
    have hmin : ∀ Q' : Submodule ℂ V, (∀ σ, ∀ v ∈ Q', a.ρ σ v ∈ Q') → Q' ≠ ⊥ →
        finrank ℂ Q ≤ finrank ℂ Q' := fun Q' hs hne => hQd ▸ Nat.find_min' hP ⟨Q', hs, hne, rfl⟩
    have hirr : (restrictρ a Q hQs).ρ.IsIrreducible := by
      haveI : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ0
      refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
      · exact bot_ne_top (α := Submodule ℂ Q) (congrArg Subrepresentation.toSubmodule hbt)
      · by_cases hU : U.toSubmodule = ⊥
        · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
        · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
          show U.toSubmodule = ⊤
          have hs : ∀ σ, ∀ v ∈ U.toSubmodule.map Q.subtype, a.ρ σ v ∈ U.toSubmodule.map Q.subtype := by
            rintro σ _ ⟨u, hu, rfl⟩
            exact ⟨_, U.apply_mem_toSubmodule σ hu, rfl⟩
          have hr : finrank ℂ (U.toSubmodule.map Q.subtype) = finrank ℂ U.toSubmodule :=
            Submodule.finrank_map_subtype_eq Q U.toSubmodule
          have hpos' : 0 < finrank ℂ U.toSubmodule :=
            Nat.pos_of_ne_zero fun h0 => hU (Submodule.finrank_eq_zero.mp h0)
          have hne : U.toSubmodule.map Q.subtype ≠ ⊥ := fun h0 => by
            rw [h0, finrank_bot] at hr; omega
          have h1 := hmin _ hs hne
          have h2 := Submodule.finrank_le U.toSubmodule
          exact Submodule.eq_top_of_finrank_eq (by omega)
    obtain ⟨T, hQT, hTs⟩ := GlobalTheory.WeilDeligne.PrimDecomp.exists_stable_isCompl E Ω A w h V a Q hQs
    have hiso : ((restrictρ a Q hQs).sum (restrictρ a T hTs)).Iso a := by
      refine ⟨Submodule.prodEquivOfIsCompl Q T hQT, fun σ v => ?_, fun v => ?_⟩
      · simp [map_add]
      · simp [hN]
    have hdim := Submodule.finrank_add_eq_of_isCompl hQT
    have hQpos : 0 < finrank ℂ Q := Nat.pos_of_ne_zero fun h0 => hQ0 (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨L, hL, hT⟩ := ih (finrank ℂ T) (by omega) T (restrictρ a T hTs) rfl rfl
    refine ⟨WD.mk (restrictρ a Q hQs) :: L, ?_, ?_⟩
    · refine List.forall_mem_cons.mpr ⟨?_, hL⟩
      obtain ⟨e, he, -⟩ := WD.iso_std (restrictρ a Q hQs)
      exact ⟨_, (WD.std (restrictρ a Q hQs)).2, (WD.sound (WD.iso_std _)).symm,
        isIrreducible_of_equiv e he hirr⟩
    · rw [show sumList (WD.mk (restrictρ a Q hQs) :: L) =
        WD.lpSum (WD.mk (restrictρ a Q hQs)) (sumList L) from rfl, ← hT, WD.lpSum_mk]
      exact (WD.sound hiso).symm

end GlobalTheory.WeilDeligne.IrrDecomp
