import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfUniq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isoV_map_mulChi {N : ℕ} {V V' : Submodule ℂ (Sm E N)} (χ : HChar E) (h : IsoV V V') :
    IsoV (V.map (mulChi N χ).toLinearMap) (V'.map (mulChi N χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := h
  let S : V ≃ₗ[ℂ] V.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V
  let S' : V' ≃ₗ[ℂ] V'.map (mulChi N χ).toLinearMap := (mulChi N χ).submoduleMap V'
  refine ⟨(S.symm.trans T).trans S', fun o φ ψ hψ => ?_⟩
  obtain ⟨φ, rfl⟩ := S.surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective ψ
  have h1 : ψ.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 + opAdd χ o • φ.1 := by
    apply (mulChi N χ).injective
    rw [← act_mulChi]
    exact hψ
  have hm : act o φ.1 ∈ V := by
    have h2 : ((opMul χ o : ℂˣ) : ℂ) • act o φ.1 ∈ V := by
      have h3 := V.sub_mem ψ.2 (V.smul_mem (opAdd χ o) φ.2)
      rwa [h1, add_sub_cancel_right] at h3
    exact (Submodule.smul_mem_iff _ (Units.ne_zero _)).1 h2
  let φo : V := ⟨act o φ.1, hm⟩
  have hψ' : ψ = ((opMul χ o : ℂˣ) : ℂ) • φo + opAdd χ o • φ := Subtype.ext h1
  rw [hψ']
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add, map_smul]
  change ((opMul χ o : ℂˣ) : ℂ) • mulChi N χ (T φo).1 + opAdd χ o • mulChi N χ (T φ).1 = act o (mulChi N χ (T φ).1)
  rw [act_mulChi, ← hT o φ φo rfl, map_add, map_smul, map_smul]

theorem sIso_twPart (χ : HChar E) {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨M, V⟩ := x
  obtain ⟨M', V'⟩ := y
  obtain ⟨h1, h2⟩ := h
  cases h1
  exact ⟨rfl, isoV_map_mulChi χ h2⟩

def R (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ) : Prop :=
  HasInfCharGL x.2 τ m ∧ x.2 ≠ ⊥

def infs {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List (Multiset ℂ) := List.ofFn fun i => P.m i τ

theorem forall₂_R {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : List.Forall₂ (R τ) (parts P) (infs P τ) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [parts, infs], fun i h₁ h₂ => ?_⟩
  have hi : i < P.c := by simpa [infs] using h₂
  have key : ∀ (x : Σ M : ℕ, Submodule ℂ (Sm E M)) (m : Multiset ℂ), x = ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ →
      m = P.m ⟨i, hi⟩ τ → R τ x m := by
    rintro x m rfl rfl
    exact ⟨P.inf _ τ, (P.discrete _).ne_bot⟩
  exact key _ _ (by simp [parts]) (by simp [infs])

theorem R_twPart (χ : HChar E) {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {m : Multiset ℂ} (h : R τ x m) :
    R τ (twPart χ x) (m.map (· + expo χ τ)) := by
  obtain ⟨M, V⟩ := x
  refine ⟨GlobalTheory.BCT.TwistDisc.hasInfCharGL_map h.1 χ, fun h0 => h.2 ?_⟩
  exact (Submodule.map_eq_bot_iff (e := mulChi M χ)).1 h0

theorem eq_of_forall₂ {τ : E →+* ℂ} : ∀ {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {l₁ l₂ : List (Multiset ℂ)},
    List.Forall₂ (R τ) l l₁ → List.Forall₂ (R τ) l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    rw [LemDd.InfUniq_holds E _ _ τ _ _ h₁.2 h₁.1 h₂.1, eq_of_forall₂ t₁ t₂]

theorem infs_eq_of_strict {n : ℕ} {P P' : Pre E n} (h : Strict P P') (τ : E →+* ℂ) : infs P τ = infs P' τ := by
  obtain ⟨-, hc, hm⟩ := h
  unfold infs
  rw [List.ofFn_congr hc]
  congr 1
  funext i
  rw [hm]
  rfl

end PositivityTheory.Rg.BcB.F.FX.Bo.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  have hF : List.Forall₂ SIso (parts D) (parts D') := by
    rw [hJ, hJ']
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_twPart χ₂ h))
  have hc : D.c = D'.c := by
    have := hF.length_eq
    simpa [parts] using this
  refine ⟨hF, hc, fun i => ?_⟩
  funext τ
  have hI : ∀ {Q : Pre E a} {S : Pre E b} {Z : Pre E n}, IsJoin χ₁ χ₂ Q S Z →
      infs Z τ = (infs Q τ).map (fun m => m.map (· + expo χ₁ τ)) ++ (infs S τ).map (fun m => m.map (· + expo χ₂ τ)) := by
    intro Q S Z hZ
    refine eq_of_forall₂ (forall₂_R Z τ) ?_
    rw [hZ]
    refine List.rel_append ?_ ?_
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R Q τ).imp fun _ _ h => R_twPart χ₁ h))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        ((forall₂_R S τ).imp fun _ _ h => R_twPart χ₂ h))
  have e : infs D τ = infs D' τ := by
    rw [hI hJ, hI hJ', infs_eq_of_strict ha, infs_eq_of_strict hb]
  unfold infs at e
  rw [List.ofFn_congr hc.symm (fun j => D'.m j τ)] at e
  have := congrFun (List.ofFn_injective e) i
  simpa using this

end PositivityTheory.Rg.BcB.F.FX.Bo

end
