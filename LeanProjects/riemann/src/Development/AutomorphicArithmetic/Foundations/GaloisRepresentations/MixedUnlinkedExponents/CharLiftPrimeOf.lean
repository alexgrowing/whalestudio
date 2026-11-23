import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def CharSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
      (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : SmIrr (GL (Fin n) (u.adicCompletion L))), π.IsLocComp v τ → P.IsLocComp u T →
      ∀ (ξ : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) →
        HasSupport T.ρ (GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
          fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def CharLiftPrime : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub L a),
    GlobalTheory.GalCut.IsLift π P → GlobalTheory.RoadU.CharLift π P

def UnlThru : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) s s', SuppAt π v s → SuppAt P w.1 s' → GlobalTheory.RoadU.Unlinked s →
      ∀ ζ hζ, IrrGL.ofChar ζ hζ ∈ s' → Thru w ζ → ∀ y ∈ s', IrrGL.ofChar ζ hζ ≠ y.nu 1 ∧ y ≠ (IrrGL.ofChar ζ hζ).nu 1

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chs_cons (ξ : kˣ →* ℂˣ) (h : IsSmoothChar ξ) (s : Multiset (IrrGL k)) : chs (IrrGL.ofChar ξ h ::ₘ s) = ξ ::ₘ chs s := by
  have e : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ h = IrrGL.ofChar ζ hζ := ⟨ξ, h, rfl⟩
  refine Multiset.filterMap_cons_some _ _ _ ?_
  rw [dif_pos e]
  obtain ⟨_, h2⟩ := e.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

theorem chs_cons_of_not {y : IrrGL k} (h : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (s : Multiset (IrrGL k)) :
    chs (y ::ₘ s) = chs s := Multiset.filterMap_cons_none _ _ (dif_neg h)

theorem chs_map {ι : Type} (t : Multiset ι) (ξ : ι → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) :
    chs (t.map fun j => IrrGL.ofChar (ξ j) (hξ j)) = t.map ξ := by
  induction t using Multiset.induction with
  | empty => rfl
  | cons a t ih => rw [Multiset.map_cons, chs_cons, ih, Multiset.map_cons]

theorem card_chs_le (s : Multiset (IrrGL k)) (h : ∀ y ∈ s, 0 < y.1) :
    Multiset.card (chs s) ≤ (s.map Sigma.fst).sum ∧
      (Multiset.card (chs s) = (s.map Sigma.fst).sum → ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) := by
  induction s using Multiset.induction with
  | empty => exact ⟨le_rfl, fun _ y hy => absurd hy (Multiset.notMem_zero _)⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    have ha := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases c : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, a = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := c
      have e : (IrrGL.ofChar ξ hξ).1 = 1 := rfl
      rw [chs_cons, Multiset.card_cons, e]
      refine ⟨by omega, fun H y hy => ?_⟩
      rcases Multiset.mem_cons.1 hy with rfl | hy
      · exact ⟨ξ, hξ, rfl⟩
      · exact h2 (by omega) y hy
    · rw [chs_cons_of_not c]
      exact ⟨by omega, fun H => by omega⟩

theorem eq_of_chs {s t : Multiset (IrrGL k)} (hs : ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (ht : ∀ y ∈ t, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (h : chs s = chs t) : s = t := by
  have key : ∀ s : Multiset (IrrGL k), (∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) →
      s = (chs s).map fun ξ => if h : IsSmoothChar ξ then IrrGL.ofChar ξ h else IrrGL.ofChar 1 isSmoothChar_one := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; rfl
    | cons a s ih =>
      intro H
      obtain ⟨ξ, hξ, rfl⟩ := H a (Multiset.mem_cons_self _ _)
      rw [chs_cons, Multiset.map_cons, dif_pos hξ, ← ih fun y hy => H y (Multiset.mem_cons_of_mem hy)]
  rw [key s hs, key t ht, h]

end

theorem charSupp_of (h1 : GamMixed) (h2 : NmEq) (h3 : SuppFacts) : CharSupp := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v u hu τ T hτ hT ξ hξ hs
  obtain ⟨⟨s', hs'⟩, huniq, hdeg, -⟩ := h3 L n hn P u
  have H := h1 K L hp n hn π P hW v ⟨u, hu⟩ _ s' ⟨τ, hτ, hs⟩ hs'
  obtain ⟨-, hsum, hpos⟩ := hdeg s' hs'
  obtain ⟨c1, c2⟩ := card_chs_le s' hpos
  rw [up, GlobalTheory.RoadU.chars, chs_map, h2 K L v ⟨u, hu⟩, Multiset.map_map] at H
  have hc : Multiset.card ((chs s').filter (Thru (v := v) ⟨u, hu⟩)) = n := by rw [H]; simp
  have hle := Multiset.filter_le (Thru (v := v) ⟨u, hu⟩) (chs s')
  have hc' := Multiset.card_le_card hle
  have e := Multiset.eq_of_le_of_card_le hle (by omega)
  have es : s' = GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    refine eq_of_chs (c2 (by omega)) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨_, _, rfl⟩
    · rw [← e, H, GlobalTheory.RoadU.chars, chs_map]; rfl
  obtain ⟨T', hT', hs''⟩ := hs'
  have h1 : (CG.mk P).IsLoc u (Quotient.mk _ T) := hT
  have h2 : (CG.mk P).IsLoc u (Quotient.mk _ T') := hT'
  obtain ⟨φ⟩ := Quotient.exact (CG.IsLoc.unique L n _ u _ _ h2 h1)
  exact es ▸ hs''.of_equiv φ

theorem charLiftPrime_of (h : CharSupp) : CharLiftPrime := by
  intro K L _ _ _ _ _ _ _ _ hp a ha π P hL
  refine ⟨hL, fun v u _ => h K L hp a ha π P ?_ v u⟩
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
    (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL K a π)] with w hw
  obtain ⟨B, hB⟩ := hw
  exact fun f hf => ⟨B, hB, hL.sat w f B hf hB⟩

def UnlThruOf : Prop := GamMixed → Spread → ChsFacts → NormVal → PolFacts → UnlThru

end UpperTheory.Gal.GamX
