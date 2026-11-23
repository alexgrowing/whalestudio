import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrystallineLatticeOfJumpPoints
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace GlobalTheory.Survey.InertPlacesGoodSet

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

theorem inert_jacobi {D : D7} {l : ℕ} (h : TwistedPlaces.InertK D l) :
    l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) l ≠ 1 := by
  unfold TwistedPlaces.InertK Host.cls primeClass at h
  split_ifs at h with h1 h3 h4 h5
  all_goals first
    | exact ⟨h1, h3, h4, h5⟩
    | simp at h

theorem eleven_le {D : D7} {l : ℕ} (hl : l.Prime) (h : TwistedPlaces.InertK D l) (hs : 10 ≤ D.host.splitBound) : 11 ≤ l := by
  by_contra hlt
  exact (inert_jacobi h).2.2.2 (D.host.split_small l hl (fun e => (inert_jacobi h).1 (e ▸ D.host.two_mem_small)) (by omega))

section
variable {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL}

attribute [local instance] nLet_neZero

theorem rowL_of_wordsB {C₂ : ℝ} (hA : WachCoordinates.Conclusion2 D C₂) (h11 : 11 ≤ D.nd.l i) {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) (hB : WordsB L C₂ (D.nd.l i) Wd) :
    RowL i r ρ π w hw Cx (C₂ * ((nLet i w hw : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ))) := by
  intro T₁ T₂ F h2 h1 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hrk : finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have := hA (D.nd.l i) (D.nbr i w hw).Kw Cx.LL (nLet i w hw) (WW HW i w hw Cx hG).emb
    ⟨hcA.1, Cx.LL.2, rfl, (WW HW i w hw Cx hG).emb_bij, (WW HW i w hw Cx hG).emb_σ, (WW HW i w hw Cx hG).v_l⟩
    (by rw [hp]; exact h11) T₁ T₂ F ⟨hb.split _, T₁.mtop, hb.dvr⟩
    ⟨T₁.fdim, T₁.mtop, T₁.cont, (hb.t1 T₁ h1).1⟩ ⟨T₂.fdim, T₂.mtop, T₂.cont, (hb.t2 T₂ h2).1⟩ hF
    D.R.r Wd.b Wd.w Wd.S Wd.η (TwistedPlaces.jA L (D.nd.l i)) Wd.up Wd.sz hrk (le_max_left _ _) hB.j_lt
    (fun a τ hτ => (hb.t1 T₁ h1).2.1 a τ hτ) hb.thick_or hB.par hB.clusters
  rw [hp] at this
  exact this

theorem setting_of_wordsNT (h2l : D.nd.l i ≠ 2) {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) (hN : WordsNT Wd)
    (ft : Fintype (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1))
    (T₁ T₂ : LatW i w hw Cx) (F : LatHom T₁.L T₂.L) (h2 : IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂) (h1 : IsSubOfTwistedDualSums i r w hw Cx T₁)
    (hF : F.Onto) :
    TruncatedSeriesCountingBounds.HidaSetting ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (WW HW i w hw Cx hG) T₁ T₂ F
      Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi :=
  ⟨caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram h2l,
    ⟨(hb.t1 T₁ h1).1, (hb.t2 T₂ h2).1, hF⟩, hN.eta_lt, (hb.t1 T₁ h1).2.1, (hb.t2 T₂ h2).2 ft,
    fun a ha => (hb.thick_or a).resolve_left ha, (hb.t1 T₁ h1).2.2⟩

theorem setCS_of_wordsAT (h11 : 11 ≤ D.nd.l i) {Wd : WordDat (nLet i w hw)} {d : ℕ}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) (hC : WordBaseC (HW := HW) ρ π hG Wd)
    (hA : WordsAT (D.nd.l i) Wd d)
    (T₁ T₂ : LatW i w hw Cx) (F : LatHom T₁.L T₂.L) (h2 : IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂) (h1 : IsSubOfTwistedDualSums i r w hw Cx T₁)
    (hF : F.Onto) :
    RamifiedCoefficientChains.SetCS (WW HW i w hw Cx hG) d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  refine ⟨caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega), by rw [hp]; exact h11,
    hA.even, hb.dvr, by rw [hp]; exact hC.zeta, ⟨(hb.t1 T₁ h1).1, (hb.t2 T₂ h2).1, hF⟩, fun a τ hτ => ?_,
    hC.mult T₂ h2, fun a => by rw [hp]; exact hA.big1 a, hA.big2⟩
  have h := (hb.t1 T₁ h1).2.1 a τ hτ
  intro z hz
  have hz' := h z hz
  have ht := hA.typ a
  unfold WordDat.win at hz'
  unfold RamifiedCoefficientChains.JumpWinS
  by_cases e : (a.val + d) % 2 = 0
  · have hu : ¬ Wd.up a = true := fun h => ht.1 h e
    rw [if_neg hu] at hz'
    rw [if_pos e]
    simp only [Set.mem_union, Set.mem_Icc] at hz' ⊢
    push_cast
    omega
  · rw [if_pos (ht.2 e)] at hz'
    rw [if_neg e]
    simp only [Set.mem_union, Set.mem_Icc] at hz' ⊢
    push_cast
    omega

end

end GlobalTheory.Survey.InertPlacesGoodSet
