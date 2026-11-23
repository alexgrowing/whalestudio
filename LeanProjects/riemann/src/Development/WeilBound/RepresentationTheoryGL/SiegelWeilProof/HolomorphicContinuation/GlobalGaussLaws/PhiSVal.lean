import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HolValueAtFinsum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {Q : PX m n} (h : tens θ τ fr (fP c Q) Ψ ∈ schwartzA θ m n) :
    (phiS θ τ fr c Ψ Q).1 = tens θ τ fr (fP c Q) Ψ := by
  unfold phiS
  rw [dif_pos h]

theorem perPsi (hA : AbsThm) (hTM : TensMem) (hLo : LocOpEx) (hLi : LocInst) (hLS : LinSec) (hGS : GSplit)
    (hIa : GIauto) (hIk : GIk) (hIi : GIinv) (hId : GIdil) (hEis : EisStrong) (hLB : GLamBd) (hLsg : GLsing)
    (hCo : PositivityTheory.PfSWUS.CoefND) (hLZ : LNZ)
    {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ)
    (Q : PX V.rank n) (g : G D n) :
    HolValueAt (PositivityTheory.PfSWUS.eis ω H (phiS θ τ fr (cLoc l τ) Ψ Q) g) (s0 V n)
      (thetaInt ω ν (phiS θ τ fr (cLoc l τ) Ψ Q) g) := by
  have hl0 := hLZ D ψ θ l hcx.hψ hcx.hθ hcx.hl
  have hmem := hTM D n V θ l s τ ε fr hcx.hθ hl0 hcx.hs hcx.hfr Ψ hΨ
  obtain ⟨L, hL⟩ := hLo D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨sec, I, hsec, hI⟩ := hLS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ
  have hstd1 : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hcx.hψ, hcx.hχ, hcx.hη, hcx.hθ, hcx.hμ, hcx.hω, hcx.hH, hcx.hl, hcx.hs, hcx.hν,
      by rw [phiS_val (hmem 1).1]; exact (hmem 1).2⟩
  have hsecSec : IsSection χ (s0 V n) (fun x => sec 1 x) := by
    obtain ⟨𝓕, h𝓕⟩ := hcx.hμ
    have := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hcx.hψ χ hcx.hχ hcx.hη θ hcx.hθ μ 𝓕 h𝓕 ω hcx.hω
      l hcx.hl s hcx.hs _ hstd1.hΦ
    rw [hsec 1]
    exact this
  have hn0 : 0 < n := hcx.hn
  have hGD : GlobData ε (cLoc l τ) sL ρ (G D n) (P D n) (GF D n) ι (s0 V n) H sec I (lamSet ψ) := {
    ιcont := hcx.hι.1
    split := by
      intro g
      obtain ⟨x, y, S, r, hr, hg, hx⟩ := hGS D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL Ψ hΨ g
      refine ⟨x, y, S, r, hr, hg, fun y' => ⟨(hx y').1, fun Q' => ?_⟩⟩
      rw [hsec Q', hsL Q' y']
      exact (hx y').2 Q'
    Icont := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).1
    Ileft := by
      rw [hI 1]
      exact (hIa D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ).2
    Ik := by
      intro Q' g k hk
      rw [hI Q', hI (ρ k Q')]
      exact hIk D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL ρ hρ Ψ hΨ Q' g k hk
    Iinv := by
      intro g a b Q'
      rw [hI]
      exact hIi D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g a b Q'
    Idil := by
      intro g X a ha
      obtain ⟨U, F, hU, hU', hFc, hF⟩ := hId D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx Ψ hΨ g X a ha
      refine ⟨U, F, hU, hU', hFc, fun y => ⟨(hF y).1, fun t => ?_, fun r => ?_⟩⟩
      · rw [hI]
        exact (hF y).2.1 t
      · rw [hI]
        exact (hF y).2.2 r
    eis := hEis D n hn0 χ V.rank hcx.hχ hcx.hη H hcx.hH (s0 V n) _ hsecSec (s0 V n)
    Λadd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').1
    Λbd := fun L' hL' => (hLB D n ψ hcx.hψ L' hL').2
    Λsing := fun F hF hinv hz => hLsg D n ψ θ τ ι hcx.hψ hcx.hθ hcx.hι F hF hinv hz
    Λval := by
      rintro L' ⟨nb, lam, 𝓖, β, g', hcd, hβ, rfl⟩
      have := hCo D n V ψ χ θ μ ω H l s ν _ hstd1 hcx.hr nb lam 𝓖 hcd β hβ g'
      rw [hI 1, hsec 1]
      exact this }
  have := hA V.rank n ε (cLoc l τ) (tLoc l τ) p q e sL ρ hLD hgood (G D n) (P D n) (GF D n) ι (s0 V n) H sec I
    (lamSet ψ) hGD Q g
  rw [hsec Q, hI Q] at this
  exact this

theorem main : MainSt := by
  intro hA hFr hEmb hSig hSp hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hCR hTL hLZ
  intro D n V ψ χ θ μ ω H l s ν Φ hStd hR hn g
  obtain ⟨τ, hτ⟩ := hSig D n V s hR hStd.hs
  obtain ⟨ε, fr, hfr⟩ := hFr D V τ s (hStd.hs τ)
  obtain ⟨ι, hι⟩ := hEmb D n θ τ hStd.hθ
  have hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι :=
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, hR, hn, hfr, hι,
      hτ ε fr hfr⟩
  have hl0 := hLZ D ψ θ l hStd.hψ hStd.hθ hStd.hl
  obtain ⟨k, Pi, Ψi, hΨ, hsum⟩ := hSp D n V θ l s τ ε fr hStd.hθ hfr Φ.1 hStd.hΦ
  have hmem : ∀ i, tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) ∈ fockA θ V n l s :=
    fun i => hTM D n V θ l s τ ε fr hStd.hθ hl0 hStd.hs hfr (Ψi i) (hΨ i) (Pi i)
  let Φi : Fin k → schwartzA θ V.rank n := fun i => phiS θ τ fr (cLoc l τ) (Ψi i) (Pi i)
  have hval : ∀ i, (Φi i).1 = tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i) := fun i => phiS_val (hmem i).1
  have hΦeq : Φ = ∑ i, Φi i := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [hval]
    exact hsum
  have hstdT : ∀ T : Finset (Fin k), PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (∑ i ∈ T, Φi i) := fun T =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ => by rw [hval]; exact (hmem i).2⟩
  have hstdi : ∀ i, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (Φi i) := fun i =>
    ⟨hStd.hψ, hStd.hχ, hStd.hη, hStd.hθ, hStd.hμ, hStd.hω, hStd.hH, hStd.hl, hStd.hs, hStd.hν, by
      rw [hval]; exact (hmem i).2⟩
  have key : ∀ i, HolValueAt (PositivityTheory.PfSWUS.eis ω H (Φi i) g) (s0 V n) (thetaInt ω ν (Φi i) g) := fun i =>
    perPsi hA hTM hLo hLi hLS hGS hIa hIk hIi hId hEis hLB hLsg hCo hLZ hcx (hΨ i) (Pi i) g
  have hth : ∀ T : Finset (Fin k), thetaInt ω ν (∑ i ∈ T, Φi i) g = ∑ i ∈ T, thetaInt ω ν (Φi i) g := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 := hTL D n V ψ χ θ μ ω H l s ν 0 0 (by simpa using hstdT ∅) (by simpa using hstdT ∅) hR g
      rw [add_zero] at h0
      simp only [Finset.sum_empty]
      linear_combination -h0
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hTL D n V ψ χ θ μ ω H l s ν _ _ (hstdi a) (hstdT T) hR g, ih]
  choose σi hσi using fun i => hCR D n V ψ χ θ μ ω H l s ν (Φi i) (hstdi i) hR
  have hsect : ∀ z, sect ω H (∑ i, Φi i) z = fun x => ∑ i, sect ω H (Φi i) z x := by
    intro z
    funext x
    simp only [sect, map_sum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
  have heq : EqRight (fun z => ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z) (PositivityTheory.PfSWUS.eis ω H Φ g) := by
    refine ⟨∑ i, |σi i|, fun z hz => ?_⟩
    have hz' : ∀ i, σi i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (σi j)) (Finset.mem_univ i))) hz
    show ∑ i, PositivityTheory.PfSWUS.eis ω H (Φi i) g z = PositivityTheory.PfSWUS.eis ω H Φ g z
    rw [hΦeq]
    unfold PositivityTheory.PfSWUS.eis
    rw [hsect z, cosetSum_finsum _ _ _ _ _ (fun i _ => hσi i z (hz' i) g)]
  have hv : thetaInt ω ν Φ g = ∑ i, thetaInt ω ν (Φi i) g := by
    rw [hΦeq]
    exact hth Finset.univ
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.Rg.Sw.Glob
