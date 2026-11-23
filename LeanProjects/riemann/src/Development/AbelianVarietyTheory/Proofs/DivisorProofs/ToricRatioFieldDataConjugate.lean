import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DistributionRelationObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmARatio

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host

theorem twisted_value {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (𝓞 E))} {χ ξ : HChar E}
    {Λ : ℂ → ℂ} {m : ℕ} (hU : UnramFin E) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q))
    (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hm : m ≠ 0) (hord : ξ.OrderDvd m) (htr : TrivOnF ξ) (htame : ∀ v, ξ.TameAt v)
    (hram : ∀ v, ξ.UnrAt v ↔ v ∉ Q) (hΛ : IsHeckeL (χ * ξ) Λ) :
    ∃ (ψc : PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) (T : (PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) → ℂ),
      (∀ y, finPart ξ y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 (belowSet Q)) χ ψ (T ψ)) ∧ Λ s = T ψc := by
  classical
  have hp : ∀ x, ξ.1 x ^ m = 1 := fun x => by
    have := congrArg (fun c : HChar E => c.1 x) hord
    simpa using this
  have hχu : ∀ v ∈ belowSet Q, ∀ P, Over P v → χ.UnrAt P := fun v hv P hP => by
    have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rwa [expIn, multiplicity_eq_zero.2 (hQ v hv).2, expAt_zero_iff] at e
  have hξu : ∀ v ∉ belowSet Q, ∀ P, Over P v → ξ.UnrAt P := fun v hv P hP =>
    (hram P).2 fun h => hv (Finset.mem_image.2 ⟨P, h, HeightOneSpectrum.ext hP⟩)
  have hv : IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
    refine ⟨hχ.1.mul (GlobalTheory.ToricDistribution.isUnitary_of_pow hm hp), hχ.2.1.mul htr, fun k => ?_,
      fun v P hP => ⟨fun hv => ?_, fun hv n => ?_⟩⟩
    · rw [HChar.inf_mul, GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one]
      exact hχ.2.2.1 k
    · intro x hx hx1
      rw [HChar.loc_mul, hχu v hv P hP x hx, htame P x hx hx1, one_mul]
    · rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) n]
      refine forall_congr' fun x => forall_congr' fun hx => ?_
      rw [HChar.loc_mul, hξu v hv P hP x hx, mul_one]
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have hex : ∀ q : HeightOneSpectrum (OF E), ∃ P, q ∈ belowSet Q → P ∈ Q ∧ Over P q := fun q => by
    by_cases e : q ∈ belowSet Q
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 e
      exact ⟨P, fun _ => ⟨hP, over_below P⟩⟩
    · exact ⟨P₀, fun h => absurd h e⟩
  choose Pq hPq using hex
  have t := GlobalTheory.ToricDistributionObj.toricSumFormula_holds E I φ hφ s κ 𝔣 (belowSet Q) (χ * ξ) Pq Λ hU hs hb hQ hv
    (fun q hq => (hPq q hq).2) hΛ
  rw [Finset.filter_false_of_mem, Finset.prod_empty, mul_one] at t
  swap
  · intro q hq h
    refine (hram (Pq q)).1 (fun x hx => ?_) (hPq q hq).1
    have := h x hx
    rwa [HChar.loc_mul, hχu q hq _ (hPq q hq).2 x hx, one_mul] at this
  have hker : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ (finPart ξ).ker := by
    refine sup_le ?_ fun y hy => ?_
    · rintro _ ⟨k, rfl⟩
      have := finPart_mul_inf ξ k
      rwa [GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one] at this
    · refine GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level htr (fun v => ?_) hy
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P _ => htame P⟩
        rw [pow_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
      · exact ⟨0, by rw [pow_zero]; exact one_dvd _, fun P hP => (ξ.unrAt_iff P).1 (hξu v hv P hP)⟩
  have hψ : ∀ y, finPart ξ y = QuotientGroup.lift _ (finPart ξ) hker (QuotientGroup.mk y) := fun _ => rfl
  obtain ⟨hfin, S, hS, hT⟩ := (isTwistedSum_iff_isToricSum hψ _).2 t
  exact ⟨_, fun ψ => ∑ᶠ q : PicO (condQ 𝔣 (belowSet Q)), ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0, hψ,
    fun ψ => ⟨hfin, S, hS, rfl⟩, hT⟩

theorem dvd_cond0 {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (v : HeightOneSpectrum (OF D.host.E))
    (h : v.asIdeal ∣ GlobalTheory.FunObj.SqNum.condF P) : v.asIdeal ∣ GlobalTheory.LamTie.cond0 D.host (P.w P.v0) := by
  obtain ⟨u, hu, hd⟩ := (v.prime.dvd_finset_prod_iff _).1 h
  have e : v = u := HeightOneSpectrum.ext
    (associated_iff_eq.1 ((v.irreducible.dvd_irreducible_iff_associated u.irreducible).1 (v.prime.dvd_of_dvd_pow hd)))
  subst e
  rcases P.mem_S0_of_sum_eq.1 hu with h0 | h1
  · have e : below (P.w P.v0) = v := (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))).trans h0.symm
    unfold GlobalTheory.LamTie.cond0
    rw [e]
    exact dvd_mul_left _ _
  · refine Dvd.dvd.mul_right (Dvd.dvd.pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    push_cast
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1 with h | h | h | h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.ThmARatio

theorem GlobalTheory.ThmARatio.values_as_toric_sums : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit _ hF hTor w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨_, _, hfd, hb, -⟩ := hF
  have hχ : fam d.G p.P.A3.A.μ0 i j (some (decide (D.what₂.places.resChar w = D.host.pde))) =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    unfold fam GlobalTheory.FunObj.SqNum.delOf Formalism.L2.Host.CharFrame.delAt
    by_cases h : D.what₂.places.resChar w = D.host.pde
    · simp only [h, decide_true, cond_true, if_true]
    · simp only [h, decide_false, cond_false, if_false]
  obtain ⟨T₀, ⟨hv, h0⟩, hne, hL, -⟩ := hTor i j s hs1 hs2 (some (decide (D.what₂.places.resChar w = D.host.pde)))
  rw [hχ] at hv h0 hL
  have hP := p.Tp.psi_is w hw
  obtain ⟨a, ha⟩ := hP.ord
  have hQ := (GlobalTheory.ToricDenom.placesBelow_splitCoprimeConductor_of_admissible (hfit.1.cond w hw) (𝔣 := GlobalTheory.FunObj.SqNum.condF d.G.pl) fun P h =>
    (hfit.1.list _ (hfit.1.setting.inW1 hw)).1 P (GlobalTheory.ThmARatio.dvd_cond0 d.G.pl _ h)).1
  obtain ⟨ψc, T, h1, h2, h3⟩ := GlobalTheory.ThmARatio.twisted_value hfd.2.2.2.2.2.2.1 hfd.2.2.1 hs1 hb hQ hv
    (pow_ne_zero a (D.what₂.places.resChar_prime w).ne_zero) ha hP.triv hP.tame hP.ram hΛ
  exact ⟨T₀, ψc, T, hv, h0, hne, (hL Λd hΛd).symm, h1, h2, h3⟩

end
