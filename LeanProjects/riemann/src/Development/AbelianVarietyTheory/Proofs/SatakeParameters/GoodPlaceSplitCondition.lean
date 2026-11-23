import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ValInert

theorem conjSelf (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hI : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : IsConjPl D.host w w := by
  intro x y hxy
  have hw : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal = w.asIdeal := hI
  let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hσ : ∀ z : 𝓞 D.host.E, ((σ z : 𝓞 D.host.E) : D.host.E) = D.host.conj (z : D.host.E) := fun z => rfl
  have key : w.asIdeal ≤ Ideal.comap σ w.asIdeal := by
    conv_lhs => rw [← hw]
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : σ (algebraMap _ _ s) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
      apply RingOfIntegers.ext
      rw [hσ]
      have hm : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) ∈ D.host.F := by
        show ((s : D.host.F) : D.host.E) ∈ D.host.F
        exact (s : D.host.F).2
      exact (GlobalTheory.DesignBC.mem_F_iff D _).1 hm
    rw [e, ← hw]
    exact Ideal.mem_map_of_mem _ hs
  have hy : y = σ x := RingOfIntegers.ext (hxy.trans (hσ x).symm)
  have hx : x = σ y := RingOfIntegers.ext (by rw [hσ, hxy, GlobalTheory.DesignBC.conj_conj])
  exact ⟨fun h => hy ▸ key h, fun h => hx ▸ key h⟩

theorem notSplit (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : IsConjPl D.host w w) : ¬ IsSplitPl D.host w := by
  rintro ⟨x, hx, hy⟩
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
    ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x, rfl⟩
  exact hy y hy' ((h x y hy').1 hx)

theorem xi_eq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (T : TupTied D C nch) (T' : TupTied D C' nch)
    (h' : HEq T T') : T.xi = T'.xi := by
  subst h
  cases h'
  rfl

theorem val_inert : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ c : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} → c = (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) := by
  intro _ hL D P X _ _ _ _ i hμ j hj w hG hI c hc
  have hcw := conjSelf D w hI
  have hLv : X.R.toLevCh.Is X.A.μ0 := X.recR.base.lev
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes X.R X.F hLv).2.1 _ w hG
  have hm0 : (X.R.C.mu0 j).UnrAt w := (X.R.C.isMu0 j).unr w fun k hk => hg (by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk')
  have hxu : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra h
    rcases (hLv.Q_ram _ w).1 h with h | ⟨PP, h, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr h)).2 hc
  have hxi : X.R.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq X.cfEq X.Tp P.tp X.tpEq]
  have hmu : (P.chr.e1 (D.naut.muC i)).1 = X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) := by
    rw [P.chr.muC i j hj, hxi, X.cfEq]
    rfl

  have hu : D.naut.unr (D.naut.locG (D.naut.muC i) w) := (P.chr.unr_iff _ w).2 (by rw [hmu]; exact hm0.mul hxu)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card _ hu).trans (D.naut.locG_dim _ w))
  have haa : a = a⁻¹ := by
    have e := (D.naut.csd_unr (D.naut.muC i) w w (D.naut.muC_csd i) hcw hu).2
    rw [ha, Multiset.map_singleton] at e
    exact Multiset.singleton_inj.1 e

  have hns := notSplit D w hcw
  have heu := (D.naut.etaTinv_def w).1
  have hee : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(-1 : ℂ)⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, D.naut.etaT_inert w hns, Multiset.map_singleton]
  have hc1 : c = a * (-1 : ℂ)⁻¹ := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ _ hu heu (D.naut.locG_dim _ w) hee, ha, Multiset.map_singleton] at hc
    exact (Multiset.singleton_inj.1 hc).symm
  have hcc : c = c⁻¹ := by
    have h1 : (-1 : ℂ)⁻¹ = -1 := by norm_num
    rw [hc1, mul_inv, inv_inv, ← haa, h1]

  have hte : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 =
      X.R.C.mu0 j * X.R.xiH (X.tupT (D.nd.mu i)) * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, hmu, P.chr.etaTinv, X.cfEq]
  have hut : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w :=
    (P.chr.unr_iff _ w).1 (by rw [D.naut.locG_tw]; exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu heu)
  have hc2 := P.chr.frob _ w hut
  rw [hc] at hc2
  have hc3 : c = (((X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ : ℂˣ) : ℂ)⁻¹ := by
    rw [Multiset.singleton_inj.1 hc2, hte]
    simp

  have hv : GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w =
      (X.R.C.mu0 j).val w * (X.R.xiH (X.tupT (D.nd.mu i))).val w * (X.R.C.eta.val w)⁻¹ := by
    rw [← GlobalTheory.LFun.val_eq_of_chrEq (hLv.mu0 j) w, ← GlobalTheory.LFun.val_eq_of_chrEq (hLv.xi _) w,
      ← GlobalTheory.LFun.val_eq_of_chrEq hLv.eta w]
    first
      | rfl
      | (simp only [GlobalTheory.DownLift.valV, GlobalTheory.DownLift.chiV, Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, GlobalTheory.LFun.val, GlobalTheory.LFun.locChar]; ext; simp)
      | (unfold GlobalTheory.DownLift.valV GlobalTheory.DownLift.chiV Formalism.IndefR.Lift.chrTh Formalism.IndefR.Links.LevCh.mu Formalism.IndefR.Lift.tup GlobalTheory.LFun.val GlobalTheory.LFun.locChar; simp)
  rw [hv, hcc, hc3, inv_inv]

end GlobalTheory.ValInert
