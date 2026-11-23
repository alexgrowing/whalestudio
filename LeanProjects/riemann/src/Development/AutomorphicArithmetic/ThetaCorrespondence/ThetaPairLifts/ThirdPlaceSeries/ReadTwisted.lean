import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper.Read
section Record
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
end Record
end GlobalTheory.ThmAUpper.Read
namespace GlobalTheory.ThmAUpper
open Read GlobalTheory.ToricDenom GlobalTheory.FunObj.SqNum in
theorem read_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit _ hF w hw i j s hs1 hs2 T₀ ψc T _ h0 _ hψ hT'
  obtain ⟨_, _, -, hb, -⟩ := hF
  obtain ⟨-, ι, hι, -, hall⟩ := hfit.1.list _ (hfit.1.setting.inW1 hw)
  refine ⟨ι, hι, fun b => ?_⟩
  have hi := i.2
  let a : Fin D.R.m := ⟨D.R.m - i - 1, by omega⟩
  have ha : a.1 + 1 = D.R.m - i := by simp only [a]; omega
  have hsN : s ≤ BlochKatoReduction.Gen.NFun D.R + 1 := by
    have h3 : halfRank D i j ≤ GlobalTheory.ChiGrid.bigN D := by
      have a : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) ≤ GlobalTheory.ChiGrid.bigN D := by
        have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
        have h2 : (i + 1) * GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ i.2
        simp only [GlobalTheory.ChiGrid.rankV, GlobalTheory.ChiGrid.bigN, Ranks.r, mul_add] at *
        omega
      have e : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) = GlobalTheory.ChiGrid.rankV D i j + D.R.t + GlobalTheory.ChiGrid.sLen D := by
        simp only [GlobalTheory.ChiGrid.rankV]; ring
      unfold halfRank; omega
    have h12 : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.ChiGrid.bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
    omega
  obtain ⟨lam, hlam, -, hth⟩ := hall j a s b hs1 hsN
  have e1 : GlobalTheory.LamTie.cond0 D.host (lamOf d.G).w0 = condF d.G.pl := cond0_eq d.G hb
  have e2 : (lamOf d.G).lam0 (D.ntw.l (ex.nch.twI w)) j a =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    rw [lambdaGrid_apply, ha, ex.nch.twI_l, nuH, xiH_base p, mul_one, div_mul_eq_mul_div]
  have e3 : GlobalTheory.LamTie.phi D.host ∘ D.eTau = cmPhi D := rfl
  have e4 : (lamOf d.G).kap j a s ∘ D.eTau = kap D 1 i j s := by
    funext τ
    simp only [Function.comp, GlobalTheory.LamTie.LamDat.kap, lamOf, kap, Formalism.L2.Host.eExp, Equiv.symm_apply_apply, ha]
    have : (GlobalTheory.ChiGrid.num D 1 τ).e (j + 1) = ⌊(D.hc τ).e j⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e (j + 1) = _
      simp [GlobalTheory.SignedHC.GridData.extend]
    rw [this]
  rw [e1, e2] at hth
  obtain ⟨u, -, hth⟩ := hth
  obtain ⟨_, π, t, hπ, ht, hδ⟩ := hth _ (hfit.1.cond w hw)
  obtain ⟨_, π0, t0, -, ht0, hδ0⟩ := hth ∅ ⟨by simp, by simp, by simp⟩
  replace ht := fun q => isClassTerm_reindex D.eTau (ht q)
  replace ht0 := fun q => isClassTerm_reindex D.eTau (ht0 q)
  rw [e3, e4] at ht ht0
  have e5 : condQ (condF d.G.pl) (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = condF d.G.pl := by
    simp [condQ, belowSet]
  have s0 := sum_th_eq ht0 hδ0 (t := T₀) (by rw [e5]; exact h0)
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb D.ntw (ex.nch.twI w) (ex.nch.k' w)
  obtain ⟨e, he, hchar⟩ := exists_pow_char hfit.1.psi hw (hp.ties.psiVal w hw) (atSide D.ntw b ι) J
  have hc : condQ (condF d.G.pl) (belowSet (ex.nch.Q w)) ≠ ⊥ :=
    mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have key : ∀ a : ℤ, J (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (ex.nch.psi' w ^ a)) =
      u * atSide D.ntw b ι (T (ψc ^ (e * a))) := fun a => by
    refine thEval_eq_twisted hJ (fun q => ?_) ht hδ (hT' _)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hchar hc π hπ y
    have h2 : ∀ (x : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ), J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ (x ^ a : _ˣ)) =
        J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ x) ^ a := fun x => by
      have := congrArg Units.val (map_zpow (Units.map (J.comp
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _)).toMonoidHom) x a)
      rw [Units.val_zpow_eq_zpow_val] at this
      exact this
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, h2, ← h1, hψ, zpow_mul, Units.val_zpow_eq_zpow_val _ a, map_zpow₀]
  refine ⟨lam, J, if b then e else -e, hlam, by cases b <;> simp [he, he.neg_left], RingHom.ext hJ, fun a => ?_⟩
  rw [hJ, s0, hlam]
  cases b
  · have : BlochKatoReduction.Gen.psiAt false (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ (-a) := by simp [BlochKatoReduction.Gen.psiAt]
    rw [this, key]
    simp only [Bool.false_eq_true, if_false, mul_neg, neg_mul]
    ring
  · have : BlochKatoReduction.Gen.psiAt true (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ a := rfl
    rw [this, key]
    simp only [if_true]
    ring
end GlobalTheory.ThmAUpper
end
end
