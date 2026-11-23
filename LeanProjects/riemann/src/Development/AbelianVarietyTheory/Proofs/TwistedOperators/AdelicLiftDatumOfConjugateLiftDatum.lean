import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjChrEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjLiftData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_galConj_mu (R : RealDat D A Ks) (hL : R.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (μ' : (AE D)ˣ →* Circle) (hμ : ChiAt R i σ μ') :
    ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add, RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hL.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hL.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

theorem exists_galConj_eta (R : RealDat D A Ks) (hL : R.Is A.μ0) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (hσ : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s) (η' : (AE D)ˣ →* Circle) (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [GlobalTheory.EtaConjChar.twVal_half _ P (GlobalTheory.EtaConjChar.locK_eq_one hH hη.2.1 P), GlobalTheory.EtaConjChar.twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl,
    ← hL.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl, ← hy1, ← hy2, hσ.1]

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q : Finset (Pl D.host.E)} (hQ : Q = ∅) (s : ℂ →+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    s ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ => χ, ξ⟩ x : ℂˣ) : ℂ) =
      ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (Units.map s.toMonoidHom).comp (χ PP), ξ'⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp [h1]

theorem is_congr {Γ Gr W : Type} [Group Γ] [Group Gr] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gr}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gr} (hJ : J = J') {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    (h : ∀ x hx hx', χ ⟨x, hx⟩ = χ' ⟨x, hx'⟩) {I : Type} [Fintype I] {y : I → Gr} {H : HMod (Gr → W)}
    (hH : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) : H.Is (Bridge.AdForms ι ρ J' χ') (Bridge.adInner ι J' y) := by
  subst hJ
  obtain rfl : χ = χ' := MonoidHom.ext fun x => h x.1 x.2 x.2
  exact hH

set_option maxHeartbeats 1000000 in

theorem isLiftDataC_of_liftData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ μ' η', ChiAt R i σ μ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ s m, GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io ∧ IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) ∧ Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y ∧ H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L _ i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hL
  classical
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨s, hs⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL D.what₂.embLL σ
  have hE : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  obtain ⟨hω, hvec, hio, -⟩ := hL
  obtain ⟨μH, hμ1, hμ2⟩ := exists_galConj_mu R hC.lev i σ s hE μ' hμ
  obtain ⟨ηH, hη1, hη2⟩ := exists_galConj_eta R hC.lev σ s hE η' hη
  have hQ := GlobalTheory.LiftLower.Q_base hC.lev
  let m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ := fun PP =>
    (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (R.chi ((i : ℕ) + 1) PP)⁻¹
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact GlobalTheory.LiftScalarCompare.primeToHost hC.lev PP hPP
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsConjChars R i A.μ0 s μ' η' m := by
    refine ⟨μH, ηH, hμ1, hη1, hμ2, hη2, fun PP hPP a k u hk hu => ?_⟩
    have hg : PP ∈ R.Pg := hPP.resolve_right (by simp [hQ])
    have h1 := hμ1 PP k
    have h2 := hC.lev.chi i PP hg a k u hk hu
    rw [hC.lev.xi_base, mul_one] at h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal, Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one] at h1
    apply Units.ext
    rw [h1, ← h2]
    rfl
  have hlv : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      (R.datWp i R.triv) (R.Q A.μ0) m f₀ f := by
    have hv := hvec.vec
    rw [hQ]
    unfold Datum.IsThPVecOf at hv
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec
    have hq : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
        Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
      intro y
      simp [Datum.omegaQ]
    simp only [GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv, hq]
    exact hv
  obtain ⟨χ', hχ, hH⟩ := hf.model
  have key : ∀ k : levJ R i A.μ0, χ' k = levFn (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)
      (Formalism.UG.bc (Lev.swapAE D) k.1.1) := fun k => Units.ext <| (hχ k).elim fun y hy =>
    hy.2.symm.trans ((hs y).symm.trans ((congrArg s hy.1).trans
      (levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hQ (s : ℂ →+* ℂ) (fun PP => (R.chi ((i : ℕ) + 1) PP)⁻¹) (R.xiR A.μ0) m _)))
  have hH' := is_congr (GlobalTheory.Survey.LevelVectorSizeBounds.grp_triv R i A.μ0 m).symm
    (χ' := GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (fun x hx _ => key ⟨x, hx⟩) hH
  refine ⟨s, m, ⟨hC, hp, hE, GlobalTheory.Survey.LevelVectorSizeBounds.isLocal_triv R, hm, hω, hvec.onb, hlv, fun P => hvec.theta P, hf.coef, hio⟩,
    hC.models.νV i A.μ0, (R.B.L i A.μ0).pres.reps, hH'⟩

end GlobalTheory.ConjLiftData

end
