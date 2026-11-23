import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

section EnlAux

variable {B B' : Base}

def enlEmb (hR : Set.range B.embLL ⊆ Set.range B'.embLL) : B.LL →+* B'.LL :=
  (RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))).comp B.embLL.rangeRestrict)

theorem enlEmb_spec (hR : Set.range B.embLL ⊆ Set.range B'.embLL) (x : B.LL) :
    B'.embLL (enlEmb hR x) = B.embLL x := by
  have h := congrArg Subtype.val ((RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).apply_symm_apply
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))) (B.embLL.rangeRestrict x)))
  exact h

def ksEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.Ks ≃ₐ[ℚ] B'.Ks :=
  (B.Ks.equivMap B.embLL.toRatAlgHom).trans ((IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm).trans (B'.Ks.equivMap B'.embLL.toRatAlgHom).symm)

theorem ksEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.Ks) : B'.embLL ((ksEquiv hK x : B'.Ks) : B'.LL) = B.embLL (x : B.LL) := by
  have h3 : (B'.Ks.equivMap B'.embLL.toRatAlgHom) (ksEquiv hK x) =
      IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm (B.Ks.equivMap B.embLL.toRatAlgHom x) := by
    exact (B'.Ks.equivMap B'.embLL.toRatAlgHom).apply_symm_apply _
  have h4 := congrArg Subtype.val h3
  rw [IntermediateField.coe_equivMap_apply] at h4
  rw [RingHom.toRatAlgHom_apply] at h4
  rw [h4]
  change ((B.Ks.equivMap B.embLL.toRatAlgHom x : B.Ks.map B.embLL.toRatAlgHom) : ℂ) = _
  rw [IntermediateField.coe_equivMap_apply]
  rfl

def oEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.O ≃+* B'.O := RingOfIntegers.mapRingEquiv (ksEquiv hK).toRingEquiv

theorem oEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.O) : B'.embLL (B'.OtoLL (oEquiv hK x)) = B.embLL (B.OtoLL x) := by
  have h := RingOfIntegers.mapRingEquiv_apply (ksEquiv hK).toRingEquiv x
  change B'.embLL (((oEquiv hK x : B'.Ks)) : B'.LL) = B.embLL ((x : B.Ks) : B.LL)
  rw [show (oEquiv hK x : B'.Ks) = ksEquiv hK (x : B.Ks) from h]
  exact ksEquiv_spec hK x

end EnlAux

section EnlAux2

variable {B B' : Base}

theorem enlEmb_LL0 (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hL : B'.embLL '' (B'.LL0 : Set B'.LL) = B.embLL '' (B.LL0 : Set B.LL)) {x : B.LL} (hx : x ∈ B.LL0) :
    enlEmb hR x ∈ B'.LL0 := by
  obtain ⟨x', hx', he⟩ : B.embLL x ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hL ▸ ⟨x, hx, rfl⟩
  have : enlEmb hR x = x' := B'.embLL.injective (by rw [enlEmb_spec, he])
  rw [this]
  exact hx'

theorem enlEmb_Ks (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hK : B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL)) {x : B'.LL} (hx : x ∈ B'.Ks) :
    ∃ x₀ ∈ B.Ks, enlEmb hR x₀ = x := by
  obtain ⟨x₀, hx₀, he⟩ : B'.embLL x ∈ B.embLL '' (B.Ks : Set B.LL) := hK ▸ ⟨x, hx, rfl⟩
  exact ⟨x₀, hx₀, B'.embLL.injective (by rw [enlEmb_spec, he])⟩

theorem coefficientFieldEnlarge_mem_larger_fixedField (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hL : B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL)) {x : B.LL} (hx : x ∈ B.LL0) :
    enlEmb hR x ∈ B'.LL0 := by
  obtain ⟨x', hx', he⟩ : B.embLL x ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hL ⟨x, hx, rfl⟩
  have : enlEmb hR x = x' := B'.embLL.injective (by rw [enlEmb_spec, he])
  rw [this]
  exact hx'

end EnlAux2

section CdAux

abbrev withCd (D : D7) (c₀ : CDHaar) : D7 := { D with cd := c₀ }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {r : ℕ}

theorem finVol_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (V : HSp D) :
    Formalism.L2.Pj.FinVol (D := withCd D c₀) V ↔ Formalism.L2.Pj.FinVol (D := D) V := by
  subst h
  rfl

theorem cuspL2_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) :
    Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu ↔ Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu := by
  subst h
  rfl

theorem peterssonDefinite_iff_of_eq_compactDualHaar (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)
    (h₁ : Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu) (h₂ : Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu) :
    Formalism.L2.Pj.L2DefiniteCuspForms (D := withCd D c₀) U σ V dict mu h₁ ↔ Formalism.L2.Pj.L2DefiniteCuspForms (D := D) U σ V dict mu h₂ := by
  subst h
  rfl

end CdAux

theorem exists_adelicCore_transport_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  intro B B' f f' T T' w w' Z Z' hX Wt z hE hf hC
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  obtain ⟨h1, hKs, hLL0, hR⟩ := hE
  have hι := enlEmb_spec hR
  have hι0 := fun x (hx : x ∈ B.LL0) => coefficientFieldEnlarge_mem_larger_fixedField hR hLL0 hx
  have hιK := fun x (hx : x ∈ B'.Ks) => enlEmb_Ks hR hKs hx
  have hO := oEquiv_spec hK
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hff := eq_of_heq hf
  subst hff
  obtain ⟨hL, hCa, hDim, hpb⟩ := hC
  have hcd : (w'.st Z').toD7.cd = (w.st Z).toD7.cd := Tr.cd_eq _ _
  let g : z.core.Q.c.F →+* _ := (enlEmb hR).comp ((algebraMap (↥z.core.Q.c.F) (w.st Z).toD7.what₂.LL) : z.core.Q.c.F →+* B.LL)
  let Q' : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (z.core.Q.H), l := (z.core.Q.l), c := (z.core.Q.c), Dw := (z.core.Q.Dw), Xo := (z.core.Q.Xo),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q', U := (z.core.U), V := (z.core.V), dict := (z.core.dict), mu := (z.core.mu),
          Kf := (z.core.Kf), pb := (z.core.pb) }
      cE := (z.core.cE), chiW := (z.core.chiW), x₀ := (z.core.x₀), iota := (z.core.iota) }
  refine ⟨core', (g.toAlgebra), ?_⟩

  refine ⟨fun y => (hι _).trans (z.alg_eq y), fun y => hι0 _ (z.fieldValues_mem_fixedField y), fun x hx => ?_,
    (HEq.refl z.core.Q.H), (HEq.refl z.core.Q.l), (HEq.refl z.core.Q.c), (HEq.refl z.core.Q.Dw),
    (HEq.refl z.core.Q.Xo), (HEq.refl z.core.U), (HEq.refl z.core.V), (HEq.refl z.core.dict),
    (HEq.refl z.core.mu), (HEq.refl z.core.Kf), (HEq.refl z.core.cE), (HEq.refl z.core.chiW),
    (HEq.refl z.core.x₀), (HEq.refl z.core.iota), ?_, (hCa), (hDim), (hpb)⟩
  · obtain ⟨x₀, hx₀, he⟩ := hιK x hx
    obtain ⟨y, hy⟩ := z.Ks_le x₀ hx₀
    exact ⟨y, (congrArg (enlEmb hR) hy).trans he⟩
  · have hPF : Q'.PinField := fun x => (hO (z.core.Q.eO x)).trans (hL.pins.2.2.1 x)
    exact
      { pins := ⟨(hL.pins.left), (hL.pins.right.left), hPF, (hL.pins.right.right.right)⟩
        half := (hL.half)
        evalWD := (hL.evalWD)
        unf := (hL.unf)
        unTest := (hL.unTest)
        chiTriv := (hL.chiTriv)
        dictU := (hL.dictU)
        spaceW := (hL.spaceW)
        levelK := (hL.levelK)
        xiAbs := (hL.xiAbs)
        muUnit := (hL.muUnit)
        muCont := (hL.muCont)
        finVol := fun j hj σ hσ => (finVol_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _).1 ((hL.finVol j hj σ hσ))
        cuspFD := (hL.cuspFD)
        supDef := (hL.supDef)
        cuspidalL2Subspace := fun j hj σ hσ => (cuspL2_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _).1 ((hL.cuspidalL2Subspace j hj σ hσ))
        l2Def := fun j hj σ hσ =>
          (peterssonDefinite_iff_of_eq_compactDualHaar (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _ ((hL.cuspidalL2Subspace j hj σ hσ)) _).1 ((hL.l2Def j hj σ hσ))
        unitIndep := (hL.unitIndep)
        ptNe := (hL.ptNe)
        cuspMul := (hL.cuspMul)
        latZ := (hL.latZ)
        cuNe := (hL.cuNe)
        expo := (hL.expo) }

theorem exists_coreJ_of_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb :=
  fun w w' Z Z' hX Wt z hE => exists_adelicCore_transport_enlargedCoefficientBase w w' Z Z' hX Wt z (isBaseEnlargementFixedCoefField_of_coeffEnlargement hE)

end GlobalTheory.Mem.R3.Rw
