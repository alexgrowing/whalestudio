import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCastMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem levOver_cast' {D : D7} {G : Type} [Group G] {i : Fin D.R.m} {Pg₁ Pg₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {β₁ β₂ : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} {e₁ : G ≃* G0 Pg₁ D.R.r} {e₂ : G ≃* G0 Pg₂ D.R.r}
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    {ι : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hP : HEq Pg₂ Pg₁) (hβ : HEq β₂ β₁) (he : HEq e₂ e₁)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La} (h : LevOver D i Pg₁ β₁ e₁ l Dw ι lev) :
    LevOver D i Pg₂ β₂ e₂ l Dw ι lev := by
  cases hP; cases hβ; cases he
  exact h

set_option maxHeartbeats 4000000 in

theorem exists_bc_stages (X X' : Stages) (hP : X'.B.toPre = X.B.toPre) (hLL : Set.range X.B.embLL ⊆ Set.range X'.B.embLL)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ex : HEq T'.x₀ T.x₀) (eι : HEq T'.iota T.iota) (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (eβW : HEq R'.βW R.βW)
    (eG : HEq R'.eG R.eG) (emu : HEq R'.C.mu0 R.C.mu0) (eeta : HEq R'.C.eta R.C.eta)
    {κ : ∀ i : Fin X.toD7.R.m, WeightFamilies.Wt X.toD7 ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin X.toD7.R.m) (σ : X.toD7.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {κ' : ∀ i : Fin X'.toD7.R.m, WeightFamilies.Wt X'.toD7 ((i : ℕ) + 1)}
    {v₀' : ∀ (i : Fin X'.toD7.R.m) (σ : X'.toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec}
    (hL : R.toLevCh.Is A.μ0) (hV : R.models_HV) (hκ : KapIs κ) (hL' : R'.toLevCh.Is A'.μ0) (hM' : R'.IsModels) (hF' : R'.fam_tie)
    (ht' : TieIn T' R' κ' v₀') (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hOF : O.c'.F = X.toD7.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins (κ i) (v₀ i (sg0 X.toD7 A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (P : Prop)
    (hc : ∀ c0L, CoefFam R c0L → P ∨ ∃ c0L', CoefFam R' c0L' ∧
      ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) :
    ∃ O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0), O'.c'.F = X'.toD7.what₂.embLL.toRatAlgHom.fieldRange ∧
      O'.Pins (κ' i') (v₀' i' (sg0 X'.toD7 A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0) ∧
      IsBCOf O' (v₀' i' (sg0 X'.toD7 A')) O (v₀ i (sg0 X.toD7 A)) (κ i) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) P := by
  obtain ⟨c₃, hF₃, h₃⟩ := GlobalTheory.RefPins.exists_coeff_rows T' ht'.alg ht'.laws.pins.2.2.1
  have hmem : ∀ y, X'.toD7.what₂.embLL y ∈ c₃.F := fun y => hF₃.ge ⟨y, rfl⟩
  let jL' : X'.toD7.what₂.LL →+* c₃.F := X'.toD7.what₂.embLL.codRestrict c₃.F hmem
  have hjL' : (inC c₃).comp jL' = X'.toD7.what₂.embLL := RingHom.ext fun _ => rfl
  have sj' : Function.Surjective jL' := fun y => by
    obtain ⟨x, hx⟩ := hF₃.le y.2
    exact ⟨x, Subtype.ext hx⟩
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  have hs : O.c'.F ≤ c₃.F := fun y hy => by
    obtain ⟨x, hx⟩ := hOF.le hy
    obtain ⟨x', hx'⟩ := hLL ⟨x, hx⟩
    exact hF₃.ge ⟨x', hx'⟩
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  have hV₃ : T'.V ((i' : ℕ) + 1) (sOv T'.toCore c₃ h₃) = Wc X'.toD7 i' := ht'.laws.spaceW _ (inR i') _ rfl
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  have hx1 := hL.xi A.μ0
  have hx1' := hL'.xi A'.μ0
  rw [hL.xi_base] at hx1
  rw [hL'.xi_base] at hx1'
  have hplace : ∀ (c0L') (c0'' : VsV X'.toD7 i' c₃.F →ₛₗ[inC c₃] (R'.cV i').W), CoefFam R' c0L' →
      CoefficientBaseChange R' i' jL' (inC c₃) (c0L' i') c0'' → ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA X'.toD7 (Vc X'.toD7 i')),
      PlaceEx R' i' A'.μ0 h c0'' := by
    rintro c0L' c0'' ⟨_, _, htie⟩ hc0 Cl _ h
    exact GlobalTheory.RationalValues.placeEx_of_type_mem R' i' jL' (inC c₃) A'.μ0 h c0'' hM'.jV htie hc0
      (GlobalTheory.RationalValues.type_mem R' i' A'.μ0 _
        (fun PP hPP x => by
          obtain ⟨y, hy⟩ := GlobalTheory.RefPins.chiVal_of_tie T' R' κ' v₀' hL' ht' i' PP hPP x
          exact ⟨jL' y, hy⟩)
        fun PP hPP => absurd (hQ' ▸ hPP) (Finset.notMem_empty _))
  have hv0' := ht'.hv₀ i' (sg0 X'.toD7 A')
  have hκ' := ht'.kap i'
  clear ht'
  have hc' : ∃ c0L', CoefFam R' c0L' ∧ (P ∨ ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) := by
    rcases hc c0L ⟨g, r, hT⟩ with h | ⟨c, h1, h2⟩
    · obtain ⟨g', r', c, h1⟩ := hF'
      exact ⟨c, ⟨g', r', h1⟩, Or.inl h⟩
    · exact ⟨c, h1, Or.inr h2⟩
  clear hc
  obtain ⟨c0L', hT', hag⟩ := hc'
  obtain ⟨c0'', hbc'⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R'.cV i').W) jL' (inC c₃) hjL' (lamV X'.toD7 i') (c0L' i')
  have hpl' := hplace c0L' c0'' hT' hbc'
  clear hplace
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX ex eι
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl := eq_of_heq ex
  obtain rfl := eq_of_heq eι
  obtain rfl : i = i' := Fin.ext hi
  have h0 : ∃ c0₃ : VsV X.toD7 i c₃.F →ₛₗ[inC c₃] (R.cV i).W, (∀ (v : VsV X.toD7 i O.c'.F) (v' : VsV X.toD7 i c₃.F),
      (v' : Pol c₃.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) =
        MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) → c0₃ v' = O.c0' v) ∧
      (HEq c0'' c0₃ ∨ P) := by
    rcases hag with hp | hag
    · obtain ⟨c0₃, h⟩ := exists_coef_ext (incF O.c' c₃ hs) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV X.toD7 i) O.c0'
      exact ⟨c0₃, h, Or.inr hp⟩
    · obtain ⟨c0₃, h1, h2⟩ := exists_cast_map (V := VsV X.toD7 i c₃.F) (σ := inC c₃) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW
        eW en ei ((by with_unfolding_all exact (c0'' :)))
      refine ⟨c0₃, fun v v' e => eq_of_heq ((h2 v').symm.trans ?_), Or.inl ((by with_unfolding_all exact (h1 :)))⟩
      exact coef_agree (W' := (R'.cV i).W) (lamV X.toD7 i) O.jL jL' (incF O.c' c₃ hs) hO.lift.field hjL' (RingHom.ext fun _ => rfl) sj sj'
        (cL' := (by with_unfolding_all exact ((c0L' i) :))) hbc ((by with_unfolding_all exact (hbc' :))) ((by with_unfolding_all exact (hag :))) v v' e
  obtain ⟨c0₃, hc0, hor⟩ := h0
  obtain ⟨io₃, hw₃, h, J', hB⟩ := exists_isBC O c₃ hs c0₃ (v₀ i (sg0 X.toD7 A)) hV hO hc0
  have hM := hB.pins
  have eχ : R'.C.mu0 i * R'.xiH A'.μ0 * R'.C.eta⁻¹ = R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹ := (by with_unfolding_all exact ((congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b⁻¹)
      (congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b) (congrFun (eq_of_heq emu) i) (hL'.xi_base.trans hL.xi_base.symm))
      (eq_of_heq eeta)) :))
  have eξ : R'.xi A'.μ0 = R.xi A.μ0 := (GlobalTheory.ChrEqUnique.chrEq_unique X.toD7).2.1 _ _ _ ((by with_unfolding_all exact (hx1' :))) hx1
  have hT1 := (tupOver_iff R A.μ0).2 ⟨repsR_map (incF O.c' c₃ hs) hB.reps, (hM.tuple ()).B, (hM.tuple ()).xi, (hM.tuple ()).phi,
    (hM.tuple ()).half⟩
  have hT2 := tupOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (βV₂ := (by with_unfolding_all exact (R'.βV :))) (βW₂ := (by with_unfolding_all exact (R'.βW :)))
    (ξR₂ := (by with_unfolding_all exact ((R'.xiR A'.μ0) :))) ePg hQ hQ' ((by with_unfolding_all exact (eβV :))) ((by with_unfolding_all exact (eβW :))) eχ eξ hT1
  have hl2 := levOver_cast' (D := X.toD7) (Pg₂ := R'.Pg) (β₂ := (by with_unfolding_all exact (R'.βW :))) (e₂ := (by with_unfolding_all exact (R'.eG :))) ePg ((by with_unfolding_all exact (eβW :))) ((by with_unfolding_all exact (eG :)))
    ((levOver_iff T R i O.lev).2 hO.lift.lev)
  let κ₀ : WeightFamilies.Wt X.toD7 ((i : ℕ) + 1) := ⟨(by with_unfolding_all exact ((κ' i).aP :)), (by with_unfolding_all exact ((κ' i).aM :)), (by with_unfolding_all exact ((κ' i).aPlus_antitone :)), (by with_unfolding_all exact ((κ' i).aM_anti :)), (κ' i).n, (κ' i).n_even⟩
  have ew : wtA κ₀ = wtA (κ i) := wtA_eq _ _
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).1 k) :))) ((hκ i τ).1 k).symm)
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).2.1 k) :))) ((hκ i τ).2.1 k).symm)
  have hio := hM.io
  rw [← ew] at hio
  let M := bc O c₃ hs c0₃ io₃ hw₃ h (v₀ i (sg0 X.toD7 A))
  refine ⟨@OMDat.mk _ G _ _ Pl0' T0' A' _ alg' R' i Unit _ (c' := c₃) (hle := h₃) (jL := jL') (hV := hV₃) (c0' := c0'') (lev := (by with_unfolding_all exact (M.lev :)))
    (dδ := (by with_unfolding_all exact (M.dδ :))) (Cl' := M.Cl') (fCl := M.fCl) (bad := M.bad) (Lh := (by with_unfolding_all exact (M.Lh :))) (La := (by with_unfolding_all exact (M.La :))) (Nc := (by with_unfolding_all exact (M.Nc :))) (gam := (by with_unfolding_all exact (M.gam :)))
    (vol := (by with_unfolding_all exact (M.vol :))) (ep := (by with_unfolding_all exact (M.ep :))) (B := (by with_unfolding_all exact (M.B :))) (epF := (by with_unfolding_all exact (M.epF :))) (io := (by with_unfolding_all exact (M.io :))) (hw := (by with_unfolding_all exact (M.hw :))) (φ := (by with_unfolding_all exact (M.φ :)))
    (w := (by with_unfolding_all exact (M.w :))) (U₂ := (by with_unfolding_all exact (M.U₂ :))) (dict₂ := (by with_unfolding_all exact (M.dict₂ :))) (xi := (by with_unfolding_all exact (M.xi :)))
    (thAd := fun _ => thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (v₀' i (sg0 _ A')))
    (Plc := fun _ x => ∃ x₀, Place R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (jVx R' i A'.μ0 x₀) x), hF₃, ?_, ?_⟩
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    obtain ⟨g', r', hT'⟩ := hT'
    apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
    case lift =>
      apply (config := { synthAssignedInstances := false }) ThPinsR.mk
      case field => exact hjL'
      case std => exact (by with_unfolding_all exact (hO.lift.std :))
      case v0 => exact hv0'
      case lev => exact (by with_unfolding_all exact (hl2 :))
      case c0 => exact ⟨g', r', c0L', hT', hbc'⟩
    case tuple =>
      intro t
      apply (config := { synthAssignedInstances := false }) ThPinsT.mk
      case reps => exact ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact (hT2.1 :)), (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
      case B => exact (by with_unfolding_all exact (hT2.2.1 :))
      case xi => exact (by with_unfolding_all exact (hT2.2.2.1 :))
      case phi => exact (by with_unfolding_all exact (hT2.2.2.2.1 :))
      case half => exact (by with_unfolding_all exact (hT2.2.2.2.2 :))
    case act => exact (by with_unfolding_all exact (hM.act :))
    case bad => exact (by with_unfolding_all exact (hM.bad :))
    case reps => exact (by with_unfolding_all exact (hM.reps :))
    case ep => exact (by with_unfolding_all exact (hM.ep :))
    case io => exact (by with_unfolding_all exact (hio :))
    case w => exact (by with_unfolding_all exact (hM.w :))
    case cov => exact (by with_unfolding_all exact (hM.cov :))
    case cxi => exact (by with_unfolding_all exact (hM.cxi :))
    case model₂ => exact (by with_unfolding_all exact (hM.model₂ :))
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    refine ⟨c₃, hs, c0₃, io₃, hw₃, h, J', hB, ?_, hor, (by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact ((HEq.refl h) :)), (by with_unfolding_all exact ((HEq.refl J') :)), (by with_unfolding_all exact (hT2.1 :)),
      (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
    exact ⟨(by with_unfolding_all exact ((HEq.refl M.c') :)), (by with_unfolding_all exact ((HEq.refl M.lev) :)), (by with_unfolding_all exact ((HEq.refl M.dδ) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.fCl) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.Lh) :)),
      (by with_unfolding_all exact ((HEq.refl M.La) :)), (by with_unfolding_all exact ((HEq.refl M.Nc) :)), (by with_unfolding_all exact ((HEq.refl M.gam) :)), (by with_unfolding_all exact ((HEq.refl M.vol) :)), (by with_unfolding_all exact ((HEq.refl M.ep) :)), (by with_unfolding_all exact ((HEq.refl M.B) :)),
      (by with_unfolding_all exact ((HEq.refl M.epF) :)), (by with_unfolding_all exact ((HEq.refl M.io) :)), (by with_unfolding_all exact ((HEq.refl M.hw) :)), (by with_unfolding_all exact ((HEq.refl M.φ) :)), (by with_unfolding_all exact ((HEq.refl M.w) :)), (by with_unfolding_all exact ((HEq.refl M.U₂) :)),
      (by with_unfolding_all exact ((HEq.refl M.dict₂) :)), (by with_unfolding_all exact ((HEq.refl M.xi) :))⟩

end GlobalTheory.Mem.R3.Rw.OmExt

end
