import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeightStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientSplitsLocalFactorTwistPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralTwistedPlaceEigenvectoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.OnePlace

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Core.Rk.IP GlobalTheory.ParHecke GlobalTheory.Core.Rk.SphCoef

theorem transport {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H)
    (m : Measure G) [m.IsHaarMeasure] (P : Subgroup G) (hP : IsOpen (P : Set G)) (h1 : m P = 1) (f : G → ℂ)
    (hf : Integrable f m) :
    ∃ (J : Subgroup H) (μ : Measure H), IsOpen (J : Set H) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧
      Integrable (fun y => f (e.symm y)) μ ∧ (∀ y, y ∈ J ↔ e.symm y ∈ P) ∧ ∫ y, f (e.symm y) ∂μ = ∫ g, f g ∂m := by
  let e' : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have he : (e' : G → H) = e := rfl
  have hJ : ((P.comap e.symm.toMulEquiv.toMonoidHom : Subgroup H) : Set H) = e.symm ⁻¹' (P : Set G) := rfl
  refine ⟨P.comap e.symm.toMulEquiv.toMonoidHom, m.map e', ?_, ?_, ?_, ?_, fun y => Iff.rfl, ?_⟩
  · rw [hJ]; exact hP.preimage e.symm.continuous
  · rw [he]; exact e.isHaarMeasure_map m
  · rw [MeasurableEquiv.map_apply, hJ, he, ← h1]
    congr 1
    ext g; simp
  · rw [integrable_map_equiv]
    convert hf using 1
    funext g; simp [he]
  · rw [integral_map_equiv]
    simp [he]

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] (P : Subgroup G) (hP : IsOpen (P : Set G)) (hc : IsCompact (P : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m P = 1 := by
  let K : TopologicalSpace.PositiveCompacts G :=
    ⟨⟨P, hc⟩, by
      simp only [hP.interior_eq]
      exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {D : D7}

theorem rcoef_eq_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] {A : HSp D} (m : Measure (GA D A))
    (hm : m.IsHaarMeasure) {u₁ u₂ : GA D A → ℂ} (h1 : MemL2Quotient (GQ A) m u₁) (h2 : MemL2Quotient (GQ A) m u₂)
    (ι : GL (I ⊕ I') k →* GA D A) (x : GA D A) (hx : ∀ y, ι y * x = x * ι y) (ξ : kˣ →* ℂˣ) (hξ : GlobalTheory.SmGL.IsUnitaryChar ξ)
    (ϖ : kˣ) (B : Multiset ℂˣ) (hg : IsGen ((GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι) ξ ϖ B u₁)
    (ht : ∀ j ∈ parahoric k I I', ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ g, u₂ (g * ι j) = (ξ d : ℂ) * u₂ g) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (I ⊕ I') k) V) (u : V) (ℓ : V →ₗ[ℂ] ℂ),
      IsGen π ξ ϖ B u ∧ IsCoType π ξ ℓ ∧ (∀ y, ℓ (π y u) = rcoef m u₁ u₂ (x * ι y)) ∧ ℓ u = rcoef m u₁ u₂ x := by
  have : m.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A m hm
  let p : Submodule ℂ (GA D A → ℂ) :=
    { carrier := {F | MemL2Quotient (GQ A) m F}
      zero_mem' := mem_l2_zero
      add_mem' := fun ha hb => mem_l2_add ha hb
      smul_mem' := fun c _ hF => mem_l2_smul c hF }
  let ρ : Representation ℂ (GL (I ⊕ I') k) (GA D A → ℂ) := (GlobalTheory.PRep.rightReg ℂ (GA D A) ℂ).comp ι
  have hst : ∀ g, p ≤ p.comap (ρ g) := fun g F hF => MemL2Quotient.mul_right hF (ι g)
  let π : Representation ℂ (GL (I ⊕ I') k) p := ρ.subrepresentation p hst
  have hπ : ∀ g (F : p), ((π g F : p) : GA D A → ℂ) = ρ g F := fun _ _ => rfl
  let ℓ : p →ₗ[ℂ] ℂ :=
    { toFun := fun F => petersson A m (rTr A x F) u₂
      map_add' := fun F G => petersson_add_left (MemL2Quotient.mul_right F.2 x) (MemL2Quotient.mul_right G.2 x) h2
      map_smul' := fun c F => petersson_smul_left c _ _ }
  refine ⟨p, inferInstance, inferInstance, π, ⟨u₁, h1⟩, ℓ, ⟨fun j hj d hd => Subtype.ext (hg.1 j hj d hd), hg.2.1,
    fun s R d hR => Subtype.ext ?_⟩, fun j hj d hd F => ?_, fun y => ?_, rfl⟩
  · rw [Submodule.coe_sum]
    exact hg.2.2 s R d hR
  · have e1 : rTr A x (π j F) = rTr A (ι j) (rTr A x F) := funext fun g => by
      show (F : GA D A → ℂ) (g * x * ι j) = (F : GA D A → ℂ) (g * ι j * x)
      rw [mul_assoc, mul_assoc, hx]
    have e2 := petersson_rTr (μ := m) (MemL2Quotient.mul_right F.2 x) h2 (ι j)
    have hn : (ξ d : ℂ) * conj (ξ d : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ d]; simp
    have e3 : ∀ φ : GA D A → ℂ, petersson A m φ u₂ = (ξ d : ℂ) * petersson A m φ (rTr A (ι j) u₂) := fun φ => by
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend, rTr, ht j hj d hd, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext q
      linear_combination (-(φ q.out * conj (u₂ q.out))) * hn
    show petersson A m (rTr A x (π j F)) u₂ = (ξ d : ℂ) * petersson A m (rTr A x F) u₂
    rw [e1, e3]
    exact congrArg _ e2
  · show petersson A m (rTr A x (ρ y u₁)) u₂ = petersson A m (rTr A (x * ι y) u₁) u₂
    congr 1
    funext g
    show u₁ (g * x * ι y) = u₁ (g * (x * ι y))
    rw [mul_assoc]

theorem val_type {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V} (hκ : κ ∈ Lev.levG s.V s.β s.L)
    (g : GA D s.V) : PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ f) = PiTensorProduct.lift.symm u.1 f := by
      rw [PiTensorProduct.lift_symm]; rfl
    have := hT.lev f κ hκ g
    rw [← e] at this
    simp only [PiLocalization₂.val, map_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  | add a b ha hb =>
    simp only [PiLocalization₂.val, map_add, Pi.add_apply] at ha hb ⊢
    rw [ha, hb]; ring

theorem hgt_split {A : HSp D} {L : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat A} {a : GL (Fin A.rank) (AE D)} (hL : IsSelfDualC A L)
    (ha : GlobalTheory.Doubling.IsMaj A a) (Sf : Finset (HeightOneSpectrum (𝓞 D.host.F))) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ Sf) (h1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v 1 = 1) {x : GA D A} (hx : x ∈ openOff A L Sf)
    (hxv : proj D.sp.cm.sig A.gram v x = 1) (y : GlobalTheory.FinZeta.Gv A v) (t : ℂ) :
    GlobalTheory.Doubling.npow (hgtL A L a (x * emb D.sp.cm.sig A.gram v y)) t =
      GlobalTheory.Doubling.npow (hgtL A L a x) t * ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y : ℝ) : ℂ) ^ t := by
  classical
  obtain ⟨-, -, h⟩ := hgtL_props D A L a hL ha
  have hne : ∀ u, u ≠ v → proj D.sp.cm.sig A.gram u (x * emb D.sp.cm.sig A.gram v y) = proj D.sp.cm.sig A.gram u x :=
    fun u hu => by rw [map_mul, proj_emb_ne _ _ hu, mul_one]
  have hxy : x * emb D.sp.cm.sig A.gram v y ∈ openOff A L Sf := fun u hu => by
    rw [hne u (fun e => hu (e ▸ hv))]; exact hx u hu
  have e : (hgtL A L a (x * emb D.sp.cm.sig A.gram v y) : ℝ) = (hgtL A L a x : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := by
    rw [(h Sf).2 _ hxy, (h Sf).2 _ hx, ← Finset.mul_prod_erase Sf _ hv, ← Finset.mul_prod_erase Sf _ hv, hxv, h1,
      Finset.prod_congr rfl fun u hu => congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L u) (hne u (Finset.ne_of_mem_erase hu))]
    simp only [map_mul, projArch_emb, proj_emb_self, hxv, mul_one, one_mul]
    ring
  simp only [GlobalTheory.Doubling.npow]
  have h0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v y := NNReal.coe_nonneg _
  rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) h0]

theorem hgt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} {H : GL n k → ℝ} (hH : IsHgt ϖ H) {g : GL n k}
    (hg : g ∈ GlobalTheory.SplitWeil.KO k n) : H g = 1 := by
  have e : GlobalTheory.GLDoubling.torusElt k n ϖ 0 = 1 := by
    simp only [GlobalTheory.GLDoubling.torusElt, Pi.zero_apply, zpow_zero]
    exact map_one _
  have h := hH.2 0
  rw [e] at h
  rw [← mul_one g, (hH.1 g hg 1).1, h]
  simp [GlobalTheory.ZonalCellDecomposition.sumAbs]

set_option maxHeartbeats 1600000 in

theorem local_factor : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ a, IsMajOf c s a → ∀ (u₁ u₂ : s.CC c) φ, IsQ w k u₁ → ∀ v₁ ∈ s.KF, ∀ v₂ ∈ s.KF, ∀ z : ℝ, (D.R.t : ℝ) / 2 - 1 < z → ∀ PP ∈ w.Q, ∃ (J : Subgroup (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (μ : Measure (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) (ζ : GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)) → ℂ), IsOpen (J : Set (GlobalTheory.FinZeta.Gv s.V (PP.under (𝓞 D.host.F)))) ∧ μ.IsHaarMeasure ∧ μ J = 1 ∧ Integrable ζ μ ∧ (∀ y ∈ J, ζ y = 1) ∧ (∀ g, gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L ↔ GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) g ∈ J) ∧ (z = (D.R.t : ℝ) / 2 → ∫ y, ζ y ∂μ = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) ∧ ∀ x ∈ intOff c s, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) x = 1 → ∀ y, flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F)) y) = ζ y * flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z x := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hQ v₁ hv₁ v₂ hv₂ z hz PP hPP
  obtain ⟨⟨v, pr, hpr⟩, hch⟩ := GlobalTheory.T.exists_charts_at_twist_places_chain D c w hw k hk.le s hs PP hPP
  obtain ⟨-, ⟨x₀, ϖ, hxϖ⟩, ⟨ι, hι⟩, hchi⟩ := hch v pr hpr
  obtain ⟨μT, hμu, hμT⟩ := hchi (c.chT (k + 1))
  obtain ⟨hv, hres, htame, hlift, hdict⟩ := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v pr hpr
  subst hv
  have hL : LiftsChar pr PP μT (w.ξ PP) := hlift k hk μT (Or.inr hμT)
  obtain ⟨⟨e, he, -, hH⟩, hlev, hlc⟩ := hdict ι hι
  have hH := hH x₀ ϖ hxϖ
  obtain ⟨-, hcard, hα⟩ := GlobalTheory.T.lower_block_parameter_twist_L_factor D c w hw k hk PP hPP _ pr hpr x₀ ϖ hxϖ
  obtain ⟨α, hαe⟩ : ∃ α : Fin (k * D.R.t) → ℂˣ,
      Finset.univ.val.map α = (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) := by
    set M := (qPar c PP x₀ k).map (· * (Circle.toUnits (c.chT (k + 1) x₀))⁻¹) with hM
    have hl : M.toList.length = k * D.R.t := by rw [Multiset.length_toList, hM, Multiset.card_map, hcard]
    refine ⟨fun i => M.toList.get (i.cast hl.symm), ?_⟩
    rw [Fin.univ_val_map, ← List.ofFn_congr hl, List.ofFn_get, Multiset.coe_toList]
  obtain ⟨hbd, hval⟩ := hα α hαe
  obtain ⟨e₀, he₁, he₂, he₃, hϖ⟩ := id hxϖ
  have hμϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x₀) := hμT x₀ ϖ ⟨e₀, he₁, he₂, he₃⟩
  letI : MeasurableSpace (Fv D.host.F (PP.under (𝓞 D.host.F))) := borel _
  haveI : BorelSpace (Fv D.host.F (PP.under (𝓞 D.host.F))) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F)))) := borel _
  haveI : BorelSpace (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F)))) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv D.host.F (PP.under (𝓞 D.host.F)))
  obtain ⟨hPo, hPc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric (Fv D.host.F (PP.under (𝓞 D.host.F)))
    (Fin D.R.r) (Blocks k D.R.t)
  obtain ⟨m₀, hm₀, hm₁⟩ := exists_haar _ hPo hPc
  obtain ⟨cf, hcf⟩ : ∃ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F (PP.under (𝓞 D.host.F))) → ℂ, ∀ g, cf g =
      GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) _) (datum μT)) (datum μT) :=
    ⟨_, fun _ => rfl⟩
  have hcoef := GlobalTheory.T.weilCoefficient_splits_localFactor_twistPlace D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP _ pr hpr ι hι μT hμT ν hν cf hcf φ
  obtain ⟨hc1, ζ₀, hζ, hζ1, hint⟩ := GlobalTheory.T.unramifiedDoublingIntegral_twisted_place_eigenvector hU _ ν hν ϖ hϖ D.R.r D.R.t k μT 1 hμu (htame μT hL).1 (htame μT hL).2
    (fun _ _ => rfl) (fun _ => by simp) (qPar c PP x₀ k) α (((D.R.t : ℝ) - 1) / 2) (by rw [one_mul, hμϖ]; exact hαe)
    (by rw [hres]; exact hbd) _ hH m₀ hm₁ cf (by rw [one_mul]; exact hcf)
  obtain ⟨hI, hIv⟩ := hint (z : ℂ) (by rw [Complex.ofReal_re]; linarith)
  obtain ⟨J, μ, hJo, hμH, hμ1, hμI, hJ, hμv⟩ := transport e m₀ _ hPo hm₁ _ hI
  obtain ⟨hr, -, hst⟩ := id hs
  obtain ⟨hr', -, hst'⟩ := id hs'
  have hH1 : ∀ y ∈ parahoric _ (Fin D.R.r) (Blocks k D.R.t), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) = 1 := fun y hy =>
    hgt_one hH (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric.1 hy).1
  refine ⟨J, μ, _, hJo, hμH, hμ1, hμI, fun y hy => ?_, fun g => ?_, fun hzt => ?_, fun x hx hxv y => ?_⟩
  · have hy' := (hJ y).1 hy
    simp only [hζ1 _ hy', hH1 _ hy']
    simp
  · rw [hJ, ← hlev, he, ContinuousMulEquiv.apply_symm_apply]
    rfl
  · rw [hμv, hIv, hres, ← hval, hzt]
    push_cast
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective y
    simp only [ContinuousMulEquiv.symm_apply_apply]
    have hθ := hw.com.inf
    haveI : s.ν.IsHaarMeasure := hst.haar
    have hL2 : ∀ (u : s.CC c), ∀ v ∈ s.KF, MemL2Quotient (GQ s.V) s.ν fun g => conj (PiLocalization₂.val u v g) := fun u v hv =>
      memL2_of_cusp_form hC hθ (mem_cuspForms.1
        (GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hθ s.M hst.sigOK u.1 u.2 v hv)).1
    obtain ⟨V, _, _, π, u, ℓ, hg, hco, hℓ, hℓ1⟩ := rcoef_eq_coef s.ν hst.haar (hL2 u₁ v₁ hv₁) (hL2 u₂ v₂ hv₂) ι x
      (fun y => by rw [he]; exact (commute_emb _ _ _ hxv).eq) μT hμu ϖ (qPar c PP x₀ k)
      (hQ v₁ PP hPP _ pr hpr x₀ ϖ hxϖ μT hL ι hι) (fun j hj d hd g => by
        rw [val_type u₂ v₂ ((hlev j).2 hj), hlc μT hL j hj d hd, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
          Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hμu d]
        simp)
    have h3 := hζ V π u ℓ hg hco y
    rw [hℓ, hℓ1] at h3
    have h2 := hcoef x (by simp only [gAt, hxv, map_one]) y
    have hS : PP.under (𝓞 D.host.F) ∈ c.S := by
      classical
      refine Finset.mem_image.2 ⟨PP, ?_, rfl⟩
      rw [hw.union]
      exact Finset.mem_union_right _ hPP
    have h5 := hgt_split (A := s.V) (L := s.Λ) hst.selfDual ha.1 c.S hS
      (by simpa using hH1 1 (one_mem _)) hx hxv (e y) ((z : ℂ) - (D.R.t : ℂ) / 2)
    have hs0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
      have a1 : s.V.rank = D.R.r + k * D.R.t := hst.rank
      have a2 : s'.V.rank = D.R.r + (k + 1) * D.R.t := hst'.rank
      rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, a1, a2]
      push_cast
      ring
    have hw' : ∀ g, wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g := fun _ => rfl
    have hc1' : conj (cf 1) ≠ 0 := by simpa using hc1
    simp only [flatInt, integrand, hs0, hw']
    rw [h5, ← he]
    apply mul_left_cancel₀ hc1'
    linear_combination (GlobalTheory.Doubling.npow (hgtL s.V s.Λ a x) ((z : ℂ) - (D.R.t : ℂ) / 2) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ _ (e y) : ℝ) : ℂ) ^ ((z : ℂ) - (D.R.t : ℂ) / 2)) *
      (rcoef s.ν (fun g => conj (PiLocalization₂.val u₁ v₁ g)) (fun g => conj (PiLocalization₂.val u₂ v₂ g)) (x * ι y) * h2 +
        coefW p.ω m X (p.pt φ) x * h3)

end GlobalTheory.ChainTw.OnePlace

end
