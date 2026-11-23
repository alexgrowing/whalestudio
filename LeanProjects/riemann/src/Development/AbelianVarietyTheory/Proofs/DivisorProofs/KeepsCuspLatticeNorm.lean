import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveStabiliserCharacterDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OnlySecondOfFormLaws
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelIsometry

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.LevelKeeps
open GlobalTheory.Dict (castFr)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_transl_nonneg (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (γ : LevelAut Dw l) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (h : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (transl Xo c γ f) := by
  rintro la _ ⟨⟨q, S, io, n, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := levR_move hpq hA γ y.1
  let y' : IntFr Xo c S io :=
    ⟨_, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (levFull Dw l γ) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V n (evI y' f) := h la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (transl Xo c γ f) = evI y' f := evR_transl hpq hA γ hf y.1
  show 0 ≤ nval S.V n (evI y (transl Xo c γ f))
  rw [e1]
  exact h0

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem norm_rdU_transl (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (γ : LevelAut Dw l) {k k' : U.Comp} {δ : GL (Fin r) E}
    (h : Carries φ (levFull Dw l γ).1 k k' δ) {w : Ix Dw → ℤ} (hw : Even (w none)) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c w) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ‖rdU U (transl Xo c γ f) k x‖ = ‖rdU U f k' (lact δ (castFr h.mt.psi x))‖ := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  obtain ⟨z, hz1, hz⟩ := exists_const_of_carries (w := 0) (n := 2) (s' := (levFull Dw l γ).2) hσ hU hpq hA hP hxi
    ⟨fun _ => antitone_const, even_two⟩ (transl Xo c γ)
    (fun f hf => by rw [← secZ_nat] at hf ⊢; exact transl_mem_secZ hpq hA' γ hf)
    (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := levR_move hpq hA' γ y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => by rw [← secZ_nat] at hf; exact evR_transl hpq hA' γ hf y⟩) h
  obtain ⟨m, hm⟩ := hw
  obtain ⟨ρ, ν, -, hν, hmv⟩ := levR_move hpq hA' γ (U.un k ⟨x, hx⟩)
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP h hν ⟨x, hx⟩ hmv
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen _ _ a₁ b₁
  have key : ∀ (w : Ix Dw → ℤ), ∀ f ∈ secZ Xo c w, rdU U (transl Xo c γ f) k x =
      toC (t₀ : CAt σ) ^ w none * rdU U f k' (lact δ (castFr h.mt.psi x)) := fun w f hf => by
    have v1 : rdU U (transl Xo c γ f) k x = toC (evR Xo c (transl Xo c γ f) (U.un k ⟨x, hx⟩)) := dif_pos hx
    have v2 : rdU U f k' (lact δ (castFr h.mt.psi x)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩)) :=
      dif_pos (h.mt.mem_dom hx)
    rw [v1, v2, evR_transl hpq hA' γ hf, GlobalTheory.FlagTan.evR_frBor hf ht, Fintype.prod_option]
    simp only [Option.elim, one_zpow, Finset.prod_const_one, mul_one]
    exact congrArg (· * toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩))) (Units.val_zpow_eq_zpow_val (α := ℂ) t₀ _)
  obtain ⟨f₂, hf₂, h0⟩ := exists_sec_two hσ hU (hU.1 ▸ hpq) k' (h.mt.mem_dom hx)
  have h2 := hz f₂ hf₂ x hx
  rw [← secZ_nat] at hf₂
  rw [key _ f₂ hf₂] at h2
  have h3 : toC (t₀ : CAt σ) ^ (2 : ℤ) = z := mul_right_cancel₀ h0 h2
  rw [key w f hf, hm, ← two_mul, zpow_mul, h3, norm_mul, norm_zpow, hz1, one_zpow, one_mul]

end Free

section Adelic

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.DictMove
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rightEquiv (V : HSp D) (κ : GA D V) : AutQ V ≃ᵐ AutQ V :=
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have hrel : ∀ (k a b : GA D V), QuotientGroup.rightRel (GQ V) a b → QuotientGroup.rightRel (GQ V) (a * k) (b * k) :=
    fun k a b h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hm : ∀ k : GA D V, Measurable (Quotient.map' (· * k) (hrel k) : AutQ V → AutQ V) := fun k _ hs =>
    measurable_mul_const k (autMk_measurable V hs)
  { toFun := Quotient.map' (· * κ) (hrel κ)
    invFun := Quotient.map' (· * κ⁻¹) (hrel κ⁻¹)
    left_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (mul_inv_cancel_right a κ)
    right_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (inv_mul_cancel_right a κ)
    measurable_toFun := hm κ
    measurable_invFun := hm κ⁻¹ }

theorem eLpNorm_right (V : HSp D) (hs : V.SigOK) (κ : GA D V) (Φ : GA D V → ℝ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (p : ENNReal) :
    eLpNorm (fun q : AutQ V => Φ (q.out * κ)) p (muQ1 V) = eLpNorm (fun q : AutQ V => Φ q.out) p (muQ1 V) := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hR := ((GlobalTheory.CoreLawsCompare.invProb_iff V hP hV _).2 rfl).2
  have hmap : (muQ1 V).map (rightEquiv V κ) = muQ1 V := Measure.ext fun s hs => by
    rw [MeasurableEquiv.map_apply]
    exact hR κ _ (fun _ => rfl) s hs
  have hout : ∀ g, Φ (autMk V g).out = Φ g := fun g => by
    have e : (QuotientGroup.rightRel (GQ V)) g (autMk V g).out := Quotient.exact (Quotient.out_eq (autMk V g)).symm
    rw [QuotientGroup.rightRel_apply] at e
    rw [← hΦ _ e g, inv_mul_cancel_right]
  conv_rhs => rw [← hmap, (rightEquiv V κ).measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext q
  rw [← hout (q.out * κ)]
  exact congrArg (fun q' : AutQ V => Φ (rightEquiv V κ q').out) (Quotient.out_eq q)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_induces (V : HSp D) {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι)
    (γ : LevelAut Dw l) : ∃ κ, Induces V l ι (levFull Dw l γ).1 κ := by
  obtain ⟨red, h1, -, h3⟩ := GlobalTheory.LevelReduction.exists_isReduction D H Dw l V ι hι
  obtain ⟨k, rfl⟩ := h1 γ
  refine ⟨k, k.2.1, ?_, fun a ha => ?_⟩
  · have e : Formalism.L2.Pj.gLat V k = Formalism.L2.Pj.gLat V 1 := by
      unfold Formalism.L2.Pj.gLat
      rw [map_one, Units.val_one]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, (k.2.2 y).2 hy, Matrix.one_mulVec _⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨_, ((k⁻¹).2.2 y).2 hy, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          map_one, Units.val_one]
    unfold latGHat
    rw [e]
  · obtain ⟨w, hw, e⟩ := h3 k a ha
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; exact (add_sub_cancel _ _).symm⟩

set_option maxHeartbeats 1000000 in

theorem petE_transl {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {V : HSp D}
    (hs : V.SigOK) (hr : V.rank = r) {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th th' : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {Kf : Subgroup (GA D V)}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hι : LatEmb V ι) (hL : DictLat U V hr dict ι e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hD : DictIsUnif V dict Kf th' hr) (hu : ∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    {G : WTZ D.host.E} (hG : Even G.2) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1)
    (γ : LevelAut Dw l) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) (hfc : rdU U f ∈ holSub U.X (modelWt U G)) :
    petE V dict (muQ1 V) (modelWt U G) (rdU U (transl Xo c γ f)) = petE V dict (muQ1 V) (modelWt U G) (rdU U f) := by
  subst hr
  obtain ⟨κ, hκ⟩ := exists_induces V hι γ
  have hN : ∀ (P : FDSec U.X) g, ptN (modelWt U G) P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  unfold petE
  simp only [hN]
  rw [← eLpNorm_right V hs κ (fun g => ‖rdU U f (dict g).1 (dict g).2‖) fun a ha h => by
    obtain ⟨a', ha', e₁⟩ := hD.1 a ha h
    have := (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hfc (dict h).1).1.1.2.2 a' ha' _ (hD.2.2.2.1 h)
    rw [hχ _ _ ha', one_mul] at this
    rw [e₁]
    exact congrArg norm this]
  congr 1
  funext q
  obtain ⟨hx, δ, hc, e₁⟩ := GlobalTheory.StabMove.exists_carries (V := V) (W := V) rfl rfl rfl (dict := dict) ι hU hW hL hth
    hD.2.2.2.1 hκ q.out
  change (dict (q.out * κ)).2 = _ at e₁
  rw [e₁]
  exact norm_rdU_transl hσ hU hpq hA hL.1.2 (fun k k' => (hW k).2.trans (hW k').2.symm) γ hc hG hf hx

end Adelic

end GlobalTheory.LevelIsometry

end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.LevDesc (transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open scoped TensorProduct
open GlobalTheory GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, Even G.2 → KeepsCusp Y.U G ∧ ∀ (γ : LevelAut (T.Q.Dw j) Y.d.l₂) (f g : Y.V G), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f → (f ∈ AllWt.latW Y.U G → g ∈ AllWt.latW Y.U G) ∧ ∀ σ, Y.nrm G σ g = Y.nrm G σ f := by
  intro D T hT j hp _ _ hj Y e o hY G hG
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := le_add_right hp
  have hA := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hA]; exact Nat.coprime_one_left _
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine ⟨GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ,
    fun γ f g hg => ⟨fun hf => ?_, fun σ => ?_⟩⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩
  · intro la v hv
    show 0 ≤ v (g : Rul Y.d.Xo₂ Y.d.c₂)
    rw [hg]
    exact GlobalTheory.LevelIsometry.val_transl_nonneg hpq hA' γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 hf la v hv
  · have hσ := goodEmb_goodOf (c := Y.d.c₂) σ
    obtain ⟨hr, hW⟩ := hY.modelW _ hσ
    obtain ⟨th, _, -, hD⟩ := hY.dictU _ hσ
    obtain ⟨x₀, -, _, g', e, F, ik, φ, th', hth', hL⟩ := hpin _ hσ
    have := GlobalTheory.LevelIsometry.petE_transl (D.sp.W_sig j) hr hσ (hY.unf _ hσ) hpq hA hW hι hL hth' hD (hY.unit _ hσ) hG
      (hχ _ hσ) γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 ((AllWt.mem_cuspW.1 f.2).2 _ hσ)
    show _ * (AllWt.petE _ _ _ _ (rdU _ (g : Rul Y.d.Xo₂ Y.d.c₂))).toReal = _
    rw [hg]
    exact congrArg (fun t : ENNReal => AllWt.lieFacZ (T.Q.Dw j) (xiR D) G * t.toReal) this
