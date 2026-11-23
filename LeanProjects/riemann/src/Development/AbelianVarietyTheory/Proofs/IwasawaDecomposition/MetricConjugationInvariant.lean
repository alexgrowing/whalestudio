import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx
open GlobalTheory.CxPts TopologicalSpace

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TrueGeo.ModelMetric

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {M : TrueGeo.Model Y}

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (ModelCharts.injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => by
    rw [RingHom.comp_apply, extEmb, IsFractionRing.lift_algebraMap]

theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) :
    extEmb σ = τ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) ((extEmb_comp σ).trans h.symm)

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp]
  rfl

def toY {σ : 𝓞 F →+* ℂ} (y : CxPts M.p σ) : Pts Y (extEmb σ) :=
  ⟨M.pb.lift y.1 (spMap (extEmb σ)) (y.2.trans (by rw [spMap_comp_spMap, extEmb_comp])),
    M.pb.lift_snd _ _ _⟩

theorem toY_j {σ : 𝓞 F →+* ℂ} (y : CxPts M.p σ) : (toY y).1 ≫ M.j = y.1 := M.pb.lift_fst _ _ _

theorem apply_toY {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ)
    (f : ∀ τ : F →+* ℂ, Pts Y τ → ℝ) (y : CxPts M.p σ) (z : Pts Y τ) (hz : z.1 ≫ M.j = y.1) :
    f (extEmb σ) (toY y) = f τ z := by
  obtain rfl := extEmb_eq h
  exact congrArg _ (Subtype.ext (M.pb.hom_ext ((toY_j y).trans hz.symm) ((toY y).2.trans z.2.symm)))

variable (M) in

def toM {σ : 𝓞 F →+* ℂ} (z : Pts Y (extEmb σ)) : CxPts M.p σ :=
  ⟨z.1 ≫ M.j, by rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, spMap_comp_spMap, extEmb_comp]⟩

theorem toY_toM {σ : 𝓞 F →+* ℂ} (z : Pts Y (extEmb σ)) : toY (toM M z) = z :=
  Subtype.ext (M.pb.hom_ext (toY_j _) ((toY _).2.trans z.2.symm))

theorem toM_toY {σ : 𝓞 F →+* ℂ} (y : CxPts M.p σ) : toM M (toY y) = y :=
  Subtype.ext (toY_j y)

theorem mem_pull {σ : 𝓞 F →+* ℂ} {L : LB M.X} {y : CxPts M.p σ} {i : L.ι}
    (h : y ∈ ptsIn M.p σ (L.U i)) : toY y ∈ ptsIn Y.str (extEmb σ) ((L.pull M.j).U fun _ => i) := by
  have h' : toY y ∈ ptsIn Y.str (extEmb σ) (M.j ⁻¹ᵁ L.U i) := by
    change ⊤ ≤ ((toY y).1 ≫ M.j) ⁻¹ᵁ L.U i
    rw [toY_j]
    exact h
  exact ptsIn_mono (fun _ hx => Set.mem_iInter.2 fun _ => hx) h'

def wtOf {L : LB M.X} (hL : L.IsLB) (ψ : ∀ τ : F →+* ℂ, Weight Y.str τ (L.pull M.j)) (σ : 𝓞 F →+* ℂ) :
    Weight M.p σ L where
  isLB := hL
  φ i y := (ψ (extEmb σ)).φ (fun _ => i) (toY y)
  trans i j y hi hj := by
    have hi' := mem_pull hi
    have hj' := mem_pull hj
    have e := gv_linComb (m := fun _ : PUnit => y) (fun _ => (toY_j y).symm) hi' hj'
    rw [Fintype.prod_unique, zpow_one] at e
    rw [(ψ _).trans _ _ _ hi' hj']
    erw [e]

end GlobalTheory.TrueGeo.ModelMetric

namespace GlobalTheory.TrueGeo.ModelMetric

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {M : TrueGeo.Model Y}

theorem isCInf_wtOf {L : LB M.X} (hL : L.IsLB) (ψ : ∀ τ : F →+* ℂ, Weight Y.str τ (L.pull M.j))
    (hψ : ∀ τ, (ψ τ).IsCInf) (σ : 𝓞 F →+* ℂ) : (wtOf hL ψ σ).IsCInf := fun i y hy => by
  have h := hψ (extEmb σ) (fun _ => i) (toY y) (mem_pull hy)
  have h' := GlobalTheory.Mean4O.OnModelCInf.baseChange_cInfAt F M.X Y.X M.p Y.str M.j M.pb (extEmb σ) σ (toM M)
    (fun _ => rfl) ((wtOf hL ψ σ).φ i) (toY y) (h.congr (.of_forall fun w => by
      show (ψ (extEmb σ)).φ (fun _ => i) (toY (toM M w)) = _
      rw [toY_toM]))
  rwa [toM_toY] at h'

theorem isConj_wtOf {L : LB M.X} (hL : L.IsLB) (ψ : ∀ τ : F →+* ℂ, Weight Y.str τ (L.pull M.j))
    (hc : ∀ τ τ', (ψ τ).IsConj (ψ τ')) (σ σ' : 𝓞 F →+* ℂ) : (wtOf hL ψ σ).IsConj (wtOf hL ψ σ') := by
  intro i y y' h hy
  have hσ := CxPts.eq_conj_of_conj h
  have he : extEmb σ' = (starRingEnd ℂ).comp (extEmb σ) :=
    extEmb_eq (by rw [RingHom.comp_assoc, extEmb_comp, hσ])
  refine hc (extEmb σ) (extEmb σ') (fun _ => i) (toY y) (toY y') ?_ (mem_pull hy)
  refine M.pb.hom_ext ?_ ?_
  · rw [toY_j, Category.assoc, toY_j]
    exact h
  · rw [(toY y').2, Category.assoc, (toY y).2, spMap_comp_spMap, he]

def hermOf {L : LB M.X} (hL : L.IsLB) (ψ : ∀ τ : F →+* ℂ, Weight Y.str τ (L.pull M.j))
    (hψ : ∀ τ, (ψ τ).IsCInf) (hc : ∀ τ τ', (ψ τ).IsConj (ψ τ')) : HermLB M.p where
  B := L
  isLB := hL
  φ := wtOf hL ψ
  cInf := isCInf_wtOf hL ψ hψ
  conj := isConj_wtOf hL ψ hc

end GlobalTheory.TrueGeo.ModelMetric

namespace GlobalTheory.TrueGeo.ModelMetric

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem base_conj {τ τ' : F →+* ℂ} {z : Pts Y τ} {z' : Pts Y τ'}
    (h : z'.1 = spMap (starRingEnd ℂ) ≫ z.1) : Var.base z' = Var.base z := by
  show z'.1 (IsLocalRing.closedPoint ℂ) = z.1 (IsLocalRing.closedPoint ℂ)
  rw [h]
  exact congrArg (fun x => z.1 x) (Subsingleton.elim _ _)

theorem h_mPow_conj {Δ : Y.Dv} {τ τ' : F →+* ℂ} (μ : Var.Met Y τ Δ) (μ' : Var.Met Y τ' Δ)
    {z : Pts Y τ} {z' : Pts Y τ'} (hb : Var.base z' = Var.base z) (hpos : z ∈ μ.posSet)
    (H : ∀ a, z ∈ Var.eqnSet τ Δ a → μ'.h a z' = μ.h a z) (k : ℕ) {b : Y.Fnˣ}
    (hbz : z ∈ Var.eqnSet τ (k • Δ) b) :
    (Var.mPow Y τ' Δ k μ').h b z' = (Var.mPow Y τ Δ k μ).h b z := by
  set g := Var.eqn Δ z
  have hg : z ∈ Var.eqnSet τ Δ g := Var.mem_eqnSet Δ z
  have hg' : z' ∈ Var.eqnSet τ' Δ g := by
    show Δ.IsEqn (Var.base z') g
    rw [hb]
    exact hg
  have hbz' : z' ∈ Var.eqnSet τ' (k • Δ) b := by
    show (k • Δ).IsEqn (Var.base z') b
    rw [hb]
    exact hbz
  have hgk : z ∈ Var.eqnSet τ (k • Δ) (g ^ k) := CartierDiv.IsEqn.nsmul hg k
  have hgk' : z' ∈ Var.eqnSet τ' (k • Δ) (g ^ k) := CartierDiv.IsEqn.nsmul hg' k
  set w : Y.Fnˣ := g ^ k / b with hw_def
  have hw : (0 : Y.Dv).IsEqn (Var.base z) w := (CartierDiv.isEqn_zero _).iff_unitAt.2 (by
    have := (CartierDiv.IsEqn.iff_unitAt hbz).1 hgk
    simpa [w] using this)
  have hg2 : z ∈ Var.eqnSet τ Δ (g * w) := by
    have := CartierDiv.IsEqn.add hg hw
    rwa [add_zero] at this
  have hg2' : z' ∈ Var.eqnSet τ' Δ (g * w) := by
    show Δ.IsEqn (Var.base z') _
    rw [hb]
    exact hg2
  have et (σ : F →+* ℂ) (y : Pts Y σ) : Var.tv b (g ^ k) y = Var.tv g (g * w) y := by
    rw [Var.tv, Var.tv, Units.val_mul, hw_def, Units.val_div_eq_div_val, mul_div_cancel_left₀ _ g.ne_zero]
  have e1 := μ.trans g (g * w) z hg hg2
  have e2 := μ'.trans g (g * w) z' hg' hg2'
  rw [H g hg, H (g * w) hg2] at e2
  have hp2 : 0 < μ.h (g * w) z := (Var.Met.mem_posSet_iff hg2).1 hpos
  have en : ‖Var.tv g (g * w) z'‖ ^ 2 = ‖Var.tv g (g * w) z‖ ^ 2 :=
    (mul_right_cancel₀ hp2.ne' (e1.symm.trans e2)).symm
  rw [(Var.mPow Y τ' Δ k μ').trans b (g ^ k) z' hbz' hgk', (Var.mPow Y τ Δ k μ).trans b (g ^ k) z hbz hgk,
    Var.mPow_h hg', Var.mPow_h hg, H g hg, et, et, en]

def powMet (A : Adl (cxSt F) Y) (m : ℕ) (τ : F →+* ℂ) : Var.Met Y τ (m • A.D) := Var.mPow Y τ A.D m (A.m τ)

theorem powMet_smooth (A : Adl (cxSt F) Y) (m : ℕ) (hsm : ∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ))
    (τ : F →+* ℂ) : Var.mSmooth Y τ _ (powMet A m τ) :=
  Var.Met.SmoothOn.mPow isOpen_univ (hsm τ) m

def powWt (A : Adl (cxSt F) Y) (m : ℕ) (hsm : ∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) {B : LB Y.X}
    {r : B.ι → Y.Fnˣ} (hr : Presents (m • A.D) B r) (τ : F →+* ℂ) : Weight Y.str τ B :=
  (powMet A m τ).toWeight (powMet_smooth A m hsm τ).posSet_eq hr

theorem powWt_isCInf (A : Adl (cxSt F) Y) (m : ℕ) (hsm : ∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) {B : LB Y.X}
    {r : B.ι → Y.Fnˣ} (hr : Presents (m • A.D) B r) (τ : F →+* ℂ) : (powWt A m hsm hr τ).IsCInf :=
  (Weight.isCInf_iff_isSmooth (Y.an τ)).2 (Var.mSmooth.isSmooth_toWeight (powMet_smooth A m hsm τ) hr)

theorem powWt_conj (A : Adl (cxSt F) Y) (m : ℕ) (hsm : ∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) {B : LB Y.X}
    {r : B.ι → Y.Fnˣ} (hr : Presents (m • A.D) B r)
    (hconj : ∀ (σ σ' : F →+* ℂ) (p : Pts Y σ) (p' : Pts Y σ') (a : Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 →
      p ∈ Var.eqnSet σ A.D a → Var.Met.h (A.m σ') a p' = Var.Met.h (A.m σ) a p) (τ τ' : F →+* ℂ) :
    (powWt A m hsm hr τ).IsConj (powWt A m hsm hr τ') := by
  intro i z z' h hz
  show -Real.log ((powMet A m τ').h (r i) z') = -Real.log ((powMet A m τ).h (r i) z)
  rw [powMet, powMet, h_mPow_conj (A.m τ) (A.m τ') (base_conj h)
    ((Var.mSmooth.posSet_eq (hsm τ)) ▸ Set.mem_univ z) (fun a ha => hconj τ τ' z z' a h ha) m
    (Var.ptsIn_subset_eqnSet hr i hz)]

end GlobalTheory.TrueGeo.ModelMetric

namespace GlobalTheory.TrueGeo.ModelMetric

theorem exists_hermLB_induced : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y) (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X), L.IsLB → ∀ (m : ℕ+) (r : (L.pull M.j).ι → Y.Fnˣ), Presents ((m : ℕ) • A.D) (L.pull M.j) r → A.ci = 0 → (∀ σ, (cxSt F).mSmooth Y σ A.D (A.m σ)) → (∀ (σ σ' : F →+* ℂ) (p : Pts Y σ) (p' : Pts Y σ') (a : Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ A.D a → Var.Met.h (A.m σ') a p' = Var.Met.h (A.m σ) a p) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * A.lg v e y = Real.log (e.w (valAt y.1 (((eqn A.D (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)))) → ∃ L' : GlobalTheory.HermLB M.p, A.Induced M L' m 0 := by
  intro F _ _ Y A M L hL m r hr hci hsm hconj hfin
  refine ⟨hermOf hL (powWt A m hsm hr) (powWt_isCInf A m hsm hr) (powWt_conj A m hsm hr hconj), ?_⟩
  refine ⟨by simp, r, hr, ?_, ?_⟩
  · intro σ y y' i f hy hi hf
    rw [hci]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    have hg : y ∈ Var.eqnSet σ ((m : ℕ) • A.D) (r i) := hr.isEqn i _ hi
    have hpos : y ∈ (powMet A m σ).posSet := (powMet_smooth A m hsm σ).posSet_eq ▸ Set.mem_univ y
    have e := apply_toY (M := M) (σ := σ.comp (algebraMap (𝓞 F) F)) (τ := σ) rfl
      (fun τ z => (powMet A m τ).wt (r i) z) y' y hy.symm
    have hp : (cxSt F).pn Y σ _ ((cxSt F).mPow Y σ A.D m (A.m σ)) ((cxSt F).cx Y σ f) y =
        Var.pn Y σ _ (powMet A m σ) (Y.cx σ f) y := rfl
    rw [hp, Var.pn_eq_exp hpos hg, Var.fval_cx]
    exact congrArg (fun t => ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-t)) e.symm
  · intro v e y yt i h1 h2
    rw [Pi.zero_apply, mul_zero, sub_zero]
    exact hfin v e y yt i h1 h2

end GlobalTheory.TrueGeo.ModelMetric
