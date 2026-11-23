import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

open Matrix GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Points
open GlobalTheory.VBExt (AdaptedChart)
open scoped ContDiff

namespace GlobalTheory.MetFam

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {t : ℝ → ℝ}

theorem famAt_chg {m n : Type} [Fintype m] [Fintype n] {y : CxPts p σ} {A : CxPts p σ → Matrix m n ℂ}
    (h : MInfAt A y) {H : ℝ → CxPts p σ → Matrix m m ℂ} {H₀ : CxPts p σ → Matrix m m ℂ}
    (hH : ∀ a b, FamAt t (fun R z => H R z a b) (fun z => H₀ z a b) y) (a b : n) :
    FamAt t (fun R z => chg (A z) (H R z) a b) (fun z => chg (A z) (H₀ z) a b) y := by
  have h₁ : VInfAt (F := m → n → ℂ) A y := vInfAt_pi fun a => vInfAt_pi fun b => h a b
  have h₂ : FamAt (F := m → m → ℂ) t H H₀ y := famAt_pi fun a => famAt_pi fun b => hH a b
  refine ((famAt_const h₁ t).prodMk h₂).comp_contDiff (Ψ := fun x => HermFrame.chg (of x.1) (of x.2) a b)
    (contDiff_iff_contDiffAt.2 fun x => ?_)
  have e₁ : MContDiffAt ∞ (fun x : (m → n → ℂ) × (m → m → ℂ) => of x.1) x := fun a b =>
    (mContDiffAt_id x.1 a b).comp x contDiffAt_fst
  have e₂ : MContDiffAt ∞ (fun x : (m → n → ℂ) × (m → m → ℂ) => of x.2) x := fun a b =>
    (mContDiffAt_id x.2 a b).comp x contDiffAt_snd
  exact (e₁.transpose.mul e₂).mul e₁.conjTranspose.transpose a b

variable {E F : X.Modules} {r s : ℕ}

theorem VFam.famAt_gram {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : VFam t h h₀) {ι : Type} [Fintype ι]
    {U : X.Opens} (e : ι → Γ(E, U)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) (a b : ι) :
    FamAt t (fun R z => ((h R).met σ).gram e z a b) (fun z => (h₀.met σ).gram e z a b) y := by
  obtain ⟨c, hc, hf⟩ := H σ y
  have hn : ∀ᶠ z in 𝓝 y, z ∈ ptsIn p σ c.U ∧ z ∈ ptsIn p σ U :=
    Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds hc) ((isOpen_ptsIn _).mem_nhds hy)
  refine (famAt_chg (A := fun z => Matrix.of fun a b => c.crd p σ (e b) z a)
    (fun a b => c.vInfAt_crd _ hy hc a) hf a b).congr
    ((tendsto_snd.eventually hn).mono fun x hx => ?_) (hn.mono fun z hz => ?_)
  · exact congrFun (congrFun (((h x.1).met σ).gram_eq c hx.1 e hx.2) a) b
  · exact congrFun (congrFun ((h₀.met σ).gram_eq c hz.1 e hz.2) a) b

theorem VFam.restrict {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : VFam t h h₀) {i : F ⟶ E}
    (hi : IsSubbundle i) (hF : IsVB F s) : VFam t (fun R => (h R).restrict hi hF) (h₀.restrict hi hF) :=
  fun _ y => ⟨_, hF.mem_pick y, fun a b => H.famAt_gram _ (hF.mem_pick y) a b⟩

theorem VFam.quot {S : ShortComplex X.Modules} {h : ℝ → VMetric p S.X₂ (r + s)} {h₀ : VMetric p S.X₂ (r + s)}
    (H : VFam t h h₀) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    VFam t (fun R => (h R).quot hS h₁ h₃) (h₀.quot hS h₁ h₃) := fun σ y => by
  obtain ⟨a, hy⟩ := Met.exists_adapted hS h₁ h₃ y
  have hn : ∀ᶠ z in 𝓝 y, z ∈ ptsIn p σ a.U := (isOpen_ptsIn _).mem_nhds hy
  have hg : FamAt (F := (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℂ) t (fun R z => ((h R).met σ).gram a.frame z)
      (fun z => (h₀.met σ).gram a.frame z) y := famAt_pi fun i => famAt_pi fun j => H.famAt_gram _ hy i j
  refine ⟨a.quot, hy, fun i j => (hg.comp (Ψ := fun M => quotGram (of M) i j)
      (T := {M | IsUnit (subGram (of M)).det}) (isOpen_iff_mem_nhds.2 fun M hM =>
        (mContDiffAt_id M).subGram.eventually_isUnit hM)
      (posDef_subGram ((h₀.met σ).posDef_gram_frame hS a hy)).det_pos.ne'.isUnit
      fun M hM => ((mContDiffAt_id M).quotGram hM i j).contDiffWithinAt).congr
    ((tendsto_snd.eventually hn).mono fun x hx => ?_) (hn.mono fun z hz => ?_)⟩
  · exact congrFun (congrFun (((h x.1).met σ).quot_G hS h₁ h₃ a hx) i) j
  · exact congrFun (congrFun ((h₀.met σ).quot_G hS h₁ h₃ a hz) i) j

theorem weight_sub_eq {B : LB X} (φ ψ : Weight p σ B) {i j : B.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (B.U i))
    (hj : y ∈ ptsIn p σ (B.U j)) : φ.φ j y - ψ.φ j y = φ.φ i y - ψ.φ i y := by
  rw [φ.trans i j y hi hj, ψ.trans i j y hi hj]; ring

theorem VFam.lFam_det {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : VFam t h h₀) (hs : ∀ R, (h R).IsCInf)
    (hs₀ : h₀.IsCInf) : LFam t (fun R => VMetric.det (hs R)) (VMetric.det hs₀) := by
  let u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun R σ y =>
    ((h R).met σ).detWeight.φ (h₀.isVB.pick y) y - (h₀.met σ).detWeight.φ (h₀.isVB.pick y) y
  have hu (R) (σ) (c : Chart E r) (y : CxPts p σ) (hy : y ∈ ptsIn p σ c.U) :
      u R σ y = ((h R).met σ).detWeight.φ c y - (h₀.met σ).detWeight.φ c y :=
    weight_sub_eq _ _ hy (h₀.isVB.mem_pick y)
  refine ⟨u, fun R σ y => ?_, fun R σ σ' _ y y' e _ => ?_, fun R => ?_, fun σ y => ?_⟩
  · have hc := h₀.isVB.mem_pick y
    refine (((hs R σ).detWeight _ y hc).add ((hs₀ σ).detWeight _ y hc).neg).congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hc] with z hz
    rw [hu R σ _ z hz, sub_eq_add_neg]
  · have hc := h₀.isVB.mem_pick y
    change u R σ' y' = u R σ y
    rw [hu R σ _ y hc, hu R σ' _ y' ((mem_ptsIn_iff_of_conj e).2 hc),
      ((h R).conj σ σ').detWeight _ y y' e hc, (h₀.conj σ σ').detWeight _ y y' e hc]
  · refine HermLB.isometric_of_eqOn fun σ c y hy => ?_
    change ((h R).met σ).detWeight.φ c y = (h₀.met σ).detWeight.φ c y + u R σ y
    rw [hu R σ c y hy]; ring
  · obtain ⟨c, hc, hf⟩ := H σ y
    have hn : ∀ᶠ z in 𝓝 y, z ∈ ptsIn p σ c.U := (isOpen_ptsIn _).mem_nhds hc
    have hg : FamAt (F := Fin r → Fin r → ℂ) t (fun R z => ((h R).met σ).G c z) (fun z => (h₀.met σ).G c z) y :=
      famAt_pi fun i => famAt_pi fun j => hf i j
    have hd (M : Fin r → Fin r → ℂ) : ContDiffAt ℝ ∞ (fun N : Fin r → Fin r → ℂ => (of N).det.re) M :=
      Complex.reCLM.contDiff.contDiffAt.comp M (mContDiffAt_id M).det
    have h₁ := hg.comp (Ψ := fun M => -Real.log (of M).det.re) (T := {M | (of M).det.re ≠ 0})
      (isOpen_ne_fun (contDiff_iff_contDiffAt.2 hd).continuous continuous_const)
      (det_re_pos ((h₀.met σ).posDef c y hc)).ne' fun M hM => ((hd M).log hM).neg.contDiffWithinAt
    have h₂ := famAt_const (vInfAt_iff_cInfAt.2 ((hs₀ σ).detWeight c y hc)) t
    refine ((h₁.prodMk h₂).comp_contDiff (Ψ := fun x => x.1 - x.2) (contDiff_fst.sub contDiff_snd)).congr
      ((tendsto_snd.eventually hn).mono fun x hx => hu x.1 σ c x.2 hx) (.of_forall fun z => (sub_self _).symm)

end

theorem lFam_grLB : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (t : ℝ → ℝ) (h : ℝ → VMetric p E r) (h₀ : VMetric p E r) (H : ∀ R, (h R).IsCInf) (H₀ : h₀.IsCInf), VFam t h h₀ → ∀ (fl : Vert.Flag E r) (i : Fin r), LFam t (fun R => VMetric.grLB fl i (H R)) (VMetric.grLB fl i H₀) :=
  fun _ _ _ _ _ _ _ h h₀ H H₀ hf fl i =>
    VFam.lFam_det (h := fun R => (h R).grMet fl i) (h₀ := h₀.grMet fl i)
      (VFam.quot (h := fun R => (h R).stepMet fl i) (h₀ := h₀.stepMet fl i) (hf.restrict _ _) _ _ _)
      (fun R => (H R).grMet fl i) (H₀.grMet fl i)

end GlobalTheory.MetFam
