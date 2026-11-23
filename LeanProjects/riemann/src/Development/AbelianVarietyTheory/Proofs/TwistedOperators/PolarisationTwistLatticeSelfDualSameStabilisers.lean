import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct nonZeroDivisors

noncomputable section

namespace GlobalTheory.ScaleSelfDual

open Matrix

section Gen

variable {E A : Type} [Field E] [NumberField E] [CommRing A] (ι : E →+* A) {n : ℕ}
  (Lc : Submodule (𝓞 E) (Fin n → E) → AddSubgroup (Fin n → A))

def ScalarsPass : Prop :=
  ∀ (N N' : Submodule (𝓞 E) (Fin n → E)) (c : E), (∀ x ∈ N, c • x ∈ N') → ∀ y ∈ Lc N, ι c • y ∈ Lc N'

variable {ι Lc}

theorem mem_iff_of_pass (hL : ScalarsPass ι Lc) {𝔞 𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h1 : 𝔞 * 𝔠 = 1)
    {N M : Submodule (𝓞 E) (Fin n → E)} (hi : ∀ a ∈ 𝔞, ∀ x ∈ N, a • x ∈ M) (hii : ∀ c ∈ 𝔠, ∀ y ∈ M, c • y ∈ N)
    (y : Fin n → A) : y ∈ Lc M ↔ ∀ c ∈ 𝔠, ι c • y ∈ Lc N := by
  refine ⟨fun hy c hc => hL M N c (hii c hc) y hy, fun h => ?_⟩
  have h1m : (1 : E) ∈ 𝔞 * 𝔠 := h1 ▸ FractionalIdeal.one_mem_one _
  have key : ι 1 • y ∈ Lc M := by
    refine FractionalIdeal.mul_induction_on (C := fun e => ι e • y ∈ Lc M) h1m (fun a ha c hc => ?_)
      (fun e e' he he' => ?_)
    · rw [map_mul, mul_smul]
      exact hL N M a (hi a ha) _ (h c hc)
    · rw [map_add, add_smul]
      exact add_mem he he'
  simpa using key

theorem mulVec_smul' (g : Matrix (Fin n) (Fin n) A) (b : A) (y : Fin n → A) : g *ᵥ (b • y) = b • (g *ᵥ y) :=
  Matrix.mulVec_smul g b y

theorem keeps_of_char {𝔠 : FractionalIdeal (𝓞 E)⁰ E} {N M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ y, y ∈ Lc M ↔ ∀ c ∈ 𝔠, ι c • y ∈ Lc N) (g : Matrix (Fin n) (Fin n) A)
    (hg : ∀ y, y ∈ Lc N ↔ g *ᵥ y ∈ Lc N) : ∀ y, y ∈ Lc M ↔ g *ᵥ y ∈ Lc M := by
  intro y
  rw [hM, hM]
  refine forall₂_congr fun c _ => ?_
  rw [hg, mulVec_smul']

theorem cong_of_char {𝔠 : FractionalIdeal (𝓞 E)⁰ E} {N M N' M' : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ y, y ∈ Lc M → ∀ c ∈ 𝔠, ι c • y ∈ Lc N) (hM' : ∀ y, (∀ c ∈ 𝔠, ι c • y ∈ Lc N') → y ∈ Lc M')
    (g : Matrix (Fin n) (Fin n) A) (hg : ∀ y ∈ Lc N, g *ᵥ y - y ∈ Lc N') : ∀ y ∈ Lc M, g *ᵥ y - y ∈ Lc M' := by
  intro y hy
  refine hM' _ fun c hc => ?_
  rw [smul_sub, ← mulVec_smul']
  exact hg _ (hM y hy c hc)

end Gen

end GlobalTheory.ScaleSelfDual

noncomputable section

namespace GlobalTheory.ScaleSelfDual

open Matrix

section Sc

variable {D : D7} {n : ℕ}

theorem smul_mem_scaleLat {𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {a : D.host.E} (ha : a ∈ 𝔟) {x : Fin n → D.host.E} (hx : x ∈ N) : a • x ∈ scaleLat 𝔟 N :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩

theorem inv_smul_mem {𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h𝔟 : 𝔟 ≠ 0) {N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {c : D.host.E} (hc : c ∈ 𝔟⁻¹) {y : Fin n → D.host.E} (hy : y ∈ scaleLat 𝔟 N) : c • y ∈ N := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have h1 : c * a ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ h𝔟]; exact FractionalIdeal.mul_mem_mul hc ha
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← ho, algebraMap_smul]
    exact N.smul_mem o hx
  | zero => simp
  | add _ _ _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul o z _ h => rw [smul_comm]; exact N.smul_mem o h

end Sc

end GlobalTheory.ScaleSelfDual

noncomputable section

namespace GlobalTheory.ScaleSelfDual

open Matrix

section Rel

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ideal_smul_pass' {𝔪 : Ideal (𝓞 E)} {N N' : Submodule (𝓞 E) (Fin n → E)} {c : E}
    (h : ∀ x ∈ N, c • x ∈ N') : ∀ x ∈ 𝔪 • N, c • x ∈ 𝔪 • N' := by
  intro x hx
  refine Submodule.smul_induction_on (p := fun x => c • x ∈ 𝔪 • N') hx (fun m hm z hz => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]; exact Submodule.smul_mem_smul hm (h z hz)
  · rw [smul_add]; exact add_mem hx hy

variable {A : Type} [CommRing A] {ι : E →+* A} {Lc : Submodule (𝓞 E) (Fin n → E) → AddSubgroup (Fin n → A)}
  {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {Λ M : Submodule (𝓞 E) (Fin n → E)}

theorem keeps_iff_rel (h𝔟 : 𝔟 ≠ 0) (hL : ScalarsPass ι Lc) (hA : ∀ a ∈ 𝔟, ∀ x ∈ Λ, a • x ∈ M)
    (hB : ∀ c ∈ 𝔟⁻¹, ∀ y ∈ M, c • y ∈ Λ) (g : Matrix (Fin n) (Fin n) A) :
    (∀ y, y ∈ Lc M ↔ g *ᵥ y ∈ Lc M) ↔ (∀ y, y ∈ Lc Λ ↔ g *ᵥ y ∈ Lc Λ) :=
  ⟨keeps_of_char (mem_iff_of_pass hL (inv_mul_cancel₀ h𝔟) hB hA) g,
    keeps_of_char (mem_iff_of_pass hL (mul_inv_cancel₀ h𝔟) hA hB) g⟩

theorem cong_iff_rel (h𝔟 : 𝔟 ≠ 0) (hL : ScalarsPass ι Lc) (hA : ∀ a ∈ 𝔟, ∀ x ∈ Λ, a • x ∈ M)
    (hB : ∀ c ∈ 𝔟⁻¹, ∀ y ∈ M, c • y ∈ Λ) (𝔪 : Ideal (𝓞 E)) (g : Matrix (Fin n) (Fin n) A) :
    (∀ y ∈ Lc M, g *ᵥ y - y ∈ Lc (𝔪 • M)) ↔ (∀ y ∈ Lc Λ, g *ᵥ y - y ∈ Lc (𝔪 • Λ)) := by
  have hA' : ∀ a ∈ 𝔟, ∀ x ∈ 𝔪 • Λ, a • x ∈ 𝔪 • M := fun a ha => ideal_smul_pass' (hA a ha)
  have hB' : ∀ c ∈ 𝔟⁻¹, ∀ x ∈ 𝔪 • M, c • x ∈ 𝔪 • Λ := fun c hc => ideal_smul_pass' (hB c hc)
  constructor
  · exact cong_of_char (fun y => (mem_iff_of_pass hL (inv_mul_cancel₀ h𝔟) hB hA y).1)
      (fun y => (mem_iff_of_pass hL (inv_mul_cancel₀ h𝔟) hB' hA' y).2) g
  · exact cong_of_char (fun y => (mem_iff_of_pass hL (mul_inv_cancel₀ h𝔟) hA hB y).1)
      (fun y => (mem_iff_of_pass hL (mul_inv_cancel₀ h𝔟) hA' hB' y).2) g

end Rel

section Pass

theorem pass_id {E : Type} [Field E] [NumberField E] {n : ℕ} :
    ScalarsPass (RingHom.id E) (fun N : Submodule (𝓞 E) (Fin n → E) => N.toAddSubgroup) :=
  fun _ _ c hc y hy => hc y hy

theorem pass_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ScalarsPass (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toRingHom
      (fun N : Submodule (𝓞 E) (Fin n → E) => (GlobalTheory.AdelicU.latLoc F N v).toAddSubgroup) := by
  intro N N' c hc y hy
  refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => _ • y ∈ GlobalTheory.AdelicU.latLoc F N' v) (fun a ha x hx => ?_)
    (by rw [smul_zero]; exact zero_mem _) (fun y z hy hz => by rw [smul_add]; exact add_mem hy hz)
    (fun y hy => by rw [smul_neg]; exact neg_mem hy) hy
  have e : ((Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toRingHom c • fun i => a ⊗ₜ[F] x i) =
      fun i => a ⊗ₜ[F] (c • x) i := by
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e]
  exact GlobalTheory.AdelicU.tmul_mem_latLoc ha (hc x hx)

theorem pass_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ} :
    ScalarsPass (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) : E →+* E ⊗[F] Formalism.L2.Herm.Af F)
      (fun N : Submodule (𝓞 E) (Fin n → E) => (Formalism.L2.Herm.hatL (F := F) N).toAddSubgroup) := by
  intro N N' c hc y hy
  change y ∈ Submodule.span _ _ at hy
  change _ ∈ Submodule.span _ _
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨c • x, hc x hx, ?_⟩
    funext i
    simp [map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul s z _ h => rw [smul_comm]; exact Submodule.smul_mem _ s h

theorem stabLoc_eq_of_rel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {Λ M : Submodule (𝓞 E) (Fin n → E)}
    (h𝔟 : 𝔟 ≠ 0) (hA : ∀ a ∈ 𝔟, ∀ x ∈ Λ, a • x ∈ M) (hB : ∀ c ∈ 𝔟⁻¹, ∀ y ∈ M, c • y ∈ Λ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.stabLoc σ J M v = GlobalTheory.AdelicU.stabLoc σ J Λ v := by
  ext g
  rw [GlobalTheory.AdelicU.mem_stabLoc, GlobalTheory.AdelicU.mem_stabLoc]
  exact keeps_iff_rel h𝔟 (pass_latLoc v) hA hB _

theorem congLev_eq_of_rel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {n : ℕ} (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) {𝔟 : FractionalIdeal (𝓞 E)⁰ E}
    {Λ M : Submodule (𝓞 E) (Fin n → E)}
    (h𝔟 : 𝔟 ≠ 0) (hA : ∀ a ∈ 𝔟, ∀ x ∈ Λ, a • x ∈ M) (hB : ∀ c ∈ 𝔟⁻¹, ∀ y ∈ M, c • y ∈ Λ)
    (𝔪 : Ideal (𝓞 E)) : congLev hc J M 𝔪 = congLev hc J Λ 𝔪 := by
  ext g
  rw [GlobalTheory.ChiGrid.mem_congLev, GlobalTheory.ChiGrid.mem_congLev]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact keeps_iff_rel h𝔟 (pass_hatL (F := F)) hA hB g.1
  · exact cong_iff_rel h𝔟 (pass_hatL (F := F)) hA hB 𝔪 g.1

end Pass

end GlobalTheory.ScaleSelfDual

noncomputable section

namespace GlobalTheory.ScaleSelfDual

open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Dual

theorem mem_span_of {E : Type} [Field E] [NumberField E] {n : ℕ} {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0)
    {Λ M : Submodule (𝓞 E) (Fin n → E)} (h : ∀ a ∈ 𝔟, ∀ x ∈ Λ, a • x ∈ M) :
    ∀ x ∈ Λ, x ∈ Submodule.span E (M : Set (Fin n → E)) := by
  intro x hx
  have h1m : (1 : E) ∈ 𝔟⁻¹ * 𝔟 := by rw [inv_mul_cancel₀ h𝔟]; exact FractionalIdeal.one_mem_one _
  have key : (1 : E) • x ∈ Submodule.span E (M : Set (Fin n → E)) := by
    refine FractionalIdeal.mul_induction_on (C := fun e => e • x ∈ Submodule.span E (M : Set (Fin n → E))) h1m
      (fun c _ a ha => ?_) (fun e e' he he' => ?_)
    · rw [mul_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span (h a ha x hx))
    · rw [add_smul]; exact add_mem he he'
  rwa [one_smul] at key

theorem fg_of_le_fg' {E : Type} [Field E] [NumberField E] {n : ℕ} {N P : Submodule (𝓞 E) (Fin n → E)} (hP : P.FG)
    (hle : N ≤ P) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian P hP
  have hfg := IsNoetherian.noetherian (N.comap P.subtype)
  have e : (N.comap P.subtype).map P.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
  exact e ▸ hfg.map _

variable {D : D7}

theorem isO_star (o : 𝓞 D.host.E) : ∃ b : 𝓞 D.host.E, (b : D.host.E) = star (o : D.host.E) := by
  have hint : IsIntegral ℤ (star (o : D.host.E)) := (o.isIntegral_coe).map (starRingEnd D.host.E).toIntAlgHom
  exact ⟨⟨_, hint⟩, rfl⟩

theorem isO_mul {a b : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (o : D.host.E) = a) (hb : ∃ o : 𝓞 D.host.E, (o : D.host.E) = b) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = a * b := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, by simp⟩

theorem isO_add {a b : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (o : D.host.E) = a) (hb : ∃ o : 𝓞 D.host.E, (o : D.host.E) = b) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = a + b := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, by simp⟩

def hf (V : HSp D) (x y : Fin V.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * V.gram i j * y j

theorem hf_smul_right (V : HSp D) (x y : Fin V.rank → D.host.E) (c : D.host.E) : hf V x (c • y) = c * hf V x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_smul_left (V : HSp D) (x y : Fin V.rank → D.host.E) (a : D.host.E) :
    hf V (a • x) y = star a * hf V x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, star_mul']
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_add_left (V : HSp D) (x x' y : Fin V.rank → D.host.E) : hf V (x + x') y = hf V x y + hf V x' y := by
  simp only [hf, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem hf_zero_left (V : HSp D) (y : Fin V.rank → D.host.E) : hf V 0 y = 0 := by
  simp [hf]

theorem isSelfDualC_scaleLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    {𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h𝔟 : 𝔟 ≠ 0) (hconj : ∀ c, c ∈ 𝔟⁻¹ ↔ star c ∈ 𝔟) :
    IsSelfDualC V (scaleLat 𝔟 Λ) := by
  obtain ⟨hlat, hdual⟩ := hΛ
  have hdual' : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = hf V x y := hdual
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  ·
    obtain ⟨d, hd, hdb⟩ := 𝔟.isFractional
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Λ.map (((LinearMap.lsmul D.host.E (Fin V.rank → D.host.E)) (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹).restrictScalars (𝓞 D.host.E))
    have hP : P.FG := hlat.fg.map _
    have hdne : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero hd)
    have hle : scaleLat 𝔟 Λ ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, x, hx, rfl⟩
      obtain ⟨o, ho⟩ := hdb a ha
      refine ⟨o • x, Λ.smul_mem o hx, ?_⟩
      show (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (o • x) = a • x
      rw [← algebraMap_smul D.host.E o x, smul_smul, ho, Algebra.smul_def d a, ← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
    exact fg_of_le_fg' hP hle
  ·
    rw [eq_top_iff, ← hlat.span_eq_top]
    exact Submodule.span_le.2 (mem_span_of h𝔟 fun a ha x hx => smul_mem_scaleLat ha hx)
  · change y ∈ scaleLat 𝔟 Λ ↔ ∀ x ∈ scaleLat 𝔟 Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = hf V x y
    constructor
    · intro hy x hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, ha, x', hx', rfl⟩ := hz
        rw [hf_smul_left, ← hf_smul_right]
        have hs : star a ∈ 𝔟⁻¹ := (hconj _).2 (by rwa [star_star])
        exact (hdual' _).1 (inv_smul_mem h𝔟 hs hy) x' hx'
      | zero => rw [hf_zero_left]; exact ⟨0, by simp⟩
      | add _ _ _ _ h h' => rw [hf_add_left]; exact isO_add h h'
      | smul o z _ h =>
        rw [← algebraMap_smul D.host.E o z, hf_smul_left]
        exact isO_mul (isO_star o) h
    · intro hy
      refine (mem_iff_of_pass (ι := RingHom.id D.host.E)
        (Lc := fun N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) => N.toAddSubgroup) pass_id (mul_inv_cancel₀ h𝔟)
        (fun _ ha _ hx => smul_mem_scaleLat ha hx) (fun _ hc _ hy => inv_smul_mem h𝔟 hc hy) y).2 fun c hc => ?_
      refine (hdual' _).2 fun x hx => ?_
      have hs : star c ∈ 𝔟 := (hconj c).1 hc
      have := hy _ (smul_mem_scaleLat hs hx)
      rw [hf_smul_left, star_star] at this
      rw [RingHom.id_apply, hf_smul_right]
      exact this

end Dual

end GlobalTheory.ScaleSelfDual

noncomputable section

namespace GlobalTheory.ScaleSelfDual

open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjFI_twist (D : D7) (i : ℕ) :
    GlobalTheory.SeeSaw.conjFI D ((D.host.AAbar * D.host.AA⁻¹) ^ i) = ((D.host.AAbar * D.host.AA⁻¹) ^ i)⁻¹ := by
  have hAAb : GlobalTheory.SeeSaw.conjFI D D.host.AAbar = D.host.AA := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; ext x; rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_mem_conjFI]
  rw [map_pow, map_mul, map_inv₀, GlobalTheory.SeeSaw.conjFI_AA, hAAb, ← inv_pow, mul_inv, inv_inv, mul_comm]

theorem twist_ne_zero (D : D7) (i : ℕ) : (D.host.AAbar * D.host.AA⁻¹) ^ i ≠ 0 := by
  have hAA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hAAb : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (RingEquiv.map_ne_zero_iff _).2 hAA
  exact pow_ne_zero _ (mul_ne_zero hAAb (inv_ne_zero hAA))

theorem twist_conj (D : D7) (i : ℕ) (c : D.host.E) :
    c ∈ ((D.host.AAbar * D.host.AA⁻¹) ^ i)⁻¹ ↔ star c ∈ (D.host.AAbar * D.host.AA⁻¹) ^ i := by
  rw [← conjFI_twist, GlobalTheory.SeeSaw.mem_conjFI, Formalism.BasicNotions.bridge_star_holds D.R D.host c]

theorem scaleLat_twist_selfDual : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ i : ℕ, IsSelfDualC V (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) ∧ (∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) ∧ ∀ 𝔪 : Ideal (𝓞 D.host.E), congLev D.sp.cm V.gram (scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) Λ) 𝔪 = congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V Λ hΛ i
  have h𝔟 := twist_ne_zero D i
  refine ⟨isSelfDualC_scaleLat V Λ hΛ h𝔟 (twist_conj D i), fun v => ?_, fun 𝔪 => ?_⟩
  · exact stabLoc_eq_of_rel _ _ h𝔟 (fun _ ha _ hx => smul_mem_scaleLat ha hx) (fun _ hc _ hy => inv_smul_mem h𝔟 hc hy) v
  · exact congLev_eq_of_rel _ _ h𝔟 (fun _ ha _ hx => smul_mem_scaleLat ha hx) (fun _ hc _ hy => inv_smul_mem h𝔟 hc hy) 𝔪

end GlobalTheory.ScaleSelfDual
