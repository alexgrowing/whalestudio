import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CoefMemFlagSec

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.L2.Pj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (T : Core D)

def forms (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n

def values (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

theorem isVal_values (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ∀ v ∈ values T j la, IsVal la v :=
  isVal_valSet la

open Classical in

def good (σ : T.Q.c.F →+* ℂ) : T.Q.c.F →+* ℂ :=
  if GoodEmb T.Q.c σ then σ else (starRingEnd ℂ).comp σ

theorem goodEmb_good (σ : T.Q.c.F →+* ℂ) : GoodEmb T.Q.c (good T σ) := goodEmb_goodOf T.Q.c σ

def supGood (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ :=
  lieFac (T.Q.Dw j) (xiR D) (wtA w) *
    (supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal

def petGood (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ :=
  (eLpNorm (onQ (T.V j σ) (T.phiAd j σ (wtA w) f)) 2 (muQ1 (T.V j σ))).toReal

def supNorm (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ := supGood T j w (good T σ) f

def petNorm (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ := petGood T j w (good T σ) f

def Cusps (j : ℕ) : Type := Σ k : (T.U j T.σ₀).Comp, FJ.CuspFD ((T.U j T.σ₀).X k) (WeightFamilies.rho D j)

def charLat (j : ℕ) (cu : Cusps T j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcFD 1 cu.2

theorem charLat_isLattice (j : ℕ) (cu : Cusps T j) : Submodule.IsLattice D.host.E (charLat T j cu) :=
  FJ.xcFD_lat 1 (fun h => one_ne_zero (α := D.host.E)
    ((FractionalIdeal.mem_zero_iff _).1 (h ▸ FractionalIdeal.one_mem_one _))) cu.2

abbrev domSec (j : ℕ) (cu : Cusps T j) (w : WeightFamilies.Wt D j) : Type :=
  flagSec T.σ₀ ((T.U j T.σ₀).X cu.1) (laU (T.U j T.σ₀) (wtA w) w.n cu.1)

variable {T}

theorem isFlagSec_rd (h : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (f : forms T j w) (k) :
    IsFlagSec ((T.U j T.σ₀).X k) (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) f.1 k) :=
  have h1 := (h.unf j hj T.σ₀ T.good_σ₀).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f.1 (cusp_le_sec _ _ _ _ _ f.2) k
  ⟨h1.1, h1.2.1⟩

theorem orbInt (h : LawsCore T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    FJ.RdOrbInt T.σ₀ (T.X₀ j) (WeightFamilies.rho D j) ((rdU (T.U j T.σ₀)).comp (forms T j w).subtype) :=
  FJ.rdOrbInt_of_latZ _ _ _ (fun f k => (isFlagSec_rd h.toLawsM hj w f k).1.continuousOn) (h.latZ j hj)

def coefIn (h : LawsCore T) {j : ℕ} (hj : InR D j) (cu : Cusps T j)
    (χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E) (w : WeightFamilies.Wt D j) :
    forms T j w →ₗ[T.Q.c.F] domSec T j cu w :=
  (FJ.sgF T.σ₀ (T.X₀ j) ((rdU (T.U j T.σ₀)).comp (forms T j w).subtype) (orbInt h hj w) cu χ).codRestrict _
    fun f => coef_mem_flagSec T.σ₀ _ _ cu.2 (FJ.orbDom_of_latZ _ (h.latZ j hj) cu) _ ⟨_, orbInt h hj w f cu⟩
      (isFlagSec_rd h.toLawsM hj w f cu.1)

open Classical in

def coef (h : LawsCore T) (j : ℕ) (cu : Cusps T j) (χ : WeightFamilies.ExpoSet D (charLat T j cu)) (w : WeightFamilies.Wt D j) :
    forms T j w →ₗ[T.Q.c.F] domSec T j cu w :=
  if hj : InR D j then coefIn h hj cu χ.1 w else 0

theorem petGood_eq {j : ℕ} (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (hm : JMemL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ)) {f : T.R j} (hf : f ∈ forms T j w) :
    petGood T j w σ f = l2C (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (xiR D) (wtA w) w.n hm f := by
  have hf' : f ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := hf
  rw [l2C, dif_pos hf', petGood, Core.phiAd, map_smul, eLpNorm_const_smul, ENNReal.toReal_mul]
  congr 1
  · simp [abs_of_pos (lieFac_pos _ _ _)]
  · exact (Lp.norm_toLp _ (hm ⟨f, hf'⟩)).symm

theorem isNormOn_supNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    IsNormOn (forms T j w) σ (supNorm T j w σ) :=
  (isNormOn_supC (xiR D) (h.supDef j hj) (dom_wtA w) (goodEmb_good T σ)).of_goodOf

theorem isNormOn_petNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    IsNormOn (forms T j w) σ (petNorm T j w σ) := by
  have hσ := goodEmb_good T σ
  have h0 := (isNormOn_l2C (xiR D) (h.l2Def j hj _ hσ) (dom_wtA w)).of_goodOf
  have e : ∀ f ∈ forms T j w, petNorm T j w σ f = _ :=
    fun f hf => petGood_eq w _ (h.cuspidalL2Subspace j hj _ hσ _ _ (dom_wtA w)) hf
  refine ⟨fun f hf => ?_, fun f hf h1 => ?_, fun a f hf => ?_, fun f hf g hg => ?_⟩
  · rw [e f hf]; exact h0.nonneg f hf
  · rw [e f hf] at h1; exact h0.defin f hf h1
  · rw [e f hf, e _ (Submodule.smul_mem _ a hf)]; exact h0.smul a f hf
  · rw [e f hf, e g hg, e _ (Submodule.add_mem _ hf hg)]; exact h0.add f hf g hg

theorem petNorm_le_supNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ forms T j w, petNorm T j w σ f ≤ supNorm T j w σ f := by
  intro f hf
  have hσ := goodEmb_good T σ
  obtain ⟨th, hr, -, hd⟩ := h.dictU j hj _ hσ
  rw [petNorm, petGood_eq w _ (h.cuspidalL2Subspace j hj _ hσ _ _ (dom_wtA w)) hf]
  exact l2C_le_supC (xiR D) hσ _ hd.2.2.2.1 (h.muUnit j hj _ hσ) f hf

def record (h : LawsCore T) : WeightFamilies.Prov D :=
  mkB T.Q.eO (forms T) (fun j hj w => h.cuspFD j hj _ _ (dom_wtA w)) (values T) (isVal_values T)
    (supNorm T) (petNorm T) (isNormOn_supNorm h.toLawsM) (isNormOn_petNorm h.toLawsM) (petNorm_le_supNorm h.toLawsM)
    (Cusps T) (charLat T) (charLat_isLattice T) (fun j cu _ w => domSec T j cu w) (coef h)

variable (T)

def CuspsMaximal (j : ℕ) : Prop :=
  ∀ k : (T.U j T.σ₀).Comp, IsEmpty (FJ.CuspFD ((T.U j T.σ₀).X k) (WeightFamilies.rho D j + 1))

def ReadingInjective (j : ℕ) : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (n : ℕ) (b : Fin n → forms T j w),
    LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun i => rdU (T.U j σ) (b i).1

def ExponentsMatch (j : ℕ) : Prop :=
  ∀ (cu : Cusps T j) (χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E), WeightFamilies.IsHerm D χ →
    ((∀ β ∈ FJ.zGam ((T.U j T.σ₀).X cu.1) cu.2, ∃ n : ℤ, FJ.prE ((T.U j T.σ₀).X cu.1) χ β = n) ↔
      WeightFamilies.IntOn D (charLat T j cu) χ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))

end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
