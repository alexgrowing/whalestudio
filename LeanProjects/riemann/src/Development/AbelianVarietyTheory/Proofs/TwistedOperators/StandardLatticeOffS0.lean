import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemModulusDivConjugateIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteAdeleSupportedDivPrimeToPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPlLoc (idem mem_idOff_iff idem_mul_self)
open GlobalTheory.AscFinWit (mem_latO_at idem_mem_latO mxAt_mul mxAt_mul')

noncomputable section

namespace GlobalTheory.AscFin.StdOff

theorem latO_le_negSp {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem depLat_iff_at {D : D7} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    {v : GlobalTheory.FinPl.Pl D} {W0 : Finset (Formalism.L2.DIV.Pl D.host.E)} (hoff : ∀ PP ∈ W0, PP.under (𝓞 D.host.F) ≠ v)
    (H : AddSubgroup (WO S T)) {u : WO S T} (hu : MxAt (· = v) u) :
    (u ∈ latO (negSp S) T (LS : Set _) (LT : Set _) (fun _ => True) ∧ ∀ e : AE D, IsIdemSum e W0 → e • u ∈ H) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  constructor
  · rintro ⟨h1, -⟩
    exact latO_negSp_le' S T _ _ _ ((mem_latO_at (S := negSp S) hu).1 h1)
  · intro h1
    refine ⟨(mem_latO_at (S := negSp S) hu).2 (latO_le_negSp S T _ _ _ h1), fun e he => ?_⟩
    have : e • u = 0 := Matrix.ext fun i j => (GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff h1 i j).1
    rw [this]
    exact zero_mem _

theorem pair_tmul_scale {D : D7} (α' : Af D.host.F) (d : D.host.F) (X : D.host.E) :
    pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) ⊗ₜ[D.host.F] X =
      pairA D.host.F 0 α' ⊗ₜ[D.host.F] ((d : D.host.E) * X) := by
  have e : (d : D.host.E) * X = d • X := rfl
  have e2 : pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) = d • pairA D.host.F 0 α' := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = d • (0 : Ainf D.host.F)
      rw [smul_zero]
    · show α' * algebraMap D.host.F (Af D.host.F) d = d • α'
      rw [Algebra.smul_def, mul_comm]
  rw [e, e2, ← TensorProduct.smul_tmul']
  exact ((TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α')).map_smul d X).symm

def gen {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin U.rank → D.host.E) :
    WO S U :=
  Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)

theorem gen_zero {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) :
    gen S U α a s 0 = 0 := by
  ext i j
  rw [gen, Matrix.of_apply, Matrix.zero_apply, Pi.zero_apply, mul_zero, zero_mul, TensorProduct.tmul_zero]

theorem gen_add {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t t' : Fin U.rank → D.host.E) : gen S U α a s (t + t') = gen S U α a s t + gen S U α a s t' := by
  ext i j
  rw [Matrix.add_apply, gen, gen, gen, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Pi.add_apply, mul_add, add_mul,
    TensorProduct.tmul_add]

theorem gen_smul {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (c : 𝓞 D.host.E) (t : Fin U.rank → D.host.E) : gen S U α a s (c • t) = gen S U α (a * (c : D.host.E)) s t := by
  ext i j
  have hc : c • t i = (c : D.host.E) * t i := Algebra.smul_def c (t i)
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, hc, ← mul_assoc]

theorem gen_smulE {D : D7} (S U : HSp D) (α : Af D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) : gen S U α a s (b • t) = gen S U α (a * b) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]

theorem gen_scale {D : D7} (S U : HSp D) (α : Af D.host.F) (d : D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) :
    gen S U (α * algebraMap D.host.F (Af D.host.F) d) a s (b • t) = gen S U α (a * ((d : D.host.E) * b)) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, pair_tmul_scale, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

theorem latO_idLat_at {D : D7} (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) (d : D.host.F) (hdI : (d : D.host.E) ∈ I)
    (hdI' : ∀ x ∈ I, ∃ y : 𝓞 D.host.E, (y : D.host.E) = (d : D.host.E) * x)
    (hsc : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) →
      ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) d) :
    latO S U LS (idLat I LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  have hAA : ∀ a ∈ D.host.AA, ∀ c : 𝓞 D.host.E, a * (c : D.host.E) ∈ D.host.AA := fun a ha c => by
    have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    rwa [Algebra.smul_def, mul_comm] at this
  have hgen : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∀ a ∈ D.host.AA, ∀ s ∈ LS, ∀ t ∈ LU,
      gen S U α a s t ∈ latO S U LS (LU : Set _) (· = v) := fun α hα hP a ha s hs t ht =>
    AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (LU : Set _) (· = v) : Set (WO S U))
    rw [SetLike.mem_coe]
    induction ht using Submodule.span_induction generalizing a with
    | mem z hz =>
      obtain ⟨s', hs', y, hy, rfl⟩ := hz
      obtain ⟨yy, hyy⟩ := hdI' s' hs'
      rw [gen_scale, ← hyy]
      exact hgen α' hα' hP' _ (hAA a ha yy) s hs y hy
    | zero =>
      rw [gen_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [gen_add]
      exact add_mem (hx a ha) (hy a ha)
    | smul c x _ hx =>
      rw [gen_smul]
      exact hx _ (hAA a ha c)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (idLat I LU : Set _) (· = v) : Set (WO S U))
    have e := gen_scale S U α' d a 1 s t
    rw [one_smul, mul_one, mul_comm a] at e
    rw [SetLike.mem_coe, e, mul_comm (d : D.host.E) a, ← gen_smulE]
    exact AddSubgroup.subset_closure ⟨α', hα', hP', a, ha, s, hs, _, Submodule.subset_span ⟨_, hdI, t, ht, rfl⟩, rfl⟩

theorem latO_shiftId {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ G.pl.S0) (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U) :
    latO S U LS (idLat (shiftId G) LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  obtain ⟨d, hdv, hdI, hdI'⟩ := GlobalTheory.T.exists_unit_mem_modulusDivConjugateIdeal G v hv
  exact latO_idLat_at S U LS LU _ v (d : D.host.F) hdI hdI' (GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place D v d hdv)

end GlobalTheory.AscFin.StdOff

open GlobalTheory.AscFin.StdOff GlobalTheory.FinZeta.VacOff

theorem GlobalTheory.AscFin.stdAt_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  classical
  intro D _ T L _ _ sc G W _ _ F _ ρ h v hv
  have hoff : ∀ PP ∈ G.pl.W0, PP.under (𝓞 D.host.F) ≠ v := fun PP hPP e => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hPP
    exact hv (by rw [← e, G.pl.under_w hu]; exact hu)
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_⟩
  · have hu := mxAt_mul' ha (F.dB ρ h).pX
    exact depLat_iff_at hoff _ hu
  · refine ⟨idem D (· = v) • a, fun i j => (mem_idOff_iff _ _).2 (by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, idem_mul_self, sub_self]), ?_⟩
    rw [HypDec.extX_apply, Matrix.smul_mul]
    exact idem_mem_latO (latO_negSp_le' _ _ _ _ _ ha.1)
  · have hu := mxAt_mul' (mxAt_mul (F.dJ ρ h).jX hξ) (F.dB ρ h).p0
    show (F.dB ρ h).ext0 _ ((F.dJ ρ h).incX _ ξ) ∈ latBig G (2 * ρ + 1) ↔ _
    exact (mem_latO_at hu).trans (by rw [latO_shiftId G v hv]; exact Iff.rfl)

end
