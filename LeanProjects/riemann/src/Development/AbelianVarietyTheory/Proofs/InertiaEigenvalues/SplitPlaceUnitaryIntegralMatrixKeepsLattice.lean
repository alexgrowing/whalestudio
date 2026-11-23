import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.SplitIntLift

theorem exists_lift {R K O : Type} [CommRing R] [CommRing K] [CommRing O] {n : ℕ} (S : Subring R) (π : R →+* K)
    (ι : O →+* K) (p : S) (hinj : ∀ x, π x = 0 → (p : R) * x = 0) (hl : ∀ o, ∃ s : S, π s = ι o)
    (h : GL (Fin n) O) (β g : GL (Fin n) R)
    (hg : (Matrix.GeneralLinearGroup.map π β)⁻¹ * Matrix.GeneralLinearGroup.map π g * Matrix.GeneralLinearGroup.map π β =
      Matrix.GeneralLinearGroup.map ι h) :
    ∃ (Y : Matrix (Fin n) (Fin n) S) (u : S), (∀ i j, π (Y i j) = ι (h.1 i j)) ∧ u * Y.det = p ∧
      (p : R) • g.1 = (p : R) • (β.1 * Y.map S.subtype * (β⁻¹).1) := by
  choose Y hY using fun i j => hl (h.1 i j)
  obtain ⟨u, hu⟩ := hl (h⁻¹).1.det
  have eY : (Matrix.of Y).map (π.comp S.subtype) = h.1.map ι := Matrix.ext hY
  refine ⟨Matrix.of Y, p * u, hY, Subtype.ext ?_, ?_⟩
  · have e1 : π ((Matrix.of Y).det : S) = ι h.1.det := by
      rw [RingHom.map_det ι, RingHom.mapMatrix_apply, ← eY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    have := hinj (u * ((Matrix.of Y).det : S) - 1) (by
      rw [map_sub, map_mul, hu, e1, ← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one, map_one, sub_self])
    push_cast
    linear_combination this
  · have e2 : Matrix.GeneralLinearGroup.map π g = Matrix.GeneralLinearGroup.map π β * Matrix.GeneralLinearGroup.map ι h *
        Matrix.GeneralLinearGroup.map π β⁻¹ := by
      rw [← hg, map_inv]; group
    have e3 : g.1.map π = (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1).map π := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
      exact (congrArg Units.val e2).trans (congrArg (fun z => β.1.map π * z * (β⁻¹).1.map π) eY.symm)
    ext i j
    have := hinj (g.1 i j - (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1) i j) (by
      rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e3 i) j)
    rw [mul_sub, sub_eq_zero] at this
    exact this

open GlobalTheory.LevSplit GlobalTheory.ParahoricLift Formalism.L2.NTheta GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7}

theorem rdE_finSw {v : FinPl D} (φ : SplitProj D v) (a : Formalism.L2.Theta.AE D) : rdE φ (finSw D a) = rdA φ a :=
  GlobalTheory.SplitProjChart.rdE_toEAf φ a

theorem finSw_surjective (z : Formalism.IndefR.Lev.EAf D) : ∃ w, finSw D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from (0, a)) ⊗ₜ x, rfl⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, RingHom.map_add _ _ _⟩

theorem cut_inj {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e)
    (x : Formalism.IndefR.Lev.EAf D) (hx : rdE φ x = 0) : finSw D e * x = 0 := by
  obtain ⟨w, rfl⟩ := finSw_surjective x
  rw [rdE_finSw] at hx
  rw [← RingHom.map_mul, ((GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.2.1 w).1 hx, RingHom.map_zero]

theorem int_lift {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e) (o : OI v) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, rdE φ s = algebraMap (OI v) (Fv D.host.F v) o := by
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  obtain ⟨a, ha⟩ := h1 (algebraMap (OI v) (Fv D.host.F v) o)
  refine ⟨⟨finSw D (e * a), swapAE_int ((h4 a).2 ⟨o, ha.symm⟩)⟩, ?_⟩
  show rdE φ (finSw D (e * a)) = _
  rw [rdE_finSw, RingHom.map_mul, he.2.2, one_mul, ha]

set_option maxHeartbeats 1000000 in

theorem lift_of_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  intro D V β Λ N hB P v φ e hP0 he0 red hred h κ hs hκ0
  have he : IsIdemAt e P := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ P hP0).2.2 e he0).1
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  have hg : (Matrix.GeneralLinearGroup.map (rdE φ) β)⁻¹ * Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) *
      Matrix.GeneralLinearGroup.map (rdE φ) β = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h := by
    rw [← hκ0]
    have : Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) =
        Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
      Units.ext (Matrix.ext fun i j => rdE_finSw φ (Formalism.L2.Theta.mt V κ i j))
    rw [this]
    rfl
  obtain ⟨Y, u, hY, hu', hκ⟩ := exists_lift (Formalism.L2.Herm.intAf D.host.F D.host.E) (rdE φ)
    (algebraMap (OI v) (Fv D.host.F v)) p (fun x hx => hp ▸ cut_inj he0 x hx) (int_lift he0) h β (finE V κ) hg
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨(T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ]
    refine Matrix.ext fun i j => ?_
    obtain ⟨hi, hr⟩ := hred (Y i j) (Y i j).2
    exact hr.symm.trans (congrArg red (Subtype.ext (hY i j)))
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

end GlobalTheory.DownLift.SplitIntLift

end
