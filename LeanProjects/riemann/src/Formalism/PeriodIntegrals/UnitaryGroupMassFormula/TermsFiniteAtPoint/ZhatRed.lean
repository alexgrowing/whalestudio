import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CarrierRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ZhatIntegral : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
    ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' →
      ∀ a b, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ZhatL (lf D F0) F' a b

theorem star_int (D : D7) (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  refine ⟨⟨star (o : D.host.E), ?_⟩, rfl⟩
  have h : IsIntegral ℤ (o : D.host.E) := o.2
  exact (h.map (starRingEnd D.host.E).toIntAlgHom)

def sgnM (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem zhatOM_eq {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * (sgnM r).map (Int.cast : ℤ → K) := by
  ext a b
  simp [ZhatOM, sgnM, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

theorem sgn_conj_entry {K : Type*} [CommRing K] (r : ℕ) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (i j) :
    ((sgnM r).map (Int.cast : ℤ → K) * B * (sgnM r).map (Int.cast : ℤ → K)) i j =
      (-1) ^ (r - i.val) * B i j * (-1) ^ (r - j.val) := by
  simp [sgnM, Matrix.mul_apply, Matrix.diagonal_apply]

theorem upB_sgn (D : D7) (r : ℕ) (b1 b2 : ℕ) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 D.host.E))
    (hB : UpB (((b1 * b2 : ℕ)) : 𝓞 D.host.E) B) :
    UpB ((b2 : ℕ) : 𝓞 D.host.E)
      ((sgnM r).map (Int.cast : ℤ → 𝓞 D.host.E) * B * (sgnM r).map (Int.cast : ℤ → 𝓞 D.host.E)) := by
  intro i j
  rw [sgn_conj_entry]
  obtain ⟨h1, h2, h3⟩ := hB i j
  refine ⟨fun h => by simp [h1 h], fun h => by subst h; simp [h2 rfl, ← mul_pow], fun h => ?_⟩
  have := h3 h
  have hd : ((b2 : ℕ) : 𝓞 D.host.E) ∣ B i j :=
    dvd_trans ⟨(b1 : 𝓞 D.host.E), by push_cast; ring⟩ this
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd _) _

theorem starO_upB (D : D7) {N : ℕ} (b1 b2 : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 D.host.E))
    (hA : LoB (((b1 * b2 : ℕ)) : 𝓞 D.host.E) A) (Ao : Matrix (Fin N) (Fin N) (𝓞 D.host.E))
    (hAo : ∀ i j, (Ao i j : D.host.E) = star ((A j i : 𝓞 D.host.E) : D.host.E)) :
    UpB ((b1 : ℕ) : 𝓞 D.host.E) Ao := by
  intro i j
  obtain ⟨h1, h2, h3⟩ := hA j i
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have e : (Ao i j : D.host.E) = ((0 : 𝓞 D.host.E) : D.host.E) := by rw [hAo, h1 h]; simp
    exact RingOfIntegers.coe_injective e
  · subst h
    have e : (Ao i i : D.host.E) = ((1 : 𝓞 D.host.E) : D.host.E) := by rw [hAo, h2 rfl]; simp
    exact RingOfIntegers.coe_injective e
  · obtain ⟨o, ho⟩ := h3 h
    obtain ⟨o', ho'⟩ := star_int D o
    refine ⟨(b2 : 𝓞 D.host.E) * o', ?_⟩
    have e : (Ao i j : D.host.E) = (((b1 : 𝓞 D.host.E) * ((b2 : 𝓞 D.host.E) * o') : 𝓞 D.host.E) : D.host.E) := by
      have ho'' : star ((o : 𝓞 D.host.E) : D.host.E) = (o' : D.host.E) := ho'.symm
      rw [hAo, ho]
      push_cast
      simp only [star_mul', star_natCast, ho'']
      ring
    exact RingOfIntegers.coe_injective e

theorem zhatReduce_of (hC : CellReduce) (hF : FrameOp) (hR : CarrierRow) (hI : ZhatIntegral) :
    ZhatReduce := by
  intro D u u' _hsig F0 Λ hΛ w
  obtain ⟨b1, hb1, hF1⟩ := hF D u
  obtain ⟨b2, hb2, hF2⟩ := hF D u'
  have hb : (((b1 * b2 : ℕ)) : 𝓞 D.host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 D.host.E) D.host.E) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) h'
  obtain ⟨Zs0, hfin, hred⟩ := hC D.host.E (D.R.rS + 1) w _ hb
  let Sg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E := (sgnM D.R.rS).map (Int.cast)
  refine ⟨(fun M => M * Sg) '' Zs0, hfin.image _, ?_⟩
  rintro x ⟨hG, hcell⟩
  have hint := hI D u u' F0 Λ hΛ x.1 x.2
  have hintO : ∀ i j, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ZhatOM (ZhatL (lf D F0) x.1) i j := by
    intro i j
    obtain ⟨o, ho⟩ := hint i j
    refine ⟨(-1) ^ (D.R.rS - j.val) * o, ?_⟩
    simp [ZhatOM, ho]
  obtain ⟨A, B, hA, hB, hmem⟩ := hred _ hintO hcell
  let Bo := (sgnM D.R.rS).map (Int.cast : ℤ → 𝓞 D.host.E) * B * (sgnM D.R.rS).map (Int.cast : ℤ → 𝓞 D.host.E)
  have hBo : UpB ((b2 : ℕ) : 𝓞 D.host.E) Bo := upB_sgn D D.R.rS b1 b2 B hB
  obtain ⟨hrow, hlf⟩ := hR D u u' F0 Λ hΛ x.1 x.2
  obtain ⟨m, hm, hmact⟩ := hF2 x.1.fl Λ hrow Bo hBo
  rw [hlf] at hm hmact
  choose st hst using fun i j => star_int D (A j i)
  have hAo := starO_upB D b1 b2 A hA st hst
  obtain ⟨n0, hn0, hn0act⟩ := hF1 F0 Λ hΛ st hAo
  have hn := PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_inv hn0
  have hiso : n0⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hn.1.1 hm.1.1
  let y : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) := Formalism.L2.SG.Saturated.mapL (n0⁻¹ * m) hiso x.1
  have hdc : DCRel Λ (lf D F0) x.1 y :=
    ⟨n0⁻¹, hn, m, hm, fun a => by simp [y, Formalism.L2.SG.Saturated.frame_mapL],
      by simp [y, Formalism.L2.SG.Saturated.mapL]⟩
  have hy : PD D Λ (lf D F0) u' y := PI.TCS.termStable_holds D u u' F0 Λ hΛ x y hdc
  have hGy : Gval (lf D F0) x.1 = Gval (lf D F0) y :=
    (term_function_const D u u' F0 Λ hΛ).1 x ⟨y, hy⟩ hdc
  refine ⟨⟨y, hy⟩, Quot.sound hdc, hGy ▸ hG, ?_⟩
  have key : ∀ {T1 T2 : D.host.E} (F1 : LFlag (VS D) D.R.rS T1) (F2 : LFlag (VS D) D.R.rS T2) a b,
      ZhatL F1 F2 a b = (VS D).hT (frame F1 a) (frame F2 b) := fun _ _ _ _ => rfl
  have hfy : ∀ b, frame y b = n0⁻¹ (m (frame x.1 b)) := fun b => by
    simp [y, Formalism.L2.SG.Saturated.frame_mapL]
  have hiso0 : ∀ v w, (VS D).hT (n0 v) (n0 w) = (VS D).hT v w := hn0.1.1
  have hZ : ZhatL (lf D F0) y =
      (A.map fun x => (x : D.host.E)) * ZhatL (lf D F0) x.1 * (Bo.map fun x => (x : D.host.E)) := by
    ext a b
    rw [key, hfy]
    have h1 : (VS D).hT (frame (lf D F0) a) (n0⁻¹ (m (frame x.1 b))) =
        (VS D).hT (n0 (frame (lf D F0) a)) (m (frame x.1 b)) := by
      rw [← hiso0 (frame (lf D F0) a) (n0⁻¹ (m (frame x.1 b)))]
      congr 1
      exact n0.apply_symm_apply _
    rw [h1, hn0act a, hmact b]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, ← key]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hst, starRingEnd_apply, star_star]
    ring
  have hBo' : (Bo.map fun x => (x : D.host.E)) = Sg * (B.map fun x => (x : D.host.E)) * Sg := by
    ext i j
    simp only [Bo, Sg, Matrix.map_apply, sgn_conj_entry]
    push_cast
    ring
  refine ⟨(A.map fun x => (x : D.host.E)) * ZhatOM (ZhatL (lf D F0) x.1) * B.map fun x => (x : D.host.E),
    hmem, ?_⟩
  show _ * Sg = _
  rw [hZ, hBo', zhatOM_eq]
  simp only [Sg, Matrix.mul_assoc]

end PI.TermsAtPtFiniteW
