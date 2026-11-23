import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRBasisOfLocBasis

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem conj_eq_complexConj (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

theorem norm_natCast_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℂ_[p])‖ = 1 := by
  rw [GlobalTheory.EigenGenerator.norm_natCast_eq]
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk)

theorem exists_unitary_at (p : ℕ) (hp : p.Prime) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ G : Matrix (Fin N) (Fin N) D.host.E, (G.map D.host.conj).transpose * G = 1 ∧
      (∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E))) ∧
      (∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram D.sp.cm.cmUnram
  have hsd : (⟨L, hL.1, hL.2.1⟩ : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat D.host.E N).SelfDual := by
    intro x
    have h3 := hL.2.2 x
    refine h3.trans (forall₂_congr fun y _ => ?_)
    have e : stdH D.host.E N y x = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y := by
      unfold stdH GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl
    rw [e]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  obtain ⟨γ, hγ, h1, h2⟩ := GlobalTheory.GenusSelfDual.inGenus_of_selfDual hsd p hp
  refine ⟨LinearMap.toMatrix' γ.toLinearMap, ?_, fun x hx => ?_, fun a => ?_⟩
  · ext a b
    have h := hγ (Pi.single b 1) (Pi.single a 1)
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm (Pi.single b (1 : D.host.E)) (Pi.single a 1) = if a = b then 1 else 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      rw [Finset.sum_eq_single b]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, Ne.symm hab, hab]
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rw [hr] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, conj_eq_complexConj]
    rw [← h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · obtain ⟨k, hk, hkx⟩ := h1 x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hkx
    choose c hc using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hy
    refine ⟨k, hk, c, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, Nat.cast_smul_eq_nsmul]
    rw [← hyx]
    have : (fun a => (c a : D.host.E)) = y := funext hc
    rw [this]
    rfl
  · have hm : (fun i => LinearMap.toMatrix' γ.toLinearMap i a) ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std D.host.E N).map γ).L := by
      refine Submodule.mem_map.2 ⟨Pi.single a 1, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod a, ?_⟩
      funext i
      simp [LinearMap.toMatrix'_apply]
    obtain ⟨k, hk, hkx⟩ := h2 _ hm
    exact ⟨k, hk, by rwa [Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.Mem.Col2.TC.AdaptedBases

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem basR_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (G : Matrix (Fin N) (Fin N) D.host.E) (hdet : G.det ≠ 0)
    (h1 : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E)))
    (h2 : ∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) :
    GL3Columns.BasR D lam τ L (G.map (tauEmb D lam τ)) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  unfold GL3Columns.BasR
  rw [hρ]
  have hdet' : (G.map ρ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ρ).2 hdet
  refine ⟨hdet', fun x hx a => ?_, fun a => ?_⟩
  · obtain ⟨k, hk, c, hc⟩ := h1 x hx
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    have hv : (fun i => ρ (x i)) = (G.map ρ).mulVec ((k : ℂ_[p])⁻¹ • fun a => ρ (c a : D.host.E)) := by
      funext i
      have e := congrArg (fun v => ρ (v i)) hc
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at e
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hk0, e, RingHom.map_mulVec]
      rfl
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet'), Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, norm_mul, norm_inv, hk1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ (c a)
  · obtain ⟨k, hk, hkL⟩ := h2 a
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    refine ⟨1, fun _ => (k : ℂ_[p])⁻¹, fun _ => (k : D.host.E) • fun i => G i a, fun _ => by rw [norm_inv, hk1, inv_one],
      fun _ => hkL, fun i => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.map_apply]
    rw [inv_mul_cancel_left₀ hk0]

theorem dualM_eq_self {N : ℕ} {G : Matrix (Fin N) (Fin N) D.host.E} (h : (G.map D.host.conj).transpose * G = 1) : dualM G = G :=
  Matrix.inv_eq_right_inv h

theorem basR_smul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} {N : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M : Matrix (Fin N) (Fin N) ℂ_[p]} (hM : GL3Columns.BasR D lam τ L M)
    {s : ℂ_[p]} (hs : ‖s‖ = 1) : GL3Columns.BasR D lam τ L (s • M) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; exact zero_ne_one hs
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, fun x hx a => ?_, fun a => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) h0
  · have e : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hs, inv_one, one_mul]
    exact h1 x hx a
  · obtain ⟨n, r, x, hr, hx, he⟩ := h2 a
    refine ⟨n, fun k => s * r k, x, fun k => by rw [norm_mul, hs, one_mul]; exact hr k, hx, fun i => ?_⟩
    rw [Matrix.smul_apply, he i, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ne_two_ne_q_of_adPl {w : D.what₂.places.Pl} (hw : AdPl D w) :
    D.what₂.places.resChar w ∉ D.host.small ∧ D.what₂.places.resChar w ≠ D.host.q := by
  unfold AdPl Formalism.BasicNotions.Host.cls at hw
  constructor
  · intro h
    simp [Formalism.BasicNotions.primeClass, h] at hw
  · intro h
    rw [h, Formalism.BasicNotions.primeClass_q] at hw
    simp at hw

theorem dgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : DgenUnitAd P O := by
  intro w hw u μ τ
  obtain ⟨h2, hq⟩ := ne_two_ne_q_of_adPl hw
  obtain ⟨M, hM, hemb, hs⟩ := (O u μ).dgen_gen
  obtain ⟨s, hs1, hs2⟩ := hs τ
  rw [← hs1]
  exact GlobalTheory.EigenGenerator.norm_generator_eq_one D _ (P.lam w) h2 hq M hemb τ s hs2

theorem exists_sys (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : ∃ Pm : SysFam D u μ,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) := by
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  choose G hG h1 h2 using fun i (c : (D.chTw u μ).cls i) =>
    exists_unitary_at (D := D) (D.what₂.places.resChar w) hp ((O u μ).lat i c).1 ((O u μ).lat i c).2
  refine ⟨fun i c _ => G i c, fun i _ c τ => ?_, fun _ _ _ _ _ _ => rfl, fun i _ c _ _ _ => (dualM_eq_self (hG i c)).symm⟩
  exact basR_of (P.lam w) τ _ (G i c) (Matrix.det_ne_zero_of_left_inverse (hG i c)) (h1 i c) (h2 i c)

end GlobalTheory.Mem.Col2.TC.AdaptedBases

open IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

end
