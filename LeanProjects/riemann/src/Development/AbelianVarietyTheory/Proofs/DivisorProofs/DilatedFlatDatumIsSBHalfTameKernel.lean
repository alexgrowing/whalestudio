import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.DilFlat

theorem eToEAf_int' {D : D7} (x : 𝓞 D.host.E) : eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩)

theorem isSBHalf_dilFlat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξR Q _ eQ hq ϖ hϖ _ Gc
  suffices hΦ : IsSBHalf eQ (lattice₂ R i) (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun v hv hv' t => by simp only [h2 v hv hv' t],
      fun t ht => h3 t (right_ne_zero_of_mul ht)⟩
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hϖE).map _
  have hc : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := eToEAf_int' ϖ
  have hfr : ∀ x : WO (Vc D i) (Wc D i), ∀ a b,
      frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x) a b =
        eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b := by
    intro x a b
    have hm : ((dil i (ϖ : D.host.E) x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D)) =
        eToEAf D (ϖ : D.host.E) • (x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D) := by
      ext a' b'
      simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hhalf : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (dil i (ϖ : D.host.E) x) ↔ IsHalf eQ x := by
    intro x
    refine ⟨fun h a b => hu.mul_left_cancel ?_, fun h a b => ?_⟩
    · have := h a b
      simp only [dil, Matrix.map_apply] at this
      rw [← this]; ring
    · simp only [dil, Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have key : (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) = fun x =>
      if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)) then
        omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)))
      else 0 := by
    funext x
    unfold flatDat
    by_cases h : IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    · rw [if_pos h, if_pos ⟨(hhalf x).2 h.1, h.2⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨(hhalf x).1 h'.1, h'.2⟩]
  rw [key]
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (fun x => frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    ?_ ?_ ?_ Q _ fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h
  · intro x u k a b
    simp only [hfr, GlobalTheory.PlaceDatum.frMapO_add]
    ring
  · obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg (R.βV i) (R.βW i)
    refine ⟨M, hM, fun u hu' a b => ?_⟩
    simp only [hfr]
    rw [mul_left_comm]
    exact mul_mem hc (h u hu' a b)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
    have hI : Ideal.span {ϖ} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hϖ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {ϖ}))
    set n := Ideal.absNorm (Ideal.span {ϖ})
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    have hnE : eToEAf D ((y : 𝓞 D.host.E) : D.host.E) * eToEAf D (ϖ : D.host.E) = (n : EAf D) := by
      rw [← RingHom.map_mul, ← map_natCast (eToEAf D)]
      congr 1
      exact_mod_cast hy
    refine ⟨K * n, Nat.mul_pos hK hn, fun t ht hti => ?_⟩
    have hnt : IsHalf eQ (n • t) := fun a b => by
      change eQ * (n • t a b) = n • t a b
      rw [mul_smul_comm, ht a b]
    have hfn : ∀ a b, frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (n • t) a b =
        (n : EAf D) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) t a b := fun a b => by
      have := GlobalTheory.PlaceDatum.frMapO_add (R.βV i) (R.βW i) 0 t n a b
      rw [zero_add] at this
      rw [this]
      simp [frMapO]
    rw [← smul_smul]
    refine h _ (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hnt) fun a b => ?_
    rw [hfn, ← hnE, mul_assoc, ← hfr]
    exact mul_mem (eToEAf_int' y) (hti a b)

end GlobalTheory.DilFlat

end
