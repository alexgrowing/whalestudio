import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mul_eq_zero_of_disj {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {a b : AE D} (ha : a ∈ idAt D P)
    (hb : b ∈ idAt D P') : a * b = 0 := by
  obtain ⟨ha0, haw⟩ := mem_idAt_iff.1 ha
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero ha0, zero_mul, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [hbw v (hd v hv), mul_zero]
    · rw [haw v hv, zero_mul]

theorem mul_eq_zero_of_off {P : Pl D → Prop} {a b : AE D} (ha : a ∈ idOff D P) (hb : b ∈ idAt D P) : a * b = 0 := by
  obtain ⟨hb0, hbw⟩ := mem_idAt_iff.1 hb
  have haw : ∀ v, P v → compAt D v a = 0 := by
    intro v hv
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨v, hv⟩)
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun v => ?_
  · rw [map_mul, compInf_eq_zero hb0, mul_zero, map_zero]
  · rw [map_mul, map_zero, compFin_eq_compAt, compFin_eq_compAt]
    by_cases hv : P v
    · rw [haw v hv, zero_mul]
    · rw [hbw v hv, mul_zero]

def idem (P : Pl D → Prop) : AE D := pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem idem_mem (P : Pl D → Prop) : idem P ∈ idAt D P := tmul_mem_idAt (indicatorAdele_supported D.host.F P) 1

theorem cA_idem (P : Pl D → Prop) : cA D (idem P) = idem P := by
  show pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] star (1 : D.host.E) = _
  rw [star_one]; rfl

theorem idem_mul {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : idem P * a = a := by
  rw [mul_comm]; exact mul_indP ha

theorem symplO_disj {S T : HSp D} {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {x y : WO S T} (hx : MxAt P x)
    (hy : MxAt P' y) : symplO S T x y = 0 := by
  refine GlobalTheory.SplitScalar.symplO_eq_zero S T (a := idem P) (b := idem P') ?_ (fun i j => idem_mul (hx i j))
    (fun i j => idem_mul (hy i j))
  rw [cA_idem]
  exact mul_eq_zero_of_disj hd (idem_mem P) (idem_mem P')

theorem mxAt_mono {P Q : Pl D → Prop} (h : ∀ p, P p → Q p) {m n : ℕ} {x : Mx D m n} (hx : MxAt P x) : MxAt Q x := by
  intro i j
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 (hx i j)
  exact mem_idAt_iff.2 ⟨h0, fun w hw' => hw w fun hp => hw' (h w hp)⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem mem_congGrp' {V : HSp D} {I : Ideal (AE D)} {g : GA D V} (hg : g ∈ congGrp V I) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp at hg
  rw [MonoidHom.mem_ker] at hg
  intro i j
  have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) hg
  rw [← Ideal.Quotient.eq]
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem actO_off {S T : HSp D} {P : Pl D → Prop} {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P)
    (hh : h ∈ grpOff T P) {u : WO S T} (hu : MxAt P u) : actO S T g h u = u := by
  have hg' := mem_congGrp' (inv_mem hg)
  have hh' := mem_congGrp' hh
  have h1 : HMul.hMul (mt T h - 1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_off (by simpa using hh' i k) (hu k j)
  have h2 : HMul.hMul (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹ - 1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      rw [mul_comm]; exact mul_eq_zero_of_off (by simpa using hg' k j) (hu i k)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  unfold actO
  rw [h1]
  exact h2

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem compAt_idem {P : Pl D → Prop} {w : Pl D} (hpw : P w) : compAt D w (idem P) = 1 := by
  rw [← compFin_eq_compAt]
  show evalV D.host.F w (indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
  rw [evalV_indP, if_pos hpw]
  rfl

theorem sub_idem_mem {P P' : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D (fun p => P p ∨ P' p)) :
    a - idem P * a ∈ idAt D P' := by
  obtain ⟨h0, hw⟩ := mem_idAt_iff.1 ha
  refine mem_idAt_iff.2 ⟨by rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero], fun w hw' => ?_⟩
  by_cases hpw : P w
  · rw [RingHom.map_sub, RingHom.map_mul, compAt_idem hpw, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, hw w (fun h => h.elim hpw hw'), mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in

theorem split_latO (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {P P' : Pl D → Prop} (hd : ∀ p, P p → ¬ P' p) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) (fun p => P p ∨ P' p)) :
    MxAt P (idem P • u) ∧ MxAt P' (u - idem P • u) ∧ idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P ∧
      u - idem P • u ∈ latO S T (LS : Set _) (LT : Set _) P' := by
  have ann := GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hLS hLT
  have hmono : ∀ (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have huM := latO_mxAt hu
  have hu1 : MxAt P (idem P • u) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (idem_mem P)
  have hu2 : MxAt P' (u - idem P • u) := fun i j => by
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact sub_idem_mem (huM i j)
  refine ⟨hu1, hu2, (ann P _ hu1).2 fun u' hu' => ?_, (ann P' _ hu2).2 fun u' hu' => ?_⟩
  · have hsub : symplO S T (idem P • u) u' = symplO S T u u' - symplO S T (u - idem P • u) u' := by
      rw [← GlobalTheory.SplitScalar.symplO_sub_left, sub_sub_cancel]
    rw [hsub, symplO_disj (fun p hp' hp => hd p hp hp') hu2 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inl hp) hu')
  · rw [GlobalTheory.SplitScalar.symplO_sub_left, symplO_disj hd hu1 (latO_mxAt hu'), sub_zero]
    exact (ann _ u huM).1 hu u' (hmono _ _ (fun p hp => Or.inr hp) hu')

theorem isHalf_parts {S T : HSp D} {P : Pl D → Prop} {e : AE D} {u : WO S T} (h : IsHalf e u) :
    IsHalf e (idem P • u) ∧ IsHalf e (u - idem P • u) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_left_comm, h i j]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, h i j, mul_left_comm, h i j]

end GlobalTheory.DisjComb

namespace GlobalTheory.DisjComb

open GlobalTheory.FinPl.LatMem

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  intro D ψ hψ S T P P' hd
  have HC := GlobalTheory.HeisComb.main D ψ S T
  have hcomm : ∀ (e : WO S T →₀ ℂ), CombAt P e → ∀ w : WO S T, MxAt P' w → ∀ f,
      heisO ψ S T w (comb ψ S T e f) = comb ψ S T e (heisO ψ S T w f) := by
    intro e he w hw f
    have h := HC.2.1 e (Finsupp.single w 1) (fun x hx y hy => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hy
      subst hy
      exact symplO_disj hd (he x hx) hw) f
    simp only [comb_single] at h
    exact h.symm
  have hmono : ∀ (LS : Lat S) (LT : Lat T) (Q Q' : Pl D → Prop), (∀ p, Q p → Q' p) →
      latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) Q' := by
    intro LS LT Q Q' hQ
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  have hnsmul : ∀ (Q : Pl D → Prop) (x : WO S T), MxAt Q x → MxAt Q ((2 : ℕ) • x) := by
    intro Q x hx i j
    rw [Matrix.smul_apply]
    exact nsmul_mem (hx i j) 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e e' he he' f
    exact HC.2.1 e e' (fun x hx y hy => symplO_disj hd (he x hx) (he' y hy)) f
  · intro e he
    have hfin : IsFinComb e := fun u hu => Matrix.ext fun i j => (mem_idAt_iff.1 (he u hu i j)).1
    refine ⟨hfin, fun LS LT f hf => ⟨HC.2.2.1 e f hf.1 hfin hψ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩⟩
    · rw [hcomm e he _ (hnsmul P' u (latO_mxAt hu)), hf.2.1 u hu]
    · rw [hcomm e he u (latO_mxAt hu), hf.2.2 e' he' u hu hh]
  · intro χS χT om hom e he g hg h hh f hf
    unfold comb
    rw [map_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [map_smul, hom.om_heis g h u f hf, actO_off hg hh (he u hu)]
  · intro e e' he he'
    obtain ⟨c'', hsupp, heq⟩ := HC.1 e e'
    refine ⟨c'', fun w hw => ?_, heq⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsupp w hw
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (he x hx i j) (he' y hy i j)
  · intro LS LT f hLS hLT
    constructor
    · intro hf
      refine ⟨⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inl hp) hu) hh⟩,
        ⟨hf.1, fun u hu => hf.2.1 u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu),
        fun e he u hu hh => hf.2.2 e he u (hmono LS LT _ _ (fun p hp => Or.inr hp) hu) hh⟩⟩
    · rintro ⟨hP, hP'⟩
      refine ⟨hP.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, nsmul_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd (hnsmul P _ hm1) (hnsmul P' _ hm2)),
          hP'.2.1 _ hl2, hP.2.1 _ hl1]
      · obtain ⟨hm1, hm2, hl1, hl2⟩ := split_latO ψ hψ hLS hLT hd hu
        obtain ⟨h1, h2⟩ := isHalf_parts (P := P) hh
        have hsum : u = idem P • u + (u - idem P • u) := (add_sub_cancel _ _).symm
        rw [hsum, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_disj hd hm1 hm2), hP'.2.2 e he _ hl2 h2,
          hP.2.2 e he _ hl1 h1]

end GlobalTheory.DisjComb
