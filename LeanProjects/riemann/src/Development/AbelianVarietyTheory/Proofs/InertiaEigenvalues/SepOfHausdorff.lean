import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeSpan

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WachTensor

noncomputable section

namespace GlobalTheory.NL.BaseField

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}

theorem res_eq_one_iff (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) : W.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h1 := W.χΓ_res g
  rw [P.PD_χ] at h1
  constructor
  · intro h
    rw [h, map_one, Units.val_one, map_one] at h1
    exact Units.ext ((algebraMap ℚ_[l] ↥LL.1).injective (h1.symm.trans (map_one _).symm))
  · intro h
    rw [h, Units.val_one, map_one] at h1
    apply W.χΓ_inj
    rw [map_one]
    exact Units.ext (Subtype.ext h1)

theorem ker_transfer {K' : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K')))
    (h : Good K s LL) (h0 : K0 K = K0 K') (g' : ↥(GK K')) (hg : W'.resΓ g' = 1) :
    ∃ g : ↥(GK K), W.resΓ g = 1 ∧ (g : GQ l) = g' :=
  have h1 := (res_eq_one_iff W' g').1 hg
  ⟨⟨g', mem_GK_of_chi P h.2.2.1 h0 g'.2 h1⟩, (res_eq_one_iff W _).2 h1, rfl⟩

theorem sep_of_hausdorff {R : Type} [CommRing R] (a : R) (h : IsHausdorff (Ideal.span {a}) R) (x : R)
    (hx : ∀ k : ℕ, a ^ k ∣ x) : x = 0 :=
  h.haus x fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end Concrete

set_option maxHeartbeats 1600000 in

theorem rings_mem (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (h0 : K0 K = K0 K') :
    (∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a) ∧
      ∀ a, ∃ a', ((F l).E K' s LL h').tie.ioE a' = ((F l).E K s LL h).tie.ioE a := by
  obtain ⟨c1, -, c3, -, c5⟩ := GlobalTheory.HWL.TensorWitt.main l LL
  have h1 : ∀ a, ∃ a', ((F l).E K' s LL h').tie.io a' = ((F l).E K s LL h).tie.io a :=
    io_mem _ _ Subtype.val_injective (descends _) c3 (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.2.2.1
      (fun g' hg' => by
        obtain ⟨g, hg, e⟩ := ker_transfer _ _ h h0 g' hg'
        exact ⟨g, hg, congrArg ((D.locA l).gRW LL) e⟩)
      (sep_of_hausdorff _ (c5 _ (GlobalTheory.Cyc.εroot_sub_one_not_unit (D.locA l) s)).toIsHausdorff)
  refine ⟨h1, ioE_mem _ _ (((D.loc l).PD_p K').trans ((D.loc l).PD_p K).symm) h1 ?_⟩
  rw [(D.loc l).PD_p K]
  exact sep_of_hausdorff _ c1.toIsHausdorff

section Two

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K K' : FinExt l} {s : ℕ} {LL : FinExt l}
  {h : Good K s LL} {h' : Good K' s LL}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  {W' : LocWach (P.PD K') ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K'))}
  (E : EtSit P AI K s LL h W) (E' : EtSit P AI K' s LL h' W') (T : Lt K LL) (T' : Lt K' LL)

set_option maxHeartbeats 800000 in

theorem jD_mem_sit (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e : ↥T.L.T →ₗ[↥(OL LL)] ↥T'.L.T)
    (he : ∀ (g : ↥(GK K)) (g' : ↥(GK K')), (g : GQ l) = g' → ∀ t, e (T.actT g t) = T'.actT g' (e t))
    (x : W.DD T) : ∃ x', E'.tie.jD T' x' =
      TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) e (E.tie.jD T x) :=
  jD_mem E.tie E'.tie (descends E') (map_ne_top E) (φRW_surjective LL) hE T T' e (fun g' hg' =>
    (ker_transfer W W' h h0 g' hg').imp fun g hg => ⟨hg.1, congrArg (AI.gRW LL) hg.2, he g g' hg.2⟩) x

variable (hle : K.1 ≤ K'.1) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T)
  (hact : ∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t))

include hact in
theorem act_fwd (g' : ↥(GK K')) (g : ↥(GK K)) (e : (g' : GQ l) = g) (t : ↥T'.L.T) :
    eT.toLinearMap (T'.actT g' t) = T.actT g (eT.toLinearMap t) :=
  (hact g' t).trans (congrArg (fun u : ↥(GK K) => T.actT u (eT t)) (Subtype.ext e))

include hact in
theorem act_bwd (g : ↥(GK K)) (g' : ↥(GK K')) (e : (g : GQ l) = g') (t : ↥T.L.T) :
    eT.symm.toLinearMap (T.actT g t) = T'.actT g' (eT.symm.toLinearMap t) := by
  apply eT.injective
  have h1 := act_fwd T T' hle eT hact g' g e.symm (eT.symm t)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 ⊢
  exact h1.symm

set_option maxHeartbeats 800000 in
include hact in
theorem jD_bwd (h0 : K0 K = K0 K') (hE : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x) (x : W.DD T) :
    ∃ x', TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap
      (E'.tie.jD T' x') = E.tie.jD T x :=
  (jD_mem_sit E E' T T' h0 hE eT.symm.toLinearMap (act_bwd T T' hle eT hact) x).imp fun _ hx' =>
    (congrArg (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) hx').trans
      (map_id_symm eT.symm (E.tie.jD T x))

set_option maxHeartbeats 800000 in
include hact in
theorem modules_eq (h0 : K0 K' = K0 K) (a1 : ∀ x, ∃ x', E'.tie.io x' = E.tie.io x)
    (a2 : ∀ x, ∃ x', E.tie.io x' = E'.tie.io x) (e1 : ∀ x, ∃ x', E'.tie.ioE x' = E.tie.ioE x)
    (e2 : ∀ x, ∃ x', E.tie.ioE x' = E'.tie.ioE x) (hQ : E'.tie.io W'.Q = E.tie.io W.Q)
    (hinj : Function.Injective E'.tie.ioE)
    (hb : IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)))
    (h10 : IsCrys (P.PD K') T'.ρ → p10 W' T') :
    (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.tie.jD T') =
      Set.range (E.tie.jD T) ∧ (IsCrys (P.PD K) T.ρ → IsCrys (P.PD K') T'.ρ →
      (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) ''
        (E'.tie.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.tie.jD T '' (W.N T : Set (W.DD T))) := by
  have d1 := jD_mem_sit E' E T' T h0 e2 eT.toLinearMap (act_fwd T T' hle eT hact)
  have d2 := jD_bwd E E' T T' hle eT hact h0.symm e1
  refine ⟨Set.Subset.antisymm ?_ ?_, fun hT hT' => ?_⟩
  · rintro _ ⟨_, ⟨x', rfl⟩, rfl⟩
    exact d1 x'
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := d2 x
    exact ⟨_, ⟨x', rfl⟩, hx'⟩
  · exact (hb hT).elim fun b => N_eq E.tie E'.tie T T' eT hT (h10 hT') b hinj a1 a2 e1 hQ d2 d1
      fun g' => ⟨⟨(g' : GQ l), GK_le hle g'.2⟩, rfl, hact g'⟩

end Two

set_option maxHeartbeats 800000 in

theorem base_indep : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → let W' := (HW l).W K' s LL h'; let E' := ((F l).E K' s LL h').tie; Set.range E.io = Set.range E'.io ∧ Set.range E.ioE = Set.range E'.ioE ∧ ∀ (T : Lt K LL) (T' : Lt K' LL) (eT : ↥T'.L.T ≃ₗ[↥(OL LL)] ↥T.L.T), (∀ (g : ↥(GK K')) (t : ↥T'.L.T), eT (T'.actT g t) = T.actT ⟨(g : GQ l), GK_le hle g.2⟩ (eT t)) → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' Set.range (E'.jD T') = Set.range (E.jD T) ∧ (IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K') T'.ρ → (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL) eT.toLinearMap) '' (E'.jD T' '' (W'.N T' : Set (W'.DD T'))) = E.jD T '' (W.N T : Set (W.DD T))) := by
  intro D HW F l _ K s LL h W E K' h' hle h0 W' E'
  have a1 := (rings_mem D HW F l K s LL h K' h' h0.symm).1
  have e1 := (rings_mem D HW F l K s LL h K' h' h0.symm).2
  have a2 := (rings_mem D HW F l K' s LL h' K h h0).1
  have e2 := (rings_mem D HW F l K' s LL h' K h h0).2
  have q := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have q1 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.1
  have q2 := (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').2.2.2.1
  refine ⟨?_, ?_, fun T T' eT hact => ?_⟩
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 a1) (Set.range_subset_iff.2 a2)
  · exact Set.Subset.antisymm (Set.range_subset_iff.2 e1) (Set.range_subset_iff.2 e2)
  have hb := N_basis D HW F l K s LL h T
  have h10 : IsCrys ((D.loc l).PD K') T'.ρ → p10 ((HW l).W K' s LL h') T' := GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F l K' s LL h' T'
  exact modules_eq ((F l).E K s LL h) ((F l).E K' s LL h') T T' hle eT hact h0 a1 a2 e1 e2 (q1.trans q.symm)
    q2 hb h10

end GlobalTheory.NL.BaseField
