import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftCocycleMem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr
open GlobalTheory.CompanionTheory.GrForm (wz wz_mem rep_add rep_neg sum_wz_sub rep_congr a_eq form_eq form_sub_mem)
open GlobalTheory.CompanionTheory.GrCech (mulMor mulT_congr mulMor_add mulMor_mul mulMor_smul res_res pull_mk)

variable {b : Base} {L : b.Fun} {Y : Scheme.{0}} {qY : Y ⟶ Spec (CommRingCat.of b.R)} (𝔭 : Pts L qY)

theorem sub_mem_of_lift {W : Y.Opens} {T T' : Thick L} (φ : T ⟶ T') (h : InY 𝔭 W T) (h' : InY 𝔭 W T') (f : Γ(Y, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev 𝔭 T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev 𝔭 T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat 𝔭 φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : Y.Opens} (T : Thick L) (h : InY 𝔭 W T) (f g : Γ(Y, W)) :
    lft 𝔭 W T f * lft 𝔭 W T g - lft 𝔭 W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec 𝔭 T h, lft_spec 𝔭 T h, lft_spec 𝔭 T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick L)) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T :=
  GlobalTheory.CompanionTheory.GrCech.J_mul_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) r hv hw

def evLift {Q : ObjectProperty (Thick L)} {W : Y.Opens} (_hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    (T : Q.FullSubcategory) : (sP Q).A.obj T := lft 𝔭 W T.obj f

theorem mk_evLift {Q : ObjectProperty (Thick L)} {W : Y.Opens} (hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    (T : Q.FullSubcategory) : Ideal.Quotient.mk T.obj.J (evLift 𝔭 hQ f T) = ev 𝔭 T.obj (hQ _ T.property) f :=
  lft_spec 𝔭 _ _ _

theorem sub_mem_of_mk {T : Thick L} {x y : T.B} (h : Ideal.Quotient.mk T.J x = Ideal.Quotient.mk T.J y) :
    x - y ∈ T.J := Ideal.Quotient.eq.1 h

theorem evLift_nat {Q : ObjectProperty (Thick L)} {W : Y.Opens} (hQ : ∀ T, Q T → InY 𝔭 W T) (f : Γ(Y, W))
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    evLift 𝔭 hQ f T' - ((sP Q).A.map φ).hom (evLift 𝔭 hQ f T) ∈ (sP Q).J.S T' := by
  refine sub_mem_of_mk (T := T'.obj) ?_
  rw [mk_evLift 𝔭, ev_nat 𝔭 φ.hom (hQ _ T.property) (hQ _ T'.property), ← mk_evLift 𝔭 hQ f T]
  rfl

def fAct {Q : ObjectProperty (Thick L)} (hF : IsFil (sP Q) (sFil Q)) {W : Y.Opens}
    (hQ : ∀ T, Q T → InY 𝔭 W T) (r : ℕ) (f : Γ(Y, W)) :
    HU (GF L r) Q r →ₗ[b.R] HU (GF L r) Q r :=
  (mulMor hF r (evLift 𝔭 hQ f) (evLift_nat 𝔭 hQ f)).pull r

section ThAct
variable {Q : ObjectProperty (Thick L)} (hF : IsFil (sP Q) (sFil Q)) {W : Y.Opens}
  (hQ : ∀ T, Q T → InY 𝔭 W T) (r : ℕ)

theorem fAct_add (f g : Γ(Y, W)) (c : HU (GF L r) Q r) :
    fAct 𝔭 hF hQ r (f + g) c = fAct 𝔭 hF hQ r f c + fAct 𝔭 hF hQ r g c := by
  refine mulMor_add hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭, map_add (Ideal.Quotient.mk T.obj.J), mk_evLift 𝔭, mk_evLift 𝔭, map_add]

theorem fAct_mul (f g : Γ(Y, W)) (c : HU (GF L r) Q r) :
    fAct 𝔭 hF hQ r (f * g) c = fAct 𝔭 hF hQ r f (fAct 𝔭 hF hQ r g c) := by
  refine mulMor_mul hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭, map_mul (Ideal.Quotient.mk T.obj.J), mk_evLift 𝔭, mk_evLift 𝔭, map_mul]

theorem fAct_one (c : HU (GF L r) Q r) : fAct 𝔭 hF hQ r 1 c = c := by
  refine (mulMor_smul hF r _ (1 : b.R) (fun T => sub_mem_of_mk (T := T.obj) ?_) r c).trans (one_smul _ _)
  rw [mk_evLift 𝔭, map_one, map_one (algebraMap b.R _)]
  exact (map_one _).symm

def fHom : Γ(Y, W) →+* AddMonoid.End (HU (GF L r) Q r) :=
  RingHom.mk' { toFun := fun f => (fAct 𝔭 hF hQ r f).toAddMonoidHom
                map_one' := AddMonoidHom.ext fun c => fAct_one 𝔭 hF hQ r c
                map_mul' := fun f g => AddMonoidHom.ext fun c => fAct_mul 𝔭 hF hQ r f g c }
    fun f g => AddMonoidHom.ext fun c => fAct_add 𝔭 hF hQ r f g c

theorem fHom_apply (f : Γ(Y, W)) (c : HU (GF L r) Q r) : fHom 𝔭 hF hQ r f c = fAct 𝔭 hF hQ r f c := rfl

theorem res_fAct {Q' : ObjectProperty (Thick L)} (hF' : IsFil (sP Q') (sFil Q')) {W' : Y.Opens}
    (hQ' : ∀ T, Q' T → InY 𝔭 W' T) (hW : W' ≤ W) (hle : Q' ≤ Q) (f : Γ(Y, W)) (c : HU (GF L r) Q r) :
    (resU (GF L r) hle).pull r (fAct 𝔭 hF hQ r f c) =
      fAct 𝔭 hF' hQ' r (rs hW f) ((resU (GF L r) hle).pull r c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change Submodule.Quotient.mk ((resU (GF L r) hle).hom.mapZ r ((mulMor hF r (evLift 𝔭 hQ f) (evLift_nat 𝔭 hQ f)).hom.mapZ r z)) =
    Submodule.Quotient.mk ((mulMor hF' r (evLift 𝔭 hQ' (rs hW f)) (evLift_nat 𝔭 hQ' (rs hW f))).hom.mapZ r ((resU (GF L r) hle).hom.mapZ r z))
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine Eq.symm (((mulT_congr hF' r (T := s.obj (Fin.last r)) (u := evLift 𝔭 hQ' (rs hW f) _) (v := evLift 𝔭 hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))) ?_ _)).trans ?_)
  · refine sub_mem_of_mk (T := (s.obj (Fin.last r)).obj) ?_
    rw [mk_evLift]
    exact (ev_res 𝔭 hW _ (hQ _ (hle _ (s.obj (Fin.last r)).property)) _ _).trans (mk_evLift 𝔭 hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))).symm
  · rfl

theorem fAct_str (a : b.R) (c : HU (GF L r) Q r) : fAct 𝔭 hF hQ r (strV qY W a) c = a • c := by
  refine mulMor_smul hF r _ a (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift 𝔭]
  exact ev_str 𝔭 _ _ a

end ThAct

theorem rp_class {W : Y.Opens} {P : ObjectProperty (Thick L)} {d r : ℕ} {u : Fin d → ∀ T : Thick L, T.B}
    {x : Idx r d → Γ(Y, W)} {c c' : HU (GF L r) P r} (h : Rp 𝔭 (W := W) P u x c) (h' : Rp 𝔭 (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inY_mono {W W' : Y.Opens} (h : W' ≤ W) {T : Thick L} (hT : InY 𝔭 W' T) : InY 𝔭 W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : Y.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(Y, V)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 V t u) {t' : Fin d → Γ(Y, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift 𝔭 W t' u := by
  intro i T hT
  rw [ht, hu i T (inY_mono 𝔭 h hT), ev_res 𝔭 h T (inY_mono 𝔭 h hT) hT]

def Free (W : Y.Opens) (P : ObjectProperty (Thick L)) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick L, T.B) : Prop :=
  (∀ cl : HU (GF L r) P r, ∃ x, Rp 𝔭 (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(Y, W), Rp 𝔭 (W := W) P u x 0 → x = 0

section Forms
variable {W : Y.Opens} {d : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
  {P : ObjectProperty (Thick L)} {r : ℕ}

theorem rp_zero (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) :
    Rp 𝔭 (W := W) P u (0 : Idx r d → Γ(Y, W)) (0 : HU (GF L r) P r) := by
  obtain ⟨c, hc⟩ := exists_rp 𝔭 W t u hu P hP r 0
  have h2 := (rp_add 𝔭 W t u hu P hP r _ _ _ _ hc (rp_add 𝔭 W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(Y, W)) (c : κ' → HU (GF L r) P r) (h : ∀ k ∈ S, Rp 𝔭 (W := W) P u (x k) (c k)) :
    Rp 𝔭 (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero 𝔭 hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rp_add 𝔭 W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hu : IsLift 𝔭 W t u) (hP : ∀ T, P T → InY 𝔭 W T) (hF : Free 𝔭 W P r u)
    {x x' : Idx r d → Γ(Y, W)} {c : HU (GF L r) P r} (h : Rp 𝔭 (W := W) P u x c) (h' : Rp 𝔭 (W := W) P u x' c) : x = x' := by
  have h2 := (rp_add 𝔭 W t u hu P hP r _ _ _ _ h (rp_add 𝔭 W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

end Forms

theorem evLift_mul_sub {W : Y.Opens} {P : ObjectProperty (Thick L)} (hP : ∀ T, P T → InY 𝔭 W T) (z x : Γ(Y, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift 𝔭 hP z T) * lft 𝔭 W T.obj x - lft 𝔭 W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift 𝔭, lft_spec 𝔭 _ (hP _ T.property), lft_spec 𝔭 _ (hP _ T.property), map_mul]

theorem rp_fAct {W : Y.Opens} {P : ObjectProperty (Thick L)} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InY 𝔭 W T) {d r : ℕ} {t : Fin d → Γ(Y, W)} {u : Fin d → ∀ T : Thick L, T.B}
    (hu : IsLift 𝔭 W t u) (z : Γ(Y, W)) (x : Idx r d → Γ(Y, W)) (c : HU (GF L r) P r)
    (hc : Rp 𝔭 (W := W) P u x c) : Rp 𝔭 (W := W) P u (fun I => z * x I) (fAct 𝔭 hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift 𝔭 hP z) (evLift_nat 𝔭 hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift 𝔭 φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift 𝔭 hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub 𝔭 hP z (x I) (s.obj (Fin.last r))) hw
    have e := GlobalTheory.CompanionTheory.GrForm.units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift 𝔭 hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft 𝔭 W (s.obj (Fin.last r)).obj (x I))
      (lft 𝔭 W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem free_of_frame (hLoc : KH.LocGr) {W : Y.Opens} {Q : ObjectProperty (Thick L)} (hin : ∀ T : Q.FullSubcategory, InY 𝔭 W T.obj)
    {d : ℕ} (u : Fin d → ∀ T : Thick L, T.B) (t : Fin d → Γ(Y, W)) (E : Frame (sP Q) d) (σ : ∀ T, E.D ⟶ T)
    (θ : Γ(Y, W) ≃+* (sP Q).A.obj E.D) (hGr : E.GrConst (sFil Q)) (hbot : (sFil Q 1).S E.D = ⊥)
    (hco : E.Coords fun i => θ (t i)) (hσ : ∀ i T, ((sP Q).A.map (σ T)).hom (θ (t i)) = u i T.obj)
    (hpt : ∀ (T : Q.FullSubcategory) (h : InY 𝔭 W T.obj) (f : Γ(Y, W)),
      Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP Q).A.map (σ T)).hom (θ f)) = ev 𝔭 T.obj h f)
    (Qp : Poly (sP Q)) (r : ℕ) (hC : ∀ r' : ℤ, r' ≤ (r : ℤ) + 1 → Qp.Crit (sFil Q) r') : Free 𝔭 W Q r u := by
  have hF : IsFil (sP Q) (sFil Q) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  obtain ⟨-, hL⟩ := hLoc Qp hF E σ hGr (r : ℤ) hC r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have key : ∀ (y : Idx r d → Γ(Y, W)) (z : ComposableArrows Q.FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP Q) (fun i T => u i T.obj) I.1 z *
          (show (sP Q).A.obj (z.obj (Fin.last r)) from lft 𝔭 W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil Q ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec 𝔭 _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil Q (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

theorem off_zero (hLoc : KH.LocGr) {Q : ObjectProperty (Thick L)} {d : ℕ} (E : Frame (sP Q) d) (σ : ∀ T, E.D ⟶ T)
    (hGr : E.GrConst (sFil Q)) (hbot : (sFil Q 1).S E.D = ⊥) (Qp : Poly (sP Q)) (r j : ℕ)
    (hC : ∀ r' : ℤ, r' ≤ (r : ℤ) + 1 → Qp.Crit (sFil Q) r') (hj : j ≠ r) : Subsingleton (HU (GF L r) Q j) := by
  have hF : IsFil (sP Q) (sFil Q) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  obtain ⟨h1, hL⟩ := hLoc Qp hF E σ hGr (r : ℤ) hC j
  rcases lt_or_gt_of_ne hj with h | h
  · obtain ⟨q, rfl⟩ : ∃ q, r = j + (q + 1) := ⟨r - j - 1, by omega⟩
    obtain ⟨h2, -⟩ := hL (q + 1) (by push_cast; ring)
    refine ⟨fun a c => ?_⟩
    have z : ∀ c : CH.H (gr (sFil Q) (((j + (q + 1) : ℕ) : ℤ))) j, c = 0 := by
      intro c
      obtain ⟨x, hx, f, hf, rfl, hs⟩ := h2 c
      have hx0 : ∀ I, x I = 0 := fun I => by
        have h3 : (sFil Q ((q + 1 : ℕ) : ℤ)).S E.D ≤ (sFil Q 1).S E.D := hF.anti (by push_cast; omega) _
        exact Ideal.mem_bot.1 (hbot ▸ h3 (hx I))
      have f0 : f = 0 := funext fun s => Subtype.ext (by
        refine (hs s).trans ?_
        have e0 : ∀ I : Idx j d, E.form σ I.1 (x I) s = 0 := fun I => by
          rw [hx0 I]
          unfold Frame.form
          rw [map_zero, mul_zero]
        have e1 : (∑ I : Idx j d, E.form σ I.1 (x I) s) = 0 := Finset.sum_eq_zero fun I _ => e0 I
        exact (congrArg (Ideal.Quotient.mk _) e1).trans (map_zero _))
      subst f0
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)
    exact (z a).trans (z c).symm
  · exact h1 (by exact_mod_cast h)

theorem basis_gen {W₀ : Y.Opens} {d : ℕ} (t₀ : Fin d → Γ(Y, W₀)) (P₀ : ObjectProperty (Thick L))
    (hP₀ : ∀ T, P₀ T → InY 𝔭 W₀ T) (r : ℕ) :
    ∃ ω : Idx r d → HU (GF L r) P₀ r, ∀ (W : Y.Opens) (hle : W ≤ W₀) (Q : ObjectProperty (Thick L)) (hQ₀ : Q ≤ P₀)
      (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InY 𝔭 W T)
      (_ : Free 𝔭 W Q r (fun k T => lft 𝔭 W₀ T (t₀ k))) (h : HU (GF L r) Q r),
      ∃! f : Idx r d → Γ(Y, W), h = ∑ k, fAct 𝔭 hF hQW r (f k) ((resU (GF L r) hQ₀).pull r (ω k)) := by
  classical
  let u : Fin d → ∀ T : Thick L, T.B := fun k T => lft 𝔭 W₀ T (t₀ k)
  have hu : IsLift 𝔭 W₀ t₀ u := fun k T h => lft_spec 𝔭 T h _
  choose ω hω using fun k : Idx r d => exists_rp 𝔭 W₀ t₀ u hu P₀ hP₀ r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hle Q hQ₀ hF hQW hFree h
  have hu' : IsLift 𝔭 W (fun i => rs hle (t₀ i)) u := isLift_res 𝔭 hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(Y, W), Rp 𝔭 (W := W) Q u f
      (∑ k, fAct 𝔭 hF hQW r (f k) ((resU (GF L r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum 𝔭 hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(Y, W₀)) I)) _
      (fun k _ => rp_fAct 𝔭 hF hQW hu' (f k) _ _
        (rp_res 𝔭 W₀ W hle t₀ u hu P₀ Q hQ₀ hP₀ hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(Y, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class 𝔭 hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp 𝔭 (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef 𝔭 hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.FibGr
end
