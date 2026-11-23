import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmoothQ
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PrepairingEtaleValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

set_option maxHeartbeats 1000000

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {ht : TFil l}
  {Lf : ∀ {M : Model l K} (r : ℕ) {j : ℕ}, M.T j → Fam M r j → Prop} (h1 : Half1 ht @Lf)
  {γ : ∀ {M : Model l K} {r j : ℕ}, Fam M r j → ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l]} (h2 : Half2 ht @γ)

include h1 h2 in
theorem indep {M : Model l K} (hM : M.Sm) {j r r' : ℕ} {v : M.T j} {x : Fam M r j} {x' : Fam M r' j} (hx : Lf r v x)
    (hx' : Lf r' v x') (a : ℕ) : γ x a = γ x' a := by
  obtain ⟨k, hk⟩ := h1.uniq M hM j
  have a1 := h1.sh r' (rfl : r + r' = r + r') hx
  have a2 := h1.sh r (Nat.add_comm r' r) hx'
  have e := hk (r + r') v _ _ a1 a2
  rw [← h2.sh hM r' rfl x (h1.comp hx) a, ← h2.sh hM r (Nat.add_comm r' r) x' (h1.comp hx') a,
    ← h2.sh hM k rfl _ (h1.comp a1) a, ← h2.sh hM k rfl _ (h1.comp a2) a, e]

def rr {M : Model l K} (hM : M.Sm) (j : ℕ) : ℕ := (h1.ex M hM j).choose

def xx {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Fam M (rr h1 hM j) j := ((h1.ex M hM j).choose_spec v).choose

theorem xx_spec {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Lf _ v (xx h1 hM v) := ((h1.ex M hM j).choose_spec v).choose_spec

variable (γ) in

def gT {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v : M.T j) : Module.Dual K (Hdg M.q a j) →+ ℂ_[l] := γ (xx h1 hM v) a

include h2 in
theorem gT_eq {M : Model l K} (hM : M.Sm) (a : ℕ) {j r : ℕ} {v : M.T j} {x : Fam M r j} (hx : Lf r v x) :
    gT h1 (@γ) hM a v = γ x a := indep h1 h2 hM (xx_spec h1 hM v) hx a

include h2 in
theorem gT_add {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v w : M.T j) :
    gT h1 (@γ) hM a (v + w) = gT h1 (@γ) hM a v + gT h1 (@γ) hM a w :=
  (gT_eq h1 h2 hM a (h1.add (xx_spec h1 hM v) (xx_spec h1 hM w))).trans
    (h2.add hM _ _ (h1.comp (xx_spec h1 hM v)) (h1.comp (xx_spec h1 hM w)) a)

include h2 in
theorem gT_smul {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (z : ℤ_[l]) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    gT h1 (@γ) hM a (z • v) φ = qC l (z : ℚ_[l]) * gT h1 (@γ) hM a v φ := by
  rw [gT_eq h1 h2 hM a (h1.smul z (xx_spec h1 hM v)), h2.lin hM _ _ (h1.comp (xx_spec h1 hM v)), θA_zA]
  rfl

include h2 in
theorem gT_act {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (σ : K.fixingSubgroup) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    qC l (period_ring_base.χ σ.1) ^ a * gT h1 (@γ) hM a (M.actT j σ v) φ = period_ring_base.σC σ.1 (gT h1 (@γ) hM a v φ) := by
  have e1 := gT_smul h1 h2 hM a ((DeRhamTwist.Twist.chi0 l σ.1 ^ rr h1 hM j : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v) φ
  replace e1 := (DFunLike.congr_fun (gT_eq h1 h2 hM a (h1.gal σ (xx_spec h1 hM v))) φ).symm.trans e1
  rw [Units.val_pow_eq_pow_val, PadicInt.coe_pow, map_pow] at e1
  have e2 := h2.gal hM σ _ (h1.comp (xx_spec h1 hM v)) a φ
  rw [e1] at e2
  have hc : qC l (period_ring_base.χ σ.1) ^ rr h1 hM j ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 (χ_ne _))
  refine mul_left_cancel₀ hc (Eq.trans ?_ e2)
  exact mul_left_comm _ _ _

def hV {M : Model l K} (hM : M.Sm) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  (TensorProduct.liftAddHom (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n)
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun u =>
      AddMonoidHom.mk' (fun φ => qC l z * gT h1 (@γ) hM a u φ) (by intros; simp [mul_add]))
        (by intros; ext; simp [gT_add h1 h2, mul_add])) (by intros; ext; simp [add_mul]))
    (by
      intro r z u
      ext φ
      simp only [AddMonoidHom.mk'_apply]
      rw [gT_smul h1 h2, Algebra.smul_def, map_mul]
      simp only [PadicInt.algebraMap_apply]
      ring) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]))

open Classical in

def hP (M : Model l K) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  if hM : M.Sm then hV h1 h2 hM a n else 0

theorem hP_tmV {M : Model l K} (hM : M.Sm) (a n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n (tmV M n z u) φ = qC l z * gT h1 (@γ) hM a u φ := by
  rw [hP, dif_pos hM]
  unfold hV tmV
  erw [TensorProduct.liftAddHom_tmul]
  rfl

theorem hP_toV {M : Model l K} (hM : M.Sm) (a : ℕ) {n r : ℕ} {u : M.T n} {x : Fam M r n} (hx : Lf r u x)
    (φ : Module.Dual K (Hdg M.q a n)) : hP h1 h2 M a n (M.toV n u) φ = γ x a φ := by
  rw [toV_eq, hP_tmV h1 h2 hM, map_one, one_mul, gT_eq h1 h2 hM a hx]

theorem hP_not {M : Model l K} (hM : ¬ M.Sm) (a n : ℕ) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n v φ = 0 := by
  rw [hP, dif_neg hM]; rfl

include h1 h2 in
theorem pre_of (hF : KFin) (hC : DlogClassExistsUnique) : Nonempty (HTPre l K) := ⟨{
  h := hP h1 h2
  lin := fun M a n z v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n (z • v) φ = qC l z * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [smul_tmV, hP_tmV h1 h2 hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add, AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  lin' := fun M a n k v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n v (k • φ) = kC K k * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [hP_tmV h1 h2 hM, gT]
        rw [h2.lin' hM _ (h1.comp (xx_spec h1 hM u)), mul_left_comm]
      · intro x y hx hy
        simp only [map_add, AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  fin := fun M hM a n => by
    have := proper_q hM
    have := smooth_q hM
    exact hF M.q a n
  equi := fun M hM a n σ v φ => by
    refine V_induction (p := fun v => qC l (period_ring_base.χ σ.1) ^ a * hP h1 h2 M a n (M.act n σ v) φ =
      period_ring_base.σC σ.1 (hP h1 h2 M a n v φ)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
    · intro z u
      simp only [act_tmV, hP_tmV h1 h2 hM]
      rw [map_mul, σC_qC, mul_left_comm, gT_act h1 h2 hM]
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, mul_add] at hx hy ⊢
      rw [hx, hy]
  nat := fun M N u hu hM hN a n v φ => by
    refine V_induction (p := fun v => hP h1 h2 M a n (Model.pullV u hu n v) φ =
      hP h1 h2 N a n v (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a n)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      simp only [pullV_tmV, hP_tmV h1 h2 hM, hP_tmV h1 h2 hN]
      rw [gT_eq h1 h2 hM a (h1.nat u hu (xx_spec h1 hN w)), h2.nat u hu hM hN _ (h1.comp (xx_spec h1 hN w))]
      rfl
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply] at hx hy ⊢
      rw [hx, hy]
  cup := fun M hM i j x y z hz m m' b b' c φ => by
    have hx := xx_spec h1 hM x
    have hy := xx_spec h1 hM y
    rw [hP_toV h1 h2 hM c (h1.cup rfl hz hx hy), h2.cup hM rfl _ _ (h1.comp hx) (h1.comp hy) b b' c φ]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hP_toV h1 h2 hM _ hx, hP_toV h1 h2 hM _ hy]
  one := fun M hM v hv φ => by rw [hP_toV h1 h2 hM 0 (h1.one M v hv), h2.one hM]
  first_chern_class_exists := fun M hM D _ hD => ⟨h1.first_chern_class_exists M D, hC M.q (genD D) (sSup_pb D _ hD)⟩
  c1 := fun M hM D hE hD r v c hv hc => by
    obtain ⟨x, hx, hl⟩ := h1.c1 M D hE hD r v hv
    have := h2.c1 hM D hD x c (h1.comp hl) hx hc
    exact ⟨fun φ => (hP_toV h1 h2 hM 1 hl φ).trans (this.1 φ),
      fun a ha φ => (hP_toV h1 h2 hM a hl φ).trans (by rw [this.2 a ha]; rfl)⟩ }⟩

end CrystallineSemistableComparison.HT
