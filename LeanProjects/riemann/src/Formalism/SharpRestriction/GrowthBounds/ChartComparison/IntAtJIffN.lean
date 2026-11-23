import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {Tau : Type} [Fintype Tau] {n : ℕ}

theorem val_tw_iff (hn : 0 < n) (k a : ℂ) (hk : k ≠ 0) (ha : a ≠ 0) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) (v : ℂ) :
    v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) M Q z ↔
      k * (a * detF c z * v) = fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z := by
  have h1 : fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z =
      k * (a * ((∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M Q z)) := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1]
  constructor
  · intro hv
    rw [nrm_val_M hn a G lam c M hM Q z v hv]
  · intro hv
    exact nrm_val_M' hn a ha G lam c M hM Q z v (mul_left_cancel₀ hk hv)

end Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} (S : StepIn M i hi G)

namespace StepIn

def sTw (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : ℂ :=
  S.kTw β * ((S.tw β).ch ((S.K β).y cl) : ℂ) *
    ∏ τ, (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ).det ^ (-(cTw D i))

def TwUnit (w : D.what₂.places.Pl) (β : S.Ch) : Prop :=
  ∀ (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ r : D.what₂.LL, r ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ r⁻¹ ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ D.what₂.embLL r = S.sTw β cl B'

def IntAtN (w : D.what₂.places.Pl) (β : S.Ch) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) : Prop :=
  ∀ B' : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ Pp ∈ IntSpan D w (M.lam i), ∀ z : Fr D i hi, S.embN β x cl z =
      fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Pp z

variable {S}

theorem sTw_ne (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : S.sTw β cl B' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (S.kTw_ne β) (Units.ne_zero _))
    (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (atInf_det_unit (embT D) B'⁻¹ τ).ne_zero)

set_option maxHeartbeats 1000000 in

theorem intAtJ_iff_N (w : D.what₂.places.Pl) (β : S.Ch) (hU : S.TwUnit w β) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) :
    S.IntAtJ w β x cl ↔ S.IntAtN w β x cl := by
  refine forall_congr' fun B' => forall_congr' fun hB => ?_
  obtain ⟨r, hr, hr', er⟩ := hU cl B' hB
  have key : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) (z : Fr D i hi),
      M.emb i x cl.1 (S.eY.symm z) =
        fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q z ↔
      S.embN β x cl z = fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1)
        (D.what₂.embLL r • Q) z := by
    intro Q z
    rw [er]
    exact val_tw_iff (D.R.N_pos i) (S.kTw β) _ (S.kTw_ne β) (Units.ne_zero _) _ (M.lam i) (cTw D i) _
      (atInf_det_unit (embT D) B'⁻¹) Q z _
  have hr0 : D.what₂.embLL r ≠ 0 := by rw [er]; exact sTw_ne β cl B'
  constructor
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r • Q, intSpan_smul w (M.lam i) r hr hQ, fun z => (key Q z).1 ?_⟩
    rw [h, Equiv.apply_symm_apply]
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r⁻¹ • Q, intSpan_smul w (M.lam i) r⁻¹ hr' hQ, fun z' => ?_⟩
    have h1 := (key (D.what₂.embLL r⁻¹ • Q) (S.eY z')).2 (by
      rw [smul_smul, map_inv₀, mul_inv_cancel₀ hr0, one_smul]
      exact h _)
    rwa [Equiv.symm_apply_apply] at h1

variable (S)

def ValIntN (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) : Prop :=
  ∀ β, ValIntAt (S.K β).lev (embT D) D.what₂.embLL (S.charts.gat β) e (S.loc β) S.pos (S.embN β) (S.K β).y (S.IntAtN w β)

variable {S}

theorem valIntJ_of (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (hU : ∀ β, S.TwUnit w β) (h : S.ValIntN e w) : S.ValIntJ e w :=
  fun β x a L cl hL hp => (h β x a L cl hL hp).trans (intAtJ_iff_N w β (hU β) x cl).symm

end StepIn

end Formalism.MainNotions.G.CmpJ

end
