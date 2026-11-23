import CompanionTheory.AutomorphicTheory.NumberFieldModels.NFTieProv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVsTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.MainStatements.NFTie

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem qr_of (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := by
  refine ⟨q.2.1, ?_⟩
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  exact q.2.2

theorem mu_domR (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
  Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec (qr_of hpl q)

theorem zeta_mu (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (NF.muZ P.k P.r Bs.μsec q.1.2) = q.1.2 :=
  Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec (qr_of hpl q).2

theorem gg_mu (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) = Complex.normSq q.1.2 - P.TT := by
  unfold Q.GGl
  rw [zeta_mu hpl q, hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem famR_rad (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    FamR P Bs (fun _ => Formalism.FourierDecayAlt.P.Qx5.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun _ _ => Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z',
    fun q => (mu_domR hpl q).2.2,
    fun x₀ hx₀ hg₀ => Φ.2.2.1 x₀ (Formalism.FourierDecayAlt.P.Qx5.mem_DomR_of_OpR hx₀ hg₀),
    fun _ hc => Formalism.FourierDecayAlt.P.Qx5.slice_FF Bs.z_mem Bs.z'_mem Φ.2 hc⟩

theorem tr_eq (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e Φ = trR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := rfl

theorem trR_congr (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', Φ x.1 x.2 = Ψ x.1 x.2) : trR P Bs.μsec e Φ = trR P Bs.μsec e Ψ := by
  funext ρ
  unfold trR
  congr 1
  funext q
  have := h _ (mu_domR hpl q)
  simp only at this
  simp only [rawR, this]

theorem trJB_of_rad (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : Top.IsRadOf P Bs Φ F) : trJB P Bs e (B.JF Bs F) = tr P Bs e Φ := by
  rw [tr_eq, trR_congr hpl h]
  funext ρ
  show MA.toSm P (rawJ P Bs e _ ρ) = _
  rw [tc_rawJ]
  rfl

section alg

variable (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
include hpl hk he

theorem tr_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : tr P Bs e (Φ + Ψ) = tr P Bs e Φ + tr P Bs e Ψ :=
  trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_rad hpl Φ) ρ) (fun ρ => smR hpl hk he (famR_rad hpl Ψ) ρ)

def tiedAlg : Subalgebra ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') × MA.A P (MA.DQ P)) where
  carrier := {x | Tied P Bs e x.1 x.2}
  mul_mem' := by
    intro x y hx hy Φ
    show tr P Bs e (x.1.1 (y.1.1 Φ)) = MA.actA P (x.2 * y.2) _
    rw [actA_mul, hx, hy]
  add_mem' := by
    intro x y hx hy Φ
    show tr P Bs e (x.1.1 Φ + y.1.1 Φ) = MA.actA P (x.2 + y.2) _
    rw [actA_add, tr_add hpl hk he, hx, hy]
  algebraMap_mem' := by
    intro z Φ
    show tr P Bs e (z • Φ) = MA.actA P (algebraMap ℂ _ z) _
    rw [actA_algebraMap]
    exact trR_smul _ _ z _

theorem tr_mul (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (f : (Fin P.r → ℂ) × Q.Mx P.k P.r → ℂ)
    (hT : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = f x • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    (φ : MA.SmQ P.r P.TT)
    (hφ : ∀ q : MA.Qp P.r P.TT, (φ : MA.Qp P.r P.TT → ℂ) q = f (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : tr P Bs e (T Φ) = fun ρ => φ * tr P Bs e Φ ρ := by
  funext ρ
  apply Subtype.ext; funext q
  rw [tr_eq, tr_eq, trR_val hpl hk he (famR_rad hpl _) ρ q]
  show _ = (φ : MA.Qp P.r P.TT → ℂ) q * ((trR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ : MA.SmQ P.r P.TT) :
    MA.Qp P.r P.TT → ℂ) q
  rw [trR_val hpl hk he (famR_rad hpl _) ρ q, hφ q]
  have := hT Φ _ (mu_domR hpl q)
  simp only at this
  simp only [rawR, this, hsV_smul, inner_smul_right]
  ring

end alg

section coords

variable {r : ℕ} {TT : ℝ}

theorem coordE_vz (x : MA.E r) : MA.coordE (M.vz) x = x.2 := by
  simp [MA.coordE, MA.zE, M.vz]

theorem coordE_vzb (x : MA.E r) : MA.coordE (M.vzb) x = star x.2 := by
  simp [MA.coordE, MA.zE, M.vzb]

def ggQ (r : ℕ) (TT : ℝ) : MA.SmQ r TT := (MA.anQ r TT).gg TT

theorem gg_apply (q : MA.Qp r TT) :
    (ggQ r TT : MA.Qp r TT → ℂ) q = ((Complex.normSq q.1.2 - TT : ℝ) : ℂ) := by
  show MA.coordE M.vz q.1 * MA.coordE M.vzb q.1 - (TT : ℂ) = _
  rw [coordE_vz, coordE_vzb, Complex.star_def, Complex.mul_conj]
  push_cast
  rfl

theorem inv_apply (φ : MA.SmQ r TT) (hφ : ∀ q, (φ : MA.Qp r TT → ℂ) q ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse φ : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((φ : MA.Qp r TT → ℂ) q)⁻¹ := by
  have hsm : (fun q : MA.Qp r TT => ((φ : MA.Qp r TT → ℂ) q)⁻¹) ∈ MA.smSub r TT := by
    show ContDiffOn ℝ MA.sm (MA.ext fun q : MA.Qp r TT => ((φ : MA.Qp r TT → ℂ) q)⁻¹) (MA.Qset r TT)
    have h0 : ContDiffOn ℝ MA.sm (MA.ext (φ : MA.Qp r TT → ℂ)) (MA.Qset r TT) := φ.2
    refine (h0.inv fun x hx => ?_).congr fun x hx => ?_
    · simp only [MA.ext, hx, dif_pos]; exact hφ _
    · simp [MA.ext, hx]
  let w : MA.SmQ r TT := ⟨_, hsm⟩
  have h1 : φ * w = 1 := by
    apply Subtype.ext; funext q
    exact mul_inv_cancel₀ (hφ q)
  have h2 : w * φ = 1 := by
    apply Subtype.ext; funext q
    exact inv_mul_cancel₀ (hφ q)
  let u : (MA.SmQ r TT)ˣ := ⟨φ, w, h1, h2⟩
  have hu : (u : MA.SmQ r TT) = φ := rfl
  rw [← hu, Ring.inverse_unit]
  rfl

end coords

theorem zeta_ne (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) : q.1.2 ≠ 0 := by
  intro h
  have h1 : P.TT < Complex.normSq q.1.2 := q.2.2
  have h2 : 0 < P.TT := by
    have := mul_pos Bs.T_pos Bs.T'_pos
    rwa [hpl.2.2.2.1, hpl.2.2.2.2.1] at this
  rw [h, map_zero] at h1
  linarith

section gens

variable (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
  (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
include hpl hk he

theorem tr_fn (j : Fin 6) (φ : MA.SmQ P.r P.TT)
    (hφ : ∀ q : MA.Qp P.r P.TT, (φ : MA.Qp P.r P.TT → ℂ) q =
      Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.1.2))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : tr P Bs e (X.fn j Φ) = fun ρ => φ * tr P Bs e Φ ρ :=
  tr_mul hpl hk he (X.fn j) (fun x => Q.fnVal P.k P.r Bs.z Bs.z' j x.2) (fun Φ x hx => X.fn_apply j Φ x hx) φ hφ Φ

theorem tr_opmul (l : Fin P.r) (i : Fin 6) (f : (Fin P.r → ℂ) → ℂ)
    (hf : ∀ (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g, Q.crd (opL l i) Φ c g = f c • Φ c g) (φ : MA.SmQ P.r P.TT)
    (hφ : ∀ q : MA.Qp P.r P.TT, (φ : MA.Qp P.r P.TT → ℂ) q = f q.1.1)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : tr P Bs e (X.op l i Φ) = fun ρ => φ * tr P Bs e Φ ρ :=
  tr_mul hpl hk he (X.op l i) (fun x => f x.1) (fun Φ x _ => by rw [X.op_apply]; exact hf _ _ _) φ hφ Φ

theorem transfer_torus_action (hG : GaugeQQ P Bs e) (Y : ℝ) (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.t Y a b Φ) = MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (tr P Bs e Φ) := by
  rw [tr_eq, trR_congr hpl (Ψ := Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ)
    (fun x hx => X.t_apply Y a b Φ x hx)]
  funext ρ
  exact hG _ _ (famR_rad hpl Φ) Y a b ρ

theorem transfer_operator_p (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 0 Φ) = MA.actA P (MA.pA P (MA.DQ P) l) (tr P Bs e Φ) := by
  show trR P Bs.μsec e (X.op l 0 Φ) = MA.actA P (MA.siteA P (MA.DQ P) l).p _
  rw [X.op_apply, actA_p]
  exact trR_p hpl hk he (famR_rad hpl Φ) l

theorem transfer_operator_pbar (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 3 Φ) = MA.actA P (MA.pbA P (MA.DQ P) l) (tr P Bs e Φ) := by
  show trR P Bs.μsec e (X.op l 3 Φ) = _
  rw [X.op_apply, MA.pbA, actA_sc]
  exact trR_pb hpl hk he (famR_rad hpl Φ) l

theorem transfer_operator_c (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 1 Φ) = MA.actA P (MA.cA P (MA.DQ P) l) (tr P Bs e Φ) := by
  rw [MA.cA, actA_sc]
  exact tr_opmul hpl hk he X l 1 (fun c => c l) (fun _ _ _ => rfl) (MA.coordQ (M.vc l)) (fun q => coordE_vc _ _) Φ

theorem transfer_operator_cbar (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 4 Φ) = MA.actA P (MA.cbA P (MA.DQ P) l) (tr P Bs e Φ) := by
  rw [MA.cbA, actA_sc]
  exact tr_opmul hpl hk he X l 4 (fun c => star (c l)) (fun _ _ _ => rfl) (MA.coordQ (M.vcb l))
    (fun q => coordE_vcb _ _) Φ

theorem transfer_operator_c_inv (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 2 Φ) = MA.actA P (MA.ciA P (MA.DQ P) l) (tr P Bs e Φ) := by
  rw [MA.ciA, actA_sc]
  exact tr_opmul hpl hk he X l 2 (fun c => (c l)⁻¹) (fun _ _ _ => rfl) (Ring.inverse (MA.coordQ (M.vc l)))
    (fun q => by rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc]) Φ

theorem transfer_operator_cbar_inv (l : Fin P.r) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.op l 5 Φ) = MA.actA P (MA.cbiA P (MA.DQ P) l) (tr P Bs e Φ) := by
  rw [MA.cbiA, actA_sc]
  exact tr_opmul hpl hk he X l 5 (fun c => (star (c l))⁻¹) (fun _ _ _ => rfl) (Ring.inverse (MA.coordQ (M.vcb l)))
    (fun q => by
      rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb]) Φ

theorem transfer_gauge_generator_z (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 0 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.zA, actA_sc]
  exact tr_fn hpl hk he X 0 (MA.coordQ M.vz) (fun q => by
    simp only [Q.fnVal, zeta_mu hpl q]; exact coordE_vz _) Φ

theorem transfer_gauge_generator_z_inv (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.ziA, actA_sc]
  exact tr_fn hpl hk he X 1 (Ring.inverse (MA.coordQ M.vz)) (fun q => by
    rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vz]; exact zeta_ne hpl ⟨x, hx⟩), coordE_vz]
    simp only [Q.fnVal, zeta_mu hpl q]) Φ

theorem transfer_gauge_generator_zbar (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 2 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.zbA, actA_sc]
  exact tr_fn hpl hk he X 2 (MA.coordQ M.vzb) (fun q => by
    simp only [Q.fnVal, zeta_mu hpl q]; exact coordE_vzb _) Φ

theorem transfer_gauge_generator_zbar_inv (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 3 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.zbiA, actA_sc]
  exact tr_fn hpl hk he X 3 (Ring.inverse (MA.coordQ M.vzb)) (fun q => by
    rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vzb]; exact (star_ne_zero).2 (zeta_ne hpl ⟨x, hx⟩)), coordE_vzb]
    simp only [Q.fnVal, zeta_mu hpl q]) Φ

theorem transfer_gauge_generator_ggi (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 4 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.ggA, actA_sc]
  exact tr_fn hpl hk he X 4 (ggQ P.r P.TT) (fun q => by
    rw [gg_apply]; simp only [Q.fnVal, gg_mu hpl q]) Φ

theorem transfer_gauge_generator_gg_inv (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    tr P Bs e (X.fn 5 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (tr P Bs e Φ) := by
  rw [MA.ggiA, actA_sc]
  refine tr_fn hpl hk he X 5 (Ring.inverse (ggQ P.r P.TT)) (fun q => ?_) Φ
  rw [inv_apply _ (fun q' => by
    rw [gg_apply]; exact Complex.ofReal_ne_zero.2 (sub_pos.2 q'.2.2).ne'), gg_apply]
  simp only [Q.fnVal, gg_mu hpl q]

end gens

theorem modelLevel_unique {L L' : R.LevelData (MA.A P (MA.DQ P)) P.r} (h : MA.IsModelLevel P (MA.DQ P) L)
    (h' : MA.IsModelLevel P (MA.DQ P) L') : L = L' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := h'
  cases L
  cases L'
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  subst a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  subst b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  rfl

end

end Formalism.MainStatements.NFTie
