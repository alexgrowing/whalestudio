import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.InertKernelTheory.FrameInt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.ScalM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

section lamC

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem qbar_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : s ^ n ∈ TaylorLogMetric.Qbar := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hs k
  | negSucc k =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hs _)

theorem lamC_of_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hs]

theorem lamC_mul_mem {s t : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (ht : t ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.mul_mem hs ht), lamC_of_mem lam hs, lamC_of_mem lam ht, ← map_mul]
  rfl

theorem lamC_inv_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s⁻¹ = (TaylorLogMetric.lamC lam s)⁻¹ := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.inv_mem hs), lamC_of_mem lam hs, ← map_inv₀]
  rfl

theorem lamC_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (s ^ n) = (TaylorLogMetric.lamC lam s) ^ n := by
  rw [lamC_of_mem lam (qbar_zpow_mem hs n), lamC_of_mem lam hs, ← map_zpow₀]
  rfl

end lamC

section minv

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

theorem mInv_fdOfCharts (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.KerInert.RepFrame.MInv X (fdOfCharts cp a bad).frM := by
  intro j La v
  show IsUnit (Matrix.det (((((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (cp.J j La) :
      (Fin (cp.N j La) → D.host.E) ≃ₗ[D.host.E] (Fin (cp.N j La) → D.host.E)) :
        (Fin (cp.N j La) → D.host.E) →ₗ[D.host.E] (Fin (cp.N j La) → D.host.E))) *
    (cp.B j La : Matrix (Fin (cp.N j La)) (Fin (cp.N j La)) D.host.E)).map (cp.iw j La v)).submatrix
      (finCongr (cp.hk j La)) (finCongr (cp.hk j La)))))
  rw [Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  apply IsUnit.map
  rw [Matrix.det_mul, LinearMap.det_toMatrix']
  exact (LinearEquiv.isUnit_det' _).mul (Matrix.isUnits_det_units _)

end minv

section scal

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : FData X D)
  (χ : TaylorLogMetric.IdE D → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

def MuAlg : Prop := ∀ j x, muT j x ∈ TaylorLogMetric.Qbar

def ChiAlg : Prop := ∀ 𝔞, χ 𝔞 ∈ TaylorLogMetric.Qbar

def ChiUnitG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j L0)))‖ = 1 ∧
      ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')))‖ = 1

def MuBdG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖(p : ℂ_[p]) ^ KG.expG X j L0 La' * TaylorLogMetric.lamC lam (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹)‖ ≤ 1

def BRG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖TaylorLogMetric.lamC lam (KG.scalG fd χ muT j L0 La')‖ = ‖(p : ℂ_[p])‖ ^ (-KG.expG X j L0 La')

variable {X hfin fd χ muT lam}

theorem muAlg_of_tie (h : MuTie D muT) : MuAlg muT := fun j x => ((h j).2.2 x).2

theorem chiAlg_of_tie (h : ChiTie D χ) : ChiAlg χ := fun 𝔞 => (h.2 𝔞).2

theorem scalG_mem (hmu : MuAlg muT) (hχ : ChiAlg χ) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    KG.scalG fd χ muT j La La' ∈ TaylorLogMetric.Qbar := by
  have hcf : Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem (hχ _) _) (qbar_zpow_mem (hχ _) _)
  unfold KG.scalG
  exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (hmu _ _) (TaylorLogMetric.Qbar.inv_mem (hmu _ _)))
    (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem (hχ _) _)) (qbar_zpow_mem (hχ _) _)

theorem scalG_of (hmu : MuAlg muT) (hχ : ChiAlg χ) (hU : ChiUnitG X hfin fd χ lam) (hB : MuBdG X hfin fd muT lam) :
    KG.ScalG X hfin fd χ muT lam := by
  intro j L0 hL0 La' hLa'
  refine ⟨scalG_mem hmu hχ j L0 La', ?_⟩
  obtain ⟨hu, hu'⟩ := hU j L0 hL0 La' hLa'
  have hm1 := hmu (j + 1) (fd.dt (j + 1) La')
  have hm0 := hmu (j + 1) (fd.dt j L0)
  have ha := hχ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j L0))
  have ha' := hχ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La'))
  have hcf : Base.chiFac χ _ _ (fd.kerN j L0) (fd.kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC lam (Base.chiFac χ _ _ (fd.kerN j L0) (fd.kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem lam ha,
      lamC_zpow_mem lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  have hexp : TaylorLogMetric.lamC lam (KG.scalG fd χ muT j L0 La') =
      TaylorLogMetric.lamC lam (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹) *
        (TaylorLogMetric.lamC lam (Base.chiFac χ _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j L0))) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La'))) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem lam hcf, lamC_zpow_mem lam ha, lamC_zpow_mem lam ha']
  rw [hexp]
  have hB' := hB j L0 hL0 La' hLa'
  calc ‖(p : ℂ_[p]) ^ KG.expG X j L0 La' *
        (TaylorLogMetric.lamC lam (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹) *
          (TaylorLogMetric.lamC lam (Base.chiFac χ _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j L0))) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La'))) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖(p : ℂ_[p]) ^ KG.expG X j L0 La' *
          TaylorLogMetric.lamC lam (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ ≤ 1 := hB'

theorem scalG_of_br (hmu : MuAlg muT) (hχ : ChiAlg χ) (hBR : BRG X hfin fd χ muT lam) :
    KG.ScalG X hfin fd χ muT lam := by
  intro j L0 hL0 La' hLa'
  refine ⟨scalG_mem hmu hχ j L0 La', ?_⟩
  exact le_of_eq (unit_of_br _ _ (hBR j L0 hL0 La' hLa'))

end scal

end Formalism.L2.KerInert.ScalM

namespace Formalism.L2.KerInert.ScalM

open Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section inst

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)

theorem mInv_fdAtL (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Formalism.L2.KerInert.RepFrame.MInv (sysAt Ch std vp unif eO eO_spec dG dG_spec om)
      (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM :=
  mInv_fdOfCharts (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a bad

theorem scalG_fdAtL (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (hmu : MuTie D muT) (hχ : ChiTie D χ)
    (hU : ChiUnitG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam)
    (hB : MuBdG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) muT lam) :
    KG.ScalG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ muT lam :=
  scalG_of (muAlg_of_tie hmu) (chiAlg_of_tie hχ) hU hB

theorem scalG_fdAtL_br (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (hmu : MuTie D muT) (hχ : ChiTie D χ)
    (hBR : BRG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ muT lam) :
    KG.ScalG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ muT lam :=
  scalG_of_br (muAlg_of_tie hmu) (chiAlg_of_tie hχ) hBR

end inst

end Formalism.L2.KerInert.ScalM
