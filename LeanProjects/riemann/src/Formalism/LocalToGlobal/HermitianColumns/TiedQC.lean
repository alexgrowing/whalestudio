import Formalism.LocalToGlobal.HermitianColumns.StepLevelQ
import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

structure TwChTied (D : D7) (inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop) where

  eCls0 : ∀ u μ, (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  eStab0 : ∀ u μ c, (D.mem u).C.stab 0 c ≃* (D.chTw u μ).stab 0 (eCls0 u μ c)

  eY : ∀ u μ i, i ≤ D.R.m → ((D.mem u).C.Y i ≃ (D.chTw u μ).Y i)
  de_eq : ∀ u μ i hi y τ, (D.chTw u μ).de i (eY u μ i hi y) τ = (D.mem u).C.de i y τ
  twisted_character_eq : ∀ u μ (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c y,
    D.e0Tw u μ φ (eCls0 u μ c) (eY u μ 0 (Nat.zero_le _) y) = φ c y

  Q : D.what₂.Tup → Finset (HeightOneSpectrum (𝓞 D.host.F))
  Q_iff : ∀ μ v, v ∈ Q μ ↔ inQ μ v

  Ch : D.what₂.Word → D.what₂.Tup → ℕ → Type
  [ChFin : ∀ u μ i, Finite (Ch u μ i)]

  Ch_m : ∀ u μ, Nonempty (Unique (Ch u μ D.R.m))

  chOf : ∀ u μ i, (D.chTw u μ).cls i → Ch u μ i

  lev : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ), 1 ≤ i → i ≤ D.R.m → Ch u μ i →
    StepLevelQ D.sp.cm (D.sp.X i) D.host.g (D.mem u).A.T D.R.f (Q μ)
  lat : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ), (D.chTw u μ).cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V

  cls : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : Ch u μ i),
    ClassTie D.sp.cm (D.sp.X i) (lev u μ i h1 hm β).Lb (lev u μ i h1 hm β).U
      (fun c : {c // chOf u μ i c = β} => (D.chTw u μ).stab i c.1) (fun c => lat u μ i c.1)

  levJ : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), 1 ≤ D.R.m - 1 →
    StepLevelQ D.sp.cm (D.sp.X (D.R.m - 1)) D.host.g (D.mem u).A.T D.R.f (Q μ)

  Yb : D.what₂.Word → D.what₂.Tup → 1 ≤ D.R.m - 1 → Type
  [YbFin : ∀ u μ h, Finite (Yb u μ h)]
  [YbAct : ∀ u μ h, MulAction (levJ u μ h).U (Yb u μ h)]

  yb : ∀ u μ h, Ch u μ (D.R.m - 1) → Yb u μ h
  yb_orbit : ∀ u μ h (y : Yb u μ h), ∃! β, ∃ κ : (levJ u μ h).U, κ • yb u μ h β = y

  levJ_Lb : ∀ u μ h β, (lev u μ (D.R.m - 1) h (Nat.sub_le _ _) β).Lb = (levJ u μ h).Lb
  levJ_le : ∀ u μ h β, (lev u μ (D.R.m - 1) h (Nat.sub_le _ _) β).U ≤ (levJ u μ h).U
  levJ_stab : ∀ u μ h β (κ : (levJ u μ h).U),
    κ.1 ∈ (lev u μ (D.R.m - 1) h (Nat.sub_le _ _) β).U ↔ κ • yb u μ h β = yb u μ h β

  DGam_one : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam

attribute [instance] TwChTied.ChFin TwChTied.YbFin TwChTied.YbAct

theorem TwChTied.finite_cls {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) :
    Finite (ClassSet (UFin D.sp.cm (D.sp.X i)) ((T.lev u μ i h1 hm β).U.subgroupOf (UAf D.sp.cm (D.sp.X i)))) :=
  Finite.of_surjective _ (T.cls u μ hμ i h1 hm β).y_bij.2

end Formalism.L2.Herm

end
