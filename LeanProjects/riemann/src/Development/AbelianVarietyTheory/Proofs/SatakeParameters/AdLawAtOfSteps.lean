import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

variable (St) in

abbrev StepDatum (i : ℕ) (hi : i + 1 ≤ D.R.m) : Type :=
  (St i (Nat.le_of_succ_le hi)).Ch → (St (i + 1) hi).Ch →
    UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → HomE D.host.E (D.R.N i) (D.R.N (i + 1)) → ℂ

structure MuLaws (_A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) : Prop where
  mu_read : ∀ i < D.R.m, ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm,
    muT (i + 1) (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ)
  mu_cls : ∀ i < D.R.m, ∀ k hk c, muT (i + 1) (Matrix.GeneralLinearGroup.det ((St k hk).y c).1) =
    (((t.O u μ).mt (i + 1) ((t.O u μ).dt k c) : ℂˣ) : ℂ)
  mu_mul : ∀ i < D.R.m, muT (i + 1) 1 = 1 ∧ ∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), muT (i + 1) (x * y) = muT (i + 1) x * muT (i + 1) y
  mu_alg : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), muT (i + 1) x ∈ TaylorLogMetric.Qbar
  mu_unr : ∀ i < D.R.m, ∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E →
    (∀ v, UnderSB t μ v → prV (E := D.host.E) v (x : AfE D.host.F D.host.E) = 1) → muT (i + 1) x = 1
  mu_rat : ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧
    ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 →
      muT (i + 1) (ratId D.host.F D.host.E z) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

variable (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

structure StepLaws (muT : ℕ → (AfE D.host.F D.host.E)ˣ → ℂ) (i : ℕ) (hi : i + 1 ≤ D.R.m) (Xi : StepDatum St i hi) : Prop where
  read : ∀ c c' z, Xi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') ((St i (Nat.le_of_succ_le hi)).y c) ((St (i + 1) hi).y c') z =
    (t.rd u μ).Xi i c c' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  rat : ∀ β β' x x' x₁ x₁', ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)),
    ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), x₁.1 = ratA D.host.F γ * x.1 → x₁'.1 = ratA D.host.F γ' * x'.1 →
    ∀ z, Xi β β' x₁ x₁' z = Xi β β' x x' (inFr
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  lev : ∀ β β' x x' x₁ x₁' (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 → ∀ z,
    muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * Xi β β' x₁ x₁' z =
      muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * Xi β β' x x' z
  away : ∀ β β' x x' x₁ x₁',
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧
      bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1) → Xi β β' x₁ x₁' = Xi β β' x x'
  loc : ∀ β β' x x', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb) (Xi β β' x x')
  supp : ∀ β β' x x' z, Xi β β' x x' z ≠ 0 → z ∈ divLat (t.rd u μ).lev (homAt (ssRec t u μ)
    (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K β).lev.Lb)
    (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K β').lev.Lb))
  int : ∀ β β' x x' z, IntOff (t.O u μ).S (Xi β β' x x' z)

variable {A dtU a}

end Split

end GlobalTheory.TwU

end
