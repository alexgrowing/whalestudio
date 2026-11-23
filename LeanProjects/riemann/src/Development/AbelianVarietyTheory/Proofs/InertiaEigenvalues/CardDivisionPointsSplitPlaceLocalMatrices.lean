import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.DivPtLocalCard

open GlobalTheory.Core.Rk.SWQ

variable {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def phi (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) :
    Matrix (Fin m) (Fin n) (AE D) →+ Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E) :=
  AddMonoidHom.mk' (fun y => B * y.map (cw h) * A) fun y y' => by
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem phi_apply (h : w.under (𝓞 D.host.F) = q) {m n : ℕ} (B : Matrix (Fin m) (Fin m) (w.adicCompletion D.host.E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion D.host.E)) (y : Matrix (Fin m) (Fin n) (AE D)) :
    phi h B A y = B * y.map (cw h) * A := rfl

theorem eq_iota_cw {h : w.under (𝓞 D.host.F) = q} {ι : w.adicCompletion D.host.E →+ AE D}
    (hι : GlobalTheory.DivPtLocal.IsIotaAt h ι) {x : AE D} (hx : ι 1 * x = x) : x = ι (cw h x) := by
  obtain ⟨-, -, -, -, h4, -, -, -⟩ := hι
  have := h4 x 1
  rw [mul_one] at this
  rw [← this, mul_comm, hx]

theorem gl_cancel {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    b.1 * ((b⁻¹).1 * Y * a.1) * (a⁻¹).1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc b.1, Units.mul_inv, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem gl_cancel' {k : Type} [Field k] {m n : ℕ} (b : GL (Fin m) k) (a : GL (Fin n) k) (Y : Matrix (Fin m) (Fin n) k) :
    (b⁻¹).1 * (b.1 * Y * (a⁻¹).1) * a.1 = Y := by
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (b⁻¹).1, Units.inv_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.DivPtLocalCard

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Rk.SWQ in

theorem GlobalTheory.DivPtLocalCard.card_DQ_eq : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) (ι 1) N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P hs ι hι N hN
  obtain ⟨e, ⟨⟨a, ha, -⟩, -⟩, -, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram S) hS.1.fg hS.1.span_eq_top (rfl : P.under (𝓞 D.host.F) = _) hs
    (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hS _)
  obtain ⟨b, hb⟩ := GlobalTheory.Core.Rk.SWQ.LatHalf.mem_latO_iff_intM D _ P rfl hs S T ΛS ΛT hS hT a ha
  have hP : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hι' := hι
  obtain ⟨-, h1, h2, h3, h4, -, -, -⟩ := hι'
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (fun v => v = P.under (𝓞 D.host.F)) with hΛ
  set c := ι 1 with hc
  set Φ := GlobalTheory.DivPtLocalCard.phi hP (b⁻¹).1 a.1 with hΦ
  have hent : ∀ y : WO S T, c • y = y → ∀ i j, y i j = ι (cw hP (y i j)) := fun y hy i j =>
    GlobalTheory.DivPtLocalCard.eq_iota_cw hι (by simpa [Matrix.smul_apply] using congrFun (congrFun hy i) j)
  have hoff : ∀ y : WO S T, c • y = y → offM (P.under (𝓞 D.host.F)) y = 0 := by
    intro y hy
    ext i j
    simp only [offM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [hent y hy i j, h3, sub_self]
  have hcA : ∀ y : WO S T, c • y = y → ∀ i j, cw hP (cA D (y i j)) = 0 := by
    intro y hy i j
    rw [hent y hy i j]
    exact h2 _
  have hmem : ∀ y : WO S T, c • y = y → (y ∈ Λ ↔ GlobalTheory.Core.Rk.SWQ.IntM (Φ y)) := fun y hy => hb y (hoff y hy) (hcA y hy)
  have hInt : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM Z ↔ Z ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank := fun Z => Iff.rfl
  have hIntN : ∀ Z, GlobalTheory.Core.Rk.SWQ.IntM (N • Z) ↔ Z ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    intro Z
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [Matrix.smul_apply, nsmul_eq_mul]
    rfl
  have hcN : ∀ y : WO S T, c • y = y → c • (N • y) = N • y := fun y hy => by rw [smul_comm, hy]
  let Ψ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → WO S T :=
    fun Z => (b.1 * Z * (a⁻¹).1).map ι
  have hΨc : ∀ Z, c • Ψ Z = Ψ Z := by
    intro Z
    ext i j
    simp only [Ψ, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hc, h4, h1, one_mul]
  have hΦΨ : ∀ Z, Φ (Ψ Z) = Z := by
    intro Z
    rw [hΦ, GlobalTheory.DivPtLocalCard.phi_apply]
    have : (Ψ Z).map (cw hP) = b.1 * Z * (a⁻¹).1 := by
      ext i j
      simp only [Ψ, Matrix.map_apply, h1]
    rw [this, GlobalTheory.DivPtLocalCard.gl_cancel']
  have hinj : ∀ y y' : WO S T, c • y = y → c • y' = y' → Φ y = Φ y' → y = y' := by
    intro y y' hy hy' H
    have H' : y.map (cw hP) = y'.map (cw hP) := by
      rw [← GlobalTheory.DivPtLocalCard.gl_cancel b a (y.map (cw hP)), ← GlobalTheory.DivPtLocalCard.gl_cancel b a (y'.map (cw hP))]
      exact congrArg (fun M => b.1 * M * (a⁻¹).1) H
    ext i j
    rw [hent y hy i j, hent y' hy' i j]
    exact congrArg ι (congrFun (congrFun H' i) j)
  have hdiv : ∀ y : ↥(GlobalTheory.DivPtFourier.divPts Λ c N), Φ y ∈ GlobalTheory.DivPtLocal.locDiv P N T.rank S.rank := by
    rintro ⟨y, hy1, hy2⟩
    rw [← hIntN, ← map_nsmul]
    exact (hmem _ (hcN y hy1)).1 hy2
  let f : ↥(GlobalTheory.DivPtFourier.divPts Λ c N) →+ GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank :=
    (QuotientAddGroup.mk' _).comp ((Φ.comp (GlobalTheory.DivPtFourier.divPts Λ c N).subtype).codRestrict _ hdiv)
  have hsurj : Function.Surjective f := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H Z =>
    have hy2 : N • Ψ Z ∈ Λ := by
      rw [hmem _ (hcN _ (hΨc Z)), map_nsmul, hΦΨ, hIntN]
      exact Z.2
    refine ⟨⟨Ψ Z, hΨc Z, hy2⟩, ?_⟩
    change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    congr 1
    exact Subtype.ext (hΦΨ Z)
  have hker : f.ker = (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (GlobalTheory.DivPtFourier.divPts Λ c N) := by
    ext ⟨y, hy1, hy2⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
    change (QuotientAddGroup.mk _ : GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change Φ y ∈ GlobalTheory.DivPtLocal.locInt P T.rank S.rank ↔ y ∈ Λ ∧ y ∈ GlobalTheory.PlaceModel.half S T c
    rw [← hInt, ← hmem y hy1]
    exact ⟨fun h => ⟨h, hy1⟩, fun h => h.1⟩
  exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj)).toEquiv

end
