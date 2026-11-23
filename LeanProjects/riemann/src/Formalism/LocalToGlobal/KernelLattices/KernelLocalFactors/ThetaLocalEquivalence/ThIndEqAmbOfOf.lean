import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPAmbOf
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.GMConjTranspose

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section U

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem TE.ufGL_apply' (γ : UF E n) (i j : Fin n) : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = γ.1 (Pi.single j 1) i := by
  have h := TE.matT_apply (ι := Unit) (fun _ => RingHom.id E) γ () i j
  simpa [TE.matT] using h

theorem TE.ufInv_apply (γ : UF E n) (i k : Fin n) : γ.1.symm (Pi.single k 1) i = star (γ.1 (Pi.single i 1) k) := by
  have h : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (γ.1.symm (Pi.single k 1))) = hStd E n (Pi.single i 1) (γ.1.symm (Pi.single k 1)) :=
    γ.2 _ _
  rw [LinearEquiv.apply_symm_apply, hStd_single_left] at h
  rw [← h, hStd_apply]
  simp [Pi.single_apply]

end U

section Eq

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem ambOf_conj (hok : s.Ok) (τ : X.Tau) (x : X.E) : X.embC (ambOf s B χ cD).σ₀ τ (star x) = star (X.embC (ambOf s B χ cD).σ₀ τ x) := by
  let _ := D.host.cmStar
  show s.σ₀ (X.emb τ (star x)) = star (s.σ₀ (X.emb τ x))
  rw [hok.1, hok.1, hok.2, ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, Formalism.L2.PairingIndexBounds.Eq.embT_star']

theorem eqLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) : (ambOf s B χ cD : Amb X).EqLaw a b := by
  obtain ⟨hcc, hδ, -, hχ, -, hok, -⟩ := hN
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN' z
  have hE := (Formalism.L2.PairingIndexBounds.Eq.SqG.eqP_outright B hcc hδ (B.stdOK hcc hδ) χ hχ).1 a b ⟨s.lat N, s.sd_lat hok hN⟩
    ⟨s.lat N', s.sd_lat hok hN'⟩ ha hb ⟨s.matU γ, s.matU_mem hok γ⟩ ⟨s.matU γ', s.matU_mem hok γ'⟩
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [s.lat_gmap, s.lat_gmap]
  have hE' := congrFun hE (fun τ => z (s.iT.symm τ))
  rw [← hE']
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  obtain ⟨τ', rfl⟩ := s.iT.surjective τ
  simp only [Equiv.symm_apply_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold Amb.pullV
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : ∀ y : X.E, TaylorLogMetric.embT D (s.iT τ') (s.iE y) = X.embC s.σ₀ τ' y := fun y => (hok.1 τ' y).symm
  have f1 : star ((B.tor).emb (s.iT τ') (s.matU γ' k i)) = X.embC s.σ₀ τ' (γ'.1.symm (Pi.single k 1) i) := by
    rw [TE.ufInv_apply, Seam.matU, Matrix.map_apply, TE.ufGL_apply']
    show star (TaylorLogMetric.embT D (s.iT τ') (s.iE _)) = _
    rw [← Formalism.L2.PairingIndexBounds.Eq.embT_star', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, ← hok.2, e1]
  have f2 : (B.tor).emb (s.iT τ') (s.matU γ l j) = X.embC s.σ₀ τ' (γ.1 (Pi.single j 1) l) := by
    rw [Seam.matU, Matrix.map_apply, TE.ufGL_apply']
    exact e1 _
  rw [f1, f2]
  rfl

theorem thIndEq_ambOf_of (hT : ThIndOfEq) {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) {D' : ℕ} (hD : 0 < D') (hLa : (ambOf s B χ cD : Amb X).LaHyp a b Sall) :
    (ambOf s B χ cD : Amb X).ThIndEq a b Sall D' :=
  hT X _ a b Sall D' (ambOf_conj s B χ cD hN.2.2.2.2.2.1) hD hLa (eqLaw_ambOf s B χ cD hN ha hb)

end Eq

end Formalism.L2.Ker
