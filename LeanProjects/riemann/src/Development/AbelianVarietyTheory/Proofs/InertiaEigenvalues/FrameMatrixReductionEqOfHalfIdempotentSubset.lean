import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSConjGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped TensorProduct

namespace GlobalTheory.RedHalfDrop

variable {D : D7}

theorem toEAf_cA_sig (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => rfl

theorem int_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (idemAt PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hu, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (h.isIdemAt hPP)
  exact hu

theorem int_cA_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (cA D (idemAt PP)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [toEAf_cA_sig]
  exact GlobalTheory.ResConjPlace.conj_mem_int _ (int_idemAt h hPP)

theorem resS_eq_zero_of_mul {e a : AE D} {PP : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : e * a = 0) :
    resS D.host.F PP ⟨toEAf D a, ha⟩ = 0 := by
  obtain ⟨hu, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hm : (⟨toEAf D e, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
      ⟨toEAf D a, ha⟩ = 0 :=
    Subtype.ext (by show toEAf D e * toEAf D a = 0; rw [← map_mul, h0, map_zero])
  have h2 := congrArg (resS D.host.F PP) hm
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem subring_hom_dite_sub_mul_eq_of_kernel {R k : Type} [CommRing R] [CommRing k] (O : Subring R) (f : O →+* k) (x c : R) (hx : x ∈ O)
    (hc : c ∈ O) (h0 : f ⟨c, hc⟩ = 0) [Decidable (x - c * x ∈ O)] [Decidable (x ∈ O)] :
    (if h : x - c * x ∈ O then f ⟨x - c * x, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hm : x - c * x ∈ O := sub_mem hx (mul_mem hc hx)
  rw [dif_pos hm, dif_pos hx]
  have e : (⟨x - c * x, hm⟩ : O) = ⟨x, hx⟩ - ⟨c, hc⟩ * ⟨x, hx⟩ := rfl
  rw [e, map_sub, map_mul, h0, zero_mul, sub_zero]

theorem redM_sub_smul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) {c : EAf D}
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    redM PP (N - c • N) = redM PP N := by
  ext i j
  unfold redM
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact subring_hom_dite_sub_mul_eq_of_kernel _ (resS D.host.F PP) _ _ (hN i j) hc h0

theorem frMapO_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  unfold frMapAdj
  have h1 : ((e • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      cA D e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  have h2 : ∀ M : Matrix (Fin S.rank) (Fin T.rank) (AE D),
      (cA D e • M).map (toEAf D) = toEAf D (cA D e) • M.map (toEAf D) :=
    fun M => Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem redM_drop : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  intro D S T βS βT Pg Qa Qb hP hQ x hx h1 h2
  obtain ⟨P, hPg, hQa, hS⟩ := hP.split
  have hab : halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
    unfold halfIdem idem
    rw [← Finset.sum_sdiff hQ]
    ring
  have hxx : (halfIdem Pg Qb + idem (Qa \ Qb)) • x = x := by
    rw [← hab]
    ext i j
    exact hx i j
  have hsub : ∀ P' ∈ Qa \ Qb, P' ∈ P := fun P' hP' => hQa (Finset.sdiff_subset hP')
  constructor
  · intro PP hPP
    have e1 := frMapAdj_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add, map_add, add_smul] at e1
    have e2 : frMapAdj S T βS βT (halfIdem Pg Qb • x) =
        frMapAdj S T βS βT x - toEAf D (cA D (idem (Qa \ Qb))) • frMapAdj S T βS βT x := by
      rw [frMapAdj_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (cA D (idem (Qa \ Qb))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      rw [map_sum, map_sum]
      exact sum_mem fun P' hP' => int_cA_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hPg hPP)) hint (by
      unfold idem
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_conj (hPg hPP) (hsub P' hP'))
    rw [e2, redM_sub_smul PP h1 hint hz]
  · intro PP hPP
    have e1 := frMapO_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add, add_smul] at e1
    have e2 : frMapO S T βS βT (halfIdem Pg Qb • x) =
        frMapO S T βS βT x - toEAf D (idem (Qa \ Qb)) • frMapO S T βS βT x := by
      rw [frMapO_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (idem (Qa \ Qb)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      rw [map_sum]
      exact sum_mem fun P' hP' => int_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hQa (hQ hPP))) hint (by
      unfold idem
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_eq_zero (hQa (hQ hPP)) (hsub P' hP')
        fun e => (Finset.mem_sdiff.1 hP').2 (e ▸ hPP))
    rw [e2, redM_sub_smul PP h2 hint hz]

end GlobalTheory.RedHalfDrop
