import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.G.Cmp Formalism.L2.G Formalism.L2.G.RelativeIndexFlags
open scoped TensorProduct

theorem det_mem_sub {K : Type} [CommRing K] (O : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (h : ∀ a b, A a b ∈ O) :
    A.det ∈ O := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (Subring.prod_mem _ fun a _ => h _ _) _

def unitsOf {K : Type} [CommRing K] (O : Subring K) : Subgroup Kˣ where
  carrier := {z | (z : K) ∈ O ∧ ((z⁻¹ : Kˣ) : K) ∈ O}
  one_mem' := ⟨O.one_mem, by rw [inv_one]; exact O.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨O.mul_mem ha hb, by rw [_root_.mul_inv_rev]; exact O.mul_mem hb' ha'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

theorem det_mem_unitsOf {K : Type} [CommRing K] (O : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (h : ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b ∈ O) (h' : ∀ a b, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ O) :
    Matrix.GeneralLinearGroup.det g ∈ unitsOf O :=
  ⟨det_mem_sub O _ h, by rw [← map_inv]; exact det_mem_sub O _ h'⟩

theorem det_bc {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.det (bc φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  exact (RingHom.map_det φ (g : Matrix (Fin n) (Fin n) A)).symm

theorem quot_calc {Q : Type} [CommGroup Q] (U : Subgroup Q) (Y dB dB' dg dk : Q) (b k : ℕ)
    (h1 : dB'⁻¹ * Y * dB ∈ U) (h2 : dB'⁻¹ * (Y * dk) * dB ∈ U) (h : Y ^ (b + k) = dg * Y ^ b * dk) :
    (dB' * dB⁻¹) ^ k * dg⁻¹ ∈ U := by
  have hk : dk ∈ U := by
    have e0 : dB'⁻¹ * (Y * dk) * dB = dB'⁻¹ * Y * dB * dk := by ac_rfl
    have e : dk = (dB'⁻¹ * Y * dB)⁻¹ * (dB'⁻¹ * (Y * dk) * dB) := by
      rw [e0, inv_mul_cancel_left]
    rw [e]
    exact U.mul_mem (U.inv_mem h1) h2
  have hY : Y ^ k = dg * dk := by
    rw [pow_add, mul_comm dg, mul_assoc] at h
    exact mul_left_cancel h
  have e : (dB' * dB⁻¹) ^ k * dg⁻¹ = ((dB'⁻¹ * Y * dB) ^ k)⁻¹ * dk := by
    have e1 : dB'⁻¹ * Y * dB = (dB' * dB⁻¹)⁻¹ * Y := by
      rw [mul_inv, inv_inv]
      ac_rfl
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = dB' * dB⁻¹ := ⟨_, rfl⟩
    rw [← hZ] at e1 ⊢
    rw [e1, mul_pow, inv_pow, hY]
    generalize Z ^ k = z
    rw [mul_inv, inv_inv, mul_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact U.mul_mem (U.inv_mem (U.pow_mem h1 k)) hk

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}

def epsU (B B' γ : GL (Fin n) E) (k : ℕ) : Eˣ :=
  (Matrix.GeneralLinearGroup.det B' * (Matrix.GeneralLinearGroup.det B)⁻¹) ^ k * (Matrix.GeneralLinearGroup.det γ)⁻¹

set_option maxHeartbeats 1000000 in

theorem epsU_ph (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (γ : GL (Fin n) E) (κ : S.U) (b k : ℕ)
    (h : y.1 ^ (b + k) = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 ^ b * κ.1) (v : Fin G.P.nV) :
    Units.map (A.phE v).toMonoidHom (epsU A.B B' γ k) ∈ unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring := by
  have key : ∀ κ' : S.U, (Matrix.GeneralLinearGroup.det (bc (A.phE v) B'))⁻¹ *
      Matrix.GeneralLinearGroup.det (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1))) *
      Matrix.GeneralLinearGroup.det (bc (A.phE v) A.B) ∈ unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring := by
    intro κ'
    obtain ⟨h1, h2⟩ := int_of_move (A.pl v).1 (A.spl v) (halg v) A.B B' (hb v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1))
      ((loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').2 κ')
    have h3 := det_mem_unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring
      ((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)) * bc (A.phE v) A.B) h1 (by
        have e : ((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)) * bc (A.phE v) A.B)⁻¹ =
            (bc (A.phE v) A.B)⁻¹ * (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)))⁻¹ * bc (A.phE v) B' := by group
        rw [e]
        exact h2)
    rwa [map_mul, map_mul, map_inv] at h3
  have k1 := key 1
  have k2 := key κ
  rw [show ((1 : S.U) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 from rfl, mul_one] at k1
  rw [map_mul, map_mul, map_mul] at k2
  have h' := congrArg (fun z => Matrix.GeneralLinearGroup.det (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z))) h
  simp only [map_mul, map_pow, bc_ph_incl] at h'
  have := quot_calc _ _ _ _ _ _ b k k1 k2 h'
  rw [det_bc, det_bc, det_bc] at this
  rw [epsU, map_mul, map_pow, map_mul, map_inv, map_inv]
  exact this

end Gen

end Formalism.MainNotions.G.ChF

end
