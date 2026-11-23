import Formalism.LocalToGlobal.Columns.TwQBridge
import Formalism.LocalToGlobal.Columns.TwQLev

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Div

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

set_option maxHeartbeats 2000000 in

theorem qbK_of_div {c : v.adicCompletion F} (hc : c ∈ v.adicCompletionIntegers F) (hc1 : Valued.v c < 1)
    {k : GL (Fin n) (v.adicCompletion F)} (hk : qbDiv c ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1)) : k ∈ qbK c := by
  classical
  let O := v.adicCompletionIntegers F
  have hkint : qbInt (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := fun i j => by
    obtain ⟨z, hz, e⟩ := hk i j
    have : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = c * z + (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
      rw [← e, Matrix.sub_apply, sub_add_cancel]
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ hc hz) (qbInt_one i j)
  let kO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hkint i j⟩
  have hres : (IsLocalRing.residue O).mapMatrix kO = 1 := by
    ext i j
    obtain ⟨z, hz, e⟩ := hk i j
    have h2 : IsLocalRing.residue O (kO i j - (1 : Matrix (Fin n) (Fin n) O) i j) = 0 := by
      apply glo_res_zero v
      show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F)) < 1
      have e1 : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F) = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e1, ← Matrix.sub_apply, e, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hz)) hc1
    rw [map_sub, sub_eq_zero] at h2
    show IsLocalRing.residue O (kO i j) = (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) i j
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit kO.det := by
    have h1 : IsLocalRing.residue O kO.det = 1 := by rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 : kO.det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← IsLocalRing.residue_eq_zero_iff] at h2
    rw [h2] at h1
    exact zero_ne_one h1
  have hinv : kO * kO⁻¹ = 1 := Matrix.mul_nonsing_inv kO hdet
  have hmap : (O.subtype).mapMatrix kO = (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := rfl
  have hk1 : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (O.subtype).mapMatrix kO⁻¹ = 1 := by
    rw [← hmap, ← map_mul, hinv, map_one]
  have hkinv : ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (O.subtype).mapMatrix kO⁻¹ := by
    have := congrArg (fun M => ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M) hk1
    simp only [mul_one] at this
    rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨hkint, fun i j => ?_, hk⟩
  rw [hkinv]
  exact (kO⁻¹ i j).2

end Div

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem qsp_locL_entry {z : Fin n → E ⊗[F] v.adicCompletion F} (hz : z ∈ Formalism.L2.Herm.locL v (stdLat E n)) (i : Fin n) :
    z i ∈ Formalism.BasicNotions.intV E v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hy i trivial)
    show inclE (F := F) (v.adicCompletion F) (y i) ∈ _
    rw [← hr]
    exact Formalism.MainNotions.Gaps.LG.sc_left_mem v r
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | smul a x _ hx => exact Subring.mul_mem _ a.2 hx

theorem qsp_single_locL (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
  classical
  refine Submodule.subset_span ⟨Pi.single j 1, fun l _ => ?_, funext fun i => ?_⟩
  · rw [Pi.single_apply]
    show (if l = j then (1 : E) else 0) ∈ (1 : Submodule (𝓞 E) E)
    by_cases h : l = j
    · rw [if_pos h]; exact Submodule.one_le.1 le_rfl
    · rw [if_neg h]; exact zero_mem _
  · show inclE (F := F) (v.adicCompletion F) ((Pi.single j (1 : E) : Fin n → E) i) = _
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp

end Lat

section Open

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)

set_option maxHeartbeats 2000000 in

theorem qbDF_spec (P : Q) : ∃ D : 𝓞 F, D ≠ 0 ∧ D ∈ (underPl F P.1).asIdeal ∧ ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
    algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) D = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  refine ⟨b ^ qbN Θ hΘ P, pow_ne_zero _ hb0, Ideal.pow_mem_of_mem _ hbP _ hNpos,
    qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P,
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _, ?_⟩
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  rw [map_pow, hbE, mul_pow, map_pow]

theorem qbF_d_int (P : Q) : qbF hc hQ P (qbD hc Θ hQ hΘ P) ∈ (qv F P.1).adicCompletionIntegers F := by
  rw [map_pow]
  exact Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _

theorem qbF_d_lt (P : Q) : Valued.v (qbF hc hQ P (qbD hc Θ hQ hΘ P)) < 1 := by
  rw [map_pow, map_pow]
  exact pow_lt_one₀ zero_le ((qbF_P hc hQ P _).2 (qbPi_spec hc hQ P).1) (Nat.pos_iff_ne_zero.1 (qbN_spec Θ hΘ P).1)

theorem qbU_of_K (P : Q) {k : GL (Fin n) ((qv F P.1).adicCompletion F)} (hk : k ∈ qbK (qbF hc hQ P (qbD hc Θ hQ hΘ P))) :
    k ∈ (qbLoc hc Θ hQ hΘ).U P :=
  ⟨hk.1, hk.2.1, 1, (Θ P).H.one_mem, by simpa using hk⟩

def qbDF (P : Q) : 𝓞 F := Classical.choose (qbDF_spec hc Θ hQ hΘ P)

theorem qbDF_prop (P : Q) : qbDF hc Θ hQ hΘ P ≠ 0 ∧ qbDF hc Θ hQ hΘ P ∈ (underPl F P.1).asIdeal ∧
    ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
      algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (qbDF hc Θ hQ hΘ P) = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w :=
  Classical.choose_spec (qbDF_spec hc Θ hQ hΘ P)

set_option maxHeartbeats 4000000 in

theorem qbOpen : QOpen (qbLoc hc Θ hQ hΘ) where
  princ P := by
    classical
    obtain ⟨hD0, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    refine ⟨Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}), Nat.pos_of_ne_zero fun h => hD0 ?_, fun x _ hy => ?_⟩
    · rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h; exact h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {qbDF hc Θ hQ hΘ P}))
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    obtain ⟨z, hz, e⟩ := hy _ (qsp_single_locL (qv F P.1) j)
    have e1 := congrFun e i
    rw [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul] at e1
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have e2 := congrArg f e1
    rw [map_sub, map_mul, map_natCast] at e2
    refine ⟨algebraMap (𝓞 F) _ t * w * f (z i), Subring.mul_mem _ (Subring.mul_mem _ (glo_algMap_int _ t) hw)
      ((((qbLoc hc Θ hQ hΘ).sp_int P (z i)).1 (qsp_locL_entry _ hz i)).1), ?_⟩
    have e3 : ((Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}) : ℕ) : (qv F P.1).adicCompletion F) =
        algebraMap (𝓞 F) _ t * (qbF hc hQ P (qbD hc Θ hQ hΘ P) * w) := by
      rw [← hDw, ← map_mul, ht, map_natCast]
    have e4 : f ((Pi.single j (1 : E ⊗[F] (qv F P.1).adicCompletion F) : Fin n → E ⊗[F] (qv F P.1).adicCompletion F) i) =
        (1 : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]; split_ifs <;> simp
    show f ((x : Matrix (Fin n) (Fin n) _) i j) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [← e4, e2, e3]
    ring
  glob := by
    classical
    refine ⟨∏ P ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P), ?_, fun u _ sa hu P => ?_⟩
    · refine Finset.prod_ne_zero_iff.2 fun P _ h => (qbDF_prop hc Θ hQ hΘ P).1 ?_
      have hinj : Function.Injective (algebraMap (𝓞 F) E) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 F) F E]
        exact (algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)
      exact hinj (by rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero, map_zero])
    obtain ⟨-, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have hφ : ∀ P' : Q, f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P') := fun P' => by
      show qbF hc hQ P _ = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, qsp_sp_F hc P.1 _ (qbSp hc hQ P),
        ← IsScalarTower.algebraMap_apply]
    have hprod : f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E
        (∏ P' ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        qbF hc hQ P (qbD hc Θ hQ hΘ P) * (w * ∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) := by
      rw [map_prod, map_prod, map_prod]
      simp only [hφ]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach Q P), hDw, mul_assoc]
    refine ⟨w * (∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) * f (prV (E := E) (qv F P.1) (sa i j : E ⊗[F] Formalism.L2.Herm.Af F)),
      Subring.mul_mem _ (Subring.mul_mem _ hw (Subring.prod_mem _ fun P' _ => glo_algMap_int _ _))
        ((((qbLoc hc Θ hQ hΘ).sp_int P _).1 (afsplit_prV_int (qv F P.1) _ (sa i j).2)).1), ?_⟩
    show f (prV (E := E) (qv F P.1) ((u : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [hu i j, map_add, map_add, map_mul, map_mul]
    have e4 : f (prV (E := E) (qv F P.1) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e4, add_sub_cancel_left]
    show f (prV (E := E) (qv F P.1) (inclE (F := F) (Formalism.L2.Herm.Af F) _)) * _ = _
    rw [afsplit_prV_inclE, hprod]
    ring

end Open

end Formalism.L2.Col
