import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.IdxNonnegOfLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.FinsumEqLogNorm

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Vals

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  have hx' : w.valuation K x ≠ 0 := by simpa using hx
  have hy' : w.valuation K y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem vAdd_prod (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vAdd_mul w _ _ (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem mem_pow_of_vAdd (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    a ∈ w.asIdeal ^ (vAdd w (algebraMap (𝓞 K) K a)).toNat := by
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
  have h0 : w.valuation K (algebraMap (𝓞 K) K a) ≠ 0 := by simpa using ha
  have hnn := volume_nonneg K w a
  rw [Int.toNat_of_nonneg hnn]
  unfold vAdd
  rw [neg_neg, WithZero.exp_log h0]

end Vals

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def smulSub (d : K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L.map ((d • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K))

theorem mem_smulSub (d : K) (L : Submodule (𝓞 K) V) (x : V) : x ∈ smulSub d L ↔ ∃ y ∈ L, d • y = x := by
  simp [smulSub]

theorem span_smulSub (d : K) (hd : d ≠ 0) (L : Submodule (𝓞 K) V) :
    Submodule.span K (smulSub d L : Set V) = Submodule.span K (L : Set V) := by
  rw [smulSub, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using Submodule.smul_mem _ d hy
  · intro hx
    refine ⟨d⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hd]

theorem smulSub_smulSub (d e : K) (L : Submodule (𝓞 K) V) : smulSub d (smulSub e L) = smulSub (d * e) L := by
  ext x
  simp only [mem_smulSub]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by rw [smul_smul]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨e • z, ⟨z, hz, rfl⟩, by rw [smul_smul]⟩

theorem fg_smulSub (d : K) (L : Submodule (𝓞 K) V) (hL : L.FG) : (smulSub d L).FG := hL.map _

theorem idx_smulSub_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M N : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) :
    idxAt w (smulSub d M) (smulSub d N) = idxAt w M N := by
  have hinj : ∀ P : Submodule (𝓞 K) V, ∀ x ∈ P, (d • LinearMap.id : V →ₗ[K] V) x = 0 → x = 0 := by
    intro P x _ hx
    simpa [hd] using hx
  exact (idx_map_inj hI w (d • LinearMap.id) M N hM hN h1 (hinj M) (hinj N)).symm

theorem idx_ge_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    vAdd w (algebraMap (𝓞 K) K a) * (Formalism.HN.rkK M : ℤ) ≤ idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hsp := (span_smulSub (algebraMap (𝓞 K) K a) haK M).symm
  have := (hI K V w M _ hM (fg_smulSub _ M hM) hsp).2.2.2.1 (vAdd w (algebraMap (𝓞 K) K a)).toNat
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
      refine ⟨1, one_notMem_w w, ?_⟩
      rw [one_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul (mem_pow_of_vAdd w a ha) hy)
  rwa [Int.toNat_of_nonneg (volume_nonneg K w a)] at this

theorem idx_le_natSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) (hm : 0 < m)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub ((m : ℕ) : K) M) ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((m : ℕ) : K) := by
  have hmK : ((m : ℕ) : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine idx_le_nat hI w M _ hM (fg_smulSub _ M hM) (span_smulSub _ hmK M).symm m hm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_smulSub _ M x).mp hx
    rw [Nat.cast_smul_eq_nsmul K m y, ← Nat.cast_smul_eq_nsmul (𝓞 K) m y]
    exact Submodule.smul_mem _ _ hy
  · intro x hx
    refine (mem_smulSub _ M _).mpr ⟨x, hx, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem idx_smulSub_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub (algebraMap (𝓞 K) K a) M) = (Formalism.HN.rkK M : ℤ) * vAdd w (algebraMap (𝓞 K) K a) := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
  have hspan : Ideal.span {a} ≠ ⊥ := by simpa using ha
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
  set m := Ideal.absNorm (Ideal.span {a}) with hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact hspan)
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha'
    exact hm0.ne' (by exact_mod_cast ha'.symm)
  have ha'K : algebraMap (𝓞 K) K a' ≠ 0 := by simpa using ha'0
  have hmK : ((m : ℕ) : K) = algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K a' := by
    rw [← map_mul, mul_comm, ha', map_natCast]
  have e1 := idx_chain hI w M (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ haK M).symm
    (by rw [span_smulSub _ (by rw [hmK]; exact mul_ne_zero haK ha'K), span_smulSub _ haK])
  have e2 : idxAt w (smulSub (algebraMap (𝓞 K) K a) M) (smulSub ((m : ℕ) : K) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K a') M) := by
    rw [hmK, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ haK M _ hM (fg_smulSub _ M hM) (span_smulSub _ ha'K M).symm
  have u := idx_le_natSub hI w m hm0 M hM
  have l1 := idx_ge_int hI w a ha M hM
  have l2 := idx_ge_int hI w a' ha'0 M hM
  rw [e1, e2, hmK, vAdd_mul w _ _ haK ha'K] at u
  nlinarith

theorem idx_smulSub (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) :
    idxAt w M (smulSub d M) = (Formalism.HN.rkK M : ℤ) * vAdd w d := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) d
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by simpa using hb0
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hd; rw [h, zero_div]
  have ha0 : a ≠ 0 := by intro h; apply haK; rw [h, map_zero]
  set d := algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b with hd'
  have hda : d * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a := by
    rw [hd', div_mul_cancel₀ _ hbK]
  have e1 := idx_chain hI w M (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) hM
    (fg_smulSub _ M hM) (fg_smulSub _ M hM) (span_smulSub _ hd M).symm
    (by rw [span_smulSub _ haK, span_smulSub _ hd])
  have e2 : idxAt w (smulSub d M) (smulSub (algebraMap (𝓞 K) K a) M) =
      idxAt w M (smulSub (algebraMap (𝓞 K) K b) M) := by
    rw [← hda, ← smulSub_smulSub]
    exact idx_smulSub_map hI w _ hd M _ hM (fg_smulSub _ M hM) (span_smulSub _ hbK M).symm
  rw [e2, idx_smulSub_int hI w a ha0 M hM, idx_smulSub_int hI w b hb0 M hM] at e1
  have hv : vAdd w (algebraMap (𝓞 K) K a) = vAdd w d + vAdd w (algebraMap (𝓞 K) K b) := by
    rw [← hda, vAdd_mul w _ _ hd hbK]
  rw [hv] at e1
  linarith

end Gen

end PI.Dv.TIW
