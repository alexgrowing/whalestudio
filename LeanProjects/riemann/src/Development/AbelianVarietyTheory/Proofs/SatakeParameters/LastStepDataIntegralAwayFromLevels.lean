import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

theorem intOff_prod {S : Finset ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntOff S (f i)) :
    IntOff S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem sNum_pow {S : Finset ℕ} {a : ℕ} (h : SNum S a) (k : ℕ) : SNum S (a ^ k) :=
  ⟨pow_pos h.1 k, fun q hq hd => h.2 q hq (hq.dvd_of_dvd_pow hd)⟩

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eval {n : ℕ} (η : Sp E n →ₗ[E] E) (c a : E) (y : Sp E n)
    (hη : ∀ i, IntAt P (c * η (Pi.single i 1))) (hy : a • y ∈ stdAt E n P) : IntAt P (a * c * η y) := by
  have hy' := mem_stdAt'.1 hy
  have e : η y = ∑ i, y i * η (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : Sp E n) = y i • Pi.single i (1 : E) by
      ext j; by_cases h : j = i <;> simp [h, Pi.single_apply], map_smul, smul_eq_mul]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  have := (hy' i).mul (hη i)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

theorem smul_symm_mem {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (a : E) {z : Sp E n} (hz : a • z ∈ localization₂ P.asIdeal N) :
    a • f.symm z ∈ stdAt E n P := by
  rw [← hf, map_smul, LinearEquiv.apply_symm_apply]
  exact hz

end Lin

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Yb : Set (Sp X.E n)} (hY : Yb ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Yb ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hq : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hs : ∀ (k : ℕ) v, v ∈ localization₂ P.1.asIdeal N → ((qOf P.1 : X.E) ^ k) • v ∈ localization₂ P.1.asIdeal N := by
    intro k v hv
    have := Submodule.smul_mem _ ((qOf P.1 : 𝓞 X.E) ^ k) hv
    rwa [← algebraMap_smul X.E, map_pow, map_natCast] at this
  have key : ∀ z, z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) →
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • z ∈ localization₂ P.1.asIdeal N := by
    intro z hz
    rw [mem_locLat] at hy hz
    have h1 := hy P
    have h2 := hz P
    rw [show z = y + (z - y) by abel, smul_add]
    split_ifs at h1 h2 ⊢ with hP
    · refine add_mem ?_ ?_
      · simpa using h1
      · exact hs 1 _ (by simpa using h2)
    · refine add_mem ?_ ?_
      · simpa [zpow_neg] using h1
      · have e : ((qOf P.1 : X.E) ^ cst.M) • (z - y) =
            ((qOf P.1 : X.E) ^ (cst.M + cst.M)) • (((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ • (z - y)) := by
          rw [smul_smul, zpow_natCast, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one]
        rw [e]
        exact hs _ _ h2
  exact key _ (Classical.epsilon_spec (p := fun z => z - y ∈ locLat (rowSG Pr sel mu) N
    (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))) ⟨y, by simp⟩)

end Yb

end GlobalTheory.CplTwoInt

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff (hc : cst.Ok) (P : rowSG Pr sel mu) (hG : P.1 ∈ Pr.vGs → cst.D P = 1)
    (hQ : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (σ : X.K →+* ℂ) {B : Finset ℕ} (hB : SNum B (qOf P.1)) {n : ℕ}
    (η : Sp X.E n →ₗ[X.E] X.E) {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • y ∈ stdAt X.E n P.1) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := by simpa [epsSg] using IntAt.coe P.1 (-1 : 𝓞 X.E)
  have hpos : 0 < qOf P.1 ^ cst.D P := pow_pos (GlobalTheory.GO.ChRoot.qOf_pos P.1) _
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    split_ifs with hη
    · refine IntOff.of_pow hpos ?_
      rw [← map_pow, psi_root hc P _ ?_, map_one]
      rw [hG hP, pow_one]
      have h1 := intAt_eval η 1 _ y (fun i => by simpa using hη i) hy
      convert he.mul h1 using 1
      ring
    · simpa using (IntOff.zero : IntOff B 0)
  · rw [if_neg hP] at hy ⊢
    split_ifs with hη
    · rw [map_mul, map_inv₀, map_pow, map_natCast]
      refine IntOff.mul ?_ (IntOff.of_pow hpos ?_)
      · simpa [Nat.cast_pow] using IntOff.inv_nat (sNum_pow hB (cst.M * n))
      · rw [← map_pow, psi_root hc P _ ?_, map_one]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hQ hP)
        have h1 := intAt_eval η _ _ y hη hy
        have hk' : IntAt P.1 ((qOf P.1 : X.E) ^ k) := by simpa using intAt_natCast (P := P.1) (qOf P.1 ^ k)
        rw [hk]
        convert (he.mul hk').mul h1 using 1
        ring
    · simpa using (IntOff.zero : IntOff B 0)

end Ft

theorem xiCpl2_intOff (hPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
      (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ
      (P : HeightOneSpectrum (𝓞 t.X.E)) x,
      IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x))) :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ p Yb d x hY
  have hok := t.idx_ok μ
  unfold XiCpl2
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul (hPhi D L hT Gi Gl K Y cX ex t u μ P.1 _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem xiCpl2_intOff_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) :=
  xiCpl2_intOff fun D L hT Gi Gl K Y cX ex t u μ P x => (GlobalTheory.T.chain_local_data_integral_off_levels D L hT Gi Gl K Y cX ex t u μ P).2 x

end GlobalTheory.CplTwoInt
