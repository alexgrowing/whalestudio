import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemWLat0OfIv

noncomputable section

open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.RedConj0Pf

open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin

section

variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))

def ivH : (Fin I.n → I.E) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  AddMonoidHom.mk' (iv I) (DictLat.iv_add I)

theorem ivH_apply (v : Fin I.n → I.E) : ivH I v = iv I v := rfl

def TH (x : I.Gf) : (Fin I.n → I.E ⊗[I.F] Af I.F) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  (Matrix.mulVecLin (I.fmat x)).toAddMonoidHom

theorem TH_apply (x : I.Gf) (v : Fin I.n → I.E ⊗[I.F] Af I.F) : TH I x v = I.fmat x *ᵥ v := rfl

theorem T_mem {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hb : ∀ i, b i ∈ I.L)
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : I.fmat x *ᵥ iv I (b i) ∈ I.Lf := by
  have hsub : Lw I w ≤ I.Lf := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have hyL : y ∈ I.L := by
      refine (Submodule.span_le.mpr ?_) hy
      rintro _ ⟨a, _, z, hz, rfl⟩
      rw [show ((a : 𝓞 I.E) : I.E) • z = a • z from algebraMap_smul I.E a z]
      exact I.L.smul_mem a hz
    exact Submodule.subset_span ⟨⟨y, hyL⟩, rfl⟩
  have hmem : ∀ j, iv I (b j) ∈ I.Lf := fun j => Submodule.subset_span ⟨⟨b j, hb j⟩, rfl⟩
  have hS : (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) ∈ I.Lf :=
    sum_mem (fun j _ => by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hmem j) _)
  have h := add_mem (hsub (hM i)) hS
  rwa [sub_add_cancel] at h

theorem red_eq {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b i)) =
      ∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j)) := by
  have hsum : (∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j))) =
      (Lw I w).mkQ (∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [hsum]
  exact (Submodule.Quotient.eq _).mpr (hM i)

theorem zcoef_q (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • (wLat0 I w).mkQ (b l) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  refine zcoef I w p hp hcard hb z ?_ l
  have h : (wLat0 I w).mkQ (∑ l, z l • b l) = 0 := by
    rw [map_sum]; simpa only [map_zsmul] using hz
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem zcoef_A (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • (Lw I w).mkQ (iv I (b l)) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  refine zcoef I w p hp hcard hb z ?_ l
  refine mem_wLat0_of_iv I w p hp.pos (p_mem I w p hp hcard) _ ?_
  have h : (Lw I w).mkQ (ivH I (∑ l, z l • b l)) = 0 := by
    rw [map_sum, map_sum]; simpa only [map_zsmul, ivH_apply] using hz
  exact (Submodule.Quotient.mk_eq_zero _).1 h

end

theorem reduction_conjugacy : Formalism.L2.SG.Pf.RowDictPf.RedConj0 := by
  intro I w p hp hcard m hm x M M' hM hM'
  subst hm
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hb, hMb0⟩ := hM
  obtain ⟨b', hb', hMb0'⟩ := hM'
  have hMb : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) :
      I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w := hMb0
  have hMb' : ∀ i, I.fmat x *ᵥ iv I (b' i) - ∑ j, ((((M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) :
      I.E ⊗[I.F] Af I.F) • iv I (b' j) ∈ Lw I w := hMb0'

  choose C hC using fun i => hb.2 (b' i) (hb'.1 i)
  choose D hD using fun i => hb'.2 (b i) (hb.1 i)
  let CM : Matrix (Fin I.n) (Fin I.n) ℤ := Matrix.of fun k i => C i k
  let DM : Matrix (Fin I.n) (Fin I.n) ℤ := Matrix.of fun k i => D i k
  let Mz : Matrix (Fin I.n) (Fin I.n) ℤ :=
    Matrix.of fun j i => ((((M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) : ℤ)
  let M'z : Matrix (Fin I.n) (Fin I.n) ℤ :=
    Matrix.of fun j i => ((((M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) j i).val : ℕ) : ℤ)
  have hCz : ∀ i, b' i - ∑ k, CM k i • b k ∈ wLat0 I w := fun i => by
    simpa only [CM, Matrix.of_apply, Int.cast_smul_eq_zsmul] using hC i
  have hDz : ∀ i, b i - ∑ k, DM k i • b' k ∈ wLat0 I w := fun i => by
    simpa only [DM, Matrix.of_apply, Int.cast_smul_eq_zsmul] using hD i

  have hqC : ∀ i, (wLat0 I w).mkQ (b' i) = ∑ k, CM k i • (wLat0 I w).mkQ (b k) := fun i => by
    have h1 : (wLat0 I w).mkQ (b' i) = (wLat0 I w).mkQ (∑ k, CM k i • b k) :=
      (Submodule.Quotient.eq _).2 (hCz i)
    rw [h1, map_sum]; simp only [map_zsmul]
  have hqD : ∀ i, (wLat0 I w).mkQ (b i) = ∑ k, DM k i • (wLat0 I w).mkQ (b' k) := fun i => by
    have h1 : (wLat0 I w).mkQ (b i) = (wLat0 I w).mkQ (∑ k, DM k i • b' k) :=
      (Submodule.Quotient.eq _).2 (hDz i)
    rw [h1, map_sum]; simp only [map_zsmul]
  have hCDz : ∀ l i, ((((1 : Matrix (Fin I.n) (Fin I.n) ℤ) - CM * DM) l i : ℤ) : ZMod p) = 0 := by
    intro l i
    refine zcoef_q I w p hp hcard hb (fun l => ((1 : Matrix (Fin I.n) (Fin I.n) ℤ) - CM * DM) l i) ?_ l
    have h2 : (wLat0 I w).mkQ (b i) = ∑ l, (CM * DM) l i • (wLat0 I w).mkQ (b l) := by
      rw [hqD i]; simp only [hqC]; exact comb _ CM DM i
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← h2, sub_self]

  have hTb : ∀ j, I.fmat x *ᵥ iv I (b j) ∈ I.Lf := T_mem I w hb.1 hMb
  have hTb' : ∀ j, I.fmat x *ᵥ iv I (b' j) ∈ I.Lf := T_mem I w hb'.1 hMb'
  have hTexp : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) =
      I.fmat x *ᵥ iv I (b' i) - ∑ k, CM k i • (I.fmat x *ᵥ iv I (b k)) := fun i => by
    rw [← TH_apply I x, ← ivH_apply I, map_sub, map_sub, map_sum, map_sum]
    simp only [map_zsmul, ivH_apply, TH_apply]
  have hTeL : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) ∈ I.Lf := fun i => by
    rw [hTexp]
    exact sub_mem (hTb' i) (Submodule.sum_mem _ fun k _ => zsmul_mem (hTb k) _)
  obtain ⟨r, hr1, hrL⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup I.L_fg le_rfl (span_of_red I w hb)
  have hTe : ∀ i, I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) ∈ Lw I w := fun i => by
    set e := b' i - ∑ k, CM k i • b k with he_def
    have he : e ∈ wLat0 I w := hCz i
    have hre : r • e ∈ Submodule.span (𝓞 I.E) (Set.range b) :=
      hrL (Submodule.smul_mem_pointwise_smul _ r I.L (wLat0_le I w he))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hre
    have hcw : ∀ j, c j ∈ w.asIdeal := indep I w hb.1 (span_of_red I w hb) c
      (by rw [hc, ← wLat0_eq]; exact (wLat0 I w).smul_mem r he)
    have h1 : Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) • (I.fmat x *ᵥ iv I e) ∈ Lw I w := by
      have e3 : Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) • (I.fmat x *ᵥ iv I e) =
          ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (c j : I.E) • (I.fmat x *ᵥ iv I (b j)) := by
        rw [← Matrix.mulVec_smul, ← DictLat.iv_smulO, ← hc, ← TH_apply I x, ← ivH_apply I, map_sum, map_sum]
        simp only [ivH_apply, DictLat.iv_smulO, TH_apply, Matrix.mulVec_smul]
      rw [e3]
      exact Submodule.sum_mem _ fun j _ => smul_mem_Lw I w (hcw j) (hTb j)
    have h2 := smul_mem_Lw I w hr1 (hTeL i)
    have e4 : Formalism.UG.inclE (F := I.F) (Af I.F) (((r - 1 : 𝓞 I.E)) : I.E) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (r : I.E) - 1 := by
      rw [sub_eq_add_neg, DictRing.incl_add, DictRing.incl_neg, DictRing.incl_one, ← sub_eq_add_neg]
    rw [e4, sub_smul, one_smul] at h2
    have h3 := sub_mem h1 h2
    rwa [sub_sub_cancel] at h3

  have hqA' : ∀ j, (Lw I w).mkQ (iv I (b' j)) = ∑ l, CM l j • (Lw I w).mkQ (iv I (b l)) := fun j => by
    have h0 : iv I (b' j) - ∑ l, CM l j • iv I (b l) ∈ Lw I w := by
      have := iv_mem_Lw I w (hCz j)
      rw [← ivH_apply I, map_sub, map_sum] at this
      simpa only [map_zsmul, ivH_apply] using this
    have h1 : (Lw I w).mkQ (iv I (b' j)) = (Lw I w).mkQ (∑ l, CM l j • iv I (b l)) :=
      (Submodule.Quotient.eq _).2 h0
    rw [h1, map_sum]; simp only [map_zsmul]
  have hA : ∀ i, (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i)) =
      ∑ l, (CM * M'z) l i • (Lw I w).mkQ (iv I (b l)) := fun i => by
    rw [red_eq I w hMb' i]; simp only [hqA']
    exact comb (fun l => (Lw I w).mkQ (iv I (b l))) CM M'z i
  have hB : ∀ i, (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i)) =
      ∑ l, (Mz * CM) l i • (Lw I w).mkQ (iv I (b l)) := fun i => by
    have h0 : I.fmat x *ᵥ iv I (b' i) =
        I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k) + ∑ k, CM k i • (I.fmat x *ᵥ iv I (b k)) := by
      rw [hTexp, sub_add_cancel]
    have hz : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b' i - ∑ k, CM k i • b k)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (hTe i)
    rw [h0, map_add, hz, zero_add, map_sum]
    simp only [map_zsmul, red_eq I w hMb]
    exact comb (fun l => (Lw I w).mkQ (iv I (b l))) Mz CM i
  have hMCz : ∀ l i, (((Mz * CM - CM * M'z) l i : ℤ) : ZMod p) = 0 := by
    intro l i
    refine zcoef_A I w p hp hcard hb (fun l => (Mz * CM - CM * M'z) l i) ?_ l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← hA i, ← hB i, sub_self]

  let φ := (Int.castRingHom (ZMod p)).mapMatrix (m := Fin I.n)
  have hφ0 : ∀ X : Matrix (Fin I.n) (Fin I.n) ℤ, (∀ l i, ((X l i : ℤ) : ZMod p) = 0) → φ X = 0 := by
    intro X hX; ext l i
    simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom, Matrix.zero_apply]
    exact hX l i
  have hCD : φ CM * φ DM = 1 := by
    have h := hφ0 _ hCDz
    rw [map_sub, map_one, map_mul, sub_eq_zero] at h
    exact h.symm
  have hDC : φ DM * φ CM = 1 := mul_eq_one_comm.1 hCD
  have hMC : φ Mz * φ CM = φ CM * φ M'z := by
    have h := hφ0 _ hMCz
    rwa [map_sub, map_mul, map_mul, sub_eq_zero] at h
  have hMz : φ Mz = (M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) := by
    ext j i
    simp only [φ, Mz, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have hM'z : φ M'z = (M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) := by
    ext j i
    simp only [φ, M'z, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Int.coe_castRingHom,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hMz, hM'z] at hMC
  refine ⟨⟨φ CM, φ DM, hCD, hDC⟩, Units.ext ?_⟩
  show (M' : Matrix (Fin I.n) (Fin I.n) (ZMod p)) = φ DM * (M : Matrix (Fin I.n) (Fin I.n) (ZMod p)) * φ CM
  rw [mul_assoc, hMC, ← mul_assoc, hDC, one_mul]

end Formalism.L2.SG.Pf.RedConj0Pf
