import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationDetBasisChange
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PowSmulLatticeLeWeightLatticeTop

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB.V0

open Formalism.BasicNotions NumberField Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

theorem residue_nat_ne_zero_level_zero (Tt : Forms0 D u) (v : (D.mem u).A.vT) (s : ℕ) (hs : ¬ (D.mem u).A.T ∣ s) :
    Tt.atT.res v (s : 𝓞 D.host.E) ≠ 0 := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  intro h
  apply hs
  rw [map_natCast] at h
  have e : (D.mem u).A.Fv v ≃+* ZMod (D.mem u).A.T :=
    FiniteField.ringEquivOfCardEq (by rw [(D.mem u).A.card_Fv v, ZMod.card])
  have h2 : (s : ZMod (D.mem u).A.T) = 0 := by
    rw [← map_natCast e s, h, map_zero]
  exact (CharP.cast_eq_zero_iff (ZMod (D.mem u).A.T) (D.mem u).A.T s).mp h2

theorem not_T_dvd_finset_prod {ι : Type} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, ¬ (D.mem u).A.T ∣ f i) :
    ¬ (D.mem u).A.T ∣ ∏ i ∈ s, f i := by
  exact not_dvd_prod_of_not_dvd (D := D) (u := u) s f h

theorem det_basis_change_mem_prime_zero (Tt : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ∃ (S : ℕ) (x : 𝓞 D.host.E), ¬ (D.mem u).A.T ∣ S ∧ Tt.atT.res v x = 0 ∧
      (x : D.host.E) = (S : D.host.E) ^ D.R.N i *
        (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).det := by
  set M : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E := ((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) with hMdef
  have hLk : Lk Tt.atT i hi v c ≤ Ld D u i hi c := sup_le (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.bwL_lcInt0 D u Tt i hi h0 c) Submodule.smul_le_right
  have hone : ¬ (D.mem u).A.T ∣ 1 := (D.mem u).A.T_prime.not_dvd_one

  choose sk hsk hskL using fun k => bwD_col_loc D u w hw hB' k
  have hcolM : ∀ k a, (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ
      (fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)) a = M a k := by
    intro k a; rw [bwD_mulVec_col, ← Units.val_mul]
  have hco : ∀ k, ∃ s' : ℕ, ¬ (D.mem u).A.T ∣ s' ∧ ∀ a, ((s' * sk k : ℕ) : D.host.E) * M a k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro k
    obtain ⟨s', hs', hm⟩ := (hB ((sk k : D.host.E) • fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)).1
      ⟨1, hone, by rw [Nat.cast_one, one_smul]; exact hLk (hskL k)⟩
    refine ⟨s', hs', fun a => ?_⟩
    have := hm a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hcolM] at this
    rw [Nat.cast_mul, mul_assoc]; exact this
  choose s2 hs2 hs2m using hco
  set S : ℕ := ∏ k, s2 k * sk k with hSdef
  have hS : ¬ (D.mem u).A.T ∣ S :=
    not_T_dvd_finset_prod D u _ _ (fun k _ => by
      intro hd
      rcases (Nat.Prime.dvd_mul (D.mem u).A.T_prime).1 hd with h | h
      · exact hs2 k h
      · exact hsk k h)
  have hSM : ∀ a k, (S : D.host.E) * M a k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro a k
    obtain ⟨q, hq⟩ : s2 k * sk k ∣ S := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    rw [hq, Nat.cast_mul, mul_comm ((s2 k * sk k : ℕ) : D.host.E), mul_assoc]
    exact Subring.mul_mem _ ⟨(q : 𝓞 D.host.E), map_natCast _ _⟩ (hs2m k a)
  choose m hm using hSM

  choose tb htb htbL using fun a => bwD_col_loc D u w hw hB a
  set t : ℕ := ∏ a, tb a with htdef
  have ht : ¬ (D.mem u).A.T ∣ t := not_T_dvd_finset_prod D u _ _ (fun a _ => htb a)
  have hbL : ∀ a, (t : D.host.E) • (fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a) ∈ (Ld D u i hi c : Set _) := by
    intro a
    obtain ⟨q, hq⟩ : tb a ∣ t := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    have h1 := (Ld D u i hi c).smul_mem (q : 𝓞 D.host.E) (htbL a)
    have e : (q : 𝓞 D.host.E) • ((tb a : D.host.E) • fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a) =
        (t : D.host.E) • fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a := by
      ext r
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hq, Nat.cast_mul, Algebra.smul_def,
        map_natCast]
      ring
    rw [← e]; exact h1
  set eb : Fin (D.R.N i) → ↥(Ld D u i hi c) := fun a => ⟨_, hbL a⟩ with hebdef
  set P := Tt.lv i hi h0
  set φ : Fin (D.R.N i) → (D.mem u).A.Fv v := fun a => (D.fm u).fv i v c (P.pr v c (eb a)) with hφdef

  have hexp : ∀ (z : Fin (D.R.N i) → D.host.E) (g : Fin (D.R.N i) → 𝓞 D.host.E) (s : ℕ),
      (∀ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) = (s : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z) a) →
      ((s * t : ℕ) : D.host.E) • z = ∑ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) • ((eb a : ↥(Ld D u i hi c)) : Fin (D.R.N i) → D.host.E) := by
    intro z g s hg
    set cz := ((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z with hcz
    have hz : z = (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ cz := by
      rw [hcz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    ext r
    simp only [hebdef, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hg, Nat.cast_mul]
    have hzr : z r = ∑ x, (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r x * cz x := by
      conv_lhs => rw [hz]
      rfl
    rw [hzr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hprS : ∀ (z : ↥(Ld D u i hi c)) (g : Fin (D.R.N i) → 𝓞 D.host.E) (s : ℕ),
      (∀ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) = (s : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z.1) a) →
      Tt.atT.res v ((s * t : ℕ) : 𝓞 D.host.E) * (D.fm u).fv i v c (P.pr v c z) = ∑ a, Tt.atT.res v (g a) * φ a := by
    intro z g s hg
    have hz : ((s * t : ℕ) : 𝓞 D.host.E) • z = ∑ a, g a • eb a := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [show ((s * t : ℕ) : 𝓞 D.host.E) • z.1 = ((s * t : ℕ) : D.host.E) • z.1 by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]]
      rw [hexp z.1 g s hg]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def]; rfl
    have := congrArg (fun y => (D.fm u).fv i v c (P.pr v c y)) hz
    simp only [P.pr_smul, map_smul, map_sum, smul_eq_mul] at this
    exact this

  have hφ : φ ≠ 0 := by
    intro h0
    apply (D.fm u).fv_ne i v c
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := P.pr_surj v c y
    obtain ⟨s3, hs3, hs3m⟩ := (hB z.1).1 ⟨1, hone, by rw [Nat.cast_one, one_smul]; exact z.2⟩
    choose g hg using hs3m
    have h := hprS z g s3 (fun a => hg a)
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 (residue_nat_ne_zero_level_zero D u Tt v _ (by
        intro hd
        rcases (Nat.Prime.dvd_mul (D.mem u).A.T_prime).1 hd with h | h
        · exact hs3 h
        · exact ht h))
    · rw [h1]; rfl

  have hrel : ∀ k, ∑ a, Tt.atT.res v (m a k) * φ a = 0 := by
    intro k
    have hg : ∀ a, algebraMap (𝓞 D.host.E) D.host.E ((sk k : 𝓞 D.host.E) * m a k) =
        (S : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ
          ((sk k : D.host.E) • fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)) a := by
      intro a
      rw [map_mul, map_natCast, hm a k, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hcolM]; ring
    have h := hprS ⟨_, hLk (hskL k)⟩ (fun a => (sk k : 𝓞 D.host.E) * m a k) S hg
    rw [((P.fv_ker v c ⟨_, hLk (hskL k)⟩).2 (hskL k)), mul_zero] at h
    simp only [map_mul, mul_assoc] at h
    rw [← Finset.mul_sum] at h
    rcases mul_eq_zero.1 h.symm with h1 | h1
    · exact absurd h1 (residue_nat_ne_zero_level_zero D u Tt v _ (hsk k))
    · exact h1

  have hdetR : (Matrix.of fun a k => Tt.atT.res v (m a k)).det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨φ, hφ, funext fun k => ?_⟩
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hrel k]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨S, (Matrix.of m).det, hS, ?_, ?_⟩
  · rw [RingHom.map_det]; exact hdetR
  · show algebraMap (𝓞 D.host.E) D.host.E (Matrix.of m).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have e : (Matrix.of m).map (algebraMap (𝓞 D.host.E) D.host.E) = (S : D.host.E) • M := by
      ext a k; simp [hm a k]
    rw [e, Matrix.det_smul, Fintype.card_fin]

theorem withTop_add_neg_nonneg (a : WithTop ℤ) (e : ℤ) (h : (e : WithTop ℤ) ≤ a) : 0 ≤ a + -(e : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    have hb : e ≤ b := by exact_mod_cast h
    have key : ((b : WithTop ℤ) + -(e : WithTop ℤ)) = ((b - e : ℤ) : WithTop ℤ) := by
      first
        | rw [sub_eq_add_neg, WithTop.coe_add, WithTop.LinearOrderedAddCommGroup.coe_neg]
        | norm_cast
        | simp [sub_eq_add_neg]
    rw [key]
    exact_mod_cast (show (0 : ℤ) ≤ b - e by omega)

theorem valuation_det_basis_change_zero (Tt : Forms0 D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w := by
  obtain ⟨S, x, hS, hx0, hxe⟩ := det_basis_change_mem_prime_zero D u Tt w hw v i hi h0 c B B' hB hB'
  have hv := hU w hw hs v x hx0
  set σ := D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG) with hσ
  set δ := (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).det with hδ
  have hS0 : D.what₂.places.val w (S : D.what₂.LL) = 0 :=
    bwA_val_nat_eq_zero D.what₂.places w S (by rw [hw]; exact hS)
  have hvx : D.what₂.places.val w (D.embE (σ (x : D.host.E))) = D.what₂.places.val w (D.embE (σ δ)) := by
    rw [hxe, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, AddValuation.map_mul, AddValuation.map_pow,
      hS0, nsmul_zero, zero_add]
  rw [hvx] at hv
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine Subring.mem_map.2 ⟨D.embE (σ δ) * ((D.mem u).A.T : D.what₂.LL)⁻¹, ?_, ?_⟩
  · show (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ δ) * ((D.mem u).A.T : D.what₂.LL)⁻¹)
    rw [AddValuation.map_mul, AddValuation.map_inv, ← hw, D.what₂.places.val_resChar]
    exact withTop_add_neg_nonneg _ _ hv
  · rw [map_mul, map_inv₀, map_natCast, bwA_embT_eq]

theorem det_basis_change_unit_zero (Tt : Forms0 D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
    ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w :=
  ⟨valuation_det_basis_change_zero D u Tt hU w hw hs v i hi h0 c B B' hB hB',
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.basis_change_mem_elementary (D := D) (u := u) Tt w hw v ((D.fm u).tauOf w v) i hi h0 c B B' hB hB').2.2.2⟩

end Formalism.L2.GlobalTheoryTheory.LemB.V0
