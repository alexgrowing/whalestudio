import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierLevelCharacterSumCongrStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierUnipotentPartCongrZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBesChar

variable {D : D7}

theorem hA_fR_nxt_zero (X : HidaSetting D) (u : D.what₂.Word) (a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (nxt X.eR (X.zR u) a)) = 0 := by
  rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_incl]
  have e1 : nxt X.eR (X.zR u) a = X.crd (nxt X.eX (X.zu u) a) := by
    unfold nxt; split_ifs <;> rfl
  have e2 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.crd (nxt X.eX (X.zu u) a)) = 0 := by
    apply X.ιE.injective
    rw [show X.fR a = X.crd (X.fY a) from rfl, GlobalTheory.St.hform_crd_setting, map_zero]
    unfold nxt
    split_ifs with hh
    · apply GlobalTheory.St.hT_symm_zero
      rw [X.ef, if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
    · exact (X.zu_orth u a).2
  rw [e1, e2, map_zero]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hs : SuppAt e V g) :
    g ∈ GfC V := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := he
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, hε] at h1
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (fstA D.host.F) (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  rw [h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

theorem smul_fact {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) (ε : R)
    (h : ∀ i j, M i j = ε * M i j) (v : Fin k → R) : M *ᵥ v = ε • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [h i j]
  ring

theorem supp_fact {A R : Type} [CommRing A] [CommRing R] {k : ℕ} (f : A →+* R) (M : Matrix (Fin k) (Fin k) A) (a : A)
    (h : ∀ i j, a * (M - 1) i j = (M - 1) i j) (v : Fin k → R) :
    (M.map f - 1) *ᵥ v = f a • ((M.map f - 1) *ᵥ v) := by
  refine smul_fact _ _ (fun i j => ?_) v
  have e1 : (M.map f - 1) i j = f ((M - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  rw [e1, ← map_mul, h i j]

theorem exists_eps (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) {e : AE D}
    {PP : Formalism.L2.DIV.Pl D.host.E} (hi : Formalism.L2.NTheta.IsIdemAt e PP)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (n : GA D (D.sp.Y 0)) (hs : SuppAt e (D.sp.Y 0) n) :
    ∃ ε : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F,
      (∀ c : ℕ, Nat.Coprime c X.B.g → ∃ t ∈ IntAf X.B.I.F X.B.I.E,
        ε = (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) ∧
      ∀ v, (X.B.I.fmat (iotaX X h n).2 - 1) *ᵥ v = ε • ((X.B.I.fmat (iotaX X h n).2 - 1) *ᵥ v) := by
  rw [X.g_eq]
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      ∃ ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F,
      (∀ c : ℕ, Nat.Coprime c (D.host.g 0 * D.host.g 1) → ∃ t ∈ IntAf I.F I.E,
        ε = (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t) ∧
      ∀ v, (I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).2 - 1) *ᵥ v =
        ε • ((I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D n)).2 - 1) *ᵥ v) := by
    intro I hI
    subst hI
    have hfin : (Formalism.L2.SG.InstExistsPf.instOf D).fmat (castGA (Eq.refl _) (Formalism.IndefR.RationalEmbedding.iota D n)).2 =
        (Lev.finE (D.sp.Y 0) n).1 := by
      have h1 := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D n)
      rw [ContinuousMulEquiv.symm_apply_apply] at h1
      rw [h1]
      rfl
    refine ⟨GlobalTheory.LevSplit.finSw D (e + cA D e), fun c hc => ?_, fun v => ?_⟩
    · have hcP : ((c : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
        intro hcm
        obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
        have h1 : ((a : 𝓞 D.host.E) * (c : 𝓞 D.host.E) + (b : 𝓞 D.host.E) * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)) = 1 := by
          have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
          push_cast at this ⊢
          exact this
        apply PP.isPrime.ne_top
        rw [Ideal.eq_top_iff_one, ← h1]
        exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hcm) (PP.asIdeal.mul_mem_left _ hg)
      have hc0 : ((c : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h0 => hcP (h0 ▸ PP.asIdeal.zero_mem)
      have hcE : (((c : ℕ) : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := by simp
      have hcE0 : (c : D.host.E) ≠ 0 := by rw [← hcE]; exact_mod_cast hc0
      have hint : finPart D (e * incA D (((c : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) ∈ intAE D :=
        not_not.1 fun hn => hcP ((hi.2 _ hc0).2 hn)
      rw [hcE] at hint
      set z := e * incA D (c : D.host.E)⁻¹ with hzdef
      have hcA : ∀ y : D.host.E, cA D (incA D y) = incA D (D.sp.cm.sig y) := fun y => rfl
      have hz : incA D (c : D.host.E) * z = e := by
        rw [hzdef, mul_comm, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hcE0, RingHom.map_one, mul_one]
      have hz' : incA D (c : D.host.E) * cA D z = cA D e := by
        have : incA D (c : D.host.E) = cA D (incA D (c : D.host.E)) := by
          rw [hcA]; exact congrArg (incA D) (map_natCast _ c).symm
        rw [this, ← RingHom.map_mul, hz]
      refine ⟨GlobalTheory.LevSplit.finSw D z + GlobalTheory.LevSplit.finSw D (cA D z),
        add_mem (GlobalTheory.LevSplit.swapAE_int hint) ?_, ?_⟩
      · rw [GlobalTheory.LevSplit.finSw_cA]
        exact PIW.NormChiNBi.sigA_int _ (GlobalTheory.LevSplit.swapAE_int hint)
      · show GlobalTheory.LevSplit.finSw D (e + cA D e) =
          ((c : ℕ) : Lev.EAf D) * (GlobalTheory.LevSplit.finSw D z + GlobalTheory.LevSplit.finSw D (cA D z))
        have hcc : ((c : ℕ) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D (incA D (c : D.host.E)) := by
          rw [GlobalTheory.LevSplit.finSw_incA, map_natCast]
        rw [hcc, mul_add, ← RingHom.map_mul, ← RingHom.map_mul, hz, hz', RingHom.map_add]
    · rw [hfin]
      exact supp_fact (GlobalTheory.LevSplit.finSw D) (mt (D.sp.Y 0) n) (e + cA D e) hs v
  exact key X.B.I h

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem besselLevel_chi_conj_eq_finite_bessel_character (X : HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf) (ε : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hε : ∀ c : ℕ, Nat.Coprime c X.B.g → ∃ t ∈ IntAf X.B.I.F X.B.I.E,
      ε = (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t)
    (hs : ∀ v, (X.B.I.fmat m - 1) *ᵥ v = ε • ((X.B.I.fmat m - 1) *ᵥ v))
    (hN : m ∈ X.NfinU u) (hK : (X.xu u)⁻¹ * m * X.xu u ∈ X.K2) :
    X.chi2 ((X.xu u)⁻¹ * m * X.xu u) = X.psiFinU u m := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, hbe, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  set y := (X.xu u)⁻¹ * m * X.xu u with hy
  have hxK := X.xu_K u
  have hmK : m ∈ X.B.I.Kset := by
    have e : m = X.xu u * y * (X.xu u)⁻¹ := by rw [hy]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hK.1) (K_inv _ hxK)
  have hsy : ∀ v, (X.B.I.fmat y - 1) *ᵥ v = ε • ((X.B.I.fmat y - 1) *ᵥ v) := by
    have e1 : ∀ v, (X.B.I.fmat y - 1) *ᵥ v =
        X.B.I.fmat (X.xu u)⁻¹ *ᵥ ((X.B.I.fmat m - 1) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v)) := by
      intro v
      rw [hy, fmat_mul, fmat_mul]
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.mulVec_mulVec,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc, fmat_inv_mul]
    intro v
    conv_lhs => rw [e1, hs, Matrix.mulVec_smul, ← e1]
  have split : ∀ (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) (f v : VA X.B.I),
      hA X.B.I f (M *ᵥ v) = hA X.B.I f v + hA X.B.I f ((M - 1) *ᵥ v) := by
    intro M f v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right]
    ring

  set T1 := ∑ a, hA X.B.I (X.f0 a) ((X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a) with hT1
  set T3 := ∑ a, hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) with hT3
  set T2 := ∑ i : Fin D.R.k, (if h : i.1 + 1 < D.R.k then
        hA X.B.I (X.bwd i) ((X.B.I.fmat y - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) with hT2
  have eAy : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y = Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + (T1 + T2) := by
    have p1 : ∀ a, hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a) =
        hA X.B.I (X.f0 a) (X.B.I.fmat 1 *ᵥ nxt X.e0 X.z0 a) + hA X.B.I (X.f0 a) ((X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a) := by
      intro a; rw [fmat_one, Matrix.one_mulVec, split]
    have p2 : ∀ i : Fin D.R.k, (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat y *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) =
        (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat 1 *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) +
        (if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat y - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
      intro i
      split_ifs with h
      · rw [fmat_one, Matrix.one_mulVec, split]
      · rw [add_zero]
    unfold Afun
    rw [Finset.sum_congr rfl (fun a _ => p1 a), Finset.sum_congr rfl (fun i _ => p2 i), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    ring
  have eC : ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)) = T3 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [split, hA_fR_nxt_zero, zero_add]
  have hA1 : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1) :=
    Afun_Kg X.B.I X.B.g X.e0 X.f0 X.z0 X.bw X.bwd
      ⟨K_one _, fun v _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩
      he0 hf0 hz0 hbw hbwd hfe hfz hbb

  have hS : (T1 - T3) + T2 = ε * ((T1 - T3) + T2) := by
    have q1 : T1 = ε * T1 := by
      rw [hT1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [hsy]
      rw [hA_smul_right]
    have q3 : T3 = ε * T3 := by
      rw [hT3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [hs]
      rw [hA_smul_right]
    have q2 : T2 = ε * T2 := by
      rw [hT2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · conv_lhs => rw [hsy]
        rw [hA_smul_right]
      · rw [mul_zero]
    rw [mul_add, mul_sub, ← q1, ← q2, ← q3]
  obtain ⟨c1, hc1, h1⟩ := GlobalTheory.T.exists_coprime_multiplier_levelCharacter_sum_congr D X u m hmK
  obtain ⟨c2, hc2, h2⟩ := GlobalTheory.T.exists_coprime_multiplier_unipotentPart_congr_zero D X u m hmK hN
  have h1' : ZMod' X.B.I X.B.g ((c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * (T1 - T3)) := by
    rw [hT1, hT3, ← Finset.sum_sub_distrib]; exact h1
  obtain ⟨t, ht, hεt⟩ := hε (c1 * c2) (Nat.Coprime.mul hc1 hc2)
  have hcS : ZMod' X.B.I X.B.g (((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((T1 - T3) + T2)) := by
    have e : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((T1 - T3) + T2) =
        (c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * (T1 - T3)) +
        (c1 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ((c2 : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * T2) := by
      push_cast; ring
    rw [e]
    exact Z_add _ _ (Z_smul _ _ (natCast_mem _ c2) h1') (Z_smul _ _ (natCast_mem _ c1) h2)
  have hZS : ZMod' X.B.I X.B.g ((T1 - T3) + T2) := by
    rw [hS, hεt, mul_comm _ t, mul_assoc]
    exact Z_smul _ _ ht hcS
  have hdiff : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y -
      ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))) := by
    rw [eAy, eC]
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + (T1 + T2) - T3 =
        Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd 1 + ((T1 - T3) + T2) := by ring
    rw [e]
    exact Z_add _ _ hA1 hZS
  show chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd y =
    psiFin X.B.I X.psiEf X.B.g X.eR X.fR (X.zR u) m
  rw [flagLevelCharacter_eq_psi_divN]
  unfold psiFin
  set C := ∑ a, hA X.B.I (incl X.B.I (X.fR a)) (X.B.I.fmat m *ᵥ incl X.B.I (nxt X.eR (X.zR u) a))
  have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y = C + (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd y - C) := by ring
  rw [e, divN_add, X.psiEf_add, psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hdiff, mul_one]

theorem rowChi_conj_eq_psiBes : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), GlobalTheory.Core.Mi.IdE X → ∀ (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), IsSplitIdem D e → Formalism.L2.NTheta.IsIdemAt e PP → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ n ∈ flagN B.d, Formalism.L2.Theta.SuppAt e (D.sp.Y 0) n → ((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u)) ∈ rowJ X h → rowChi X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) = psiBes ψ B.d 1 (vecB B.o B.ζ) n := by
  intro D X h u ψ A B _hE PP e hsp hid hg n hn hsupp hJ
  have hGf : n ∈ GfC (D.sp.Y 0) := mem_GfC_of_suppAt hsp hsupp
  have h1 : (iotaX X h n).1 = 1 := (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h n).2 hGf
  have hix : iotaX X h ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) :=
    ContinuousMulEquiv.apply_symm_apply _ _
  have hι : iotaX X h (((iotaX X h).symm (1, X.xu u))⁻¹ * n * ((iotaX X h).symm (1, X.xu u))) =
      (1, (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u) := by
    rw [map_mul, map_mul, map_inv, hix]
    ext
    · simp [h1]
    · rfl
  have hK : (X.xu u)⁻¹ * (iotaX X h n).2 * X.xu u ∈ X.K2 := by
    have h2 := hJ
    unfold rowJ at h2
    rw [Set.mem_preimage, hι] at h2
    exact h2.2
  obtain ⟨ε, hε, hs⟩ := exists_eps X h hid hg n hsupp
  have hN : (iotaX X h n).2 ∈ X.NfinU u := ((B.tieN n).1 hn).2
  have hc := besselLevel_chi_conj_eq_finite_bessel_character X u _ ε hε hs hN hK
  have hψ := B.tieψ n hn
  rw [h1, Formalism.L2.S.Pv.TauS.psiInfU_one, one_mul] at hψ
  rw [rowChi, hι]
  dsimp only
  rw [hc, ← hψ, star_star]

end GlobalTheory.RowBesChar
