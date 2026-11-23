import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLabWD
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N NumberField Polynomial

namespace Formalism.L2

open Formalism.L2.NT Formalism.L2.Host

variable (D : D7)

def KQbar (jE : D.host.E →+* Qb) : Fld := D.host.K.map jE.toRatAlgHom

def MrayC (jE : D.host.E →+* Qb) : Fld := rayField (KQbar D jE) (D.host.QS * D.host.q * D.host.d)

def RegParts (Sig : List (Part D.naut.CG)) : Prop :=
  ∀ p ∈ Sig, ∀ τ, (D.naut.infG p.π τ).Nodup ∧
    ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2

def IsBcRow (i : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  HasParamW D.nd D.naut i σ Sig ∧ (∀ p ∈ Sig, D.naut.csd p.π) ∧ RegParts D Sig

def msOf (Sig : List (Part D.naut.CG)) : Multiset (ℕ × ℕ) :=
  Multiset.ofList (Sig.map fun p => (p.a, p.d))

def BcUnique : Prop :=
  ∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (Sig Sig' : List (Part D.naut.CG)),
    IsBcRow D i σ Sig → IsBcRow D i' σ Sig' → msOf D Sig = msOf D Sig'

def BcExists : Prop := ∀ (σ : D.what₂.FT) (i : D.nd.Loc), ∃ Sig, IsBcRow D i σ Sig

def ParC : Type :=
  {Sig : List (Part D.naut.CG) //
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r}

def RayLarger (jE : D.host.E →+* Qb) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (p : D.host.E)) ∧ ¬ SplitsIn (MrayC D jE) p

def RedCompat (i : D.nd.Loc) (B : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hpl : p = D.nd.l i)
    (κ : IsLocalRing.ResidueField B ≃+* Fb p hp) : Prop :=
  ∀ y : D.nd.O i, ∃ h : D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) ∈ B,
    fbCast hpl hp (D.nd.lPrime i).out (κ (IsLocalRing.residue B ⟨_, h⟩)) =
      D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)

def LocCompat : Prop :=
  ∀ w : D.what₂.places.Pl, ∃ (B : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField B ≃+* Fb (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)),
    ∀ (i : D.nd.Loc) (h : D.nd.w i = w), RedCompat D i B (D.what₂.places.resChar_prime w) (h ▸ D.nd.w_l i) κ

structure NormalizedTypesCompatibility (jE : D.host.E →+* Qb) where

  eM : D.ntypes.Mray ≃+* MrayC D jE
  eM_K : ∀ x : D.host.K, ((eM (algebraMap D.host.K D.ntypes.Mray x) : MrayC D jE) : Qb) = jE x

  tA : Fin 2 → ValuationSubring ℂ
  tκ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (tA k) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)
  teichC_def : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsTeich (tA k) (tκ k) (D.ntypes.teichC k)

  iota_loc : ∀ i : D.nd.Loc, haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime :=
      ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
      (∀ y : D.nd.O i, ∃ h : D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) ∈ B,
        fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
          (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
      ∀ k v x, D.ntypes.iota k v (D.nd.w i) x = redThrough B κ (D.ntypes.teichC k x)

  ζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ℕ → Formalism.CyclotomicNorms.Fbar (D.host.g k)
  ζ_gen : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsGenSys (ζ k)

  O : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (ζ k) (ζ_gen k))
  eSer_def : ∀ k f, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.ntypes.eSer k f = eSerO (O k) D.R.r f

  kv : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)

  tg_tame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (kv k v) (D.ntypes.tg k v) (ζ k)

  O_equiv : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant (O k)

  O_tw : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabTwLawO (O k)

  eP : D.ntypes.Par ≃ ParC D
  locPar_def : ∀ σ w, D.ntypes.locPar σ w = isoLoc D.nd D.naut (eP σ).1 w

variable {D}
variable {jE : D.host.E →+* Qb}

theorem splitsIn_mrayC_iff (T : NormalizedTypesCompatibility D jE) (p : ℕ) :
    SplitsIn (MrayC D jE) p ↔ (placesOver D.ntypes.Mray p).ncard = Module.finrank ℚ D.ntypes.Mray := by
  unfold SplitsIn plOver placesOver
  rw [ncard_places_of_equiv T.eM p, finrank_eq_of_equiv T.eM]

theorem mrayRay_of_tied (T : NormalizedTypesCompatibility D jE) (hC : RayCFT (KQbar D jE) (D.host.QS * D.host.q * D.host.d))
    (a : ℕ) (ha : 1 ≤ a) : Formalism.MainNotions.ArithmeticCylinders.MrayRay D a := by
  rintro p hp ⟨π, hπK, hpp, hπ1⟩
  rw [← splitsIn_mrayC_iff T]
  have hcond : D.ntypes.cond = D.host.QS * D.host.q * D.host.d := rfl
  refine hC.2.2 p ⟨hp, jE π, ⟨π, hπK, rfl⟩,
    (NumberField.RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hπ1
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    set N : Qb := ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) with hN
    have hc' : jE (algebraMap (𝓞 D.host.E) D.host.E c) * N ^ (b + 1) =
        jE (algebraMap (𝓞 D.host.E) D.host.E π) - 1 := by
      have h1 := congrArg (fun x : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E x)) hc
      simp only [map_mul, map_sub, map_one, map_pow, map_natCast, Nat.cast_pow] at h1
      rw [hcond] at h1
      rw [hN]
      exact_mod_cast h1
    have e0 : algebraMap (𝓞 D.host.E) D.host.E π = (π : D.host.E) := rfl
    rw [e0] at hc'
    have hci : IsIntegral ℤ (jE (algebraMap (𝓞 D.host.E) D.host.E c)) :=
      ((RingOfIntegers.isIntegral c).algebraMap).map jE.toIntAlgHom
    by_cases h0 : N = 0
    · rw [h0, div_zero]
      exact isIntegral_zero
    · have e : (jE (π : D.host.E) - 1) / N = jE (algebraMap (𝓞 D.host.E) D.host.E c) * N ^ b := by
        rw [← hc', div_eq_iff h0]
        ring
      rw [e]
      have hNi : IsIntegral ℤ N := by
        rw [hN, ← map_natCast (algebraMap ℤ Qb)]
        exact isIntegral_algebraMap
      exact hci.mul (hNi.pow b)
  · haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
    haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
    letI : Algebra D.host.E Qb := jE.toAlgebra
    haveI : IsScalarTower ℚ D.host.E Qb := IsScalarTower.of_algebraMap_eq fun x =>
      congrFun (congrArg DFunLike.coe (Subsingleton.elim (algebraMap ℚ Qb)
        ((algebraMap D.host.E Qb).comp (algebraMap ℚ D.host.E)))) x
    refine ⟨(D.host.conj : D.host.E →ₐ[ℚ] D.host.E).liftNormal Qb, ?_⟩
    have hσ := AlgHom.liftNormal_commutes (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) Qb (π : D.host.E)
    have e1 : (algebraMap D.host.E Qb) = jE := rfl
    rw [e1] at hσ
    rw [hσ, ← map_mul]
    change jE ((π : D.host.E) * D.host.conj (π : D.host.E)) = (p : Qb)
    rw [hpp, map_natCast]

theorem not_mrayRay_zero (T : NormalizedTypesCompatibility D jE) (h : RayLarger D jE) : ¬ Formalism.MainNotions.ArithmeticCylinders.MrayRay D 0 := by
  intro hM
  obtain ⟨p, hp, ⟨π, hK, hpp⟩, hns⟩ := h
  apply hns
  rw [splitsIn_mrayC_iff T]
  refine hM p hp ⟨π, hK, hpp, ?_⟩
  rw [pow_zero, Nat.cast_one, Ideal.span_singleton_one]
  exact Submodule.mem_top

namespace NT

def RayCFTImQ : Prop :=
  ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → ∀ z ∈ K, z ^ 2 = -(d : Qb) → 0 < d → 0 < m → 2 * d ∣ m →
    RayCFT K m

end NT

theorem finrank_KQbar (jE : D.host.E →+* Qb) : Module.finrank ℚ (KQbar D jE) = 2 := by
  have h : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (d := D.host.d) D.host.hyp.2.1.pos
      (D.host.sqd_sq)
  rw [← h]
  exact (IntermediateField.equivMap D.host.K jE.toRatAlgHom).toLinearEquiv.finrank_eq.symm

theorem sqrtMinusD_mem_KQbar (jE : D.host.E →+* Qb) : jE D.host.sqrtMinusD ∈ KQbar D jE :=
  (IntermediateField.mem_map _).2 ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _, rfl⟩

theorem sqrtMinusD_sq_Qbar (jE : D.host.E →+* Qb) : (jE D.host.sqrtMinusD) ^ 2 = -(D.host.d : Qb) := by
  rw [← map_pow, show D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) from D.host.sqd_sq,
    map_neg, map_natCast]

theorem hostCond_pos : 0 < D.host.QS * D.host.q * D.host.d :=
  Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos

theorem rayCFT_KQbar (h : NT.RayCFTImQ) : RayCFT (KQbar D jE) (D.host.QS * D.host.q * D.host.d) :=
  h (KQbar D jE) D.host.d _ (finrank_KQbar (D := D) jE) (jE D.host.sqrtMinusD) (sqrtMinusD_mem_KQbar (D := D) jE)
    (sqrtMinusD_sq_Qbar (D := D) jE) D.host.hyp.2.1.pos (hostCond_pos (D := D))
    (Nat.mul_dvd_mul_right
      (((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd).mul_right D.host.q) D.host.d)

theorem mrayRay_of_tied' (T : NormalizedTypesCompatibility D jE) (hC : NT.RayCFTImQ) (a : ℕ) (ha : 1 ≤ a) :
    Formalism.MainNotions.ArithmeticCylinders.MrayRay D a :=
  mrayRay_of_tied T (rayCFT_KQbar hC) a ha

theorem teichC_injective (T : NormalizedTypesCompatibility D jE) (k : Fin 2) : Function.Injective (D.ntypes.teichC k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  (T.teichC_def k).injective

theorem teichC_zero (T : NormalizedTypesCompatibility D jE) (k : Fin 2) : D.ntypes.teichC k 0 = 0 :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  (T.teichC_def k).map_zero

theorem iota_indep (T : NormalizedTypesCompatibility D jE) (i : D.nd.Loc) (k : Fin 2) (v v' : D.nd.PlG k) :
    D.ntypes.iota k v (D.nd.w i) = D.ntypes.iota k v' (D.nd.w i) := by
  obtain ⟨B, κ, -, h⟩ := T.iota_loc i
  ext x
  rw [h, h]

theorem globalDatumRegularity_of_typesCompatibility (T : NormalizedTypesCompatibility D jE) : GlobalDatumRegularity D := by
  intro i k v u y _hl hy
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨B, κ, hcomp, hiota⟩ := T.iota_loc i
  obtain ⟨hyB, hyκ⟩ := hcomp y
  rw [← hyκ]
  congr 1
  set ū : Formalism.CyclotomicNorms.Fbar (D.host.g k) := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))
  have hfin : ū ^ orderOf u = 1 := by
    simp only [ū]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hpos : 0 < orderOf ū := (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, orderOf_pos u, hfin⟩).orderOf_pos
  rw [hiota, redThrough_primeToPart B κ (D.ntypes.teichC k) ū hpos]
  unfold redThrough
  have hB : D.ntypes.teichC k ū ∈ B := hy ▸ hyB
  rw [dif_pos hB]
  congr 2
  exact Subtype.ext hy

theorem eSer_zero_of_tie (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : D.ntypes.eSer k f = 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [T.eSer_def]
  exact eSerO_eq_zero _ _ f hf

theorem natCast_g_ne_zero (k : Fin 2) : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := by
  have h : ((D.host.g k : ℕ) : D.nd.Om) = algebraMap D.host.E D.nd.Om ((D.host.g k : ℕ) : D.host.E) := by
    rw [map_natCast]
  rw [h]
  intro h0
  have h1 := (algebraMap D.host.E D.nd.Om).injective (h0.trans (map_zero _).symm)
  exact (Nat.cast_ne_zero.mpr (D.host.g_prime k).ne_zero) h1

theorem exists_tameRoot (k : Fin 2) (d : ℕ) (hd : 0 < d) :
    ∃ y : D.nd.Om, y ^ (D.host.g k ^ d - 1) = ((D.host.g k : ℕ) : D.nd.Om) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have h2 : 2 ≤ D.host.g k ^ d :=
    le_trans (D.host.g_prime k).two_le (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hd) _)
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

theorem tg_tameQuot_mem (k : Fin 2) (v : D.nd.PlG k) (d : ℕ) (hd : 0 < d) (y : D.nd.Om)
    (hy : y ^ (D.host.g k ^ d - 1) = ((D.host.g k : ℕ) : D.nd.Om)) :
    (D.ntypes.tg k v) y / y ∈ D.nd.plOm.1 (D.naut.plGw k v) := by
  have h2 : 2 ≤ D.host.g k ^ d :=
    le_trans (D.host.g_prime k).two_le (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hd) _)
  exact tameQuot_mem _ _ (by omega) (natCast_g_ne_zero k) hy

theorem tame_agree (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (v v' : D.nd.PlG k) (d : ℕ) (hd : 0 < d) (y : D.nd.Om)
    (hy : y ^ (D.host.g k ^ d - 1) = ((D.host.g k : ℕ) : D.nd.Om)) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (T.kv k v) ((D.ntypes.tg k v) y / y) =
      redThrough (D.nd.plOm.1 (D.naut.plGw k v')) (T.kv k v') ((D.ntypes.tg k v') y / y) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [T.tg_tame k v d hd y hy, T.tg_tame k v' d hd y hy]

variable (D) in

def TameSurj : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k))
      (ζ : ℕ → Formalism.CyclotomicNorms.Fbar (D.host.g k)), IsGenSys ζ →
      ∃ σ : D.nd.Om ≃ₐ[D.host.E] D.nd.Om, TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
        TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ ζ

variable (D)

theorem bcUnique_of_bcTie (h : BcTie D.nd D.naut D.ntypes) : BcUnique D := by
  intro i i' σ Sig Sig' h1 h2
  have e1 := h i σ Sig h1.1 h1.2.1 h1.2.2
  have e2 := h i' σ Sig' h2.1 h2.2.1 h2.2.2
  exact e1.symm.trans e2

theorem bcUnique : BcUnique D := bcUnique_of_bcTie D D.bc_tie

theorem bc_eq_msOf (σ : D.what₂.FT) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (h : IsBcRow D i σ Sig) :
    D.ntypes.bc σ = msOf D Sig :=
  D.bc_tie i σ Sig h.1 h.2.1 h.2.2

variable {D}

theorem lpDim_foldr {w : PlE D.host} {a : ℕ} {β : Type} (π : D.naut.CG a) (L : List β) (f : β → ℝ)
    (z : D.naut.LP w) :
    D.naut.lpDim (L.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG π w) (f k)) acc) z) =
      L.length * a + D.naut.lpDim z := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.lpDim_sum, D.naut.lpDim_tw, D.naut.locG_dim, ih]
    ring

theorem lpDim_spehLoc (p : Part D.naut.CG) (w : PlE D.host) :
    D.naut.lpDim (spehLoc D.nd D.naut p w) = p.a * p.d := by
  unfold spehLoc
  have h := lpDim_foldr (D := D) p.π (do let a ← List.range p.d; pure (a : ℝ))
    (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (D.naut.lpZero w)
  rw [h, D.naut.lpDim_zero, add_zero, mul_comm]
  congr 1
  simp

theorem lpDim_isoLoc (Sig : List (Part D.naut.CG)) (w : PlE D.host) :
    D.naut.lpDim (isoLoc D.nd D.naut Sig w) = rankIso D.nd D.naut Sig := by
  induction Sig with
  | nil => simp [isoLoc, rankIso, D.naut.lpDim_zero]
  | cons p Sig ih =>
    unfold isoLoc at ih ⊢
    unfold rankIso at ih ⊢
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [D.naut.lpDim_sum, lpDim_spehLoc, ih]

theorem locPar_dim_of (T : NormalizedTypesCompatibility D jE) (σ : D.ntypes.Par) (w : PlE D.host) :
    D.naut.lpDim (D.ntypes.locPar σ w) = D.R.r := by
  rw [T.locPar_def, lpDim_isoLoc]
  exact (T.eP σ).2.2.2.1

theorem labPar_monic_of (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (σ : D.ntypes.Par) (v : D.nd.PlG k) :
    (D.ntypes.labPar k σ v).Monic ∧ (D.ntypes.labPar k σ v).natDegree = D.R.r := by
  rw [D.ntypes.labPar_def, T.locPar_def]
  exact (T.eP σ).2.2.2.2 k v

section Deg

variable {G : Type} [Group G] {g : ℕ} (f₀ : (ZMod g)[X])

theorem degSer_idem (f : (ZMod g)[X]) : degSer (G := G) f₀ f * degSer f₀ f = degSer f₀ f := by
  unfold degSer; split_ifs <;> simp

theorem degSer_central (f : (ZMod g)[X]) (a : MonoidAlgebra ℂ G) : degSer f₀ f * a = a * degSer f₀ f := by
  unfold degSer; split_ifs <;> simp

theorem degSer_orth (f f' : (ZMod g)[X]) (h : f ≠ f') : degSer (G := G) f₀ f * degSer f₀ f' = 0 := by
  unfold degSer
  split_ifs with h1 h2 <;> simp_all

theorem degSer_zero (P : (ZMod g)[X] → Prop) (h0 : P f₀) (f : (ZMod g)[X]) (hf : ¬ P f) :
    degSer (G := G) f₀ f = 0 := by
  unfold degSer
  rw [if_neg]
  rintro rfl
  exact hf h0

theorem degSer_sum (S : Finset (ZMod g)[X]) (h0 : f₀ ∈ S) : ∑ f ∈ S, degSer (G := G) f₀ f = 1 := by
  classical
  unfold degSer
  rw [Finset.sum_ite_eq' S f₀ (fun _ => (1 : MonoidAlgebra ℂ G)), if_pos h0]

end Deg

end Formalism.L2
