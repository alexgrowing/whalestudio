import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.IdxDet

open GlobalTheory.LatBasisAt

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (w : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt w a ↔ a ∈ locRing w := by
  rw [mem_locRing]
  constructor
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [← h]; field_simp⟩
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [h]; field_simp⟩

theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (a : locRing P) : P.valuation E (a : E) ≤ 1 :=
  GlobalTheory.CharValCompare.intAt_iff.1 ((intAt_iff_mem P _).2 a.2)

theorem val_unit (P : HeightOneSpectrum (𝓞 E)) (u : (locRing P)ˣ) :
    P.valuation E ((u : locRing P) : E) = 1 := by
  have h : P.valuation E ((u : locRing P) : E) * P.valuation E (((u⁻¹ : (locRing P)ˣ) : locRing P) : E) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  refine le_antisymm (val_le_one P _) ?_
  rw [← h]
  exact mul_le_of_le_one_right' (val_le_one P _)

theorem val_irreducible (P : HeightOneSpectrum (𝓞 E)) [IsDiscreteValuationRing (locRing P)]
    {p : locRing P} (hp : Irreducible p) : P.valuation E (p : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ1 : π ∈ locRing P := by
    rw [← intAt_iff_mem, GlobalTheory.CharValCompare.intAt_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hπ0 : (⟨π, hπ1⟩ : locRing P) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hp
  have h1 : π * ((u : locRing P) : E) = (p : E) ^ k := by
    simpa using congrArg Subtype.val hu
  have h2 := congrArg (P.valuation E) h1
  rw [map_mul, val_unit, mul_one, hπ, map_pow] at h2
  have hp0 : P.valuation E (p : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hp.ne_zero (Subtype.ext h)
  have hle := val_le_one P p
  rw [← WithZero.exp_log hp0] at h2 hle ⊢
  generalize WithZero.log (P.valuation E (p : E)) = a at h2 hle ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  congr 1
  have : a ∣ 1 := ⟨-k, by linarith⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h
  · omega
  · exact h

theorem relIndex_mulVec : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (M : Matrix ι ι E) (L₀ L₁ : AddSubgroup (ι → E)), M.det ≠ 0 → (∀ x, x ∈ L₀ ↔ ∀ i, IntAt P (x i)) → (∀ x, x ∈ L₁ ↔ ∃ y ∈ L₀, x = M.mulVec y) → L₁ ≤ L₀ → ((L₁.relIndex L₀ : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ ordE P M.det := by
  intro E _ _ ι _ _ P M L₀ L₁ hdet h0 h1 hle
  haveI := P.isPrime
  haveI := P.isMaximal
  haveI : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot (locRing P)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (locRing P)
  have hent : ∀ i j, M i j ∈ locRing P := by
    intro i j
    have hs : (Pi.single j 1 : ι → E) ∈ L₀ := by
      rw [h0]
      intro k
      rw [intAt_iff_mem, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have := (h0 _).1 (hle ((h1 _).2 ⟨_, hs, rfl⟩)) i
    rw [intAt_iff_mem] at this
    simpa using this
  let N : Matrix ι ι (locRing P) := Matrix.of fun i j => ⟨_, hent i j⟩
  have hN : N.map (algebraMap (locRing P) E) = M := by
    ext i j; rfl
  have hNd : ((N.det : locRing P) : E) = M.det := by
    rw [← hN]
    exact RingHom.map_det (algebraMap (locRing P) E) N
  have hne : N.det ≠ 0 := by
    intro h
    rw [h] at hNd
    exact hdet hNd.symm
  have hinj : Function.Injective (Matrix.toLin' N) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hv
  obtain ⟨m, ⟨v, hv⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (locRing P) ι) hp _ hinj
  rw [LinearMap.det_toLin'] at hv
  have hord : ordE P M.det = m := by
    have e1 : M.det * ((v : locRing P) : E) = (p : E) ^ m := by
      rw [← hNd]; exact_mod_cast congrArg Subtype.val hv
    have e2 := congrArg (P.valuation E) e1
    rw [map_mul, val_unit, mul_one, map_pow, val_irreducible P hp, ← WithZero.exp_nsmul] at e2
    unfold ordE
    rw [e2, WithZero.log_exp]
    simp
  have hq : Nat.card (locRing P ⧸ Ideal.span {p}) = Ideal.absNorm P.asIdeal := by
    rw [← hp.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (locRing P)).toEquiv).symm
  let e : (ι → locRing P) →+ (ι → E) :=
    { toFun := fun x i => (x i : E)
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hei : Function.Injective e := by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  have hW0 : L₀ = AddSubgroup.map e ⊤ := by
    ext x
    rw [h0]
    constructor
    · intro hx
      exact ⟨fun i => ⟨_, (intAt_iff_mem P _).1 (hx i)⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩ i
      exact (intAt_iff_mem P _).2 (y i).2
  have hcomm : ∀ y, M.mulVec (e y) = e (Matrix.toLin' N y) := by
    intro y
    funext i
    rw [← hN]
    exact (RingHom.map_mulVec (algebraMap (locRing P) E) N y i).symm
  have hW1 : L₁ = AddSubgroup.map e (LinearMap.range (Matrix.toLin' N)).toAddSubgroup := by
    ext x
    rw [h1, hW0]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (hcomm y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, trivial, rfl⟩, (hcomm y).symm⟩
  have : L₁.relIndex L₀ = Ideal.absNorm P.asIdeal ^ m := by
    rw [hW1, hW0, AddSubgroup.relIndex_map_map_of_injective _ _ hei, AddSubgroup.relIndex_top_right, ← hq]
    exact hc
  rw [this, hord, zpow_natCast, Nat.cast_pow]

end GlobalTheory.IdxDet
