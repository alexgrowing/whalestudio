import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel

open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeckeStdFacts

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem triv_mul {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GAf L n} (hx : TrivOutside T x)
    (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem triv_inv {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GAf L n} (hx : TrivOutside T x) :
    TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem triv_one {T : Set (HeightOneSpectrum (𝓞 L⁺))} : TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

def locK (n : ℕ) (v : HeightOneSpectrum (𝓞 L⁺)) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ}
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, triv_mul ha.2 hb.2⟩
  one_mem' := ⟨one_mem _, triv_one⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, triv_inv ha.2⟩

theorem mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    rw [GlobalTheory.FinTypCount.inv_val]
    rfl
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem mem_GLint_iff {F : Type} [Field F] {O : Subring F} {x : GL (Fin n) F} :
    x ∈ Formalism.UG.GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem proj_mem (s : SplitPlace L) {z : AL L} (hz : z ∈ ALint L) :
    s.proj z ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  have key : ALint L ≤ ((s.v.adicCompletionIntegers L⁺).toSubring).comap s.proj := by
    rw [ALint, Subring.closure_le]
    rintro y (⟨o, rfl⟩ | ⟨a, ha, rfl⟩)
    · show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring
      have e : s.proj ((o : L) ⊗ₜ[L⁺] (1 : AFplus L)) = s.i (o : L) := by
        simp [SplitPlace.proj]
      rw [e]
      exact s.split_le_one o
    · show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring
      have e : s.proj ((1 : L) ⊗ₜ[L⁺] a) = a s.v := by
        simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      rw [e]
      exact ha s.v
  exact key hz

theorem loc_mem_GLint_iff (s : SplitPlace L) {x : GAf L n} (hx : TrivOutside {s.v} x) :
    s.loc n x ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring ↔ x ∈ Umax L n := by
  rw [mem_GLint_iff, ← map_inv]
  exact ⟨fun h => mem_Umax_of_loc s x hx h.1 h.2,
    fun h => ⟨fun i j => proj_mem s (h i j), fun i j => proj_mem s (inv_mem h i j)⟩⟩

theorem exists_tSet_eq (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : IsUnif L s.v ϖ) :
    ∃ α : GAf L n, TrivOutside {s.v} α ∧ ∀ x, x ∈ tSet L n s ϖ k ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂ := by
  obtain ⟨-, -, hlift⟩ := GlobalTheory.SplitAdelic.main L n s
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    have : Valued.v (0 : s.v.adicCompletion L⁺) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hdet : (Formalism.UG.diagJ n ϖ k).det ≠ 0 := by
    rw [Formalism.UG.diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs; exacts [h0, one_ne_zero]
  obtain ⟨α, ⟨hα, eα⟩, -⟩ := hlift (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)
  have eα' : ((s.loc n α : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) = Formalism.UG.diagJ n ϖ k := by
    rw [eα]; rfl
  refine ⟨α, hα, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hx, a, ha, b, hb, e⟩
    obtain ⟨a', ⟨ha', rfl⟩, -⟩ := hlift a
    obtain ⟨b', ⟨hb', rfl⟩, -⟩ := hlift b
    refine ⟨a', ⟨(loc_mem_GLint_iff s ha').1 ha, ha'⟩, b', ⟨(loc_mem_GLint_iff s hb').1 hb, hb'⟩, ?_⟩
    refine (hlift (s.loc n x)).unique ⟨hx, rfl⟩ ⟨triv_mul (triv_mul ha' hα) hb', Units.ext ?_⟩
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, eα']
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨triv_mul (triv_mul ha.2 hα) hb.2, _, (loc_mem_GLint_iff s ha.2).2 ha.1, _, (loc_mem_GLint_iff s hb.2).2 hb.1, ?_⟩
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, eα']

theorem exists_cong_conj (a : GAf L n) : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → a⁻¹ * κ * a ∈ Umax L n := by
  obtain ⟨m, hm, h⟩ := GlobalTheory.FinTypCount.exists_denom_matrix (a.1 : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨m', hm', h'⟩ := GlobalTheory.FinTypCount.exists_denom_matrix ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun κ hκ i j => ?_⟩
  choose y hy ey using hκ.2
  set A : Matrix (Fin n) (Fin n) (AL L) := (a.1 : Matrix (Fin n) (Fin n) (AL L))
  set B : Matrix (Fin n) (Fin n) (AL L) := ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))
  have hBA : B * A = 1 := Units.inv_mul a.1
  have hκe : (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (m' : AL L) • (m : AL L) • Matrix.of y := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have := ey i j
    push_cast at this
    linear_combination this
  have e : (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((m' : AL L) • B) * Matrix.of y * ((m : AL L) • A) := by
    change B * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) * A = _
    rw [hκe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_comm]
  show (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  rw [e, Matrix.add_apply]
  refine add_mem ?_ ?_
  · by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  · simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact sum_mem fun l _ => mul_mem (sum_mem fun l' _ => mul_mem (h' i l') (hy l' l)) (h l j)

theorem exists_reps {G : Type} [Group G] (U : Subgroup G) (D : Set G) (hD : ((fun x : G => (x : G ⧸ U)) '' D).Finite) :
    ∃ R : Finset G, (∀ γ ∈ R, γ ∈ D) ∧ ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ U := by
  classical
  have hc : ∀ c ∈ hD.toFinset, ∃ x ∈ D, (x : G ⧸ U) = c := fun c hc => by simpa using hc
  choose! r hrD hr using hc
  refine ⟨hD.toFinset.image r, fun γ hγ => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    exact hrD c hc
  · have hm : (x : G ⧸ U) ∈ hD.toFinset := hD.mem_toFinset.2 ⟨x, hx, rfl⟩
    refine ⟨r x, ⟨Finset.mem_image.2 ⟨_, hm, rfl⟩, QuotientGroup.eq.1 (hr _ hm)⟩, ?_⟩
    rintro γ ⟨hγ, e⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    have : c = (x : G ⧸ U) := (hr c hc).symm.trans (QuotientGroup.eq.2 e)
    rw [this]

theorem finite_dc (v : HeightOneSpectrum (𝓞 L⁺)) (a : GAf L n) :
    ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' {x | ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂}).Finite := by
  obtain ⟨N, hN, h⟩ := exists_cong_conj a
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  refine ((J.finite_toSet).image fun j : GAf L n => ((j * a : GAf L n) : GAf L n ⧸ Umax L n)).subset ?_
  rintro _ ⟨_, ⟨k₁, h₁, k₂, h₂, rfl⟩, rfl⟩
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJ k₁ h₁.1
  refine ⟨j, hj, QuotientGroup.eq.2 ?_⟩
  have := mul_mem (h κ hκ) h₂.1
  convert this using 1
  group

theorem exists_repsU (v : HeightOneSpectrum (𝓞 L⁺)) (a : GAf L n) : ∃ R : Finset (GAf L n),
    (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * a * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n :=
  exists_reps (Umax L n) _ (finite_dc v a)

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_eq_sum {J : Subgroup (GAf L n)} {v : HeightOneSpectrum (𝓞 L⁺)} {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    {f : GAf L n → W} (hf : ∀ κ ∈ J, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    have hu : γ⁻¹ * hc.choose ∈ J := QuotientGroup.eq.1 hc.choose_spec.2.symm
    have := congrFun (hf _ hu (triv_mul (triv_inv (hD γ (h1 γ hγ))) (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 e⟩)
    · exact absurd (dif_neg h) hc

theorem exists_int_of_normalizes {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)
    (O : Subring F) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (g : GL (Fin n) F)
    (hg : ∀ u ∈ Formalism.UG.GLint (Fin n) O, g * u * g⁻¹ ∈ Formalism.UG.GLint (Fin n) O) :
    ∃ h ∈ Formalism.UG.GLint (Fin n) O, ∀ x : GL (Fin n) F, g * x * g⁻¹ = h * x * h⁻¹ := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_mem _, fun x => Units.ext (Subsingleton.elim _ _)⟩
  have one_mem' : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) F) a b ∈ O := fun a b => by
    by_cases h : a = b <;> simp [Matrix.one_apply, h, O.one_mem, O.zero_mem]
  have off : ∀ i j : Fin n, i ≠ j → ∀ a b, (g.1 * Matrix.single i j (1 : F) * (g⁻¹).1) a b ∈ O := by
    intro i j hij a b
    let u : GL (Fin n) F := ⟨1 + Matrix.single i j 1, 1 - Matrix.single i j 1,
      by simp [add_mul, mul_sub, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm],
      by simp [sub_mul, mul_add, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]⟩
    have sm : ∀ a b, (Matrix.single i j (1 : F)) a b ∈ O := fun a b => by
      rw [Matrix.single_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    have hu : u ∈ Formalism.UG.GLint (Fin n) O :=
      mem_GLint_iff.2 ⟨fun a b => add_mem (one_mem' a b) (sm a b), fun a b => sub_mem (one_mem' a b) (sm a b)⟩
    have h1 := (mem_GLint_iff.1 (hg u hu)).1 a b
    have e : (g * u * g⁻¹).1 = 1 + g.1 * Matrix.single i j (1 : F) * (g⁻¹).1 := by
      show g.1 * (1 + Matrix.single i j 1) * (g⁻¹).1 = _
      rw [mul_add, add_mul, mul_one, g.mul_inv]
    rw [e, Matrix.add_apply] at h1
    simpa using sub_mem h1 (one_mem' a b)
  have all : ∀ i j : Fin n, ∀ a b, (g.1 * Matrix.single i j (1 : F) * (g⁻¹).1) a b ∈ O := by
    intro i j a b
    by_cases hij : i = j
    · subst hij
      by_cases hk : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := hk
        have e : g.1 * Matrix.single i i (1 : F) * (g⁻¹).1 =
            (g.1 * Matrix.single i k (1 : F) * (g⁻¹).1) * (g.1 * Matrix.single k i (1 : F) * (g⁻¹).1) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (g⁻¹).1, g.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.single i k (1 : F)),
            Matrix.single_mul_single_same, one_mul]
        rw [e, Matrix.mul_apply]
        exact sum_mem fun c _ => mul_mem (off i k hk.symm a c) (off k i hk c b)
      · push Not at hk
        have e : Matrix.single i i (1 : F) = 1 := by
          ext c d
          rw [hk c, hk d]; simp
        rw [e, mul_one, g.mul_inv]
        exact one_mem' a b
    · exact off i j hij a b
  have prod : ∀ a i j b, g.1 a i * (g⁻¹).1 j b ∈ O := by
    intro a i j b
    have := all i j a b
    simpa [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq] using this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) (fun p => w (g.1 p.1 p.2))
    Finset.univ_nonempty
  set c := g.1 p.1 p.2 with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : g.1 = 0 := by
      ext a b
      have := hp (a, b) (Finset.mem_univ _)
      rw [h0, map_zero] at this
      simpa using this
    exact g.ne_zero hz
  let h : GL (Fin n) F := ⟨c⁻¹ • g.1, c • (g⁻¹).1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, g.mul_inv],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul, g.inv_mul]⟩
  refine ⟨h, mem_GLint_iff.2 ⟨fun a b => ?_, fun a b => prod p.1 p.2 a b⟩, fun x => Units.ext ?_⟩
  · show c⁻¹ * g.1 a b ∈ O
    rw [hO, map_mul, map_inv₀]
    have h0 : 0 < w c := zero_lt_iff.2 ((map_ne_zero w).2 hc0)
    exact (inv_mul_le_one₀ h0).2 (hp (a, b) (Finset.mem_univ _))
  · show g.1 * x.1 * (g⁻¹).1 = (c⁻¹ • g.1) * x.1 * (c • (g⁻¹).1)
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem triv_conj {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GAf L n} (hx : TrivOutside T x) (κ : GAf L n) :
    TrivOutside T (κ * x * κ⁻¹) := by
  intro w hw
  have h1 : (κ.1 : Matrix (Fin n) (Fin n) (AL L)) * (((κ⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 :=
    Units.mul_inv κ.1
  have : ((κ * x * κ⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) = (κ.1 : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (((κ⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, Matrix.map_mul, hx w hw, mul_one, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem conj_mem_tSet (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) {J : Subgroup (GAf L n)}
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {κ : GAf L n} (hκ : κ ∈ J) {x : GAf L n}
    (hx : x ∈ tSet L n s ϖ k) : κ * x * κ⁻¹ ∈ tSet L n s ϖ k := by
  obtain ⟨-, -, hlift⟩ := GlobalTheory.SplitAdelic.main L n s
  obtain ⟨h, hh, e⟩ := exists_int_of_normalizes (n := n) (Valued.v : Valuation (s.v.adicCompletion L⁺) _)
    (s.v.adicCompletionIntegers L⁺).toSubring (fun _ => Iff.rfl) (s.loc n κ) (by
      intro u hu
      obtain ⟨u', ⟨hu', rfl⟩, -⟩ := hlift u
      have h1 : u' ∈ J := (hJ _ hu').2 ((loc_mem_GLint_iff s hu').1 hu)
      have h2 := triv_conj hu' κ
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (loc_mem_GLint_iff s h2).2 ((hJ _ h2).1 (mul_mem (mul_mem hκ h1) (inv_mem hκ))))
  obtain ⟨hx, a, ha, b, hb, ex⟩ := hx
  refine ⟨triv_conj hx κ, h * a, mul_mem hh ha, b * h⁻¹, mul_mem hb (inv_mem hh), ?_⟩
  rw [map_mul, map_mul, map_inv, e, Units.val_mul, Units.val_mul, ex]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem tSet_triv {s : SplitPlace L} {ϖ : s.v.adicCompletion L⁺} {k : ℕ} {x : GAf L n} (hx : x ∈ tSet L n s ϖ k) :
    TrivOutside {s.v} x := hx.1

theorem hyp_at {J : Subgroup (GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hB : NG.HypOutside J χ B)
    {v : HeightOneSpectrum (𝓞 L⁺)} (hv : v ∉ B) (κ : GAf L n) (hκ : TrivOutside {v} κ) :
    (κ ∈ J ↔ κ ∈ Umax L n) ∧ ∀ h : κ ∈ J, χ ⟨κ, h⟩ = 1 := by
  refine hB κ fun w hw => hκ w ?_
  rintro rfl
  exact hv (by simpa using hw)

theorem fixed_of_type {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hB : NG.HypOutside J χ B) {v : HeightOneSpectrum (𝓞 L⁺)} (hv : v ∉ B)
    {f : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (κ : GAf L n) (hκ : κ ∈ J) (ht : TrivOutside {v} κ) :
    NG.rt L n κ f = f := by
  have := hf.2 ⟨κ, hκ⟩
  rw [(hyp_at hB hv κ ht).2 hκ] at this
  simpa using this

theorem exists_data (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : IsUnif L s.v ϖ) :
    ∃ (α : GAf L n) (R : Finset (GAf L n)), TrivOutside {s.v} α ∧
      (∀ x, x ∈ tSet L n s ϖ k ↔
        ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) ∧
      (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) ∧ ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := by
  obtain ⟨α, hα, hset⟩ := exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, h1, h2⟩ := exists_repsU (n := n) s.v α
  refine ⟨α, R, hα, fun x => (hset x).trans ⟨?_, ?_⟩, fun γ hγ => (hset γ).2 (h1 γ hγ), fun x hx => h2 x ((hset x).1 hx)⟩
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, e⟩
  · rintro ⟨a, ha, b, hb, ha', hb', e⟩
    exact ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, e⟩

theorem reps_level {v : HeightOneSpectrum (𝓞 L⁺)} {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {J : Subgroup (GAf L n)} (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n))
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) :
    ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J := by
  intro x hx
  refine (existsUnique_congr fun γ => and_congr_right fun hγ => ?_).1 (h2 x hx)
  exact (hJ _ (triv_mul (triv_inv (hD γ (h1 γ hγ))) (hD x hx))).symm

theorem rt_rt (a b : GAf L n) (f : GAf L n → W) : NG.rt L n a (NG.rt L n b f) = NG.rt L n (a * b) f :=
  funext fun x => congrArg f (mul_assoc x a b)

theorem heckeD_type {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hB : NG.HypOutside J χ B) {s : SplitPlace L} (hv : s.v ∉ B)
    {ϖ : s.v.adicCompletion L⁺} {k : ℕ} {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k)
    (h2 : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) {f : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) :
    NG.heckeD J (tSet L n s ϖ k) f = ∑ γ ∈ R, NG.rt L n γ f :=
  heckeD_eq_sum (fun _ => tSet_triv) h1
    (reps_level (fun _ => tSet_triv) (fun κ hκ => (hyp_at hB hv κ hκ).1) h1 h2) (fixed_of_type hB hv hf)

theorem heckeD_mem {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    (hB : NG.HypOutside J χ B) {s : SplitPlace L} (hv : s.v ∉ B)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) (k : ℕ) {f : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) :
    NG.heckeD J (tSet L n s ϖ k) f ∈ NG.TypeSp ρ J χ := by
  classical
  obtain ⟨α, R, -, -, h1, h2⟩ := exists_data (n := n) s ϖ k hϖ
  have hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n) := fun κ hκ => (hyp_at hB hv κ hκ).1
  have h2' := reps_level (fun _ => tSet_triv) hJ h1 h2
  have key : ∀ κ : J, NG.rt L n (κ : GAf L n) (NG.heckeD J (tSet L n s ϖ k) f) =
      ((χ κ : ℂˣ) : ℂ) • NG.heckeD J (tSet L n s ϖ k) f := by
    rintro ⟨κ, hκ⟩
    have hinj : Function.Injective fun γ : GAf L n => κ * γ * κ⁻¹ := fun a b h => by simpa using h
    have e := heckeD_eq_sum (J := J) (D := tSet L n s ϖ k) (fun _ => tSet_triv) (R := R.image fun γ => κ * γ * κ⁻¹)
      (by
        intro γ hγ
        obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
        exact conj_mem_tSet s ϖ k hJ hκ (h1 δ hδ))
      (by
        intro x hx
        have hx' := conj_mem_tSet s ϖ k hJ (inv_mem hκ) hx
        obtain ⟨γ, ⟨hγ, hm⟩, hu⟩ := h2' _ hx'
        refine ⟨κ * γ * κ⁻¹, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, ?_⟩, ?_⟩
        · convert mul_mem (mul_mem hκ hm) (inv_mem hκ) using 1
          group
        · rintro _ ⟨hδ, hm'⟩
          obtain ⟨δ, hδ', rfl⟩ := Finset.mem_image.1 hδ
          rw [hu δ ⟨hδ', ?_⟩]
          convert mul_mem (mul_mem (inv_mem hκ) hm') hκ using 1
          group) (fixed_of_type hB hv hf)
    rw [Finset.sum_image (hinj.injOn)] at e
    conv_rhs => rw [e]
    rw [heckeD_type hB hv h1 h2 hf, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← map_smul, ← hf.2 ⟨κ, hκ⟩, rt_rt, rt_rt]
    simp
  refine ⟨⟨fun γ g => ?_, ?_⟩, key⟩
  · rw [heckeD_type hB hv h1 h2 hf, Finset.sum_apply, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    show f (γ * g * δ) = ρ γ (f (g * δ))
    rw [mul_assoc, hf.1.1]
  · obtain ⟨N, hN0, hN⟩ := hN
    refine ⟨N, hN0, fun κ hκ g => ?_⟩
    obtain ⟨h, e⟩ := hN κ hκ
    have := congrFun (key ⟨κ, h⟩) g
    rw [e, Units.val_one, one_smul] at this
    exact this

theorem heckeD_comm {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    (hB : NG.HypOutside J χ B) {s s' : SplitPlace L} (hv : s.v ∉ B) (hv' : s'.v ∉ B)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) (k : ℕ)
    {ϖ' : s'.v.adicCompletion L⁺} (hϖ' : IsUnif L s'.v ϖ') (k' : ℕ) {f : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) :
    NG.heckeD J (tSet L n s ϖ k) (NG.heckeD J (tSet L n s' ϖ' k') f) =
      NG.heckeD J (tSet L n s' ϖ' k') (NG.heckeD J (tSet L n s ϖ k) f) := by
  obtain ⟨α, R, hα, hs, h1, h2⟩ := exists_data (n := n) s ϖ k hϖ
  obtain ⟨β, S, hβ, hs', h1', h2'⟩ := exists_data (n := n) s' ϖ' k' hϖ'
  rw [heckeD_type hB hv h1 h2 (heckeD_mem hN hB hv' hϖ' k' hf), heckeD_type hB hv' h1' h2' (heckeD_mem hN hB hv hϖ k hf),
    heckeD_type hB hv h1 h2 hf, heckeD_type hB hv' h1' h2' hf]
  by_cases hvv : s'.v = s.v
  · have hS : ∀ x, x ∈ tSet L n s' ϖ' k' ↔
        ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂ := hvv ▸ hs'
    exact GlobalTheory.SplitHeckeComm.doubleCoset_comm L n W s α β R S hα (hvv ▸ hβ) (fun x hx => h2 x ((hs x).2 hx))
      (fun γ hγ => (hs γ).1 (h1 γ hγ)) (fun x hx => h2' x ((hS x).2 hx)) (fun γ hγ => (hS γ).1 (h1' γ hγ)) f
      fun κ hκ ht => fixed_of_type hB hv hf κ ((hyp_at hB hv κ ht).1.2 hκ) ht
  · obtain ⟨-, hc, -⟩ := GlobalTheory.SplitAdelic.main L n s
    simp only [map_sum, rt_rt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ hδ => Finset.sum_congr rfl fun γ hγ => ?_
    rw [(hc γ δ (h1 γ hγ).1 fun w hw => (h1' δ hδ).1 w ?_).eq]
    rintro rfl
    exact hw hvv

theorem heckeD_lin {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hB : NG.HypOutside J χ B) {s : SplitPlace L} (hv : s.v ∉ B)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) (k : ℕ) {f f' : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ)
    (hf' : f' ∈ NG.TypeSp ρ J χ) (c : ℂ) :
    NG.heckeD J (tSet L n s ϖ k) (c • f + f') = c • NG.heckeD J (tSet L n s ϖ k) f + NG.heckeD J (tSet L n s ϖ k) f' := by
  obtain ⟨α, R, -, -, h1, h2⟩ := exists_data (n := n) s ϖ k hϖ
  rw [heckeD_type hB hv h1 h2 hf, heckeD_type hB hv h1 h2 hf',
    heckeD_type hB hv h1 h2 (add_mem (Submodule.smul_mem _ c hf) hf')]
  simp only [map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]

theorem heckeD_smul {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hB : NG.HypOutside J χ B) {s : SplitPlace L} (hv : s.v ∉ B)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) (k : ℕ) {f : GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (c : ℂ) :
    NG.heckeD J (tSet L n s ϖ k) (c • f) = c • NG.heckeD J (tSet L n s ϖ k) f := by
  obtain ⟨α, R, -, -, h1, h2⟩ := exists_data (n := n) s ϖ k hϖ
  rw [heckeD_type hB hv h1 h2 hf, heckeD_type hB hv h1 h2 (Submodule.smul_mem _ c hf)]
  simp only [map_smul, Finset.smul_sum]

theorem exists_fg_eval {σ : Type} (A : Subring ℂ) (D : ℂ) (hD : D ≠ 0) (P : MvPolynomial σ ℂ) :
    ∃ M : Submodule A ℂ, M.FG ∧ ∀ y : σ → ℂ, (∀ p, D * y p ∈ A) → MvPolynomial.eval y P ∈ M := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨Submodule.span A {c}, Submodule.fg_span_singleton c, fun y _ => by
      simpa using Submodule.mem_span_singleton_self c⟩
  | add P Q hP hQ =>
    obtain ⟨M, hM, h⟩ := hP
    obtain ⟨M', hM', h'⟩ := hQ
    exact ⟨M ⊔ M', hM.sup hM', fun y hy => by
      rw [map_add]; exact Submodule.add_mem_sup (h y hy) (h' y hy)⟩
  | mul_X P p hP =>
    obtain ⟨M, hM, h⟩ := hP
    refine ⟨M.map (LinearMap.mulLeft A D⁻¹), hM.map _, fun y hy => ⟨_, M.smul_mem ⟨_, hy p⟩ (h y hy), ?_⟩⟩
    show D⁻¹ * (D * y p * MvPolynomial.eval y P) = _
    rw [map_mul, MvPolynomial.eval_X]
    field_simp

theorem q_mem (s : SplitPlace L) : ((s.q : ℕ) : 𝓞 L⁺) ∈ s.v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem q_ne_zero (s : SplitPlace L) : s.q ≠ 0 := by
  haveI : Finite (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  exact Nat.card_pos.ne'

theorem not_dvd_q (s : SplitPlace L) {l : ℕ} (hl : l.Prime) (h : ¬ s.Above l) : ¬ l ∣ s.q := by
  intro hd
  apply h
  haveI : Finite (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  haveI := Fact.mk hl
  haveI := s.v.isPrime
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 L⁺ ⧸ s.v.asIdeal) l hd
  have h1 : l • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hl.one_lt.ne hx
  rw [nsmul_eq_mul] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right h0
  show _ ∈ _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem exists_pow_val (s : SplitPlace L) (y : s.v.adicCompletion L⁺) :
    ∃ e : ℕ, ∀ e' ≥ e, Valued.v (((s.q : ℕ) : s.v.adicCompletion L⁺) ^ e' * y) ≤ 1 := by
  have hq : Valued.v ((s.q : ℕ) : s.v.adicCompletion L⁺) < 1 := by
    have := (s.split_mem_ideal _).1 ((s.split_alg_mem _).2 (q_mem s))
    simpa using this
  rcases eq_or_ne (Valued.v y) 0 with h0 | h0
  · exact ⟨0, fun e' _ => by rw [map_mul, h0, mul_zero]; exact zero_le_one⟩
  · obtain ⟨e, he⟩ := exists_pow_lt₀ hq (Units.mk0 _ h0)⁻¹
    refine ⟨e, fun e' he' => ?_⟩
    rw [map_mul, map_pow]
    have h1 : Valued.v ((s.q : ℕ) : s.v.adicCompletion L⁺) ^ e' ≤ (Valued.v y)⁻¹ :=
      (pow_le_pow_right_of_le_one' hq.le he').trans (by simpa using he.le)
    calc _ ≤ (Valued.v y)⁻¹ * Valued.v y := by gcongr
      _ = 1 := inv_mul_cancel₀ h0

theorem exists_pow_denom (s : SplitPlace L) {x : GAf L n} (hx : TrivOutside {s.v} x) :
    ∃ e : ℕ, ∀ i j, ((s.q ^ e : ℕ) : AL L) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  obtain ⟨ε, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have one_mem' : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) (AL L)) a b ∈ ALint L := fun a b => by
    by_cases h : a = b <;> simp [Matrix.one_apply, h, Subring.one_mem, Subring.zero_mem]
  let z : Fin n → Fin n → AL L := fun i j =>
    (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j
  choose e₁ h₁ using fun p : Fin n × Fin n => exists_pow_val s (s.proj (z p.1 p.2))
  choose e₂ h₂ using fun p : Fin n × Fin n => exists_pow_val s (s.proj (conjAL L (z p.1 p.2)))
  refine ⟨∑ p, (e₁ p + e₂ p), fun i j => ?_⟩
  have hle : e₁ (i, j) + e₂ (i, j) ≤ ∑ p, (e₁ p + e₂ p) :=
    Finset.single_le_sum (f := fun p => e₁ p + e₂ p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
  set e := ∑ p, (e₁ p + e₂ p)
  have hz : ((s.q ^ e : ℕ) : AL L) * z i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s ε he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [map_mul, map_natCast, Nat.cast_pow]
      exact h₁ (i, j) e (by omega)
    · rw [map_mul, map_natCast, map_mul, map_natCast, Nat.cast_pow]
      exact h₂ (i, j) e (by omega)
  have := add_mem hz (mul_mem (natCast_mem (ALint L) (s.q ^ e)) (one_mem' i j))
  simpa only [z, mul_sub, sub_add_cancel] using this

theorem exists_ring (q : ℕ) (hq : q ≠ 0) (S : Set ℂ) (hS : S.Finite) (hint : ∀ x ∈ S, IsIntegral ℤ x) :
    ∃ A : Subring ℂ, IsNoetherianRing A ∧ S ⊆ A ∧ (q : ℂ)⁻¹ ∈ A ∧
      ∀ μ : ℂ, IsIntegral A μ → ∃ m : ℕ, IsIntegral ℤ ((q : ℂ) ^ m * μ) := by
  have hM : Submonoid.powers (q : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hq)
  let R : Subalgebra ℤ ℚ := Localization.subalgebra.ofField ℚ (Submonoid.powers (q : ℤ)) hM
  haveI : IsLocalization (Submonoid.powers (q : ℤ)) R := Localization.subalgebra.isLocalization_ofField ℚ _ hM
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing (Submonoid.powers (q : ℤ)) R inferInstance
  let A : Subalgebra R ℂ := Algebra.adjoin R S
  have hint' : ∀ x ∈ S, IsIntegral R x := fun x hx => (hint x hx).tower_top
  haveI : Algebra.FiniteType R A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.adjoin hint'
  refine ⟨A.toSubring, ‹IsNoetherianRing A›, Algebra.subset_adjoin, ?_, fun μ hμ => ?_⟩
  · have hr : (q : ℚ)⁻¹ ∈ R := ⟨1, q, Submonoid.mem_powers _, by simp⟩
    have := A.algebraMap_mem ⟨_, hr⟩
    have e : algebraMap R ℂ ⟨_, hr⟩ = (q : ℂ)⁻¹ := by
      show (((q : ℚ)⁻¹ : ℚ) : ℂ) = _
      simp
    rw [e] at this
    exact this
  · have h1 : IsIntegral A μ := hμ
    have h2 : IsIntegral R μ := isIntegral_trans μ h1
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers (q : ℤ)) μ h2
    refine ⟨m, ?_⟩
    simpa [Submonoid.smul_def] using hm

theorem eigen_integral {ρ : Representation ℂ (GQ L n) W} (hρ : IsAlgWeight L n ρ) (s : SplitPlace L)
    (R : Finset (GAf L n)) (hR : ∀ γ ∈ R, TrivOutside {s.v} γ) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) (hf0 : f ≠ 0)
    {μ : ℂ} (hμ : ∑ γ ∈ R, NG.rt L n γ f = μ • f) : ∃ m : ℕ, IsIntegral ℤ ((s.q : ℂ) ^ m * μ) := by
  classical
  obtain ⟨-, ι, _, _, b, P, hP⟩ := hρ
  obtain ⟨hγ, N, hN, hfix⟩ := hf
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hf0
  obtain ⟨i₀, hi₀⟩ : ∃ i, b.repr (f g₀) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hg₀ (b.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨C, hC⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  let β := RingOfIntegers.basis L
  obtain ⟨A, hA, hSA, hqA, hint⟩ := exists_ring s.q (q_ne_zero s)
    (Set.range fun p : (L →+* ℂ) × Module.Free.ChooseBasisIndex ℤ (𝓞 L) => p.1 (β p.2 : L)) (Set.finite_range _) (by
      rintro _ ⟨p, rfl⟩
      exact (RingOfIntegers.isIntegral_coe (β p.2)).map p.1.toIntAlgHom)
  have hOA : ∀ (τ : L →+* ℂ) (o : 𝓞 L), τ (o : L) ∈ A := by
    intro τ o
    rw [← β.sum_repr o, RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_zsmul, map_zsmul]
    exact zsmul_mem (hSA ⟨(τ, i), rfl⟩) _
  obtain ⟨D₀, hD₀, h₀⟩ := GlobalTheory.FinTypCount.exists_denom_matrix (g₀.1 : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨D₁, hD₁, h₁⟩ := GlobalTheory.StabFin.exists_common_denom (L := L) (ι := T × Fin n × Fin n)
    fun p => (((p.1 : GAf L n)⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) p.2.1 p.2.2
  have hD : ((D₀ * D₁ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD₀ hD₁).ne'
  choose M hM hMe using fun j => exists_fg_eval A _ hD (P i₀ j)
  let Nn : Submodule A ℂ := ⨆ p : T × C × ι,
    (M p.2.2).map (LinearMap.mulRight A (b.repr (f (p.1 * p.2.1)) p.2.2))
  have hNn : Nn.FG := Submodule.fg_iSup _ fun p => (hM _).map _
  have key : ∀ x, TrivOutside {s.v} x → b.repr (f (g₀ * x)) i₀ ∈ Nn := by
    intro x hx
    obtain ⟨γ, t, u, ht, hu, e⟩ := hT (g₀ * x)
    obtain ⟨c, hc, κ, hκ, rfl⟩ := hC u hu
    obtain ⟨e₀, he₀⟩ := exists_pow_denom s hx
    obtain ⟨γ₀, -, hγ₀⟩ := GlobalTheory.StabFin.exists_rat γ
    have hmat := hP γ γ₀ (by ext i j; exact hγ₀ i j)
    have e1 : f (g₀ * x) = ρ γ (f (t * c)) := by
      rw [e, ← hγ, ← hfix κ hκ (γ * (t * c))]
      simp only [mul_assoc]
    have eγ : (γ : GAf L n) = g₀ * x * (c * κ)⁻¹ * t⁻¹ := by rw [e]; group
    have hden : ∀ p : (L →+* ℂ) × Fin n × Fin n,
        ((D₀ * D₁ : ℕ) : ℂ) * p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) ∈ A := by
      rintro ⟨τ, i, j⟩
      have hmem : ((D₀ * s.q ^ e₀ * D₁ : ℕ) : AL L) *
          (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
        rw [eγ, GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe]
        simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
        refine sum_mem fun a _ => sum_mem fun a' _ => sum_mem fun a'' _ => ?_
        have := mul_mem (mul_mem (mul_mem (h₀ i a'') (he₀ a'' a')) (inv_mem hu a' a)) (h₁ (⟨t, ht⟩, a, j))
        convert this using 1
        push_cast
        ring
      have hz : IsIntegral ℤ (((D₀ * s.q ^ e₀ * D₁ : ℕ) : L) * (γ₀ : Matrix (Fin n) (Fin n) L) i j) := by
        apply GlobalTheory.StabFin.isIntegral_of_mem
        rw [hγ₀] at hmem
        convert hmem using 1
        rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul']
      have h2 := mul_mem (pow_mem hqA e₀) (hOA τ ⟨_, hz⟩)
      have hq : (s.q : ℂ) ≠ 0 := by exact_mod_cast q_ne_zero s
      have e2 : ((D₀ * D₁ : ℕ) : ℂ) * τ ((γ₀ : Matrix (Fin n) (Fin n) L) i j) =
          (s.q : ℂ)⁻¹ ^ e₀ * τ (((D₀ * s.q ^ e₀ * D₁ : ℕ) : L) * (γ₀ : Matrix (Fin n) (Fin n) L) i j) := by
        rw [map_mul, map_natCast, inv_pow]
        push_cast
        field_simp
      exact e2 ▸ h2
    rw [e1, ← LinearMap.toMatrix_mulVec_repr b b, hmat]
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => ?_
    exact Submodule.mem_iSup_of_mem (⟨t, ht⟩, ⟨c, hc⟩, j) ⟨_, hMe j _ hden, rfl⟩
  let N' : Submodule A ℂ := Submodule.span A {z | ∃ x, TrivOutside {s.v} x ∧ z = b.repr (f (g₀ * x)) i₀}
  have hle : N' ≤ Nn := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact key x hx)
  have hfg : N'.FG := hNn.of_le hle
  have hne : N' ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨_, Submodule.subset_span ⟨1, triv_one, by rw [mul_one]⟩, hi₀⟩
  refine hint μ (isIntegral_of_smul_mem_submodule N' hne hfg μ fun z hz => ?_)
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have := congrFun hμ (g₀ * x)
    rw [Finset.sum_apply, Pi.smul_apply] at this
    rw [← Finsupp.smul_apply, ← map_smul, ← this, map_sum, Finsupp.finsetSum_apply]
    exact sum_mem fun γ hγ => Submodule.subset_span ⟨x * γ, triv_mul hx (hR γ hγ), by rw [← mul_assoc]; rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem heckeStdPlain : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hN hB s ϖ k hv hϖ _ _
  refine ⟨fun f hf => Submodule.smul_mem _ _ (heckeD_mem hN hB hv hϖ k hf), fun f hf f' hf' c => ?_,
    fun s' ϖ' k' hv' hϖ' _ _ f hf => ?_, fun f hf hf0 μ hμ l hl hs => ?_⟩
  · unfold NG.tN
    rw [heckeD_lin hB hv hϖ k hf hf', smul_add, smul_comm]
  · unfold NG.tN
    rw [heckeD_smul hB hv hϖ k (heckeD_mem hN hB hv' hϖ' k' hf), heckeD_smul hB hv' hϖ' k' (heckeD_mem hN hB hv hϖ k hf),
      heckeD_comm hN hB hv hv' hϖ k hϖ' k' hf, smul_comm]
  · obtain ⟨α, R, -, -, h1, h2⟩ := exists_data (n := n) s ϖ k hϖ
    have hq : (s.q : ℂ) ^ (k * (n - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast q_ne_zero s)
    unfold NG.tN at hμ
    rw [heckeD_type hB hv h1 h2 hf, inv_smul_eq_iff₀ hq, smul_smul] at hμ
    obtain ⟨m, hm⟩ := eigen_integral a.alg s R (fun γ hγ => (h1 γ hγ).1) hf.1 hf0 hμ
    refine ⟨s.q ^ (m + k * (n - 1)), fun h => not_dvd_q s hl hs (hl.dvd_of_dvd_pow h), ?_⟩
    rw [Nat.cast_pow, pow_add, mul_assoc]
    exact hm

end GlobalTheory.HeckeStdFacts
