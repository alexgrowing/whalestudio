import Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsMemMapEqSmul
import Formalism.SharpRestriction.LevelLetterCocycles.SumSubEqSumIocOfSub
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

section LemG2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def WachGammaDerivation [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (dop : W.DD T₂ →ₗ[O] W.DD T₂), (∀ z, W.π₀ • dop z = W.γ T₂ z - z) →
    ∀ (cc : ℤ → O),
      (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
    ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
      ∃ w, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i w ∧
        aeval dop (∏ j ∈ Finset.Icc ((b i : ℤ) - ⌈aR PD.p (hpar n b S + η)⌉₊ + 1) (b i : ℤ),
          (X - C (cc j))) x = Formalism.MainNotions.LiftingTheory.qp W ^ ⌈aR PD.p (hpar n b S + η)⌉₊ • w

section SlopeTestRemainingChoices

variable (W : LocWach PD LL O v n)

theorem map_letA_smul_comm {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (a : LetA O n)
    (x : W.DD T₁) : W.map F (a • x) = a • W.map F x := by
  first
  | exact map_smul (W.map F) a x
  | exact LinearMap.map_smul_of_tower (W.map F) a x
  | (rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul])

theorem map_gamma_comm {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (x : W.DD T₁) :
    W.map F (W.γ T₁ x) = W.γ T₂ (W.map F x) := by
  exact W.map_γ F W.gam x

theorem smul_eq_algebraMap_letA_smul (T : LocLat G Qp LL O) (c : O) (y : W.DD T) :
    c • y = (algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) c)) • y := by
  first
  | (rw [algebraMap_smul, algebraMap_smul])
  | simp [algebraMap_smul]

theorem gammaD_smul_letA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul] <;> rfl

theorem letGamma_idempotent (g₀ : PowerSeries O →ₐ[O] PowerSeries O) (i : ZMod n) :
    letγ g₀ (letE i : LetA O n) = letE i := by
  funext j
  have e : (letγ g₀ (letE i : LetA O n)) j = g₀ ((letE i : LetA O n) j) := rfl
  rw [e]
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem idempotent_mul_self' (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  first
  | (unfold letE; rw [← Pi.single_mul, mul_one])
  | (funext j; by_cases h : j = i <;> simp [letE, h])

theorem gammaD_idempotent_smul' (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n) (x : W.DD T) :
    W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [gammaD_smul_letA W T g (letE i) x]
  exact congrArg (· • W.γD T g x) (letGamma_idempotent (W.γ₀ g) i)

theorem gammaA_q_of_mem_delta (hπΔ : W.π₀ ∈ W.AΔ) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add, (hπΔ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) δ hδ, map_natCast]

theorem uniformizer_unit_and_delta_card (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) {T : LocLat G Qp LL O}
    (hT : IsCrys PD T.ρ) :
    IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧ W.π₀ ∈ W.AΔ ∧
      (∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = W.π₀ • x') ∧ W.DelF.card = PD.p - 1 := by
  obtain ⟨hb, hs, hp⟩ := hA
  have hf : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hb).finrank_eq, Module.finrank_self]
  obtain ⟨hcard, -, h3⟩ := h9 T hT hs hp
  obtain ⟨hr, hm⟩ := h3 hf
  obtain ⟨hΔ, -, ⟨w, hw⟩, -⟩ := hr
  obtain ⟨-, hm2⟩ := hm
  refine ⟨?_, hΔ, hm2, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · rw [hcard, hf, Nat.div_one]

theorem isUnit_q_of_uniformizer_unit (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  haveI := W.EE_complete
  have hj : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨u, hu⟩ := hπ
  have h1 := (Ideal.mem_jacobson_bot.mp hj) (↑u⁻¹)
  unfold Formalism.MainNotions.LiftingTheory.qp
  rw [map_add, map_natCast, ← hu]
  have e : (u : W.EE) + ((PD.p : ℕ) : W.EE) = u * (((PD.p : ℕ) : W.EE) * ↑u⁻¹ + 1) := by
    rw [mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one, add_comm]
  rw [e]
  exact u.isUnit.mul h1

theorem exists_derivation_gamma_sub (T : LocLat G Qp LL O) (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    ∃ dop : W.DD T →ₗ[O] W.DD T, ∀ z, W.π₀ • dop z = W.γ T z - z := by
  obtain ⟨u, hu⟩ := hπ
  refine ⟨{ toFun := fun z => ((u⁻¹ : W.EEˣ) : W.EE) • (W.γ T z - z),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro a b
    simp only [map_add, smul_sub, smul_add]
    abel
  · intro c z
    simp only [RingHom.id_apply]
    rw [map_smul, ← smul_sub, smul_eq_algebraMap_letA_smul W T c (W.γ T z - z), smul_eq_algebraMap_letA_smul W T c,
      smul_smul, smul_smul, mul_comm]
  · intro z
    show W.π₀ • (((u⁻¹ : W.EEˣ) : W.EE) • (W.γ T z - z)) = _
    rw [← algebraMap_smul W.EE W.π₀, smul_smul, ← hu, Units.mul_inv, one_smul]

theorem map_comm_derivation {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ z, W.π₀ • dop₁ z = W.γ T₁ z - z)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ z, W.π₀ • dop₂ z = W.γ T₂ z - z) (y : W.DD T₁) :
    W.map F (dop₁ y) = dop₂ (W.map F y) := by
  obtain ⟨u, hu⟩ := hπ
  have hinj : ∀ a b : W.DD T₂, W.π₀ • a = W.π₀ • b → a = b := by
    intro a b h
    rw [← algebraMap_smul W.EE W.π₀ a, ← algebraMap_smul W.EE W.π₀ b, ← hu] at h
    have h' := congrArg (fun t => ((u⁻¹ : W.EEˣ) : W.EE) • t) h
    simpa [smul_smul] using h'
  apply hinj
  rw [← map_letA_smul_comm W F W.π₀ (dop₁ y), hd₁, hd₂, map_sub, map_gamma_comm W F y]

def invariantLetter (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O (W.DD T) :=
  W.NΔ T ⊓ (W.Nl T i).restrictScalars O

theorem mem_invariantLetter_iff {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} :
    x ∈ invariantLetter W T i ↔ Formalism.MainNotions.LiftingTheory.InNΔi W T i x := by
  first
  | exact Iff.rfl
  | simp [invariantLetter, Formalism.MainNotions.LiftingTheory.InNΔi]

theorem idempotent_smul_of_mem_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (h : x ∈ W.Nl T i) :
    (letE i : LetA O n) • x = x := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, idempotent_mul_self']

theorem mem_letter_of_idempotent_smul {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hN : x ∈ W.N T)
    (h : (letE i : LetA O n) • x = x) : x ∈ W.Nl T i := by
  exact Submodule.mem_map.mpr ⟨x, hN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact h⟩

theorem derivation_preserves_invariants {T : LocLat G Qp LL O} (i : ZMod n)
    (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    (hmod : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = W.π₀ • x')
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ z, W.π₀ • dop z = W.γ T z - z) :
    ∀ y ∈ invariantLetter W T i, dop y ∈ invariantLetter W T i := by
  intro y hy
  obtain ⟨u, hu⟩ := hπ
  have hinj : ∀ a b : W.DD T, W.π₀ • a = W.π₀ • b → a = b := by
    intro a b h
    rw [← algebraMap_smul W.EE W.π₀ a, ← algebraMap_smul W.EE W.π₀ b, ← hu] at h
    have h' := congrArg (fun t => ((u⁻¹ : W.EEˣ) : W.EE) • t) h
    simpa [smul_smul] using h'
  have hy' : y ∈ W.NΔ T ∧ y ∈ W.Nl T i := (mem_invariantLetter_iff W).mp hy
  obtain ⟨hyΔ, hyl⟩ := hy'
  obtain ⟨x', hx'Δ, hx'⟩ := hmod y hyΔ
  have hdx : dop y = x' := hinj _ _ (by rw [hd, hx'])
  have hdΔ : dop y ∈ W.NΔ T := by rw [hdx]; exact hx'Δ
  have hey : (letE i : LetA O n) • y = y := idempotent_smul_of_mem_letter W hyl
  have hγy : W.γ T y = (letE i : LetA O n) • W.γ T y := by
    conv_lhs => rw [← hey]
    exact gammaD_idempotent_smul' W T W.gam i y
  have hdN : dop y ∈ W.N T :=
    (show dop y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (dop y) = dop y from hdΔ).1
  have hdl : dop y ∈ W.Nl T i := by
    refine mem_letter_of_idempotent_smul W hdN ?_
    apply hinj
    rw [smul_comm, hd, smul_sub, ← hγy, hey]
  exact (mem_invariantLetter_iff W).mpr (show Formalism.MainNotions.LiftingTheory.InNΔi W T i (dop y) from ⟨hdΔ, hdl⟩)

theorem exists_invariant_preimage_average (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n) {y₀ : W.DD T₁} (hy₀ : y₀ ∈ W.Nl T₁ i) {t : W.DD T₂}
    (ht : ∀ δ ∈ W.DelF, W.γD T₂ δ t = t) (hF : W.map F y₀ = t) :
    ∃ y ∈ invariantLetter W T₁ i, W.map F y = t := by
  obtain ⟨uc, huc⟩ := hΔ
  have hNγ : ∀ g : W.Gam, ∀ z ∈ W.N T₁, W.γD T₁ g z ∈ W.N T₁ := fun g z hz => W.N_Γ T₁ g z hz
  have hmγ : ∀ (g : W.Gam) (z : W.DD T₁), W.map F (W.γD T₁ g z) = W.γD T₂ g (W.map F z) :=
    fun g z => W.map_γ F g z
  have hclos : ∀ a ∈ W.DelF, ∀ b ∈ W.DelF, a * b ∈ W.DelF := by
    intro a ha b hb
    obtain ⟨k, hk, hak⟩ := (W.DelF_def a).mp ha
    obtain ⟨m, hm, hbm⟩ := (W.DelF_def b).mp hb
    refine (W.DelF_def _).mpr ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hak, one_pow, Nat.mul_comm k m, pow_mul, hbm, one_pow, one_mul]
  have hinv : ∀ a ∈ W.DelF, a⁻¹ ∈ W.DelF := by
    intro a ha
    obtain ⟨k, hk, hak⟩ := (W.DelF_def a).mp ha
    exact (W.DelF_def _).mpr ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩
  set r : LetA O n := algebraMap O (LetA O n) ((uc⁻¹ : Oˣ) : O) with hr
  set s : W.DD T₁ := ∑ δ ∈ W.DelF, W.γD T₁ δ y₀ with hs
  have hy₀N : y₀ ∈ W.N T₁ := by
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy₀
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact (W.N T₁).smul_mem _ hz
  have hey₀ : (letE i : LetA O n) • y₀ = y₀ := idempotent_smul_of_mem_letter W hy₀
  have hsN : s ∈ W.N T₁ := (W.N T₁).sum_mem (fun δ _ => hNγ δ y₀ hy₀N)
  have hyN : r • s ∈ W.N T₁ := (W.N T₁).smul_mem r hsN
  have hsΔ : ∀ δ' ∈ W.DelF, W.γD T₁ δ' s = s := by
    intro δ' hδ'
    rw [hs, map_sum]
    refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun a ha => hclos _ hδ' _ ha)
      (fun a ha => hclos _ (hinv _ hδ') _ ha) (fun a _ => by simp) (fun a _ => by simp) ?_
    intro a _
    exact (W.γD_mul T₁ δ' a y₀).symm
  have hyΔ : ∀ δ' ∈ W.DelF, W.γD T₁ δ' (r • s) = r • s := by
    intro δ' hδ'
    rw [gammaD_smul_letA W T₁ δ' r s, hsΔ δ' hδ', hr, AlgHom.commutes]
  have hyl : r • s ∈ W.Nl T₁ i := by
    refine mem_letter_of_idempotent_smul W hyN ?_
    rw [smul_comm, hs, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    rw [← gammaD_idempotent_smul' W T₁ δ i y₀, hey₀]
  refine ⟨r • s, (mem_invariantLetter_iff W).mpr
    (show Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (r • s) from ⟨⟨hyN, hyΔ⟩, hyl⟩), ?_⟩
  have hterm : ∀ δ ∈ W.DelF, W.map F (W.γD T₁ δ y₀) = t := by
    intro δ hδ
    rw [hmγ, hF, ht δ hδ]
  rw [map_letA_smul_comm W F r s, hs, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul (LetA O n), smul_smul, hr, ← map_natCast (algebraMap O (LetA O n)),
    ← map_mul, ← huc, Units.inv_mul, map_one, one_smul]

end SlopeTestRemainingChoices

end LemG2

end Formalism.MainNotions.RamifiedCoefficientChains.S9
