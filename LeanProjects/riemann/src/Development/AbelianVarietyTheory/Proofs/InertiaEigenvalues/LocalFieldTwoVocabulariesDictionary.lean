import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DelGlob.LocalDict

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (uniformizer F) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have h0 : φ (uniformizer F) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer F) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer F := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {F}

theorem ord_eq_ord (x : Fˣ) : GlobalTheory.SmGL.ord F x = GroundTheory.LocalField.ord (x : F) := by
  rw [GlobalTheory.SmGL.ord, GroundTheory.LocalField.ord, GroundTheory.LocalField.normalizedValuation_apply]

theorem isUnram_iff (χ : Fˣ →* ℂˣ) : GlobalTheory.SplitWeil.IsUnram χ ↔ GroundTheory.LocalField.IsUnramifiedChar χ := by
  constructor
  · intro h x hx
    exact MonoidHom.mem_ker.mpr (h x (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.mp hx))
  · intro h x hx
    exact MonoidHom.mem_ker.mp (h (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.mpr hx))

theorem mem_unitFilt_iff (n : ℕ) (x : Fˣ) :
    x ∈ GlobalTheory.LocLanglands.unitFilt F n ↔ x ∈ GroundTheory.LocalField.unitFiltrationUnits F n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [pow_zero]
    exact (Valuation.map_sub _ _ _).trans (by simp [h])
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    rw [GroundTheory.LocalField.mem_unitFiltrationUnits_iff hn hϖ]
    have hv : valuation F (ϖ : F) = uniformizer F := by
      have e : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (valuation F (ϖ : F)) =
          IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (uniformizer F) := by
        rw [← GroundTheory.LocalField.normalizedValuation_apply, GroundTheory.LocalField.normalizedValuation_uniformizer hϖ,
          valueGroupIso_uniformizer]
      exact EquivLike.injective _ e
    rw [hv]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hlt : valuation F ((x : F) - 1) < 1 :=
        h.trans_lt (pow_lt_one₀ zero_le uniformizer_lt_one (by omega))
      simpa using (valuation F).map_one_add_of_lt hlt

theorem quasiCharConductor_eq_of_hasExponent (χ : Fˣ →* ℂˣ) (a : ℕ) (h : GlobalTheory.LocLanglands.HasExponent χ a) :
    GroundTheory.LocalField.quasiCharConductor χ = a := by
  have hmem : ∀ n, GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker ↔
      ∀ x ∈ GlobalTheory.LocLanglands.unitFilt F n, χ x = 1 := by
    intro n
    constructor
    · intro hk x hx; exact MonoidHom.mem_ker.mp (hk ((mem_unitFilt_iff n x).1 hx))
    · intro hk x hx; exact MonoidHom.mem_ker.mpr (hk x ((mem_unitFilt_iff n x).2 hx))
  unfold GroundTheory.LocalField.quasiCharConductor
  apply le_antisymm
  · exact Nat.sInf_le ((hmem a).2 h.1)
  · by_contra hlt
    push_neg at hlt
    have hs : GroundTheory.LocalField.unitFiltrationUnits F
        (sInf {n : ℕ | GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker}) ≤ χ.ker :=
      Nat.sInf_mem (s := {n : ℕ | GroundTheory.LocalField.unitFiltrationUnits F n ≤ χ.ker}) ⟨a, (hmem a).2 h.1⟩
    obtain ⟨x, hx, hx'⟩ := h.2 _ hlt
    exact hx' (((hmem _).1 hs) x hx)

theorem addCharConductor_eq_of_hasConductor (ψ : AddChar F Circle) (c : Fˣ)
    (h : GlobalTheory.SplitWeil.HasConductor ψ c) :
    GroundTheory.LocalField.addCharConductor ψ = GlobalTheory.SmGL.ord F c := by
  have key : ∀ n : ℤ, GroundTheory.LocalField.IsTrivialOn ψ n ↔ GlobalTheory.SmGL.ord F c ≤ n := by
    intro n
    obtain ⟨y, hy⟩ := GroundTheory.LocalField.exists_normalizedValuation_eq F (-n)
    have hball : ∀ z : F, z ∈ GroundTheory.LocalField.valBall F n ↔ valuation F z ≤ valuation F y := by
      intro z
      rw [GroundTheory.LocalField.mem_valBall, ← hy, GroundTheory.LocalField.normalizedValuation_le_iff]
    have e1 : GroundTheory.LocalField.IsTrivialOn ψ n ↔ ∀ z : F, valuation F z ≤ valuation F y → ψ z = 1 :=
      forall_congr' fun z => imp_congr_left (hball z)
    rw [e1, h y, ← GroundTheory.LocalField.normalizedValuation_le_iff, hy,
      GroundTheory.LocalField.normalizedValuation_eq_exp_ord c.ne_zero, WithZero.exp_le_exp, ord_eq_ord]
    omega
  unfold GroundTheory.LocalField.addCharConductor
  have hs : {n : ℤ | GroundTheory.LocalField.IsTrivialOn ψ n} = Set.Ici (GlobalTheory.SmGL.ord F c) := by
    ext n; exact key n
  rw [hs, csInf_Ici]

end GlobalTheory.DelGlob.LocalDict

namespace GlobalTheory.DelGlob

theorem localVocabularyDictionary : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F], resCard F = GroundTheory.LocalField.residueCard F ∧ (∀ x : Fˣ, ord F x = GroundTheory.LocalField.ord (x : F)) ∧ (∀ χ : Fˣ →* ℂˣ, IsUnram χ ↔ GroundTheory.LocalField.IsUnramifiedChar χ) ∧ (∀ (χ : Fˣ →* ℂˣ) (a : ℕ), HasExponent χ a → GroundTheory.LocalField.quasiCharConductor χ = a) ∧ ∀ (ψ : AddChar F Circle) (c : Fˣ), HasConductor ψ c → GroundTheory.LocalField.addCharConductor ψ = ord F c := by
  intro F _ _ _ _
  exact ⟨rfl, fun x => LocalDict.ord_eq_ord x, fun χ => LocalDict.isUnram_iff χ,
    fun χ a h => LocalDict.quasiCharConductor_eq_of_hasExponent χ a h,
    fun ψ c h => LocalDict.addCharConductor_eq_of_hasConductor ψ c h⟩

end GlobalTheory.DelGlob
