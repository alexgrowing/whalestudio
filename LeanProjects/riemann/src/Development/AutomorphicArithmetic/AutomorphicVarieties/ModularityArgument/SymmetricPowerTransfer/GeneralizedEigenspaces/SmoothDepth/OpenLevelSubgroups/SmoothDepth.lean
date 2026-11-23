import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.smoothDepth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ u ∈ Hi.Uc k (c + 1), χ u = 1 := by
  intro k _ _ _ _ χ hχ
  have hopen : IsOpen (χ.ker : Set kˣ) := hχ
  obtain ⟨U, hU, hUe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp hopen
  have h1U : (1 : k) ∈ U := by
    have h : (1 : kˣ) ∈ Units.val ⁻¹' U := by
      rw [hUe]
      exact χ.ker.one_mem
    exact h
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff.mp (hU.mem_nhds h1U)
  have hu1 : uniformizer k < 1 := uniformizer_lt_one
  obtain ⟨c₀, hc₀⟩ := exists_pow_lt₀ hu1 γ
  refine ⟨c₀, fun c hc u hu => ?_⟩
  obtain ⟨-, hv⟩ := Sig.mem_Uc.mp hu
  have hlt : valuation k ((u : k) - 1) < γ :=
    calc valuation k ((u : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) := hv
      _ = uniformizer k ^ (c + 1) := zpow_natCast _ _
      _ ≤ uniformizer k ^ c₀ := pow_le_pow_right_of_le_one' hu1.le (by omega)
      _ < γ := hc₀
  have hmem : (u : k) ∈ U := hγ ⟨(u : k) - 1, hlt, by ring⟩
  have h : u ∈ Units.val ⁻¹' U := hmem
  rw [hUe] at h
  exact h
