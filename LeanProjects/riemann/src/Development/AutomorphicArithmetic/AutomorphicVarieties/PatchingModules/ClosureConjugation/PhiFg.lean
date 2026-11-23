import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem finite_open_homs_to_finite_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : TopFG G)
    (Z : Type) [Group Z] [Finite Z] : Finite {φ : G →* Z // IsOpen (φ.ker : Set G)} := by
  obtain ⟨s, hs, hgen⟩ := h
  rw [topGen_iff] at hgen
  have : Finite s := hs.to_subtype
  let f : {φ : G →* Z // IsOpen (φ.ker : Set G)} → (s → Z) := fun φ x => φ.1 x
  apply Finite.of_injective f
  intro φ ψ hφψ
  apply Subtype.ext
  have hK : IsOpen ((φ.1.ker ⊓ ψ.1.ker : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact φ.2.inter ψ.2
  have hle : φ.1.ker ⊓ ψ.1.ker ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    show φ.1 g = ψ.1 g
    rw [hg.1, hg.2]
  have hopen := Subgroup.isOpen_mono hle hK
  have hcl := Subgroup.isClosed_of_isOpen _ hopen
  have hs' : Subgroup.closure (s : Set G) ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    rw [Subgroup.closure_le]
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have htop := Subgroup.topologicalClosure_minimal _ hs' hcl
  rw [hgen] at htop
  ext g
  exact htop (Subgroup.mem_top g)

theorem UpperTheory.V.Pa.phi_fg :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l), (∃ s : Finset F.Γ, (Subgroup.closure (s : Set F.Γ)).topologicalClosure = ⊤) → PhiCond F.G₀ l := by
  intro l _ F hF
  obtain ⟨s, hs⟩ := hF
  have hΓ : TopFG F.Γ := ⟨(s : Set F.Γ), s.finite_toSet, (topGen_iff _).mpr hs⟩
  have hopen : IsOpen ((F.η.ker : Subgroup F.Γ) : Set F.Γ) := F.η_open
  have hG : TopFG F.G₀ := ((TopFG.subgroup_quot F.Γ hΓ).1 _ hopen)
  have : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hopen).isCompact
  intro H hH
  have hH' : TopFG H := (TopFG.subgroup_quot F.G₀ hG).1 H hH
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact finite_open_homs_to_finite_group H hH' (Multiplicative (ZMod l))
