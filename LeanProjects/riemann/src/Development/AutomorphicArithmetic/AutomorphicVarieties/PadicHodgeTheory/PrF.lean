import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.prF :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0dual ((cycA l l E).comp φ) ρ = ⊥ → UpperTheory.V.Loc.finiteCocycles φ ρ = Z1 ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hpos hd
  obtain ⟨h0, -, -, hf⟩ := UpperTheory.V.Loc.posBasic hP φ hφ ρ hc hpos
  obtain ⟨hfin, -, h1, h2⟩ := UpperTheory.V.Loc.tateRat (v := l) (l := l) hP φ hφ ρ hc
  have hB := (UpperTheory.V.Loc.z1fMap φ ρ ρ).1 hc
  rw [hd, finrank_bot] at h2
  rw [h0, finrank_bot, h2, if_pos rfl, zero_add, zero_add] at h1
  have htop : finiteCohomology φ ρ = ⊤ := Submodule.eq_top_of_finrank_eq (hf.trans h1.symm)
  refine le_antisymm (fun c hc' => hc'.1) (fun c hc' => ?_)
  have hm : (Submodule.mkQ _ (⟨c, hc'⟩ : ↥(ReciprocityTheory.Gal.Z1 ρ)) : ReciprocityTheory.Gal.H1 ρ) ∈ finiteCohomology φ ρ := by
    rw [htop]; trivial
  obtain ⟨y, hy, hyc⟩ := hm
  have hsub := (Submodule.Quotient.eq _).1 hyc
  have h3 : (y : G → V) - c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := hB hsub
  have h4 := (UpperTheory.V.Loc.finiteCocycles φ ρ).sub_mem hy h3
  simpa using h4
