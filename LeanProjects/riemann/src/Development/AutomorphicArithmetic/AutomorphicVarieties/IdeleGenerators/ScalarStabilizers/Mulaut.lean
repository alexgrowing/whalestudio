import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerIsOpen
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem stab_open {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (h : {k | ρ k v = v} ∈ nhds (1 : G)) : IsOpen {k | ρ k v = v} :=
  _root_.UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open ρ v h

private theorem fin_mul {X ι : Type*} (S : Submodule ℂ (X → ℂ)) (f g h : ι → S) (e : ∀ i, (h i).1 = (f i).1 * (g i).1)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)))
    (hg : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range h)) := by
  have h1 : ((Submodule.span ℂ (Set.range f)).map S.subtype).FG := (Module.Finite.iff_fg.1 hf).map _
  have h2 : ((Submodule.span ℂ (Set.range g)).map S.subtype).FG := (Module.Finite.iff_fg.1 hg).map _
  have h3 := Module.Finite.iff_fg.2 (h1.mul h2)
  have h4 : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range h)).map S.subtype) := by
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range f)).map S.subtype *
      (Submodule.span ℂ (Set.range g)).map S.subtype) (Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.subtype_apply, e]
    exact Submodule.mul_mem_mul ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype (Module.Finite.iff_fg.1 h4))

theorem UpperTheory.V.Sd.Hm.mulaut :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 →
        TR.IsAutForm φ → TR.IsAutForm ψ →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z χ) '' TR.Zalg F a)) → TR.IsAutForm χ := by
  intro F _ _ _ a φ ψ χ e hφ hψ hz
  have hrt : ∀ g, (TR.rt F a g χ).1 = (TR.rt F a g φ).1 * (TR.rt F a g ψ).1 := fun g => by
    funext x
    simp only [TR.rt_apply, Pi.mul_apply, e]
  refine ⟨fun γ g => ?_, ?_, ?_, hz, fun g => ?_⟩
  · rw [e, Pi.mul_apply, Pi.mul_apply, hφ.left, hψ.left]
  · refine stab_open _ _ (Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)
    have h1 : TR.rt F a (finGL F a k) φ = φ := hk.1
    have h2 : TR.rt F a (finGL F a k) ψ = ψ := hk.2
    change TR.rt F a (finGL F a k) χ = χ
    exact Subtype.ext (by rw [hrt, h1, h2, e])
  · exact fin_mul _ _ _ _ (fun k => hrt _) hφ.kfin hψ.kfin
  · obtain ⟨C, N, h1⟩ := hφ.growth g
    obtain ⟨C', N', h2⟩ := hψ.growth g
    refine ⟨C * C', N + N', fun y => ?_⟩
    rw [e, Pi.mul_apply, norm_mul]
    refine (mul_le_mul (h1 y) (h2 y) (norm_nonneg _) ((norm_nonneg _).trans (h1 y))).trans_eq ?_
    ring
