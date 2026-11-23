import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.ExistsAlgHomEndIntertwiningMemAdjoin
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (hτ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (D X : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ (fixedVectors τ U)] [Nontrivial (fixedVectors τ U)], IsClosed (D : Set H) → π.IsInvariant D → X = D ⊓ fixU π U → X ≤ spanFix τ π D U → ∃ c : Module.End ℂ (fixedVectors τ U) →ₐ[ℂ] Module.End ℂ X, (∀ t f, Eqv τ π D f → ∀ (x : fixedVectors τ U) (y : X), (y : H) = f x → ((c t y : X) : H) = f (t x)) ∧ ∀ t, c t ∈ Algebra.adjoin ℂ {a : Module.End ℂ X | ∃ g, ∀ v : X, ((a v : X) : H) = prj (fixU π U) (π g v)} := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π U hUc hUo D X _ _ _ hD hinv hX hle
  subst hX
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U
  have hm : ∀ f, Eqv τ π D f → ∀ x : fixedVectors τ U, f x ∈ D ⊓ fixU π U := fun f hf x =>
    ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  let res : ∀ f, Eqv τ π D f → fixedVectors τ U →ₗ[ℂ] ↥(D ⊓ fixU π U) := fun f hf =>
    (f ∘ₗ (fixedVectors τ U).subtype).codRestrict _ (hm f hf)
  let e : S →ₗ[ℂ] fixedVectors τ U := fixedProj τ hτ hUc hUo
  let b : G → Module.End ℂ (fixedVectors τ U) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ U).subtype
  let a : G → Module.End ℂ ↥(D ⊓ fixU π U) := fun g =>
    ((prj (fixU π U) ∘L π g).toLinearMap ∘ₗ (D ⊓ fixU π U).subtype).codRestrict _ fun v =>
      ⟨p3 D hD hinv _ (hinv g _ v.2.1), p1 _⟩
  obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ U) ↥(D ⊓ fixU π U) {k | ∃ f hf, k = res f hf}
    (Set.range fun g => (b g, a g)) (by
      rw [eq_top_iff]
      rintro ⟨y, hy⟩ -
      have h3 : spanFix τ π D U ≤ (⨆ k ∈ {k | ∃ f hf, k = res f hf}, LinearMap.range k).map (D ⊓ fixU π U).subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨f, hf, x, hx, rfl⟩
        exact ⟨res f hf ⟨x, hx⟩, Submodule.mem_iSup_of_mem (res f hf) (Submodule.mem_iSup_of_mem ⟨f, hf, rfl⟩ ⟨_, rfl⟩), rfl⟩
      obtain ⟨z, hz, e⟩ := h3 (hle hy)
      exact (Subtype.ext e : z = ⟨y, hy⟩) ▸ hz) (by
      rintro _ ⟨g, rfl⟩ _ ⟨f, hf, rfl⟩
      refine LinearMap.ext fun x => Subtype.ext ?_
      show prj (fixU π U) (π g (f x)) = f (fixedProj τ hτ hUc hUo (τ g x))
      rw [← hf.map]
      exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f ⟨fun _ => trivial, hf.map⟩ _) (by
      intro x hx
      let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
        refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp⟩⟩
      have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
        rcases eq_bot_or_eq_top W with h | h
        · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
          have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
          rw [h', map_one] at this
          exact (hx (Subtype.ext this)).elim
        · exact congrArg Subrepresentation.toSubmodule h
      rw [eq_top_iff]
      rintro y -
      have h4 : e y = y := Subtype.ext (fixedProj_apply_of_mem hτ hUc hUo y.2)
      rw [← h4]
      refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
  refine ⟨c, fun t f hf x y hy => ?_, fun t => Algebra.adjoin_mono ?_ (h2 t)⟩
  · obtain rfl : y = res f hf x := Subtype.ext hy
    exact congrArg Subtype.val (LinearMap.congr_fun (h1 t _ ⟨f, hf, rfl⟩) x)
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, fun _ => rfl⟩
