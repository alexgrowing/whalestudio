import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CocW

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R e) k = algebraMap F R (b.repr e k) := by
  have : inclR (F := F) R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem scalar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    (∃ C : Set (AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ e : E, y - inclR (AF F) e ∈ C) ∧
    (∀ C : Set (AF F ⊗[F] E), IsCompact C → {e : E | inclR (AF F) e ∈ C}.Finite) ∧
    NoncompactSpace (AF F ⊗[F] E) := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨hC, hfin, hnc⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hd : 0 < Module.finrank F E := by rw [h.2.2.1]; norm_num
  let b := Module.finBasis F E
  let φ : AF F ⊗[F] E → Fin (Module.finrank F E) → AF F :=
    fun y k => (Algebra.TensorProduct.basis (AF F) b).repr y k
  have hφ : IsHomeomorph φ := hb _ b
  have hcont : ∀ k, Continuous fun y => φ y k := fun k => (continuous_apply k).comp hφ.continuous
  have hsub : ∀ y e k, φ (y - inclR (AF F) e) k = φ y k - algebraMap F (AF F) (b.repr e k) := by
    intro y e k
    simp only [φ, map_sub, Finsupp.sub_apply, repr_inclR]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hCc, hCy⟩ := hC
    refine ⟨φ ⁻¹' Set.pi Set.univ fun _ => C, ?_, ?_⟩
    · exact (hφ.homeomorph φ).isCompact_preimage.2 (isCompact_univ_pi fun _ => hCc)
    · intro y
      choose l hl using fun k => hCy (φ y k)
      refine ⟨∑ k, l k • b k, ?_⟩
      intro k _
      rw [hsub, b.repr_sum_self]
      exact hl k
  · intro C hCc
    have hS : ∀ k, {l : F | algebraMap F (AF F) l ∈ (fun y => φ y k) '' C}.Finite :=
      fun k => hfin _ (hCc.image (hcont k))
    refine ((Set.Finite.pi hS).preimage (f := fun (e : E) k => b.repr e k) ?_).subset ?_
    · intro x _ y _ hxy
      apply b.repr.injective
      ext k
      exact congrFun hxy k
    · intro e he k _
      refine ⟨inclR (AF F) e, he, ?_⟩
      exact repr_inclR (AF F) b e k
  · refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun y => φ y ⟨0, hd⟩ := by
      intro r
      obtain ⟨y, hy⟩ := hφ.surjective fun _ => r
      exact ⟨y, congrFun hy _⟩
    have := hK.image (hcont ⟨0, hd⟩)
    rwa [Set.image_univ, hsurj.range_eq] at this

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h n M
  obtain ⟨⟨C, hCc, hCy⟩, hfin, hnc⟩ := scalar F E σ h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hCc, ?_⟩
    intro y
    choose X hX using fun a i => hCy (y a i)
    exact ⟨X, fun a _ i _ => hX a i⟩
  · intro C hCc
    have hcont : ∀ a i, Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i :=
      fun a i => (continuous_apply i).comp (continuous_apply a)
    have hS : ∀ a i, {e : E | inclR (AF F) e ∈ (fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i) '' C}.Finite :=
      fun a i => hfin _ (hCc.image (hcont a i))
    refine (Set.Finite.pi fun a => Set.Finite.pi (hS a)).subset ?_
    intro X hX a _ i _
    exact ⟨ratTup (AF F) X, hX, rfl⟩
  · intro hn hM
    refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      fun r => ⟨fun _ _ => r, rfl⟩
    have hc : Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      (continuous_apply (⟨0, hM⟩ : Fin M)).comp (continuous_apply (⟨0, hn⟩ : Fin n))
    have := hK.image hc
    rwa [Set.image_univ, hsurj.range_eq] at this

end GlobalTheory.CompanionTheory.SW.CocW
