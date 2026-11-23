import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSumStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

section Linear

variable {ι O : Type} [Fintype ι] [CommRing O]
variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]

theorem mem_eig (ρ : O →+* Module.End R N) (σ : O →+* R) (u : N) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

def Splits (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : Prop :=
  ∀ m : N, ∃! f : ι → N, (∀ s a, ρ a (f s) = τ s a • f s) ∧ ∑ s, f s = m

def sumMap (ρ : O →+* Module.End R N) (τ : ι → O →+* R) : (∀ s, eigSp ρ (τ s)) →ₗ[R] N :=
  ∑ s, (eigSp ρ (τ s)).subtype ∘ₗ LinearMap.proj s

theorem sumMap_apply (ρ : O →+* Module.End R N) (τ : ι → O →+* R) (g : ∀ s, eigSp ρ (τ s)) :
    sumMap ρ τ g = ∑ s, (g s : N) := by
  simp [sumMap, LinearMap.sum_apply]

theorem sumMap_bij {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    Function.Bijective (sumMap ρ τ) := by
  constructor
  · intro g g' e
    have := (h (sumMap ρ τ g)).unique (y₁ := fun s => (g s : N)) (y₂ := fun s => (g' s : N))
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g s).2 a, (sumMap_apply ρ τ g).symm⟩
      ⟨fun s a => (mem_eig ρ (τ s) _).1 (g' s).2 a, by rw [e, sumMap_apply]⟩
    exact funext fun s => Subtype.ext (congrFun this s)
  · intro m
    obtain ⟨f, ⟨hf, hs⟩, -⟩ := h m
    exact ⟨fun s => ⟨f s, (mem_eig ρ (τ s) _).2 (hf s)⟩, by rw [sumMap_apply]; exact hs⟩

theorem exists_bases [DecidableEq ι] [IsLocalRing R] [Module.Finite R N] [Module.Projective R N]
    {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) :
    ∃ r : ι → ℕ, Nonempty (∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) := by
  let e := LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h)
  haveI hP : Module.Projective R (∀ s, eigSp ρ (τ s)) := Module.Projective.of_equiv e.symm
  have key : ∀ s, Module.Free R (eigSp ρ (τ s)) ∧ Module.Finite R (eigSp ρ (τ s)) := fun s => by
    haveI : Module.Finite R (∀ s, eigSp ρ (τ s)) := Module.Finite.equiv e.symm
    haveI : Module.Finite R (eigSp ρ (τ s)) :=
      Module.Finite.of_surjective (LinearMap.proj s : (∀ s, eigSp ρ (τ s)) →ₗ[R] eigSp ρ (τ s))
        (fun y => ⟨Pi.single s y, by simp⟩)
    haveI : Module.Projective R (eigSp ρ (τ s)) :=
      Module.Projective.of_split (LinearMap.single R (fun s => eigSp ρ (τ s)) s) (LinearMap.proj s)
        (LinearMap.ext fun y => by simp)
    haveI : Module.FinitePresentation R (eigSp ρ (τ s)) := Module.finitePresentation_of_projective _ _
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  refine ⟨fun s => Module.finrank R (eigSp ρ (τ s)), ⟨fun s => ?_⟩⟩
  haveI := (key s).1
  haveI := (key s).2
  exact Module.finBasis R _

def totBasis [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) : Module.Basis (Σ s, Fin (r s)) R N :=
  (Pi.basis b).map (LinearEquiv.ofBijective (sumMap ρ τ) (sumMap_bij h))

theorem totBasis_apply [DecidableEq ι] {ρ : O →+* Module.End R N} {τ : ι → O →+* R} (h : Splits ρ τ) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (s : ι) (i : Fin (r s)) :
    totBasis h b ⟨s, i⟩ = b s i := by
  simp only [totBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply, sumMap_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

variable {T N' : Type} [CommRing T] [AddCommGroup N'] [Module T N']

theorem image_frame [DecidableEq ι] {θ : R →+* T} {ρ : O →+* Module.End R N} {τ : ι → O →+* R}
    {ρ' : O →+* Module.End T N'} (h' : Splits ρ' fun s => θ.comp (τ s)) {r : ι → ℕ}
    (b : ∀ s, Module.Basis (Fin (r s)) R (eigSp ρ (τ s))) (β : N →ₛₗ[θ] N')
    (B : Module.Basis (Σ s, Fin (r s)) T N') (hB : ∀ s i, B ⟨s, i⟩ = β (b s i))
    (hρ : ∀ a e, ρ' a (β e) = β (ρ a e)) (s : ι) :
    LinearIndependent T (fun i => β (b s i)) ∧
      Submodule.span T (Set.range fun i => β (b s i)) = eigSp ρ' (θ.comp (τ s)) := by
  have hv : ∀ s i, ∀ a, ρ' a (β (b s i)) = (θ.comp (τ s)) a • β (b s i) := fun s i a => by
    rw [hρ, (mem_eig ρ (τ s) _).1 (b s i).2 a, β.map_smulₛₗ]
    rfl
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_⟩
  · have := B.linearIndependent.comp (Sigma.mk s) sigma_mk_injective
    convert this using 1
    exact funext fun i => (hB s i).symm
  · rintro _ ⟨i, rfl⟩
    exact (mem_eig ρ' _ _).2 (hv s i)
  · let f : ι → N' := fun s' => ∑ i, B.repr w ⟨s', i⟩ • β (b s' i)
    have hf : ∀ s' a, ρ' a (f s') = (θ.comp (τ s')) a • f s' := fun s' a => by
      simp only [f, map_sum, Finset.smul_sum, map_smul, hv s']
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    have hsum : ∑ s', f s' = w := by
      have := B.sum_repr w
      rw [Fintype.sum_sigma] at this
      simpa only [f, hB] using this
    have hw' := (mem_eig ρ' _ _).1 hw
    have hu := (h' w).unique (y₁ := f) (y₂ := fun s' => if s' = s then w else 0) ⟨hf, hsum⟩
      ⟨fun s' a => by
        by_cases e : s' = s
        · subst e; simpa using hw' a
        · simp [e], by simp⟩
    have : w = f s := by simpa using (congrFun hu s).symm
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

namespace GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk

open GlobalTheory.CompanionTheory.Ar.LieVB

theorem splits_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {S : Type} [CommRing S] (κ : c.F →+* S) {N : Type} [AddCommGroup N] [Module S N]
    (ρ : 𝓞 E →+* Module.End S N) : Splits ρ (fun s : E →+* ℂ => κ.comp (tauIn c s)) := by
  letI : Algebra c.F S := κ.toAlgebra
  exact fun m => GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ m

theorem exists_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  classical
  intro E _ _ _ H l c X t A _ _ x κ σ
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨N, _, _, ⟨M⟩⟩ := lieModel_exists X t.G A x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X t.G A x N M (𝓞 E) t.act.act t.act.hom t.act.one t.act.mul
    t.act.add
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change X t.G A x N M
  have hsp := splits_of c κ ρ
  obtain ⟨r, ⟨b⟩⟩ := exists_bases hsp
  refine ⟨r σ, fun i => M.pt (b σ i), ?_⟩
  intro T _ θ x' hx' v hv
  subst hx'
  obtain ⟨N', _, _, ⟨M'⟩⟩ := lieModel_exists X t.G T (spMap θ ≫ x)
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act X t.G T (spMap θ ≫ x) N' M' (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  let q := Fintype.equivFin (Σ s, Fin (r s))
  obtain ⟨β, B, hB, hβ⟩ := basis_tr θ x (spMap θ ≫ x) rfl M M' ((totBasis hsp b).reindex q)
  have hB' : ∀ s i, (B.reindex q.symm) ⟨s, i⟩ = β (b s i) := fun s i => by
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      totBasis_apply]
  have hact : ∀ a e, ρ' a (β e) = β (ρ a e) := fun a e => pt_left_inj M' (by
    rw [hβ, hρ a e, Over.comp_left, ← Category.assoc, ← hβ e, hρ' a (β e), Over.comp_left])
  have hsp' : Splits ρ' (fun s : E →+* ℂ => θ.comp (κ.comp (tauIn c s))) := splits_of c (θ.comp κ) ρ'
  obtain ⟨hli, hspan⟩ := image_frame hsp' b β (B.reindex q.symm) hB' hact σ
  have hvv : v = fun k => M'.pt (β (b σ k)) := funext fun k => Over.OverMorphism.ext (by
    rw [hv k, hβ])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action X T t.G (spMap θ ≫ x) N' M').2 (𝓞 E) t.act ρ' ((θ.comp κ).comp (tauIn c σ)) hρ').2 _ _).2
    ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk
