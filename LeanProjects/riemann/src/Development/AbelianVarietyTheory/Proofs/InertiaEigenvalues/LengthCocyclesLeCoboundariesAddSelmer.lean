import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob

noncomputable section

namespace GlobalTheory.Cut.SelClass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem length_le_cob_add {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    (C : Submodule R (Γ → M)) (hC : C ≤ ReciprocityTheory.Gal.Z1 rho) (S : Submodule R (ReciprocityTheory.Gal.H1 rho))
    (hS : ∀ f (hf : f ∈ C), (Submodule.Quotient.mk ⟨f, hC hf⟩ : ReciprocityTheory.Gal.H1 rho) ∈ S) :
    Module.length R ↥C ≤ Module.length R ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) + Module.length R ↥S := by

  let ψ : ↥C →ₗ[R] ReciprocityTheory.Gal.H1 rho :=
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype).mkQ ∘ₗ Submodule.inclusion hC
  have hker : ∀ x : ↥C, ψ x = 0 → (x : Γ → M) ∈ ReciprocityTheory.Gal.B1 rho := by
    intro x hx
    have h := (Submodule.Quotient.mk_eq_zero _).1 hx
    simpa using h
  have hrange : LinearMap.range ψ ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hS x.1 x.2
  let K := LinearMap.ker ψ.rangeRestrict
  have hsplit := Module.length_eq_add_of_exact K.subtype ψ.rangeRestrict
    (Submodule.subtype_injective _) ψ.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map _)

  let j : ↥K →ₗ[R] ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) :=
    LinearMap.codRestrict (C ⊓ ReciprocityTheory.Gal.B1 rho) (C.subtype ∘ₗ K.subtype) (fun x => by
      refine ⟨x.1.2, hker x.1 ?_⟩
      have hx : ψ.rangeRestrict x.1 = 0 := x.2
      exact congrArg Subtype.val hx)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hK := Module.length_le_of_injective j hj
  have hI := Module.length_le_of_injective (Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)
  rw [hsplit]
  exact add_le_add hK hI

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem mk_mem_selG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (P : LocPrime l)
    (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
    (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (f : ↥(ReciprocityTheory.Gal.Z1 (WKG M)))
    (hl : ∀ w hw, (fun g => Br.phi (nb w hw) k (f.1 (Br.ι (nb w hw) g).1)) ∈
      HfD (P.PD (nb w hw).Kw) (Br.lat (nb w hw) (M.comp (Dec (F := E) (A.1 w)).subtype)))
    (hu : ∀ v, v ∉ placesOver E l → v ∉ Sig → ∀ g ∈ Ine (F := E) (A.1 v), f.1 g = 0) :
    (Submodule.Quotient.mk f : ReciprocityTheory.Gal.H1 (WKG M)) ∈ Br.selG A l P nb Sig M := by
  unfold Br.selG GaloisCohomology.SelAll GaloisCohomology.bkCond Br.LlG Sel
  refine (Submodule.mem_iInf _).2 fun v => ?_
  rw [Submodule.mem_comap]
  dsimp only
  split_ifs with h1 h2 h3
  · unfold Br.bkG
    refine Submodule.mem_map.2 ⟨_, ?_, rfl⟩
    exact hl v h2
  · exact Submodule.mem_top
  · exact Submodule.mem_top
  · have hv : v ∉ placesOver E l := h1
    unfold GaloisCohomology.unrAt H1ur
    rw [LinearMap.mem_ker]
    unfold ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

    convert (ReciprocityTheory.Gal.B1 _).zero_mem using 1
    funext g
    exact hu v hv h3 _ g.2

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  intro D i ρ π C hC hfin hine
  unfold lenCob
  refine length_le_cob_add _ C hC _ (fun f hf => ?_)
  unfold Br.selPi
  refine mk_mem_selG D.nd.plOm (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i) _ (WpO D.nd i ρ π) ⟨f, hC hf⟩ ?_ ?_
  · intro w hw
    exact hfin f hf w hw
  · intro v hv hSig g hg
    have hSv : v ∉ D.nd.S i := fun h => hSig (Or.inl h)
    have hQv : v ∉ D.nd.Q i := fun h => hSig (Or.inr h)

    have hmem : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) D.R.r) Subtype.val f ∈ resIne i C v :=
      Submodule.mem_map_of_mem hf
    rw [hine v hv hSv hQv, Submodule.mem_bot] at hmem
    exact congrFun hmem ⟨g, hg⟩

end GlobalTheory.Cut.SelClass

end
