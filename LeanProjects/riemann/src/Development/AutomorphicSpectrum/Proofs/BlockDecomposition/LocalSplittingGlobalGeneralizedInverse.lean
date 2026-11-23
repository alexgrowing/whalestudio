import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem projective_of_genInverse_of_exact {S P Q T : Type} [CommRing S]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q] [Module.Projective S Q]
    [AddCommGroup T] [Module S T] (f : P →ₗ[S] Q) (g : Q →ₗ[S] T) (s : Q →ₗ[S] P)
    (hs : f ∘ₗ s ∘ₗ f = f) (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective S T := by
  have hker : LinearMap.ker g ≤ LinearMap.ker (LinearMap.id - f ∘ₗ s) := by
    intro q hq
    obtain ⟨p, rfl⟩ := (hex q).1 hq
    have hp : f (s (f p)) = f p := LinearMap.congr_fun hs p
    simp [LinearMap.mem_ker, hp]
  let t : T →ₗ[S] Q := (LinearMap.ker g).liftQ (LinearMap.id - f ∘ₗ s) hker ∘ₗ
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap
  refine Module.Projective.of_split t g ?_
  ext x
  obtain ⟨q, rfl⟩ := hg x
  have h1 : (g.quotKerEquivOfSurjective hg).symm (g q) = Submodule.Quotient.mk q := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, hex.apply_apply_eq_zero, sub_zero]

theorem exists_genInverse_of_forall_maximal (R A B : Type) [CommRing R] [AddCommGroup A]
    [Module R A] [Module.Finite R A] [Module.Projective R A] [AddCommGroup B] [Module R B]
    [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (h : ∀ (m : Ideal R) [m.IsMaximal], ∃ s : Localization.AtPrime m ⊗[R] B →ₗ[Localization.AtPrime m] Localization.AtPrime m ⊗[R] A, f.baseChange (Localization.AtPrime m) ∘ₗ s ∘ₗ f.baseChange (Localization.AtPrime m) = f.baseChange (Localization.AtPrime m)) :
    ∃ s : B →ₗ[R] A, f ∘ₗ s ∘ₗ f = f := by
  haveI : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  haveI : Module.FinitePresentation R (B ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (LinearMap.range f).mkQ_surjective
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f)
  haveI : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) := fun P _ =>
    (isLocalizedModule_iff_isBaseChange P.primeCompl _ _).2 (TensorProduct.isBaseChange R _ _)
  haveI : Module.Projective R (B ⧸ LinearMap.range f) := by
    refine Module.projective_of_localization_maximal' (fun P _ => Localization.AtPrime P)
      (fun P _ => Localization.AtPrime P ⊗[R] (B ⧸ LinearMap.range f))
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) (B ⧸ LinearMap.range f) 1) ?_
    intro m hm
    obtain ⟨s, hs⟩ := h m
    refine GlobalTheory.CompanionTheory.PerfVB.projective_of_genInverse_of_exact (f.baseChange (Localization.AtPrime m))
      ((LinearMap.range f).mkQ.baseChange (Localization.AtPrime m)) s hs ?_ ?_
    · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      exact lTensor_exact _ (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective
    · rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective _ (LinearMap.range f).mkQ_surjective
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (LinearMap.range f).mkQ_surjective
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ : B →ₗ[R] B) b ∈
      LinearMap.range f := by
    intro b
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    have hb : (LinearMap.range f).mkQ (t ((LinearMap.range f).mkQ b)) =
        (LinearMap.range f).mkQ b := LinearMap.congr_fun ht ((LinearMap.range f).mkQ b)
    change (LinearMap.range f).mkQ (b - t ((LinearMap.range f).mkQ b)) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict (LinearMap.range f) (LinearMap.id - t ∘ₗ (LinearMap.range f).mkQ) hmem)
    f.surjective_rangeRestrict
  refine ⟨s, ?_⟩
  ext a
  have h2 : (LinearMap.range f).mkQ (f a) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self f a
  have h1 : f (s (f a)) = f a - t ((LinearMap.range f).mkQ (f a)) :=
    congrArg Subtype.val (LinearMap.congr_fun hs (f a))
  rw [h2, map_zero, sub_zero] at h1
  simpa only [LinearMap.comp_apply] using h1

end GlobalTheory.CompanionTheory.PerfVB
