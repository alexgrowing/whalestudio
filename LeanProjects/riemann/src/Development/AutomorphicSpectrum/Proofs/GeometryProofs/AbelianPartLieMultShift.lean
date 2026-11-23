import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenDecompositionExactSequenceStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbMult

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem lieMult_iff_family {S : Scheme.{0}} {k : Type} [Field k] {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    {V : Type} [AddCommGroup V] [Module k V] {x : Sp k ⟶ S} (M : LieModel G x V) (act : OAct O G)
    (ρ : O →+* Module.End k V) (h : M.IsActOf act.act ρ) (τ : O →+* k) (n : ℕ) :
    LieMult act x τ n ↔ ∃ b : Fin n → V, LinearIndependent k b ∧ Submodule.span k (Set.range b) = eigSp ρ τ := by
  rw [Fl.Test.lieMult_iff_exists_frame]
  constructor
  · rintro ⟨v, hv⟩
    choose e he using fun i => M.onto (v i) (hv.1 i).1
    obtain rfl : v = fun i => M.pt (e i) := funext fun i => (he i).symm
    exact ⟨e, (Fl.Test.isEigFrame_iff M act ρ h τ e).1 hv⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun i => M.pt (b i), (Fl.Test.isEigFrame_iff M act ρ h τ b).2 hb⟩

theorem lieMult_abPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  intro E _ _ _ H S t L _ _ z P
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  obtain ⟨m, hm⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := m
  refine ⟨Module.finrank ℤ P.τ.X / Module.finrank ℚ E, ?_⟩
  intro k _ _ g τ n hn
  haveI : CharZero k := charZero_of_injective_ringHom g.injective
  obtain ⟨V₂, _, _, ⟨M₂⟩⟩ := lieModel_exists (Sp L) P.tK.G k (spMap g)
  obtain ⟨V₃, _, _, ⟨M₃⟩⟩ := lieModel_exists (Sp L) P.tB.G k (spMap g)
  let D := GlobalTheory.Diag.diagAct (Sp L) (𝓞 E) P.τ.X
  let M₁ := Fl.Test.torusModel (spMap g) P.τ.X
  obtain ⟨ρ₁, hρ₁, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₁ (𝓞 E) D.act D.hom D.one D.mul D.add
  obtain ⟨ρ₂, hρ₂, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₂ (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₃, hρ₃, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₃ (𝓞 E) P.tB.act.act P.tB.act.hom
    P.tB.act.one P.tB.act.mul P.tB.act.add
  obtain ⟨f, hf, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₁ M₂ P.τ.i
  obtain ⟨h, hh, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₂ M₃ (P.τ.q ≫ P.e.hom)
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.torus_extension_tangent_exact L P.tK.G P.τ k g
  haveI hmono : Mono P.τ.i := ⟨fun a b hab => P.τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  have finj : Function.Injective f := fun a b hab => M₁.inj ((cancel_mono P.τ.i).1 (by
    rw [← hf, ← hf, hab]))
  have hsur : Function.Surjective h := fun y => by
    obtain ⟨v, hv, hvq⟩ := hsurj (M₃.pt y ≫ P.e.inv) ((M₃.tan y).comp_monHom P.e.inv)
    obtain ⟨a, rfl⟩ := M₂.onto v hv
    refine ⟨a, M₃.inj ?_⟩
    rw [hh, ← Category.assoc, hvq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hex : LinearMap.range f = LinearMap.ker h := by
    ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    have h1 : h a = 0 ↔ M₂.pt a ≫ P.τ.q = 1 := by
      constructor
      · intro h0
        have := hh a
        rw [h0, Fl.Test.pt_zero, ← Category.assoc] at this
        refine (cancel_mono P.e.hom).1 ?_
        rw [← this, MonObj.one_comp]
      · intro h0
        refine M₃.inj ?_
        rw [hh, ← Category.assoc, h0, MonObj.one_comp, Fl.Test.pt_zero]
    rw [h1, hker _ (M₂.tan a)]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M₁.pt c, M₁.tan c, (hf c).symm⟩
    · rintro ⟨w, hw, hwa⟩
      obtain ⟨c, rfl⟩ := M₁.onto w hw
      exact ⟨c, M₂.inj ((hf c).trans hwa)⟩
  have eqf : ∀ a c, f (ρ₁ a c) = ρ₂ a (f c) := fun a c => M₂.inj (by
    rw [hf, hρ₂ a (f c), hρ₁ a c, hf, Category.assoc, Category.assoc]
    exact congrArg (M₁.pt c ≫ ·) (hm a))
  have eqh : ∀ a c, h (ρ₂ a c) = ρ₃ a (h c) := fun a c => M₃.inj (by
    rw [hh, hρ₃ a (h c), hρ₂ a c, hh, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (M₂.pt c ≫ ·) (P.act a))
  obtain ⟨bas⟩ := GlobalTheory.T.eigenspace_basis_exists E P.τ.X k τ
  obtain ⟨b₁, hb₁, hb₁'⟩ := (lieMult_iff_family M₁ D ρ₁ hρ₁ τ _).1
    ((GlobalTheory.Diag.lieMult_iff (spMap g) τ _).2 ⟨bas⟩)
  obtain ⟨b₂, hb₂, hb₂'⟩ := (lieMult_iff_family M₂ P.tK.act ρ₂ hρ₂ τ n).1 hn
  obtain ⟨hle, b₃, hb₃⟩ := GlobalTheory.T.eigen_decomposition_exact_sequence E k _ _ _ ρ₁ ρ₂ ρ₃ f h finj hsur hex eqf eqh τ _ n b₁ b₂ hb₁ hb₁' hb₂ hb₂'
  exact ⟨hle, (lieMult_iff_family M₃ P.tB.act ρ₃ hρ₃ τ _).2 ⟨b₃, hb₃⟩⟩

end GlobalTheory.CompanionTheory.Ar.AbMult
