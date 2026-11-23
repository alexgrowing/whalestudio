import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPairAvoidingSmallSets
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.TwoSections

theorem exists_torsion_pair (M : Type) [CommGroup M] (P : M → Prop) (n : ℕ) (x : M)
    (h : ∀ c : M, 6 * Nat.card {h : M // h ^ n = 1 ∧ ¬ P (c * h)} < Nat.card {h : M // h ^ n = 1}) :
    ∃ b c : M, b ^ n = 1 ∧ c ^ n = 1 ∧ P b ∧ P c ∧ P (b * c) ∧ P (x * b) ∧ P (x * c) ∧ P (x * b * c) := by
  let H : Subgroup M := (powMonoidHom n : M →* M).ker
  have hH : Nat.card H = Nat.card {h : M // h ^ n = 1} := rfl
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by have := h 1; omega)
  have hB : ∀ c : M, 6 * Nat.card {h : H | ¬ P (c * h)} < Nat.card H := fun c => by
    have e : {h : H | ¬ P (c * h)} ≃ {h : M // h ^ n = 1 ∧ ¬ P (c * h)} :=
      Equiv.subtypeSubtypeEquivSubtypeInter (fun h : M => h ^ n = 1) (fun h => ¬ P (c * h))
    rw [Nat.card_congr e, hH]
    exact h c
  obtain ⟨b, c, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.exists_pair_avoiding_small_sets H _ _ (hB 1) (hB x)
  simp only [Set.mem_ofPred_eq, not_not, _root_.one_mul, Subgroup.coe_mul] at h1 h2 h3 h4 h5 h6
  exact ⟨b, c, b.2, c.2, h1, h2, h3, h4, h5, by rwa [_root_.mul_assoc]⟩

theorem exists_pushHom {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (q : X ⟶ S') (s : X ⟶ S) (e : q ≫ f = s) :
    ∃ ρ : (Over.mk q ⟶ G') →* (Over.mk s ⟶ G), ∀ c, (ρ c).left = c.left ≫ φ := by
  subst e
  exact ⟨pushHom h (Over.mk q), fun _ => rfl⟩

theorem exists_residue_point (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (w : X)
    (hw : IsClosed ({w} : Set X)) : ∃ (p : ℕ) (_ : Fact p.Prime) (x : Sp (kb p) ⟶ X), ∀ s, x s = w := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int X π).2.1 w hw
  obtain ⟨p, hp⟩ := CharP.exists (X.residueField w)
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime (X.residueField w) p⟩
  have : CharP (kb p) p := charP_kb
  have : IsAlgClosed (kb p) := isAlgClosed_kb
  letI : Algebra (ZMod p) (X.residueField w) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) (X.residueField w) := Module.Finite.of_finite
  let r : X.residueField w →+* kb p := (IsAlgClosed.lift (R := ZMod p) (S := X.residueField w) (M := kb p)).toRingHom
  refine ⟨p, hpp, Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w, fun s => ?_⟩
  have : (Spec.map (CommRingCat.ofHom r) ≫ X.fromSpecResidueField w) s ∈ Set.range (X.fromSpecResidueField w) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [Scheme.range_fromSpecResidueField] at this

end GlobalTheory.ZJ.TwoSections

namespace GlobalTheory.ZJ
open TwoSections

theorem Core.Law.six_of_few : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  intro hext C L T n hT hB hS hF w hw
  letI := L.grp
  letI := L.comm
  have := C.lft
  have := C.flat
  have hlft : LocallyOfFiniteType C.GG.hom := (GlobalTheory.ZJ.core_basic C).2.1
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨p, hp, x, hx⟩ := @exists_residue_point C.G.toScheme (C.GG.hom ≫ C.π) hlft' w hw
  obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
  obtain ⟨y, hy, hyU⟩ := hlift (x ≫ C.GG.hom)
  obtain ⟨τ⟩ := hT p y hyU
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_thetaExtension_test hext C T p y τ fun p _ y τ => (L.test p y τ).1
  let s₀ : Sp (kb p) := IsLocalRing.closedPoint (kb p)
  have hs : ∀ s : Sp (kb p), s = s₀ := fun s => Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
  have hr : rPt p s₀ = cPt p := IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hz : y (cPt p) = (x ≫ C.GG.hom) s₀ := by rw [← hy, Scheme.Hom.comp_apply, hr]
  obtain ⟨N, hN, hsec⟩ := hS _ (hcl (x ≫ C.GG.hom) s₀)
  have hrange : Set.range (x ≫ C.GG.hom) ⊆ Set.range N.ι := by
    rintro _ ⟨s, rfl⟩
    rw [hs s, Scheme.Opens.range_ι]
    exact hN
  let t : Sp (kb p) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (x ≫ C.GG.hom) hrange
  have ht : t ≫ N.ι = x ≫ C.GG.hom := IsOpenImmersion.lift_fac _ _ _
  have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = t ≫ N.ι := by rw [Category.assoc, τ.fac, hy, ht]
  have hpb := (L.test p y τ).1
  let c₀ : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H :=
    Over.homMk (hpb.lift x (rPt p ≫ spMap τ.j) (ht.symm.trans e.symm)) (hpb.lift_snd _ _ _)
  have hc₀ : c₀.left ≫ τ.f = x := hpb.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := exists_pushHom (L.test p y τ) _ _ e
  obtain ⟨b, c, hb, hc, h1, h2, h3, h4, h5, h6⟩ := exists_torsion_pair (Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H)
    (fun c => ⊤ ≤ c.left ⁻¹ᵁ Out.nonzeroLocus E.θ) n c₀ (hF p y τ E)
  obtain ⟨b₁, hb₁, hb₂⟩ := hsec p y τ t b hz (ht.trans hy.symm) hb
  obtain ⟨c₁, hc₁, hc₂⟩ := hsec p y τ t c hz (ht.trans hy.symm) hc
  have key : ∀ d : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H, ⊤ ≤ d.left ⁻¹ᵁ Out.nonzeroLocus E.θ →
      Set.range (ρ d).left ⊆ T.Om L := by
    rintro d hd _ ⟨s, rfl⟩
    have := τ.j_loc
    have h0 : τ.H.hom (d.left s) = IsLocalRing.closedPoint τ.V := by
      rw [← Scheme.Hom.comp_apply, Over.w d, hs s]
      exact (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (spMap τ.j) hr).trans (IsLocalRing.comap_closedPoint τ.j))
    rw [hρ]
    exact (Scheme.Hom.comp_apply _ _ _).symm ▸ (hB p y τ E _ h0).2 (hd trivial)
  refine ⟨N, Over.homMk b₁ hb₁, Over.homMk c₁ hc₁, kb p, inferInstance, t, ρ c₀, ρ b, ρ c, ?_,
    (hρ b).trans hb₂.symm, (hρ c).trans hc₂.symm, ?_⟩
  · rw [hρ, hc₀]
    ext v
    exact ⟨fun ⟨s, h⟩ => h ▸ hx s, fun h => ⟨s₀, (hx _).trans h.symm⟩⟩
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, ← map_mul] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [key _ h1, key _ h2, key _ h3, key _ h4, key _ h5, key _ h6]

end GlobalTheory.ZJ
end
