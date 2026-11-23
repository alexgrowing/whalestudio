import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleSpecialFibreExtendedPrincipalPolarisatioStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibresStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ExtAmple

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem relAmple_pullback_of_fac {S S₀ T : Scheme.{0}} [IsAffine S₀] {B : Over S} {A : Over S₀} {L : LB B.left}
    {L₀ : LB A.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) {g : S₀ ⟶ S} {φ : A.left ⟶ B.left}
    (h : IsPullback φ A.hom B.hom g) (e : LBIso L₀ (L.pull φ)) (hA : RelAmple A L₀) (y : T ⟶ S₀) :
    RelAmple ((Over.pullback (y ≫ g)).obj B) (L.pull (pullback.fst B.hom (y ≫ g))) := by
  let ψ : pullback B.hom (y ≫ g) ⟶ A.left :=
    h.lift (pullback.fst B.hom (y ≫ g)) (pullback.snd B.hom (y ≫ g) ≫ y) (by rw [Category.assoc]; exact pullback.condition)
  have hψ : ψ ≫ φ = pullback.fst B.hom (y ≫ g) := h.lift_fst _ _ _
  have H : IsPullback ψ (pullback.snd B.hom (y ≫ g)) A.hom y := by
    refine IsPullback.of_right ?_ (h.lift_snd _ _ _) h
    rw [hψ]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨w, hw⟩ : LBIso (L.pull (pullback.fst B.hom (y ≫ g))) (L₀.pull ψ) :=
    LBIso.chartPull
      (chartPullSame L (fun _ : PUnit => pullback.fst B.hom (y ≫ g)) (fun _ => φ) (fun _ => 1) ψ fun _ => hψ.symm)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L₀ _ _ rfl) (LBIso.symm e)
  exact relAmple_pull (A' := (Over.pullback (y ≫ g)).obj B) H hL₀ (pull_isLB hL _)
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA

theorem fac_or_fac (V K k : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] [Field k] (f : V →+* k) :
    (∃ g : K →+* k, f = g.comp (algebraMap V K)) ∨
      ∃ g : IsLocalRing.ResidueField V →+* k, f = g.comp (IsLocalRing.residue V) := by
  by_cases hf : RingHom.ker f = ⊥
  · have hi : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f).2 hf
    exact Or.inl ⟨IsFractionRing.lift hi, RingHom.ext fun x => (IsFractionRing.lift_algebraMap hi x).symm⟩
  · have hm : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hf
    have he := IsLocalRing.eq_maximalIdeal hm
    exact Or.inr ⟨Ideal.Quotient.lift _ f (fun a ha => by rw [← he] at ha; exact ha), RingHom.ext fun x => rfl⟩

theorem relAmple_extension : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → IsAdicComplete (IsLocalRing.maximalIdeal V) V → RelAmple B M.L.L := by
  intro h₁ h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ e hc
  refine GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres h₁ h₂ V hc B hB M fun k _ x => ?_
  obtain ⟨f, rfl⟩ := Spec.map_surjective x
  rcases fac_or_fac V K k f.hom with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hx : Spec.map f = spMap g ≫ spMap (algebraMap V K) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac M.L.isLB P.isLB hφ.1 e P.ample _
  · have hx : Spec.map f = spMap g ≫ spMap (IsLocalRing.residue V) := by
      rw [← Spec.map_comp]; congr 1; exact CommRingCat.hom_ext hg
    rw [hx]
    exact relAmple_pullback_of_fac (A := (Over.pullback (spMap (IsLocalRing.residue V))).obj B) M.L.isLB
      (pull_isLB M.L.isLB _) (IsPullback.of_hasPullback _ _) (lbIso_self (pull_isLB M.L.isLB _))
      (GlobalTheory.T.relAmple_specialFibre_extended_principalPolarisation h₁ h₂ V K P B M φ hB hφ e hc) _

end GlobalTheory.ExtAmple
