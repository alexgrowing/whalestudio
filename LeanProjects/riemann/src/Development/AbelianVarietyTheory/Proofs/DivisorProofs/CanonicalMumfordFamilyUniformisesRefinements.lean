import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinementIsFactorBaseChangeCanonicalMumfordFamiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonFam

theorem gm_iso {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (hp : x ∈ B.U p.1 ⊓ A.U p.2) (hq : x ∈ B.U q.1 ⊓ A.U q.2) :
    gm (𝟙 X) x _ (w.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (w.s q) := by
  have hm : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨hp, hq⟩
  have e := congrArg (gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2))) (hw p q)
  exact (gm_res _ x _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) x p q hm) (gm_res _ x _ hm _))))

theorem lbIso_trans {X : Scheme.{0}} {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨w', hw'⟩ := H'

  have cself : ∀ (x : X) (r : C.ι) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      gm (𝟙 X) x (C.U r ⊓ C.U r) (C.g r r) = 1 := by
    intro x r p hr hp
    have e := gm_iso hw' x (r, p) (r, p) ⟨hr, hp⟩ ⟨hr, hp⟩
    rw [gm_self hB (𝟙 X) x hp, inv_one, _root_.mul_one] at e
    exact mul_eq_right.1 e.symm
  have glue : ∀ (r : C.ι) (i : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U i)ˣ, ∀ (x : X) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      x ∈ A.U i → gm (𝟙 X) x _ s = gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := by
    intro r i
    let W : B.ι → X.Opens := fun p => C.U r ⊓ B.U p ⊓ A.U i
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U i := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => hx.1
    have l₂ : ∀ p, W p ≤ B.U p ⊓ A.U i := fun p x hx => ⟨hx.1.2, hx.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₁ p) (w'.s (r, p)) * res (l₂ p) (w.s (p, i))
    have hu : ∀ (x : X) (p : B.ι) (hx : x ∈ W p), gm (𝟙 X) x (W p) (u p) =
        gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := fun x p hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x (l₁ p) hx _) (gm_res _ x (l₂ p) hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U r ⊓ A.U i) W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, ⟨⟨hx.1, hp⟩, hx.2⟩⟩) u (fun p p' x hx => by
        rw [hu x p hx.1, hu x p' hx.2]
        have hr : x ∈ C.U r := hx.1.1.1
        have hp : x ∈ B.U p := hx.1.1.2
        have hp' : x ∈ B.U p' := hx.2.1.2
        have hi : x ∈ A.U i := hx.1.2
        rw [gm_iso hw' x (r, p) (r, p') ⟨hr, hp⟩ ⟨hr, hp'⟩, gm_iso hw x (p, i) (p', i) ⟨hp, hi⟩ ⟨hp', hi⟩]
        simp only []
        rw [cself x r p hr hp, gm_self hA (𝟙 X) x hi, inv_one]
        simp only [_root_.one_mul, _root_.mul_one]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun x p hr hp hi => ?_⟩
    have hx : x ∈ W p := ⟨⟨hr, hp⟩, hi⟩
    exact (gm_res _ x (l₀ p) hx s).symm.trans ((congrArg (gm (𝟙 X) x (W p)) (hs p)).trans (hu x p hx))
  choose s hs using glue
  refine ⟨⟨fun q => s q.1 q.2⟩, fun q q' => unit_ext fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have hr : x ∈ C.U q.1 := hx.1.1
  have hi : x ∈ A.U q.2 := hx.1.2
  have hr' : x ∈ C.U q'.1 := hx.2.1
  have hi' : x ∈ A.U q'.2 := hx.2.2
  have hm : (𝟙 X : X ⟶ X) x ∈ C.U q.1 ⊓ A.U q.2 ⊓ (C.U q'.1 ⊓ A.U q'.2) := hx
  refine (gm_res _ x _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C (𝟙 X) x q q' hm) (gm_res _ x _ hx _))).symm)
  show gm (𝟙 X) x _ (s q.1 q.2) = _ * _ * gm (𝟙 X) x _ (s q'.1 q'.2)
  rw [hs q.1 q.2 x p hr hp hi, hs q'.1 q'.2 x p hr' hp hi',
    gm_iso hw' x (q.1, p) (q'.1, p) ⟨hr, hp⟩ ⟨hr', hp⟩, gm_iso hw x (p, q.2) (p, q'.2) ⟨hp, hi⟩ ⟨hp, hi'⟩]
  simp only []
  rw [gm_self hB (𝟙 X) x hp, inv_one]
  simp only [_root_.one_mul, _root_.mul_one]
  ac_rfl

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

end GlobalTheory.Mum.CanonFam

open GlobalTheory.Mum.CanonFam in

theorem GlobalTheory.Mum.CanonFam.exists_unif_refines : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro R _ _ _ hR Q G _ _ P hG hC R' _ _ _ ρ hR' hinj hfin D ε hRef
  obtain ⟨D', F, hF, A', G', _, _, U', oA, oG, G₁, _, _, inc, pr, π, π₂, hG', hlin, hG₁, hinc, hpr, hip, hpi, hpb, hsq,
    hlb⟩ := GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily R hR Q G P hG hC R' ρ hR' hinj hfin D ε hRef
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data R' (base_of_isCN hR') D D' F hF A' G' hG' U' oA oG hlin G₁ hG₁ inc pr hinc hpr hip hpi
  refine ⟨G₁, inferInstance, inferInstance, π, π₂, A, U, hpb, hsq, ?_⟩
  have l1 : (abelian₂ G₁ U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have l2 : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  exact lbIso_trans l1 (pull_isLB l2 _) hU hlb
