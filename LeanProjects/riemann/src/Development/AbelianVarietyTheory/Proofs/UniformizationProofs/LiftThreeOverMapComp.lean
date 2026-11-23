import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.SeparatedSymmetricModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPreCompare

section General

variable {X₁ X₂ Y Y₁ Y₂ T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂}
  {K : Type} [Fintype K]

def wv (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ := gw w r z p (fun _ => q)

def Carries (w : LB.Iso (L.pull a) (M.pull b)) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {φ₁ : K → (Y₁ ⟶ X₁)} (s : LB.Gen (LB.LinComb L φ₁ ε)) (f₁ : T ⟶ Y₁)
    {φ₂ : K → (Y₂ ⟶ X₂)} (t : LB.Gen (LB.LinComb M φ₂ ε)) (f₂ : T ⟶ Y₂) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι), (∀ k, b (ψ k (r z)) ∈ M.U (p k)) →
    (∀ k, a (ψ k (r z)) ∈ L.U (q k)) →
    gm (r ≫ f₂) z (LB.wchart M φ₂ p) (t.s p) =
      (∏ k, wv w (r ≫ ψ k) z (p k) (q k) ^ ε k) * gm (r ≫ f₁) z (LB.wchart L φ₁ q) (s.s q)

variable {w : LB.Iso (L.pull a) (M.pull b)} {ψ : K → (T ⟶ Y)} {ε : K → ℤ}
  {φ₁ : K → (Y₁ ⟶ X₁)} {s : LB.Gen (LB.LinComb L φ₁ ε)} {f₁ : T ⟶ Y₁}
  {φ₂ : K → (Y₂ ⟶ X₂)} {t : LB.Gen (LB.LinComb M φ₂ ε)} {f₂ : T ⟶ Y₂}

theorem Carries.comp (H : Carries w ψ ε s f₁ t f₂) {T' : Scheme.{0}} (h : T' ⟶ T) {ψ' : K → (T' ⟶ Y)}
    {g₁ : T' ⟶ Y₁} {g₂ : T' ⟶ Y₂} (e : ∀ k, ψ' k = h ≫ ψ k) (e₁ : g₁ = h ≫ f₁) (e₂ : g₂ = h ≫ f₂) :
    Carries w ψ' ε s g₁ t g₂ := by
  obtain rfl : ψ' = fun k => h ≫ ψ k := funext e
  subst e₁ e₂
  intro Z r z p q hp hq
  simpa only [Category.assoc] using H Z (r ≫ h) z p q hp hq

theorem Carries.congr {a' : Y ⟶ X₁} {b' : Y ⟶ X₂} {w' : LB.Iso (L.pull a') (M.pull b')} (ha : a = a') (hb : b = b')
    (hw : HEq w w') : Carries w ψ ε s f₁ t f₂ ↔ Carries w' ψ ε s f₁ t f₂ := by
  subst ha hb
  rw [eq_of_heq hw]

end General

section Rigid

variable {X X' T Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_ratio {M : LB X} (cov : ∀ x, ∃ j, x ∈ M.U j) {t t' : LB.Gen M} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι), r z ∈ M.U j →
      gm r z _ (t.s j) = gm r z ⊤ u * gm r z _ (t'.s j) := by
  obtain ⟨u, hu⟩ := glue_unit ⊤ M.U (fun _ => le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (cov x))
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, GtCoordCompare.gm_gen ht (𝟙 X) x hx.1 hx.2,
        GtCoordCompare.gm_gen ht' (𝟙 X) x hx.1 hx.2, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨u, fun Z r z j hj => ?_⟩
  rw [← gm_res r z (le_top : M.U j ≤ ⊤) hj u, hu, map_mul, map_inv, inv_mul_cancel_right]

theorem exists_rigidified (hL : L.IsLB) (hL' : L'.IsLB) (π : X' ⟶ T) (σ : T ⟶ X') (hσ : σ ≫ π = 𝟙 T)
    (w₀ : LB.Iso L' (L.pull F)) (hw₀ : w₀.IsGen) (ρ' : LB.Gen (L'.pull σ)) (hρ' : ρ'.IsGen) {φ : Y ⟶ X}
    (ρ : LB.Gen (L.pull φ)) (hρ : ρ.IsGen) (h : T ⟶ Y) (e : σ ≫ F = h ≫ φ) :
    ∃ w : LB.Iso L' (L.pull F), w.IsGen ∧ PMaps w (K := PUnit) (fun _ => σ) (fun _ => φ) (fun _ => 1) ρ' ρ h := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w₀).1 hw₀) hL hL' ρ' hρ'
  have ex : ∀ g : T ⟶ X, g = h ≫ φ → ∃ t' : LB.Gen (L.pull g), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p,
      r z ∈ (L.pull g).U p → gm r z _ (t'.s p) = gm (r ≫ h) z ((L.pull φ).U p) (ρ.s p) := by
    rintro _ rfl
    exact ⟨LB.pullGen L _ _ ρ h, DVR.pullGen_isGen _ _ _ _ hρ h, fun Z r z p hp =>
      (gm_res r z _ hp _).trans (gm_pull r h z _ (mem_pull.2 (mem_pull₂.1 hp)) _)⟩
  obtain ⟨t', ht', hv'⟩ := ex _ e
  obtain ⟨u, hu⟩ := exists_ratio (M := L.pull (σ ≫ F)) (fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL (F (σ x))
    exact ⟨fun _ => j, mem_pull₂.2 hj⟩) ht' ht
  let w : LB.Iso L' (L.pull F) := ⟨fun p => res le_top (pullU π ⊤ u) * w₀.s p⟩
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w r z j k = gm (r ≫ π) z ⊤ u * gw w₀ r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) (GtCoordCompare.gm_res_pull_top r z π
      (V := (L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _ u))
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', (isGen_iff w₀).1 hw₀ Z r z j j' k k' hj hj' hk hk']
    exact mul_left_comm _ _ _
  · have m : r z ∈ (L.pull (σ ≫ F)).U p := mem_pull₂.2 (hp _)
    refine (hv' Z r z p m).symm.trans ((hu Z r z p m).trans ?_)
    refine (congrArg _ (hv Z r z p q m (Set.mem_iInter.2 hq))).trans ?_
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, hw Z (r ≫ σ) z _ _ (hp _) (hq _),
      Category.assoc, hσ, Category.comp_id, _root_.mul_assoc]

end Rigid

section Cube

open GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {S S' : Scheme.{0}} (p : S' ⟶ S) {G : Over S} {H T : Over S'}

end Cube

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ}

structure GtMatch (g : GtCoord I D e G) (j : CanonicalRigidImages.GtIso D I e G) : Prop where
  q : g.q = j.q
  i : g.i = j.i
  t : ∀ χ, HEq (g.t χ) (j.x χ)

theorem Oφ_eq {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G} (h : g.q = j.q) (χ : D.X) :
    D.Oφ g.pG χ = CanonicalRigidImages.oφ D I e j.q χ := by
  rw [← h]
  exact congrArg (fun y => ![y.left, _, _, _]) (_root_.mul_comm g.pG (toUnit _ ≫ D.c χ))

theorem Oinvε_eq : Oinvε = CanonicalRigidImages.oεinv := by decide

variable {LG : RigLB G} {g : GtCoord I D e G} {j : CanonicalRigidImages.GtIso D I e G}
  {w : LB.Iso (LG.L.pull (fstG I e G).left) (D.P.L.pull g.pG.left)}
  {ph : LB.Iso (LG.L.pull (toG I e G).F) (D.P.L.pull (toB j).F)}

end Clauses

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {rA : LB.Gen (A.L.pull (eSec A.A))}

structure Match (u : Out.UnifPre I D A G) (v : SeparatedSymmetricModel.UnifPre R I D A rA G) : Prop where
  gen : v.gen = u.gen.symm
  LG : v.LG = u.LG
  cub : HEq v.cub u.cubG
  sym : HEq v.sym u.symG
  gt : ∀ e, GtMatch (u.gt e) (v.j e)
  w : ∀ e, HEq (u.w e) (v.ph e)

end Main

end GlobalTheory.UnifPreCompare
