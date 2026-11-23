import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.RigCmpPf

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    eSec G' ≫ F = f ≫ eSec G := (cubeMapOf h).e_comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def upt (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {e : ℕ} {Z : Scheme.{0}}
    (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) : Z ⟶ (thickObj R I e G).left :=
  a ≫ eSec (thickObj R I e G)

omit [IsDomain R] [IsCommMonObj G] in
theorem eSec_fst (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ (fstG I e G).left = (a ≫ thick R I e) ≫ eSec G :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (UnitValue.eSec_pullback_fst (thick R I e) G)).trans
    (Category.assoc _ _ _).symm)

theorem eSec_pG {e : ℕ} (g : GtCoord I D e G) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ g.pG.left = (a ≫ thick R I e) ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (η[thickObj R I e G] ≫ g.q) = η[thickObj R I e D.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) := congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_fst (G := D.P.A) e a)
  unfold upt
  rw [← h2]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)

theorem rig_val (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (z : Z) {JG : (Z ⟶ G.left) → U.P.L.L.ι} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJG : Good U.P.L.L z JG)
    (hJ : Good D.P.L z J) :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw (U.w e) (upt G a) z (J ((upt G a) ≫ (U.gt e).pG.left))
          (fun _ => JG ((upt G a) ≫ (fstG I e G).left)) *
        val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z JG := by
  have h := (U.w_vals e (Over.mk a) z JG J hJG hJ _ (fun _ => rfl)).1
  rw [one_left] at h
  exact h

theorem rig_level {V : Type} [CommRing V] [IsDomain V] {I' : Ideal V} {D' : DegPre V}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (a' : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (ha : a ≫ thick R I e = (a' ≫ thick V I' e) ≫ spMap φ) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw C.v (upt G' a' ≫ (U'.gt e).pG.left) z (J (upt G a ≫ (U.gt e).pG.left))
          (J' (upt G' a' ≫ (U'.gt e).pG.left)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (a' ≫ thick V I' e) z J' := by
  have hG := eSec_comm C.pb
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨K', hK'⟩ := exists_good_pt U'.P.L.isLB z
  have e₁ := rig_val U e a z hK hJ
  have e₂ := rig_val U' e a' z hK' hJ'
  have e₃ := (C.wL_map.vals (Over.mk (a' ≫ thick V I' e)) z K' K hK' hK _ (fun _ => rfl)).1
  rw [one_left] at e₃
  have hx : upt G a ≫ (fstG I e G).left = (upt G' a' ≫ (fstG I' e G').left) ≫ F := by
    rw [eSec_fst e a, eSec_fst e a', ha]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hG.symm).trans (Category.assoc _ _ _).symm)
  have e₄ := ((C.lev e _ _ _ (hx.trans (Category.assoc _ _ _))).2 z J J' hJ hJ').2 _ _
    (hK (upt G a ≫ (fstG I e G).left)) (hK' (upt G' a' ≫ (fstG I' e G').left))
  have f₃ : val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z K =
      gw C.wL (upt G' a' ≫ (fstG I' e G').left) z (K (upt G a ≫ (fstG I e G).left))
        (K' (upt G' a' ≫ (fstG I' e G').left)) *
      val (L := U'.P.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) U'.P.L.rig
        (a' ≫ thick V I' e) z K' := by
    rw [ha, hx, eSec_fst e a']
    exact e₃
  exact e₁.trans ((congrArg _ f₃).trans ((_root_.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄.symm).trans ((_root_.mul_assoc _ _ _).trans (congrArg _ e₂.symm)))))

end GlobalTheory.RigCmpPf

namespace GlobalTheory

open RigCmpPf in

theorem rigCmp_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  intro R V _ _ _ _ _ _ I I' φ hI' hφ D D' A G _ _ A' G' _ _ U U' F C
  have hB := eSec_comm C.pbB
  have key := AbelianPartIso.pmaps_of_thickenings hI' D.P.isLB D'.P.isLB C.v C.v_gen (eSec D'.P.A)
    (spMap φ ≫ eSec D.P.A) hB D'.rig D'.rig_gen
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (spMap φ))
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) fun e z p q hp hq => by
      have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono hφ _
      let a : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
        spMap (Ideal.quotientMap _ φ hle)
      have ha : a ≫ thick R I e = (𝟙 _ ≫ thick V I' e) ≫ spMap φ := by
        rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : Unit => thick V I' e ≫ spMap φ ≫ eSec D.P.A)
        (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (fun _ : Unit => thick V I' e ≫ eSec D'.P.A)
        (fun _ => q) (fun _ _ _ => rfl) (fun _ => hq)
      have E := rig_level C e a (𝟙 _) ha z hJ hJ'
      have hp' : (a ≫ thick R I e) ≫ eSec D.P.A = thick V I' e ≫ spMap φ ≫ eSec D.P.A := by
        rw [ha, Category.id_comp]
        exact Category.assoc _ _ _
      rw [eSec_pG (U.gt e) a, eSec_pG (U'.gt e) (𝟙 _), hp', ha, Category.id_comp, eJ (), eJ' (),
        val_of _ _ z J (fun _ => p) (fun _ => (congrArg J (Category.assoc _ _ _)).trans (eJ ())),
        val_of _ _ z J' (fun _ => q) (fun _ => eJ' ())] at E
      refine Eq.trans ?_ E
      have m₁ : thick V I' e z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      have m₂ : spMap φ (thick V I' e z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      exact (gm_res _ z _ m₁ _).trans (gm_pull _ (spMap φ) z _ m₂ _)
  intro Z r z p q hp hq
  have hm : (spMap φ ≫ eSec D.P.A) (r z) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun g => g (r z) ∈ D.P.L.U (p PUnit.unit)) hB).mp (hp PUnit.unit)
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have m₁ : r z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  have m₂ : spMap φ (r z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  exact ((gm_res r z _ m₁ _).trans (gm_pull r (spMap φ) z _ m₂ _)).symm

end GlobalTheory
end
