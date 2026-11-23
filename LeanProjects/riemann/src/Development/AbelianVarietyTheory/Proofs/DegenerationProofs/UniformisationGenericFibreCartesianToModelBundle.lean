import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.GenericFibre

theorem exists_iso_section {X₁ X₂ Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {g : Y ⟶ X₁} {f : Y ⟶ X₂} (i : X₁ ⟶ Y)
    (hi : i ≫ g = 𝟙 X₁) (w₀ : LB.Iso (L₁.pull g) (L₂.pull f)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso L₁ (L₂.pull (i ≫ f)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
  have pt : ∀ x : X₁, g (i x) = x := fun x => congrArg (fun q : X₁ ⟶ X₁ => q x) hi
  have le : ∀ p : (PUnit → L₂.ι) × L₁.ι, (L₂.pull (i ≫ f)).U p.1 ⊓ L₁.U p.2 ≤
      i ⁻¹ᵁ ((L₂.pull f).U p.1 ⊓ (L₁.pull g).U (fun _ => p.2)) := fun p y hy =>
    ⟨mem_pull.2 ((mem_pull (F := i ≫ f)).1 hy.1), mem_pull.2 (by rw [pt]; exact hy.2)⟩
  let w : LB.Iso L₁ (L₂.pull (i ≫ f)) := ⟨fun p => res (le p) (pullU i _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
    intro Z r z j k hj hk
    have hm : r z ∈ (L₂.pull (i ≫ f)).U (fun _ => j) ⊓ L₁.U k := ⟨(mem_pull (F := i ≫ f)).2 hj, hk⟩
    exact (gm_res r z (le (fun _ => j, k)) hm _).trans (gm_pull r i z _ (le (fun _ => j, k) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, key⟩
  rw [key Z r z j k hj hk, key Z r z j' k' hj' hk',
    BoxExpansion.pw_trans hw (r ≫ i) z (j₁ := k) (j₁' := k') (j₂ := j) (j₂' := j')
      (by show g (i (r z)) ∈ _; rw [pt]; exact hk) (by show g (i (r z)) ∈ _; rw [pt]; exact hk') hj hj',
    Category.assoc, Category.assoc, hi, Category.comp_id]

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ z J, Good L z J → sval s' (𝟙 _) z J = sval s h z J := by
  subst e
  exact ⟨pullSec L φ ε s h, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_isoData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  intro R _ _ I D A G _ _ U
  obtain ⟨w₀, hw₀⟩ := U.ext
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hi' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨w, hw, key⟩ := exists_iso_section U.gen.inv.left hi w₀ hw₀
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK R)
  have hp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨ρ, hρ, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw U.LG.isLB A.isLB (ρ₀ := U.LG.rig) U.LG.rigGen
  refine ⟨w₀, ρ, w, hp, ⟨hw₀, hρ, fun z JA JG hA hG => ?_⟩, hw, hr, fun F _ _ k σ th H => ?_⟩
  · have e₁ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
      (cubeMapOf hp₁).e_comm.trans (Category.id_comp _)
    have e₂ : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G :=
      (cubeMapOf hp₂).e_comm
    have := hr _ (𝟙 _) z JG JA hG hA
    rw [Category.id_comp, Category.id_comp, wVal, key _ _ _ _ _ (hG (eSec A.A ≫ _ ≫ _)) (hA _), ← Category.assoc, e₁, e₂] at this
    exact this.symm
  · obtain ⟨σ', hσ⟩ := exists_pull_sec σ (UnifPre.gFK (G := G) F) (fun _ : Fin 1 => UnifPre.gFK (G := G) F)
      (funext fun _ => (Category.comp_id _).symm)
    have e : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    refine ⟨σ', hσ, fun s hs => ⟨σ', BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e (Category.id_comp _)
      fun y J₁ J₂ h₁ h₂ => ?_, hs⟩⟩
    have e' : ((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [e, Category.assoc, hi', Category.comp_id]
    have := H _ (U.genF F).left y J₂ J₁ h₂ h₁
    rw [wVal, key _ _ _ _ _ (h₂ (((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ _ ≫ _)) (h₁ _),
      ← Category.assoc, ← Category.assoc, e', e, zpow_natCast] at this
    exact (hσ y J₂ h₂).trans this

end GlobalTheory.Ex.GenericFibre
end
