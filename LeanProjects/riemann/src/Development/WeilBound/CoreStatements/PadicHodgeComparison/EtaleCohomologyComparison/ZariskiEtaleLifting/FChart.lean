import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

abbrev ChI (A : Type) : Type := {S : Set A // S.Nonempty}

def chPi {C : Type u} [Category.{v} C] {A : Type} (Q : A → C → Prop)
    (hQ : ∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') (hA : ∀ T, ∃ α, Q α T) : C ⥤ ChI A where
  obj T := ⟨{α | Q α T}, hA T⟩
  map f := homOfLE (show _ ≤ _ from fun α h => hQ α f h)

def chPhi {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hm : ∀ T, S.1 ⊆ (P.obj (ι.obj T)).1) : C₁ ⥤ StructuredArrow S P :=
  Functor.toStructuredArrow ι S P (fun T => homOfLE (show S ≤ _ from hm T)) (fun _ => Subsingleton.elim _ _)

lemma chPhi_equiv {C : Type u} [Category.{v} C] {C₁ : Type u'} [Category.{v'} C₁] {A : Type} (P : C ⥤ ChI A)
    (S : ChI A) (ι : C₁ ⥤ C) (hO : Onto ι (fun T => S.1 ⊆ (P.obj T).1)) :
    (chPhi P S ι hO.mem).IsEquivalence := by
  have := hO.full
  have := hO.faithful
  have : (chPhi P S ι hO.mem).Full :=
    ⟨fun {X Y} f => ⟨ι.preimage f.right, StructuredArrow.hom_ext _ _ (ι.map_preimage f.right)⟩⟩
  have : (chPhi P S ι hO.mem).Faithful :=
    ⟨fun {X Y} f g h => ι.map_injective (congrArg (fun k => CommaMorphism.right k) h)⟩
  have : (chPhi P S ι hO.mem).EssSurj := ⟨fun X => by
    obtain ⟨T₁, ⟨e⟩⟩ := hO.ess X.right (leOfHom X.hom)
    exact ⟨T₁, ⟨StructuredArrow.isoMk e (Subsingleton.elim _ _)⟩⟩⟩
  exact {}

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.chart : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → (∀ T, ∃ α, Q α T) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hA hS
  let π := chPi Q hQ hA
  have key : ∀ S : ChI A, RI s (n + 1) (StructuredArrow.proj S π ⋙ F) (StructuredArrow.pre S G π) := by
    intro S
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S.1 S.2
    have hO2 : Onto ι (fun T => S.1 ⊆ (π.obj T).1) := hO
    have hO2' : Onto ι' (fun T => S.1 ⊆ ((G ⋙ π).obj T).1) := hO'
    let Φ := chPhi π S ι hO2.mem
    let Φ' := chPhi (G ⋙ π) S ι' hO2'.mem
    let X := StructuredArrow.proj S π ⋙ F
    have h1 : RI 1 (n + 1) X Φ := (P.ri_calc X Φ (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv π S ι hO2)
    have h2 : RI s (n + 1) (Φ ⋙ X) G₁ := hR
    have h3 : RI (1 * s) (n + 1) X (G₁ ⋙ Φ) := (P.ri_calc X Φ G₁ 1 s (n + 1)).1 h1 h2
    have iso : G₁ ⋙ Φ ≅ Φ' ⋙ StructuredArrow.pre S G π :=
      NatIso.ofComponents (fun T => StructuredArrow.isoMk (e.app T) (Subsingleton.elim _ _))
        (fun f => StructuredArrow.hom_ext _ _ (e.hom.naturality f))
    have h4 : RI (1 * s) (n + 1) X (Φ' ⋙ StructuredArrow.pre S G π) :=
      (P.ri_calc X (G₁ ⋙ Φ) (𝟭 _) (1 * s) 1 (n + 1)).2.2.2.2.1 _ iso h3
    have h5 : RI 1 (n + 1) (StructuredArrow.pre S G π ⋙ X) Φ' :=
      (P.ri_calc (StructuredArrow.pre S G π ⋙ X) Φ' (𝟭 _) 1 1 (n + 1)).2.2.2.2.2.1 (chPhi_equiv (G ⋙ π) S ι' hO2')
    have h6 := (P.ri_calc X (StructuredArrow.pre S G π) Φ' 1 (1 * s) (n + 1)).2.2.1 h5 h4
    rwa [one_mul, one_mul] at h6
  intro j hj
  have h := CrystallineSemistableComparison.P.rel π (Mor.restrict F G) s j (fun S q hq => key S q (by omega))
  have he : s ^ (2 * n + 3) = s ^ (2 * j + 3) * s ^ (2 * (n - j)) := by
    rw [← pow_add]; congr 1; omega
  rw [he]
  exact (CrystallineSemistableComparison.P.upTo_alg _ LinearMap.id _ _).2.2.2.1 h
