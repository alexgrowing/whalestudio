import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImplocusOpenClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem clopenCond_comp_eq_one {Y : Scheme.{0}} (Zt B : Over Y) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : IsUnit (n : Γ(Y, ⊤))) (g : Zt ⟶ B) (hg : g ^ n = 1) :
    ClopenCond Zt (fun _ z => z ≫ g = 1) := by
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  obtain ⟨u, hu, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n g hg
  obtain ⟨u', hu', -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B n (1 : Zt ⟶ B) (one_pow n)
  refine (clopenCond_eq u u').congr fun T z => ⟨fun h => ?_, fun h => ?_⟩
  · have hz : (z ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion B n (z ≫ g) hz).unique ?_ ?_
    · rw [Category.assoc, hu]
    · rw [Category.assoc, hu', MonObj.comp_one, h]
  · rw [← hu, ← Category.assoc, h, Category.assoc, hu', MonObj.comp_one]

theorem kerlocus_open_closed : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  intro Y A _ _ n J _ B _ f B' _ f' hA hB hB' hf hf' hn
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  have hι : torsion.ι A n ^ n = 1 := GlobalTheory.LatticeTorsion.torsionι_pow_eq_one A n
  have hpow : ∀ (C : Over Y) [GrpObj C] (g : A ⟶ C) [IsMonHom g], (torsion.ι A n ≫ g) ^ n = 1 := by
    intro C _ g _
    rw [← MonObj.pow_comp, hι, MonObj.one_comp]
  obtain ⟨W, hWo, hWc, H1, H2⟩ := implocus_open_closed Y (torsion A n)
    (fun _ z => ∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) (fun _ z => z ≫ (torsion.ι A n ≫ f') = 1) hfin het
    (ClopenCond.forall_finite fun i =>
      clopenCond_comp_eq_one _ (B i) (hB i) n hn _ (hpow (B i) (f i)))
    (clopenCond_comp_eq_one _ B' hB' n hn _ (hpow B' f'))
  have key : ∀ T : Over Y, (∀ z : T ⟶ torsion A n, (∀ i, z ≫ (torsion.ι A n ≫ f i) = 1) →
      z ≫ (torsion.ι A n ≫ f') = 1) ↔
      ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
    intro T
    constructor
    · intro H a ha hfa
      obtain ⟨z, hz, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A n a ha
      have h := H z (fun i => by rw [← Category.assoc, hz, hfa i])
      rwa [← Category.assoc, hz] at h
    · intro H z hz
      have h := H (z ≫ torsion.ι A n) (by rw [← MonObj.comp_pow, hι, MonObj.comp_one])
        (fun i => by rw [Category.assoc]; exact hz i)
      rwa [Category.assoc] at h
  refine ⟨W, hWo, hWc, fun Tb t => (H1 Tb t).trans ?_, fun k _ _ x => (H2 k x).trans (key _)⟩
  exact forall_congr' fun T => forall_congr' fun σ => forall_congr' fun _ => key T

end GlobalTheory.LevCover
