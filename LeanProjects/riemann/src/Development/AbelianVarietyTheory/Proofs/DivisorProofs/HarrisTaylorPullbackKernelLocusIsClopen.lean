import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem isMonHom_id_npow {Y : Scheme.{0}} (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  have h := Grp.Hom.hom_hom_zpow (G := Grp.mk A) (H := Grp.mk A) (𝟙 _) (n : ℤ)
  have h' : IsMonHom ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (n : ℤ)).hom.hom := inferInstance
  rw [h, zpow_natCast] at h'
  exact h'

theorem polKer_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, hc⟩ hB hq
  have hpY : IsUnit ((p : ℕ) : Γ(Y, ⊤)) := by
    have := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  have hn : IsUnit ((c ^ 3 : ℕ) : Γ(Y, ⊤)) := by
    rw [hc, ← pow_mul, Nat.cast_pow]
    exact hpY.pow _
  obtain ⟨C, _, Q, h, hC, -, -, hh, -, hT⟩ := GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom p D R b N Y s o B ψ' hB hq.2.1
  haveI := isMonHom_id_npow B c
  have hcomp : ∀ {T : Over Y} (x : T ⟶ B), x ≫ (𝟙 B) ^ c = x ^ c := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨W₁, o₁, c₁, H₁, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => C) (fun _ => h) B ((𝟙 B) ^ c) hB
    (fun _ => hC) hB (fun _ => hh) inferInstance hn
  obtain ⟨W₂, o₂, c₂, H₂, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => B) (fun _ => (𝟙 B) ^ c) C h hB
    (fun _ => hB) hC (fun _ => inferInstance) hh hn
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t => ?_⟩
  rw [Set.subset_inter_iff, H₁, H₂]
  constructor
  · rintro ⟨h₁, h₂⟩ T σ hσ x hx
    rw [hT]
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · rw [← hcomp]; exact h₁ T σ hσ x hx fun _ => hx'
    · exact h₂ T σ hσ x hx fun _ => by rw [hcomp]; exact hx'
  · intro H
    refine ⟨fun T σ hσ x hx hx' => ?_, fun T σ hσ x hx hx' => ?_⟩
    · rw [hcomp]; exact ((H T σ hσ x hx).1 ((hT T x).2 (hx' ())))
    · exact (hT T x).1 ((H T σ hσ x hx).2 (by rw [← hcomp]; exact hx' ()))

end GlobalTheory.UPel.HT.ES
