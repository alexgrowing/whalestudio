import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_clopen_kerStableAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  haveI : IsMonHom ψ := hq.1
  haveI : IsMonHom ψ' := hq.2.1
  haveI := D.finO
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := D.O)
  have key : ∀ a : D.O, ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y),
      Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A,
        g ^ c = 1 → g ≫ ψ = 1 → g ≫ o.act.act a ≫ ψ = 1 := by
    intro a
    haveI := o.act.hom a
    obtain ⟨W, hW1, hW2, hW, -⟩ := GlobalTheory.LevCover.kerlocus_open_closed Y o.A c Unit (fun _ => B) (fun _ => ψ) B
      (o.act.act a ≫ ψ) o.ab (fun _ => hB) hB (fun _ => inferInstance) inferInstance hc
    refine ⟨W, hW1, hW2, fun Tb t => (hW Tb t).trans ?_⟩
    simp only [forall_const]
  choose W hW1 hW2 hW using key
  have hkill : ∀ (T : Over Y) (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    have h1 : g ^ c = g ≫ (𝟙 o.A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, ← hq.2.2.1, ← Category.assoc, hg, MonObj.one_comp]
  refine ⟨⋂ a ∈ S, W a, isOpen_biInter_finset (fun a _ => hW1 a),
    isClosed_iInter fun a => isClosed_iInter fun _ => hW2 a, fun Tb t => ?_⟩
  rw [Set.subset_iInter₂_iff]
  constructor
  · intro h T σ hσ g hg a
    let f : D.O →+ Additive (T ⟶ B) := AddMonoidHom.mk' (fun a => Additive.ofMul (g ≫ o.act.act a ≫ ψ))
      (fun a a' => by
        rw [o.act.add]
        haveI := o.act.hom a
        haveI := o.act.hom a'
        rw [MonObj.mul_comp, MonObj.comp_mul]
        rfl)
    have hSk : (S : Set D.O) ⊆ (f.toIntLinearMap.ker : Set D.O) := fun a ha => by
      have := (hW a Tb t).1 (h a ha) T σ hσ g (hkill T g hg) hg
      simp [f, this]
    have htop : (⊤ : Submodule ℤ D.O) ≤ LinearMap.ker f.toIntLinearMap := by
      rw [← hS]; exact Submodule.span_le.mpr hSk
    have ha : f a = 0 := htop Submodule.mem_top
    simpa [f] using ha
  · intro h a _
    exact (hW a Tb t).2 fun T σ hσ g _ hg => h T σ hσ g hg a

end GlobalTheory.UPel.HT.ES
