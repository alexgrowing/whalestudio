import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.PtCoverPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sec_of {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ S k) (hf : Etale f)
    (hs : Surjective f) : ∃ s : S k ⟶ Y, s ≫ f = 𝟙 _ := by
  have hmem : Sieve.generate (Presieve.singleton f) ∈ Scheme.etaleTopology (S k) := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨y, rfl⟩ := hs.surj u
    exact ⟨Y, f, y, hf, rfl, ⟨Y, 𝟙 Y, f, Presieve.singleton.mk, Category.id_comp f⟩⟩
  obtain ⟨Z, h, g, hg, hcomp⟩ := PtCover_of k _ hmem
  cases hg
  exact ⟨h, hcomp⟩

theorem ptVanT_holds : PtVanT := by
  intro hIn k _ _ q n i hn
  have hzero : ∀ x : Ht q (sch.obj (S k)) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hIn.a5 (ZMod q) (S k) (tw q i) n hn x
    obtain ⟨s, hsf⟩ := sec_of f hf hs
    calc x = pull (ZMod q) (𝟙 (sch.obj (S k))) (tw q i) n x := (pull_id _ _ _ _ x).symm
      _ = pull (ZMod q) (sch.map s ≫ sch.map f) (tw q i) n x := by
        rw [← CategoryTheory.Functor.map_comp, hsf, CategoryTheory.Functor.map_id]
      _ = pull (ZMod q) (sch.map s) (tw q i) n (pull (ZMod q) (sch.map f) (tw q i) n x) :=
        pull_comp _ _ _ _ _ x
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end UpperTheory.Gal.KunnethLefschetz
