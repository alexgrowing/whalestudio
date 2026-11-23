import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RatPtsEquiv

theorem rat_equiv : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), ∃ r : ↥(GQ V) ≃* ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))), ∀ γ, finM V hn γ.1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1).1 := by
  intro D V n hn
  subst hn
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro δ
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let φ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))) →* ↥(GQ V) :=
    { toFun := fun δ => ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        exact map_one (bc (incA D))
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext
        exact map_mul (bc (incA D)) a.1 b.1 }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h1 : (bc (incA D) a.1 : GL (Fin V.rank) _) = bc (incA D) b.1 := congrArg (fun x => x.1.1) h
      apply Subtype.ext; apply Units.ext
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) h1
      exact hinj this
    · intro γ
      obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 γ.2
      exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩
  refine ⟨(MulEquiv.ofBijective φ hφ).symm, fun γ => ?_⟩
  set δ := (MulEquiv.ofBijective φ hφ).symm γ with hδ
  have hγ : γ = φ δ := by
    rw [hδ]; exact ((MulEquiv.ofBijective φ hφ).apply_symm_apply γ).symm
  rw [hγ]
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  rfl

end GlobalTheory.RatPtsEquiv
