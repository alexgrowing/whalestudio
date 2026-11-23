import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwLatRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem seam_lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) : s.lat (Formalism.HermitianLatticesTheory.gmap g N) = mvL (seamGL s g) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  unfold mvL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formalism.L2.Col.mem_gmap] at hx
    refine ⟨s.vec (g.symm x), (s.mem_lat N _).2 ⟨_, hx, rfl⟩, ?_⟩
    show (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (g.symm x l)) = fun l => s.iE (x l)
    rw [seamGL_mulVec, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    refine ⟨g x0, ?_, ?_⟩
    · rw [Formalism.L2.Col.mem_gmap, LinearEquiv.symm_apply_apply]; exact hx0
    · show (fun l => s.iE (g x0 l)) = (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x0 l))
      rw [seamGL_mulVec]

set_option maxHeartbeats 1000000 in

theorem lat_moved : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a _ _ i hi β x x₁ γ hγ hx g hg p hp
  have e1 : ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
  rw [e1, seam_lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]

end GlobalTheory.TwLatRat

end
