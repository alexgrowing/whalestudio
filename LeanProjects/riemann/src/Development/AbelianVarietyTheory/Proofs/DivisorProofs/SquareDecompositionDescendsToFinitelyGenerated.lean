import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [Field k] (A₀ : Over (Sp k))

theorem lbIso_lbPow_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {L : LB A₀.left} (hL : L.IsLB) (N : ℕ) :
    LBIso (lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) N)
      ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) N).pull (bcMap A₀.hom ρ)) := by
  have h₁ : LBIso (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hL _ (bcMap_fst A₀.hom ρ).symm
  have hR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow (pull_isLB hR _) N)
    (pull_isLB (isLB_lbPow hR N) _) (lbIso_lbPow h₁ N) (lbIso_lbPow_pull hR _ N)

theorem lbIso_linComb_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {M : LB A₀.left} (hM : M.IsLB) {K : Type} [Fintype K]
    (φS : K → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))))
    (φR : K → (pullback A₀.hom (spMap (algebraMap k R)) ⟶ pullback A₀.hom (spMap (algebraMap k R))))
    (ε : K → ℤ) (hφ : ∀ o, φS o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ φR o) :
    LBIso (LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) φS ε)
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) φR ε).pull (bcMap A₀.hom ρ)) := by
  have hR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have h₁ : LBIso (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hM _ (bcMap_fst A₀.hom ρ).symm
  exact LBIso.trans (LB.isLB_linComb (pull_isLB hM _) _ _) (LB.isLB_linComb (pull_isLB hR _) _ _)
    (pull_isLB (LB.isLB_linComb hR _ _) _) (PelPrim.lbIso_linComb h₁ φS ε)
    (SymExtend.lbIso_linComb_pull hR (bcMap A₀.hom ρ) φS φR ε (bcMap A₀.hom ρ) hφ)

theorem comm_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    (f : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)
    (g : (Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀)
    (h : bcMap A₀.hom ρ ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ g.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, Category.assoc, h]
  · have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
    have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
    rw [Category.assoc, bcMap_snd, ← Category.assoc, hf, Category.assoc, hg, bcMap_snd]

def fam {S : Type} [CommRing S] [Algebra k S] {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)) :
    Option (Fin r) → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))) :=
  fun o => o.elim (𝟙 _) fun i => (β i).left

theorem fam_comm {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀))
    (gam : Fin r → ((Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀))
    (h : ∀ i, bcMap A₀.hom ρ ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _) (o : Option (Fin r)) :
    fam A₀ β o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ fam A₀ gam o := by
  cases o with
  | none => simp [fam]
  | some i => exact comm_bc A₀ ρ (β i) (gam i) (h i)

end GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent GlobalTheory.SqDecSpread in

theorem GlobalTheory.SqDecSpread.sqDec_fg : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀],
    IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω))))
      (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) →
    ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀)
      (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  intro k Ω _ _ _ A₀ _ hA L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have := hA.proper
  have := hA.smooth
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  choose Ri g hRi hg hgeq using fun i => haveI := hβ i; exists_fg_isMonHom (A := A₀) (A' := A₀) (β i)
  let R₁ : Subalgebra k Ω := ⨆ i, Ri i
  have hR₁ : R₁.FG := fg_iSup hRi
  choose gam hgam hgameq using fun i => haveI := hg i; exists_specialise (g i) (Subalgebra.inclusion (le_iSup Ri i))
  have key₁ : ∀ i, bcMap A₀.hom R₁.val ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _ := by
    intro i
    rw [hgameq i, ← Category.assoc, bcMap_comp_of_eq A₀.hom (Subalgebra.inclusion (le_iSup Ri i)) R₁.val (Ri i).val
      (fun _ => rfl), hgeq i]
  have hL₁ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hM₁ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hLΩ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have hMΩ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have H₁ : LBIso ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) N).pull (baseChangeMap A₀.hom R₁.val))
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) (fam A₀ gam) ε).pull
        (baseChangeMap A₀.hom R₁.val)) :=
    LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (isLB_lbPow hLΩ N) (pull_isLB (LB.isLB_linComb hM₁ _ _) _)
      (lbIso_lbPow_bc A₀ R₁.val hL N).symm
      (LBIso.trans (isLB_lbPow hLΩ N) (LB.isLB_linComb hMΩ _ _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) H
        (lbIso_linComb_bc A₀ R₁.val hM (fam A₀ β) (fam A₀ gam) ε (fam_comm A₀ R₁.val β gam key₁)))
  obtain ⟨R, hR, hRfg, H₂⟩ := exists_fg_lbIso A₀.hom hR₁ _ _ (isLB_lbPow hL₁ N) (LB.isLB_linComb hM₁ _ _) H₁
  choose δ hδ hδeq using fun i => haveI := hgam i; exists_specialise (gam i) (Subalgebra.inclusion hR)
  have hLR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have hMR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  refine ⟨R, hRfg, N, a₀, r, a, δ, hN, ha₀, hδ, ?_⟩
  exact LBIso.trans (isLB_lbPow hLR N) (pull_isLB (isLB_lbPow hL₁ N) _) (LB.isLB_linComb hMR _ _)
    (lbIso_lbPow_bc A₀ (Subalgebra.inclusion hR) hL N)
    (LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) (LB.isLB_linComb hMR _ _) H₂
      (lbIso_linComb_bc A₀ (Subalgebra.inclusion hR) hM (fam A₀ δ) (fam A₀ gam) ε
        (fam_comm A₀ (Subalgebra.inclusion hR) δ gam fun i => (hδeq i).symm)).symm)
