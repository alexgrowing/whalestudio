import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH

theorem exists_sec_pull_of_comp {X Y Z : Scheme.{0}} (L : LB X) (j : Y ⟶ X) (n : Z ⟶ Y) (φ : Z ⟶ X) (e : n ≫ j = φ)
    (σ : LB.Sec (L.pull j)) : ∃ θ : LB.Sec (L.pull φ), ∀ y, n y ∈ nonzeroLocus σ → y ∈ nonzeroLocus θ := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : PUnit => j) (fun _ => 1) σ n, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : y ∈ Z.basicOpen ((n.app _).hom (σ.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  have h₂ : y ∈ (L.pull (n ≫ j)).U k := mem_pull.2 ((mem_pull (F := j)).1 (Y.basicOpen_le _ hk))
  exact (Z.basicOpen_res _ _).ge ⟨h₂, h₁⟩

theorem unif_pullback_of_unif_ring : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → IsOpen (abLocus Q.G) → Q.Ab → Q.LocTheta → HypS Q.G Q.L.L → (∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι))) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus Q.G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj Q.G)], ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj Q.G)), LBIso U.LG.L (Q.L.L.pull (pullback.fst Q.G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Q.G) := by
  intro H o Ω _ _ _ _ S ρ M U₀ Q _ hop hab hth hS hpol R _ _ _ _ hN hI hC ξ hne _
  have h := isGrpPullback_pullback Q.G ξ
  obtain ⟨hL, hr, ⟨c', -⟩, hs⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf h) Q.L Q.cub
  have hrefl : LBIso (Q.L.L.pull (pullback.fst Q.G.hom ξ)) (Q.L.L.pull (pullback.fst Q.G.hom ξ)) :=
    ⟨_, CubePf.idIsoL_isGen hL⟩
  let W₀ : M.Z.Opens := ⟨abLocus Q.G, hop⟩
  let W : (Sp R).Opens := ξ ⁻¹ᵁ W₀
  let G' := (Over.pullback ξ).obj Q.G
  have h₀ := isGrpPullback_pullback Q.G W₀.ι
  have h₁ := isGrpPullback_pullback G' W.ι
  have sq : (ξ ∣_ W₀) ≫ W₀.ι = W.ι ≫ ξ := morphismRestrict_ι ξ W₀
  have h₂ := (h₁.comp h).congr sq.symm rfl
  let ψ : ((Over.pullback W.ι).obj G').left ⟶ ((Over.pullback W₀.ι).obj Q.G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst Q.G.hom W₀.ι = pullback.fst G'.hom W.ι ≫ pullback.fst Q.G.hom ξ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback W.ι).obj G') ((Over.pullback W₀.ι).obj Q.G) (ξ ∣_ W₀) ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hsa := IsSemiAbelian.pullback W₀.ι Q.G Q.semi
  have hA : IsAbelianScheme ((Over.pullback W₀.ι).obj Q.G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := hab.2 W₀ subset_rfl, geomConnected := hsa.geomConnected }
  have hiso : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom ξ)).pull (pullback.fst G'.hom W.ι))
      ((Q.L.L.pull (pullback.fst Q.G.hom W₀.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => pullback.fst G'.hom W.ι) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => (Category.comp_id _).symm)
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => ψ) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => hψ.trans (Category.comp_id _).symm)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB Q.L.isLB (𝟙 _))⟩
  obtain ⟨hA', ha, hk⟩ := GlobalTheory.pol_pull _ _ _ _ _ ψ _ _ (pull_isLB Q.L.isLB _) (pull_isLB hL _) hA h₃ hiso
  obtain ⟨ha₀, hk₀⟩ := hpol W₀ subset_rfl
  have hsp : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G') := by
    obtain ⟨E, hE⟩ := GlobalTheory.ZJ.SplitAll.fieldPoint (G := Q.G) Q.split _ (spMap (IsLocalRing.residue R) ≫ ξ)
    exact ⟨E, isGt_of_iso (pullCompIso _ ξ Q.G) hE⟩
  have hθ' : ∃ θ : LB.Sec (Q.L.L.pull (pullback.fst Q.G.hom ξ)), ∃ x ∈ nonzeroLocus θ,
      G'.hom x = IsLocalRing.closedPoint R := by
    obtain ⟨N, σ, hz, hσ⟩ := hth (ξ (IsLocalRing.closedPoint R))
    have hξ : ξ ⁻¹ᵁ N = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hz
    obtain ⟨n, hn⟩ : ∃ n : G'.left ⟶ (Q.G.hom ⁻¹ᵁ N).toScheme, n ≫ (Q.G.hom ⁻¹ᵁ N).ι = pullback.fst Q.G.hom ξ :=
      ⟨IsOpenImmersion.lift _ (pullback.fst Q.G.hom ξ) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ N) h.1.w).mpr (hξ.ge (Set.mem_univ (G'.hom y)))),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨θ, hθ⟩ := exists_sec_pull_of_comp Q.L.L _ n _ hn σ
    obtain ⟨x, hx, hx'⟩ := hσ _ hz
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback h.1 _ _ hx'
    refine ⟨θ, y, hθ y ?_, hy'⟩
    have e : n y = x := (Q.G.hom ⁻¹ᵁ N).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q y) hn).trans hy)
    rwa [e]
  obtain ⟨D, A, U, hU, hP⟩ := H R hN hI hC G' ((cubeMapOf h).rigLB Q.L hL hr) c' W
    (IsSemiAbelian.pullback ξ Q.G Q.semi) (hs Q.sym)
    (GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.G G' ξ _ Q.L.L _ Q.L.isLB hL h hrefl hS) hsp hθ' hne
    (Set.ext fun x => abLocus_pullback abLocusOne Q.semi h.1 x) hA'.proper
    (ha ha₀) (hk hk₀)
  exact ⟨D, A, U, by rw [hU]; exact hrefl, hP⟩

end GlobalTheory.ZH

end
