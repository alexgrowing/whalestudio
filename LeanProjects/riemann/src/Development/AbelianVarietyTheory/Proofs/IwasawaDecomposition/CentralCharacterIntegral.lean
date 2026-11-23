import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.CenIntAtLoc

open Formalism.L2.DIV

theorem mapCoef_mem_center {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : ∀ a, z * a = a * z) :
    Formalism.MainNotions.PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    have e : MonoidAlgebra.of S G m = MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of R G m) := by
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
    rw [e]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem coeff_mapCoef {R S M : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : MonoidAlgebra R M) (m : M) :
    (Formalism.MainNotions.PairedCharacterCondition.mapCoef f z).coeff m = f (z.coeff m) := by
  simp [Formalism.MainNotions.PairedCharacterCondition.mapCoef]

theorem cenInt_of_allT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G}
    {ψ1 : P1 →* D.what₂.LLˣ} {X0 : BaseLevelRowSide D} {tp : D.what₂.Tup → T} {eG : G ≃* G0g D.nd}
    (h : AllT D A P0 ψ0 P1 ψ1 X0 tp eG) (v : InfinitePlace D.what₂.LL) (hv : Formalism.DivisionValues.IsConjAt v)
    (hpos : ∀ k τ, ((A.fam.L k τ).S.H.map v.embedding).PosDef)
    (hact : ∀ k τ, (A.fam.L k τ).S.ActGood (A.fam.L k τ).r) : GlobalTheory.PendOf.CenInt D := by
  intro i z hz x hx
  have hc := mapCoef_mem_center (Int.castRingHom ℂ) z hz
  have key : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ x ∈ GlobalTheory.EtaJoin.genSet D μ j,
      ∃ y ∈ GlobalTheory.EtaJoin.lat D μ j, D.what₂.jMt μ j y = D.ntypes.cenMt μ j ⟨_, hc⟩ (D.what₂.jMt μ j x) := by
    intro μ j h1 h2 x hx
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
    let a : MonoidAlgebra D.what₂.LL G :=
      MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm (Formalism.MainNotions.PairedCharacterCondition.mapCoef (Int.castRingHom D.what₂.LL) z)
    have hcoef : ∀ g : G, a.coeff g = ((z.coeff (eG g) : ℤ) : D.what₂.LL) := by
      intro g
      simp [a, coeff_mapCoef]
    have ha : ∀ g : G, D.what₂.embLL (a.coeff g) =
        ((⟨_, hc⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g) := by
      intro g
      rw [hcoef g]
      simp [coeff_mapCoef]
    have hcL := mapCoef_mem_center (Int.castRingHom D.what₂.LL) z hz
    have hac : ∀ b, a * b = b * a := by
      intro b
      obtain ⟨b', rfl⟩ := (MonoidAlgebra.mapDomainRingEquiv D.what₂.LL eG.symm).surjective b
      simp only [a, ← map_mul]
      rw [Subalgebra.mem_center_iff.mp hcL b']
    have hint : ∀ t : G, ∃ n : ℤ, a.coeff t = n := fun t => ⟨_, hcoef t⟩
    obtain ⟨-, -, h3⟩ := h.cen μ ⟨_, hc⟩ a ha
    classical
    have h3' := h3 k ((h.eMt k μ).symm x)
    rw [LinearEquiv.apply_symm_apply] at h3'
    obtain ⟨hgen, hlat⟩ := h.latL k μ
    have hx' : (h.eMt k μ).symm x ∈ lNab D A P0 ψ0 k (tp μ) := by
      rw [hlat]
      refine ⟨fun v => if v = D.what₂.jMt μ ((k : ℕ) + 1) x then 1 else 0, ?_⟩
      have hxg : D.what₂.jMt μ ((k : ℕ) + 1) x ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen := hx
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
      rw [Finset.sum_eq_single_of_mem _ hxg]
      · simp
      · intro b _ hb
        simp [hb]
    have hy' := GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms D.what₂.LL v hv (A.fam.L k (tp μ)).S (hpos k (tp μ)) G (A.fam.L k (tp μ)).r (hact k (tp μ))
      (A.fam.lvlA P0 ψ0).P (A.fam.lvlA P0 ψ0).ψ a hac hint _ hx'
    obtain ⟨c, hc'⟩ := (hlat _).mp hy'
    have hsrc : ∀ u : (D.what₂.MtLat μ ((k : ℕ) + 1)).gen, ∃ w, D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ w) = u.1 := by
      intro u
      obtain ⟨w, hw⟩ := hgen u.1 u.2
      exact ⟨w, hw⟩
    choose ws hws using hsrc
    refine ⟨∑ u ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen.attach, c u.1 • h.eMt k μ (ws u), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      show D.what₂.jMt μ ((k : ℕ) + 1) (h.eMt k μ (ws u)) ∈ (D.what₂.MtLat μ ((k : ℕ) + 1)).gen
      rw [hws u]
      exact u.2
    · rw [h3']
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hc'
      rw [hc', map_sum, ← Finset.sum_attach (D.what₂.MtLat μ ((k : ℕ) + 1)).gen]
      refine Finset.sum_congr rfl fun u _ => ?_
      have e1 : c u.1 • h.eMt k μ (ws u) = ((c u.1 : 𝓞 D.what₂.LL) : D.what₂.LL) • h.eMt k μ (ws u) := rfl
      rw [e1, LinearMap.map_smulₛₗ, hws u]
  obtain ⟨y, hy, hyx⟩ := key (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 x hx
  refine ⟨y, hy, ?_⟩
  rw [hyx]
  unfold NTypes.onMt
  rw [dif_pos hc]

end GlobalTheory.CenIntAtLoc

namespace GlobalTheory.CenIntAtLoc

theorem cenInt_at (hL : GlobalTheory.Published.LocalLanglandsGL) :
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.PendOf.CenInt (w.D Z) := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ w Z _ _ t _ _ _ _ _ hR _ => ?_
  obtain ⟨r⟩ := hR
  refine cenInt_of_allT r.all (InfinitePlace.mk (w.st Z).B.embLL) (GlobalTheory.Mem.R3.OkVals.isConjAt_embLL _) (fun k τ => ?_) (fun k τ => ?_)
  · exact (Formalism.L2.Col.mtK_rat _ _ _ τ.1 t.hX ((k : ℕ) + 1)).posH _ _
  · exact Formalism.L2.Col.unipotentActionClassSum_good _ _ _ τ.1 t.hX ((k : ℕ) + 1) _

end GlobalTheory.CenIntAtLoc
