import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AePolynomialNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSectionsCotangentIndepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDimStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplexStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem goodStalks_structureModule {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} {d : ℕ}
    (t : Fin d → L.Sec) (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) (h : CotIndep t) :
    GoodStalks (structureModule X) t := by
  intro x i hx
  have := hreg x
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.weakly_regular_of_cotangent_indep (X.presheaf.stalk x) d (fun j => germSec (t j) hx) (hdim x)
    (h x i hx)
  have e : ((structureModule X).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    structureModuleStalkEquiv x
  refine ⟨(LinearEquiv.isWeaklyRegular_congr e _).2 h₁, ?_⟩
  set I := Ideal.span (Set.range fun j => germSec (t j) hx) with hI
  have hmap : (I • (⊤ : Submodule (X.presheaf.stalk x) ((structureModule X).presheaf.stalk x :))).map
      e.toLinearMap = I := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective,
      smul_eq_mul, Ideal.mul_top]
  rw [(Submodule.Quotient.equiv _ I e hmap).length_eq]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNum_eq_ncard {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K X)) {L : LB X} (hL : L.IsLB) (d : ℕ) :
    ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists K F → suppDim F ≤ (d : ℕ) →
      ∀ t : Fin d → L.Sec, GoodStalks F t →
        interNum K F (fun _ : Fin d => L) =
            ((support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}).ncard : ℤ) ∧
          ∀ x ∈ support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}, IsClosed ({x} : Set X) := by
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF hd t hg
    have hlen : ∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1 := by
      intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
      have h := (hg x i hi).2
      have e : Ideal.span (Set.range fun j : Fin 0 => germSec (t j) hi) = ⊥ := by simp
      rw [e, Submodule.bot_smul] at h
      rwa [(Submodule.quotEquivOfEqBot _ rfl).length_eq] at h
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.euler_char_zero_dim_support hp F hd hlen
    have e : support F ∩ {x | ∀ j : Fin 0, x ∉ nonzeroLocus (t j)} = support F := by simp
    rw [e, interNum_of_isEmpty]
    exact ⟨h₁, h₂⟩
  | succ d ih =>
    intro F _ hF hd t hg
    have hg' : GoodStalks F (Fin.cons (t 0) (Fin.tail t) : Fin (d + 1) → L.Sec) := by
      rwa [Fin.cons_self_tail]
    obtain ⟨hm, hc⟩ := GlobalTheory.T.hyperplane_cut_good_stalks hL F (t 0) (Fin.tail t) hg'
    have e : (fun _ : Fin (d + 1) => L) = Fin.cons L (fun _ : Fin d => L) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hS : support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)} =
        support (cut F hL (t 0)) ∩ {x | ∀ j, x ∉ nonzeroLocus (Fin.tail t j)} := by
      rw [support_cut]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Fin.forall_fin_succ, Fin.tail]
      tauto
    rw [e, interNum_cons_eq_interNum_cut hL (t 0) (fun _ => hL) hF, hS]
    exact ih (cut F hL (t 0)) (FiniteCohTwists.cut hL _ hF) (suppDim_cut_le F hL (t 0) hd) _ hc

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem secVal_comb (Y : Var ℂ) (L : LB Y.X) {n : ℕ} (c : Fin n → ℂ) (b : Fin n → L.Sec) (i : L.ι)
    (y : CxPts Y.str (RingHom.id ℂ)) :
    secVal Y.str (RingHom.id ℂ) (∑ j, algebraMap ℂ Γ(Y.X, ⊤) (c j) • b j) i y =
      ∑ j, c j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
  have e : ∀ a : ℂ, algebraMap ℂ Γ(Y.X, ⊤) a = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str ⊤ a := fun a => by
    rw [← GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact (GlobalTheory.GeomConnConst.algX_top_strHom ℂ Y.X a).symm
  simp only [e, map_sum, secVal_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem koszul_count : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  intro Y Δ L r hL n b hb hP
  obtain ⟨Q, hQ, hC⟩ := GlobalTheory.T.generic_sections_cotangent_indep Y L hL n Y.dim b hb
  filter_upwards [GlobalTheory.T.ae_polynomial_nonvanishing _ _ Q hQ] with C hCQ
  have hct := hC C hCQ
  set t : Fin Y.dim → L.Sec := fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j with ht
  have hp : IsProjOver (strHom ℂ Y.X) := by
    rw [GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact Y.isProjOver
  have hg : GoodStalks (structureModule Y.X) t :=
    goodStalks_structureModule t (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).1) (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).2) hct
  obtain ⟨h₁, h₂⟩ := interNum_eq_ncard hp hL Y.dim (structureModule Y.X)
    (Y.isAmple_projective_O_one.finiteCohTwists Y.algebraMap_Γ _)
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq]) t hg
  rw [support_structureModule, Set.univ_inter] at h₁ h₂
  have hset : {y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι),
      y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0} =
      {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ {x | ∀ j, x ∉ nonzeroLocus (t j)}} := by
    ext y
    simp only [Set.mem_setOf_eq]
    have key : ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        (∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 ↔
          y.1 (IsLocalRing.closedPoint ℂ) ∉ nonzeroLocus (t k)) := fun k i hi => by
      rw [← secVal_comb Y L (C k) b i y, ← mem_ptsIn, ← secVal_ne_zero_iff (t k) hi, not_not]
    constructor
    · intro h k
      obtain ⟨i, hi⟩ := exists_mem_ptsIn hL.cover y
      exact (key k i hi).1 (h k i hi)
    · intro h k i hi
      exact (key k i hi).2 (h k)
  rw [hset, GlobalTheory.T.closed_points_count_complex Y _ h₂, ← h₁]
  exact (Var.inter_eq_of_toPic_eq (fun _ => hL) (fun _ => hP.toPic_eq)).symm

end GlobalTheory.CompanionTheory.KoszulCount
