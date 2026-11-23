import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem prodRel_map {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (T : ∀ l, (X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, T l (g i l) (y l) = 0 := by
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ (⊤ : Submodule ℂ (X l → ℂ))) ∧
      ∀ u ∈ S.image (fun i => g i l), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.finset_functions_recovered_from_values ⊤ _ (fun _ _ => Submodule.mem_top)
  choose s E _ hE using hkey
  have h1 : ∀ i ∈ S, ∏ l, T l (g i l) (y l) =
      ∑ ξ ∈ Fintype.piFinset s, (∏ l, g i l (ξ l)) * ∏ l, T l (E l (ξ l)) (y l) := by
    intro i hi
    have h2 : ∀ l, T l (g i l) (y l) = ∑ x ∈ s l, g i l x * T l (E l x) (y l) := by
      intro l
      conv_lhs => rw [hE l (g i l) (Finset.mem_image_of_mem _ hi)]
      simp [map_sum, Finset.sum_apply]
    simp only [h2]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i hi, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h ξ, zero_mul]

theorem prodRel_allSome {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, f i l (y l) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  choose T hT using fun l => (hf i₀ hi₀ l).1
  rw [← prodRel_map S x g T h y]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [fun l => (hf i hi l).2 _ (hT l)]

theorem prodRel_allSome₂ {ι κ I : Type} [Fintype ι] [Fintype κ] {X Y : ι → Type} {X' Y' : κ → Type} (S : Finset I) (x : I → ℂ)
    (g : I → ∀ l, X l → ℂ) (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (g' : I → ∀ l, X' l → ℂ) (f' : I → ∀ l, Y' l → ℂ) (Q' : ∀ l, ((X' l → ℂ) →ₗ[ℂ] (Y' l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (hf' : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q' l) fun T => f' i l = T (g' i l))
    (h : ∀ (z : ∀ l, X l) (z' : ∀ l, X' l), ∑ i ∈ S, x i * ((∏ l, g i l (z l)) * ∏ l, g' i l (z' l)) = 0)
    (y : ∀ l, Y l) (y' : ∀ l, Y' l) :
    ∑ i ∈ S, x i * ((∏ l, f i l (y l)) * ∏ l, f' i l (y' l)) = 0 := by
  simp only [← mul_assoc]
  refine prodRel_allSome S (fun i => x i * ∏ l, f i l (y l)) g' f' Q' hf' (fun z' => ?_) y'
  have := prodRel_allSome S (fun i => x i * ∏ l, g' i l (z' l)) g f Q hf (fun z => by
    rw [← h z z']
    exact Finset.sum_congr rfl fun i _ => by ring) y
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem unfolded_eq_of_local_eq : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R Fc _ ch _ _ hcon t e _ τ φ hτ α SA xA F Gd fr fd hA hloc M hM P h u y
  have key := hcon t M hM P h ((SchRow ch.G × SchDown ch.G t) ⊕ α) (τ.support.disjSum SA)
    (Sum.elim (fun d => τ d) fun a => -xA a) (Sum.elim (fun d => d.1) fr) (Sum.elim (fun d => d.2) fd) ?_ ?_ u y
  · rw [Finset.sum_disjSum] at key
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    exact add_neg_eq_zero.mp key
  · intro i hi j
    have hv := (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta
    rcases i with d | a
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hτ d (by simpa using hi)).2 j).2 hv
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hA a (by simpa using hi)).2 j).2 hv
  · intro y v
    refine prodRel_allSome₂ (τ.support.disjSum SA) (Sum.elim (fun d => τ d) fun a => -xA a)
      (Sum.elim (fun d => (φ d).1) F) (Sum.elim (fun d => d.1) fr)
      (fun i => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.G.latS (.chi i D.R.m : Pair T) : Set _)
          (ch.G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.rm.vX i D.R.m))
      (Sum.elim (fun d => (φ d).2) Gd) (Sum.elim (fun d => d.2) fd)
      (fun j => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) (ch.G.latS (.mu t D.R.m j : Pair T) : Set _)
          (ch.G.latT (.mu t D.R.m j : Pair T) : Set _) fun _ => True) 1 (ch.rm.vT D.R.m j)) ?_ ?_ ?_ y v
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).1 l).2
      · exact ((hA a (by simpa using hi)).1 l).2
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).2 l).2
      · exact ((hA a (by simpa using hi)).2 l).2
    · intro z z'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← mul_assoc]
      exact add_neg_eq_zero.mpr (hloc z z')

end GlobalTheory.LocAsm
