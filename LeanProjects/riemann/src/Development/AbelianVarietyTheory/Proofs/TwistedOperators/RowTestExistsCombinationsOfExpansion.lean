import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombsExist

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

set_option maxHeartbeats 1000000 in

theorem exists_comb_model {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D)
    (Φ : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0 ∧ IsHalf (e + cA D e) u) ∧ ∀ f₀ Tm,
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
      comb ψ S T c f₀ = Tm Φ := by
  classical
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf e u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D e) u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨ψ (symplOH S T x y) • Finsupp.single (x + y) 1, fun u hu => ?_, fun f₀ Tm hTm => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hu))]
      have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
      have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have a1 := congrFun (congrFun h1 i) j
        have a2 := congrFun (congrFun h2 i) j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
        rw [RingHom.map_add, a1, a2, add_zero]
      · rw [Matrix.add_apply, mul_add, half1 x ((isHalf_iff S T).2 hx) i j, half2 y ((isHalf_iff S T).2 hy) i j]
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy, GlobalTheory.LocComb.comb_smul, GlobalTheory.LocComb.comb_single]
  | zero => exact ⟨0, by simp, fun f₀ Tm _ => by rw [LinearMap.map_zero]; simp [comb]⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, h1, h2⟩ := hg
    obtain ⟨c', h1', h2'⟩ := hg'
    exact ⟨c + c', fun w hw => (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w), fun f₀ Tm h => by
      rw [LinearMap.map_add, GlobalTheory.LocComb.comb_add, h2 f₀ Tm h, h2' f₀ Tm h]⟩
  | smul a g _ hg =>
    obtain ⟨c, h1, h2⟩ := hg
    exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun f₀ Tm h => by
      rw [LinearMap.map_smul, GlobalTheory.LocComb.comb_smul, h2 f₀ Tm h]⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

theorem exists_isCombOf {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d : FinDatum G t p) : ∃ c, IsCombOf W d c := by
  obtain ⟨c, h1, h2⟩ := exists_comb_model W.ψ _ _ _ _ d.e d.fn W.ψ_std hS hT (idemSum_mul_self d.e_is) d.e_is.2
    (infPart_idemSum d.e_is) d.sb
  exact ⟨c, fun u hu => (h1 u hu).1, fun u hu => (h1 u hu).2, fun f₀ hth hvac =>
    ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1, h2 f₀⟩⟩

theorem exists_isCombs {μ₀ : T} (hL : L.Is μ₀) (τ : PureDat G t →₀ ℂ) : ∃ c, IsCombs W τ c := by
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.top j)) (G.Λ (.top j)) := fun j hj =>
    (G.isV (X := .top j) hj fun _ h => by cases h).sd
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m)) := fun i hi => by
    cases i with
    | zero => exact (colY_isV D T L μ₀ hL D.R.m le_rfl).sd
    | succ i => exact (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun _ h => by cases h).sd
  choose c₁ h₁ using fun (d : PureDat G t) (j : Fin D.R.m) =>
    exists_isCombOf W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d.1 j)
  choose c₂ h₂ using fun (d : PureDat G t) (i : Fin D.R.m) =>
    exists_isCombOf W (p := .chi i D.R.m) (isSelfDualC_neg (sdG (i + 1) i.2)) (sdG i i.2.le) (d.2 i)
  refine ⟨fun d => (fun j => if h : j < D.R.m then c₁ d ⟨j, h⟩ else 0, c₂ d), fun d _ => ⟨fun j => ?_, h₂ d⟩⟩
  dsimp only
  rw [dif_pos j.2]
  exact h₁ d j

theorem combs_exist : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ _ _ _ τ _ => exists_isCombs ch.W s.core.lev τ⟩⟩

end GlobalTheory.CombsExist

end
