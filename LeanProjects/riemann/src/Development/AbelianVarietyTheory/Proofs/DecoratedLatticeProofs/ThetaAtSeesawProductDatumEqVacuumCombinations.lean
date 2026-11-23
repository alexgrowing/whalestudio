import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulEqZeroOfNePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSplitPlacesSchrodingerModelSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorSplitPlaceLatticeIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnitsStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.VecProd

section Gen
variable {D : D7}

theorem isHalf_add_iff {a b : AE D} (hab : b * a = 0) {m n : ℕ} (t : Mx D m n) :
    IsHalf (a + b) t ↔ IsHalf b (t - t.map (fun x => a * x)) := by
  constructor
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply]
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero]
    linear_combination h1
  · intro h i j
    have h1 := h i j
    simp only [Matrix.sub_apply, Matrix.map_apply] at h1
    rw [mul_sub, ← mul_assoc, hab, zero_mul, sub_zero] at h1
    linear_combination h1

theorem isHalf_zero_iff {m n : ℕ} (t : Mx D m n) : IsHalf (0 : AE D) t ↔ t = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := h i j
    rw [zero_mul] at h1
    simpa using h1.symm
  · rintro rfl i j
    simp

theorem half_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {w : Mx D m n} (hw : IsHalf a w) :
    IsHalf (b + a) w := by
  intro i j
  have h : b * w i j = 0 := by rw [← hw i j, ← mul_assoc, hab, zero_mul]
  rw [add_mul, h, zero_add, hw i j]

theorem half_conj_add_of_right {a b : AE D} (hab : b * a = 0) {m n : ℕ} {y : Mx D m n} (hy : IsHalf (cA D a) y) :
    IsHalf (cA D (b + a)) y := by
  intro i j
  have h : cA D b * y i j = 0 := by rw [← hy i j, ← mul_assoc, ← map_mul, hab, map_zero, zero_mul]
  rw [map_add, add_mul, h, zero_add, hy i j]

theorem symplO_sub {S T : HSp D} (x w y : WO S T) :
    symplO S T (x - w) y = symplO S T x y - symplO S T w y := by
  have h : hO S T (x - w) y = hO S T x y - hO S T w y := by
    simp only [hO, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  unfold symplO
  rw [h, mul_sub, map_sub]

theorem hO_zero' {S T : HSp D} {a b : AE D} (hab : b * a = 0) {w y : WO S T} (hw : IsHalf a w)
    (hy : IsHalf (cA D b) y) : hO S T w y = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  have h1 : cA D (y c j) = b * cA D (y c j) := by
    conv_lhs => rw [← hy c j, map_mul, Formalism.L2.Theta.cA_cA]
  rw [h1, ← hw d i]
  linear_combination (incA D (S.gram⁻¹ i j) * cA D (y c j) * incA D (T.gram c d) * w d i) * hab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem down_sub_mul (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) {a : AE D}
    (ha : a * p.e = 0) (t : WO S T) :
    p.down FS FT (t - t.map (fun x => a * x)) = p.down FS FT t := by
  have h0 : p.π a = 0 := TOneModel.pi_of_mul p ha
  unfold Place.down
  have h : (t - t.map (fun x => a * x) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    ext i j
    simp [Matrix.map_apply, map_sub, map_mul, h0]
  rw [h]

theorem up_add (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x y : Matrix Y Y' k) :
    p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply, map_add]

theorem down_up (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have h : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := by
    ext i j
    simp [Matrix.map_apply, p.π_ι]
  rw [h]
  calc FT.γ * (FT.β * x * FS.γ) * FS.β = (FT.γ * FT.β) * x * (FS.γ * FS.β) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [FT.γβ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem tensorAt_shift (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Φ : WO S T → ℂ)
    (Ψ : Matrix Y Y' k → ℂ) (x : Matrix Y Y' k) :
    p.tensorAt FS FT Φ (fun t => Ψ (t + x)) = fun t => p.tensorAt FS FT Φ Ψ (t + p.up FS FT x) := by
  funext t
  simp only [Place.tensorAt]
  rw [Witness.down_add p FS FT t (p.up FS FT x), down_up, up_add]
  congr 2
  abel

theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) {e : AE D} (he : e * p.e = 0) (Φ : WO S T → ℂ)
    (hΦ : ∀ t, Φ t ≠ 0 → IsHalf e t) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D p.e) y) :
    p.tensorAt FS FT Φ (fun t => ψ (symplO S T (p.up FS FT t) y) * Ψ t) =
      fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
  · simp [h0]
  · have hh := hΦ _ h0
    have hz : symplO S T (t - p.up FS FT (p.down FS FT t)) y = 0 := by
      unfold symplO
      rw [hO_zero' (a := e) (b := p.e) (by rw [mul_comm]; exact he) hh hy, mul_zero, map_zero]
    have hs := symplO_sub t (p.up FS FT (p.down FS FT t)) y
    rw [hz] at hs
    have h2 : symplO S T t y = symplO S T (p.up FS FT (p.down FS FT t)) y := by linear_combination -hs
    rw [h2]
    ring

theorem tensorL_isModel (ψ : AddChar (AF D.host.F) ℂ) (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) (e : AE D) (he : e * p.e = 0) (Λ : AddSubgroup (WO S T))
    (Φ : WO S T → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → IsHalf e t) (f₀ : WO S T → ℂ)
    (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) Λ 1 f₀ T')
    (hθ : ∀ Φ', IsSBHalf (e + p.e) Λ Φ' → IsThetaFunO ψ S T (T' Φ'))
    (hsb : ∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) Λ (p.tensorAt FS FT Φ Ψ)) :
    p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  refine ⟨fun Ψ => hθ _ (hsb Ψ.1 Ψ.2), fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · have hfun : (Ψ' : Matrix Y Y' k → ℂ) = fun t => (Ψ : Matrix Y Y' k → ℂ) (t + x) := funext h
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [hfun, tensorAt_shift]
    exact hT.trans _ (hsb Ψ.1 Ψ.2) _ (half_add_of_right he (Witness.up_half p FS FT x))
  · have hfun : (Ψ' : Matrix Y Y' k → ℂ) = fun t => ψ (symplO S T (p.up FS FT t) y) * (Ψ : Matrix Y Y' k → ℂ) t :=
      funext h
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [hfun, tensorAt_modul p ψ FS FT he Φ hΦ _ hy]
    exact hT.modul _ (hsb Ψ.1 Ψ.2) _ (half_conj_add_of_right he hy)

end Gen

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fam
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem orth_succ {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v)
    (i : Fin n) : (L 0).q.e * (L i.succ).q.e = 0 :=
  GlobalTheory.T.splitPlaceIdempotent_mul_eq_zero_of_ne_place D _ _ (L 0).q (L i.succ).q fun h => Fin.succ_ne_zero i (hinj h).symm

theorem orth_sum {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) :
    (∑ i : Fin n, (L i.succ).q.e) * (L 0).q.e = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact orth_succ L hinj i

theorem prodDat_zero (L : Fin 0 → LocPl ψ S T M M') (Λ : AddSubgroup (WO S T)) :
    prodDat L = halfInd (0 : AE D) Λ := by
  funext x
  unfold prodDat halfInd
  have hs : (∑ i, (L i).q.e) = 0 := Fin.sum_univ_zero _
  by_cases hx : x = 0
  · subst hx
    have h1 : IsHalf (∑ i, (L i).q.e) (0 : WO S T) := by rw [hs]; exact (isHalf_zero_iff _).2 rfl
    rw [if_pos h1, if_pos ⟨Λ.zero_mem, (isHalf_zero_iff _).2 rfl⟩, Fin.prod_univ_zero]
  · have h1 : ¬ IsHalf (∑ i, (L i).q.e) x := by rw [hs]; exact fun h => hx ((isHalf_zero_iff _).1 h)
    rw [if_neg h1, if_neg (fun h => hx ((isHalf_zero_iff _).1 h.2))]

theorem prodDat_succ {n : ℕ} (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) :
    prodDat L = (ofSplit (L 0).q).tensorAt (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ) (L 0).Φ.1 := by
  funext t
  have hup := TOneModel.up_down_eq (ofSplit (L 0).q) (L 0).FS (L 0).FT t
  have hpe : (ofSplit (L 0).q).e = (L 0).q.e := rfl
  simp only [prodDat, Place.tensorAt]
  rw [hup, hpe]
  have hd : ∀ i : Fin n, (ofSplit (L i.succ).q).down (L i.succ).FS (L i.succ).FT
      (t - t.map (fun a => (L 0).q.e * a)) = (ofSplit (L i.succ).q).down (L i.succ).FS (L i.succ).FT t :=
    fun i => down_sub_mul _ _ _ (orth_succ L hinj i) t
  simp only [hd]
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  have hiff := isHalf_add_iff (a := (L 0).q.e) (b := ∑ i : Fin n, (L i.succ).q.e) (orth_sum L hinj) t
  by_cases h : IsHalf ((L 0).q.e + ∑ i : Fin n, (L i.succ).q.e) t
  · rw [if_pos h, if_pos (hiff.1 h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), zero_mul]

theorem halfInd_zero_isSBHalf (Λ : AddSubgroup (WO S T)) : IsSBHalf (0 : AE D) Λ (halfInd 0 Λ) := by
  refine ⟨fun t h => ?_, 1, one_pos, fun u _ hh t => ?_, fun t h => ?_⟩
  · by_contra hc
    exact h (by simp [halfInd, hc])
  · rw [(isHalf_zero_iff u).1 hh]
    simp
  · rw [one_smul]
    by_contra hc
    exact h (by simp [halfInd, hc])

theorem prodDat_isSBHalf (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (n : ℕ) :
    ∀ (L : Fin n → LocPl ψ S T M M'), Function.Injective (fun i => (L i).q.v) →
      IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (prodDat L) := by
  induction n with
  | zero =>
    intro L _
    rw [prodDat_zero L (latO S T (M : Set _) (M' : Set _) fun _ => True)]
    simpa using halfInd_zero_isSBHalf (D := D) (latO S T (M : Set _) (M' : Set _) fun _ => True)
  | succ n ih =>
    intro L hinj
    rw [prodDat_succ L hinj, Fin.sum_univ_succ, add_comm]
    exact GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' (L 0) _ (orth_sum L hinj) _
      (ih (fun i => L i.succ) (hinj.comp (Fin.succ_injective n))) _ (L 0).Φ.2

end Fam

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Core
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem step (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') {n : ℕ}
    (L : Fin (n+1) → LocPl ψ S T M M') (hinj : Function.Injective fun i => (L i).q.v) (f₀ : WO S T → ℂ)
    (hf₀ : Vac ψ S T M M' (fun _ => True) f₀) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T') :
    ∃ Tm : SB (Matrix (L 0).Y (L 0).Y' (L 0).k) →ₗ[ℂ] (WO S T → ℂ),
      (ofSplit (L 0).q).IsModel ψ (L 0).FS (L 0).FT Tm ∧ Tm (L 0).Φ = T' (prodDat L) ∧
      ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
        IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i : Fin n, (L i.succ).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧
        ∀ Φ₀ : SB (Matrix (L 0).Y (L 0).Y' (L 0).k),
          (Φ₀ : Matrix (L 0).Y (L 0).Y' (L 0).k → ℂ) = Set.indicator {x | (ofSplit (L 0).q).up (L 0).FS (L 0).FT x ∈
            latO S T (M : Set _) (M' : Set _) (· = (L 0).q.v)} (fun _ => 1) →
          Tm Φ₀ = T'' (prodDat fun i : Fin n => L i.succ) := by
  have horth := orth_sum L hinj
  have hsum : ∑ i, (L i).q.e = (∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e := by
    rw [Fin.sum_univ_succ, add_comm]
  have hT2 := hT
  rw [hsum] at hT2
  have hθ : ∀ Φ', IsSBHalf ((∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ' →
      IsThetaFunO ψ S T (T' Φ') := by
    intro Φ' h
    rw [← hsum] at h
    exact GlobalTheory.T.isThetaFunO_splitPlaces_schrodingerModel_sum D ψ hψ S T M M' hM hM' (n+1) L hinj f₀ T' hf₀ hT Φ' h
  have hsbL := prodDat_isSBHalf hM hM' n (fun i => L i.succ) (hinj.comp (Fin.succ_injective n))
  have hsb : ∀ Ψ ∈ SB (Matrix (L 0).Y (L 0).Y' (L 0).k), IsSBHalf ((∑ i : Fin n, (L i.succ).q.e) + (L 0).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True)
      ((ofSplit (L 0).q).tensorAt (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ) Ψ) :=
    fun Ψ hΨ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' (L 0) _ horth _ hsbL Ψ hΨ
  have hmodel := tensorL_isModel (ofSplit (L 0).q) ψ (L 0).FS (L 0).FT _ horth _
    (prodDat fun i : Fin n => L i.succ) hsbL.1 f₀ T' hT2 hθ hsb
  obtain ⟨T'', hT'', hT''eq⟩ := GlobalTheory.T.isPlaceModel_tensor_splitPlaceLatticeIndicator D ψ S T M M' hM hM' (L 0) _ horth f₀ T' hT2
  refine ⟨T' ∘ₗ (ofSplit (L 0).q).tensorL (L 0).FS (L 0).FT (prodDat fun i : Fin n => L i.succ), hmodel, ?_,
    T'', hT'', ?_⟩
  · rw [LinearMap.comp_apply, Place.tensorL_apply, prodDat_succ L hinj]
  · intro Φ₀ hΦ₀
    rw [LinearMap.comp_apply, Place.tensorL_apply, hΦ₀, hT''eq]

theorem isOne_intInd (P : LocPl ψ S T M M') :
    IsOne (⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩ : SB (Matrix P.Y P.Y' P.k)) := rfl

theorem core (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (f₀ : WO S T → ℂ)
    (hf₀ : Vac ψ S T M M' (fun _ => True) f₀) (n : ℕ) :
    ∀ (L : Fin n → LocPl ψ S T M M'), Function.Injective (fun i => (L i).q.v) →
      ∀ T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
        IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' →
        T' (prodDat L) = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) f₀ := by
  induction n with
  | zero =>
    intro L _ T' hT
    rw [prodDat_zero L (latO S T (M : Set _) (M' : Set _) fun _ => True)]
    have h := hT.vac
    rw [Fin.sum_univ_zero, one_smul] at h
    rw [h]
    rfl
  | succ n ih =>
    intro L hinj T' hT
    obtain ⟨Tm, hTm, hTmΦ, T'', hT'', hT''eq⟩ := step hψ hM hM' L hinj f₀ hf₀ T' hT
    have h1 := (L 0).e_is.2 Tm hTm _ (L 0).Φ (isOne_intInd (L 0)) rfl
    have h2 := (L 0).o_is Tm hTm ⟨_, GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' (L 0)⟩ _ (isOne_intInd (L 0)) rfl
    have h3 := hT''eq ⟨_, GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' (L 0)⟩ rfl
    rw [← hTmΦ, h1, h2, h3, ih _ (hinj.comp (Fin.succ_injective n)) T'' hT'', List.finRange_succ,
      List.foldr_cons, List.foldr_map]

end Core

end GlobalTheory.VecProd

namespace GlobalTheory.VecProd

section Fin2
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : Lat S} {M' : Lat T}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  have h0 : ∀ w : WO S T, symplOH S T w 0 = 0 := fun w => by simp [symplOH, symplO, hO]
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp only [heisO, add_zero, h0, AddChar.map_zero_eq_one, one_mul]

noncomputable def oneLoc (P : LocPl ψ S T M M') : LocPl ψ S T M M' where
  k := P.k
  q := P.q
  unit := P.unit
  Y := P.Y
  Y' := P.Y'
  FS := P.FS
  FT := P.FT
  Φ := ⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩
  e := Finsupp.single 0 1
  e_is := by
    refine ⟨fun u hu => ?_, fun Tm _ Φ₀ Φ h0 hΦ => ?_⟩
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      intro i j
      simp
    · rw [comb_single_zero]
      congr 1
      exact Subtype.ext (hΦ.trans h0.symm)
  o := P.o
  o_at := P.o_at
  o_is := P.o_is

theorem oneLoc_e (P : LocPl ψ S T M M') : (oneLoc P).e = Finsupp.single 0 1 := rfl
theorem oneLoc_o (P : LocPl ψ S T M M') : (oneLoc P).o = P.o := rfl

theorem prodDat_perm {n : ℕ} (L : Fin n → LocPl ψ S T M M') (σ : Equiv.Perm (Fin n)) :
    prodDat (fun i => L (σ i)) = prodDat L := by
  funext x
  unfold prodDat
  rw [Equiv.sum_comp σ (fun i => (L i).q.e),
    Equiv.prod_comp σ (fun i => (L i).Φ.1 ((ofSplit (L i).q).down (L i).FS (L i).FT x))]

theorem vac_at_of_model (hψ : IsStdChar D ψ (-1)) (P : LocPl ψ S T M M') (N : Lat S) (N' : Lat T)
    (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') (hI : IntIn P.q S P.FS N ∧ IntIn P.q T P.FT N')
    (g : WO S T → ℂ) (Tm : SB (Matrix P.Y P.Y' P.k) →ₗ[ℂ] (WO S T → ℂ))
    (hTm : (ofSplit P.q).IsModel ψ P.FS P.FT Tm)
    (hg : Tm ⟨Place.intInd P.Y P.Y', Place.intInd_mem_SB _ _ _⟩ = g) : Vac ψ S T N N' (· = P.q.v) g := by
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.T.exists_splitPoint_weilChar_conductor_one_of_units D P.k P.q ψ hψ P.unit
  have h := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D P.k P.q P.unit P.Y P.Y' S T P.FS P.FT ψ ψk hψ hch hcond N N' hN hN' hI.1 hI.2).1
    Tm _ hTm (isOne_intInd P)
  rwa [hg] at h

end Fin2

theorem thetaAt_prodDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ f₀ f, Vac ψ S T M M' (fun _ => True) f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ (prodDat L) f → IsThetaFunO ψ S T f → f = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) f₀ ∧ ∀ (N : Lat S) (N' : Lat T), IsSelfDualC S N → IsSelfDualC T N' → (∀ i, IntIn (L i).q S (L i).FS N ∧ IntIn (L i).q T (L i).FT N') → (∀ p, (∀ i, p ≠ (L i).q.v) → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → Vac ψ S T N N' (fun _ => True) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
  intro D ψ hψ S T M M' hM hM' n L hinj f₀ f hf₀ hθ _
  obtain ⟨⟨T', hT'⟩, hall⟩ := hθ
  have hcore := core hψ hM hM' f₀ hf₀
  refine ⟨(hall T' hT').trans (hcore n L hinj T' hT'), fun N N' hN hN' hI hV => ?_⟩

  have hg1 : T' (prodDat fun i => oneLoc (L i)) =
      (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀ := by
    rw [hcore n (fun i => oneLoc (L i)) hinj T' hT']
    simp only [oneLoc_e, oneLoc_o, comb_single_zero]

  have hloc : ∀ j : Fin n, Vac ψ S T N N' (· = (L j).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    intro j
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.pos; omega⟩
    let L1 : Fin (m+1) → LocPl ψ S T M M' := fun i => oneLoc (L i)
    let σ : Equiv.Perm (Fin (m+1)) := Equiv.swap 0 j
    have hinjσ : Function.Injective fun i => (L1 (σ i)).q.v := hinj.comp σ.injective
    have hTσ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L1 (σ i)).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' := by
      rw [Equiv.sum_comp σ (fun i => (L1 i).q.e)]
      exact hT'
    obtain ⟨Tm, hTm, hTmΦ, -⟩ := step hψ hM hM' (fun i => L1 (σ i)) hinjσ f₀ hf₀ T' hTσ
    have hval : Tm (L1 (σ 0)).Φ = (List.finRange (m+1)).foldr (fun i g => comb ψ S T (L i).o g) f₀ := by
      rw [hTmΦ, prodDat_perm L1 σ]
      exact hg1
    have hv := vac_at_of_model hψ (L1 (σ 0)) N N' hN hN' (hI (σ 0)) _ Tm hTm hval
    have h0 : σ 0 = j := Equiv.swap_apply_left _ _
    have hq : (L1 (σ 0)).q.v = (L j).q.v := by rw [h0]; rfl
    rw [hq] at hv
    exact hv

  have hQc : Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    have hbase : Vac ψ S T M M' (fun p => ∀ i, p ≠ (L i).q.v) f₀ := by
      have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T (fun p => ∀ i, p ≠ (L i).q.v) (fun p => ∃ i, p = (L i).q.v)
        (fun p hp ⟨i, hi⟩ => hp i hi)).2.2.2.2 M M' f₀ hM hM'
      have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i, p = (L i).q.v) = fun _ => True := by
        funext p
        apply propext
        constructor
        · intro _
          trivial
        · intro _
          by_cases h : ∃ i, p = (L i).q.v
          · exact Or.inr h
          · exact Or.inl fun i hi => h ⟨i, hi⟩
      rw [hfun] at hiff
      exact (hiff.1 hf₀).1
    have hbaseN : Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v) f₀ := by
      refine ⟨hbase.1, ?_⟩
      rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ hV]
      exact hbase.2
    have hl : ∀ l : List (Fin n), Vac ψ S T N N' (fun p => ∀ i, p ≠ (L i).q.v)
        (l.foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
      intro l
      induction l with
      | nil => exact hbaseN
      | cons i l ih =>
        rw [List.foldr_cons]
        have hdisj : ∀ p, p = (L i).q.v → ¬ ∀ i', p ≠ (L i').q.v := fun p hp h => h i hp
        have hc : CombAt (· = (L i).q.v) (L i).o := fun u hu => GlobalTheory.T.matrixSupported_splitPlace_of_isHalf_conjSum D _ (L i).q u ((L i).o_at u hu)
        exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = (L i).q.v) _ hdisj).2.1 _ hc).2 N N' _ ih
    exact hl _

  have hstep : ∀ j : ℕ, j ≤ n → Vac ψ S T N N' (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v)
      ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < 0 ∧ p = (L i).q.v) =
          fun p => ∀ i, p ≠ (L i).q.v := by
        funext p
        simp
      rw [hfun]
      exact hQc
    | succ j ih =>
      intro hj
      have hj' : j < n := hj
      let jj : Fin n := ⟨j, hj'⟩
      have hdisj : ∀ p, ((∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v) → ¬ (p = (L jj).q.v) := by
        rintro p (h | ⟨i, hi, rfl⟩) hp
        · exact h jj hp
        · have h2 : i = jj := hinj hp
          rw [h2] at hi
          exact lt_irrefl _ hi
      have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).2.2.2.2 N N'
        ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) f₀) hN hN'
      have hfun : (fun p => ((∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j ∧ p = (L i).q.v) ∨ p = (L jj).q.v) =
          fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < j + 1 ∧ p = (L i).q.v := by
        funext p
        apply propext
        constructor
        · rintro ((h | ⟨i, hi, h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, h⟩
          · exact Or.inr ⟨jj, by simp [jj], h⟩
        · rintro (h | ⟨i, hi, h⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
            · exact Or.inl (Or.inr ⟨i, hi, h⟩)
            · exact Or.inr (by rw [h, show i = jj from Fin.ext hi])
      rw [hfun] at hiff
      exact hiff.2 ⟨ih (by omega), hloc jj⟩
  have hfin := hstep n le_rfl
  have hfun : (fun p => (∀ i, p ≠ (L i).q.v) ∨ ∃ i : Fin n, i.val < n ∧ p = (L i).q.v) = fun _ => True := by
    funext p
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      by_cases h : ∃ i, p = (L i).q.v
      · obtain ⟨i, hi⟩ := h
        exact Or.inr ⟨i, i.isLt, hi⟩
      · exact Or.inl fun i hi => h ⟨i, hi⟩
  rw [hfun] at hfin
  exact hfin

end GlobalTheory.VecProd

end
