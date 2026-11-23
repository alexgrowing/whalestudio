import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SuppTwoOfOffTypeData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl

noncomputable section
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseTiltMove

variable {D : D7}

theorem incA_inj : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective

theorem incA_apply (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem mulVec_latV_of_rat (S : HSp D) (γ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : y ∈ latV S L P) :
    γ.map (incA D) *ᵥ y ∈ latV S M P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, 1, rfl, γ *ᵥ x, hLM x hx, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, incA_apply, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
      ← TensorProduct.tmul_sum]
  | zero => simp only [Matrix.mulVec_zero]; exact (latV S M P).zero_mem
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact (latV S M P).add_mem hu hv
  | neg u _ hu => rw [Matrix.mulVec_neg]; exact (latV S M P).neg_mem hu

theorem exists_rat_of_GQ (S : HSp D) (δ : GA D S) (h : δ ∈ GQ S) :
    ∃ γ : GL (Fin S.rank) D.host.E, mt S δ = γ.val.map (incA D) ∧ mt S δ⁻¹ = (γ⁻¹).val.map (incA D) := by
  obtain ⟨γ, -, hγ⟩ := h
  have e : matHom S δ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ := hγ.symm
  refine ⟨γ, ?_, ?_⟩
  · show (matHom S δ).val = _
    rw [e]; rfl
  · show (matHom S δ⁻¹).val = _
    rw [map_inv, e, ← map_inv]; rfl

theorem moves_of_rat (S : HSp D) (δ : GA D S) (γ γ' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (h : mt S δ = γ.map (incA D)) (h' : mt S δ⁻¹ = γ'.map (incA D)) (L M : Lat S)
    (hLM : ∀ x ∈ L, γ *ᵥ x ∈ M) (hML : ∀ x ∈ M, γ' *ᵥ x ∈ L) (P : Pl D → Prop) : Moves S δ L M P := by
  intro y _
  refine ⟨fun hy => h ▸ mulVec_latV_of_rat S γ L M hLM P y hy, fun hy => ?_⟩
  have e : mt S δ⁻¹ *ᵥ (mt S δ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.FinPl.PlacesAdeles.mt_mul, inv_mul_cancel, GlobalTheory.FinPl.PlacesAdeles.mt_one,
      Matrix.one_mulVec]
  rw [← e, h']
  exact mulVec_latV_of_rat S γ' M L hML P _ hy

theorem moves_of_isFinOf (S : HSp D) {δ b : GA D S} (hb : IsFinOf δ b) (L M : Lat S)
    (h : Moves S δ L M (fun _ => True)) : Moves S b L M (fun _ => True) := by
  obtain ⟨-, a, ha, hab⟩ := hb
  have hb' : b = a⁻¹ * δ := by rw [← hab, inv_mul_cancel_left]
  intro y hy
  have hy' := GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S _ δ hy
  rw [hb', GlobalTheory.FinPl.PlacesAdeles.mt_mul, ← Matrix.mulVec_mulVec,
    GlobalTheory.FinPl.PlacesAdeles.mulVec_off (GlobalTheory.FinPl.SuppTwoAsm.ginf_le_grpOff S _ (inv_mem ha)) hy']
  exact h y hy

theorem moves_one (S : HSp D) (L : Lat S) (P : Pl D → Prop) : Moves S 1 L L P := by
  intro y _
  rw [GlobalTheory.FinPl.PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem sumLat_mulVec {n k c : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (M₀ : Matrix (Fin n) (Fin k) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (a : Matrix (Fin n) (Fin c) D.host.E)
    (𝔟 𝔟' : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (t : Fin c → D.host.E) (hM : γ * M₀ = M₀)
    (ha : γ * a = a * diagonal t) (ht : ∀ p, ∀ u ∈ 𝔟 p, t p * u ∈ 𝔟' p) :
    ∀ x ∈ sumLat M₀ Λ a 𝔟, γ *ᵥ x ∈ sumLat M₀ Λ a 𝔟' := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  refine ⟨y, hy, fun p => t p * u p, fun p => ht p _ (hu p), ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hM, Matrix.mulVec_mulVec, ha, ← Matrix.mulVec_mulVec]
  congr 2
  funext p
  exact Matrix.mulVec_diagonal _ _ _

section Grid

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem lat_grid (j : ℕ) (h1 : 1 ≤ j) (h : j < D.R.m) :
    G.Λ (.grid D.R.m j) = (G.rowDec j h).lat (G.Λ (.top j)) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact G.sp.rowLat j' h

variable {G}

theorem tilt_cols {j : ℕ} (hj : j < D.R.m) (hodd : Odd j) {δ : GA D (G.V (.grid D.R.m j))} (hδ : IsTilt G j δ)
    (γ : Matrix (Fin (G.V (.grid D.R.m j)).rank) (Fin (G.V (.grid D.R.m j)).rank) D.host.E)
    (hγ : mt _ δ = γ.map (incA D)) :
    γ * frameMat _ _ (G.rowDec j hj).ι = frameMat _ _ (G.rowDec j hj).ι ∧
      γ * (G.rowDec j hj).a = (G.rowDec j hj).a * diagonal (GlobalTheory.RowShape.tiltSc D j) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, D.R.m - 1 - j = 2 * σ := by
    obtain ⟨a, ha⟩ := D.R.m_even; obtain ⟨b, hb⟩ := hodd; exact ⟨(D.R.m - 1 - j) / 2, by omega⟩
  obtain ⟨h0, he, he'⟩ := hδ.2.2 σ hj hσ
  rw [hγ, ← Matrix.map_mul] at h0 he he'
  have h0 := Matrix.map_injective incA_inj h0
  have he := Matrix.map_injective incA_inj he
  have he' := Matrix.map_injective incA_inj he'
  refine ⟨h0, Matrix.ext fun k p => ?_⟩
  rw [Matrix.mul_diagonal]
  by_cases hp : 2 * p.1 < D.R.m - 1 - j
  · have := congrFun (congrFun he k) ⟨p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have e1 : (γ * (rowJac G j hj σ hσ).e) k ⟨p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := rfl
    have e2 : (rowJac G j hj σ hσ).e k ⟨p.1, by omega⟩ = (G.rowDec j hj).a k p := rfl
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]
  · have := congrFun (congrFun he' k) ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩
    simp only [Matrix.mul_diagonal] at this
    have hq : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) (⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ : Fin σ)).rev = p :=
      Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    have e1 : (γ * (rowJac G j hj σ hσ).e') k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (γ * (G.rowDec j hj).a) k p := by
      simp only [Matrix.mul_apply, GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    have e2 : (rowJac G j hj σ hσ).e' k ⟨D.R.m - 1 - j - 1 - p.1, by omega⟩ = (G.rowDec j hj).a k p := by
      simp only [GlobalTheory.RowUnf.rowJac, GlobalTheory.RowUnf.jacDec, Matrix.submatrix_apply, id_eq, hq]
    rw [← e1, this, e2]
    simp [GlobalTheory.RowShape.tiltSc, hodd, hp]

end Grid

section Main

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : GlobalTheory.RowShape.tiltSc D j p ≠ 0 := by
  unfold GlobalTheory.RowShape.tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem moves_idx (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (hj : j ∈ idx D) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  have hj' : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := List.mem_range'_1.1 hj
  have hjm : j < D.R.m := by omega
  obtain ⟨δ, hδ, hfin⟩ := hb.2.1 j hj
  refine moves_of_isFinOf _ hfin _ _ ?_
  have hN : GlobalTheory.RowShape.rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (GlobalTheory.RowShape.rowId D j) := by
    unfold GlobalTheory.RowShape.rowN; rw [dif_pos hjm]
  rw [lat_grid G j hj'.1 hjm, hN]
  by_cases hodd : Odd j
  · obtain ⟨γ, hγ, hγ'⟩ := exists_rat_of_GQ _ δ hδ.1
    obtain ⟨h0, ha⟩ := tilt_cols hjm hodd hδ γ.val hγ
    set t := GlobalTheory.RowShape.tiltSc D j
    have hinv : (γ⁻¹).val * γ.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h0' : (γ⁻¹).val * frameMat _ _ (G.rowDec j hjm).ι = frameMat _ _ (G.rowDec j hjm).ι := by
      conv_lhs => rw [← h0]
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hdd : diagonal t * diagonal (fun p => (t p)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal,
        show (fun p => t p * (t p)⁻¹) = fun _ => (1 : D.host.E) from funext fun p => mul_inv_cancel₀ (tiltSc_ne_zero j p)]
      exact Matrix.diagonal_one
    have ha' : (γ⁻¹).val * (G.rowDec j hjm).a = (G.rowDec j hjm).a * diagonal (fun p => (t p)⁻¹) := by
      calc (γ⁻¹).val * (G.rowDec j hjm).a
          = (γ⁻¹).val * ((G.rowDec j hjm).a * (diagonal t * diagonal (fun p => (t p)⁻¹))) := by
            rw [hdd, Matrix.mul_one]
        _ = (γ⁻¹).val * (γ.val * (G.rowDec j hjm).a) * diagonal (fun p => (t p)⁻¹) := by
            simp only [ha, Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine moves_of_rat _ δ γ.val (γ⁻¹).val hγ hγ' _ _ ?_ ?_ _
    · refine sumLat_mulVec _ _ _ _ _ _ t h0 ha fun p u hu => ?_
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hu
    · refine sumLat_mulVec _ _ _ _ _ _ (fun p => (t p)⁻¹) h0' ha' fun p u hu => ?_
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hu
      rw [← mul_assoc, inv_mul_cancel₀ (tiltSc_ne_zero j p), one_mul]
      exact hz
  · have h1 : δ = 1 := hδ.2.1 (Nat.not_odd_iff_even.1 hodd)
    subst h1
    have hI : GlobalTheory.RowShape.rowId D j = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) := by
      funext p
      simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc, hodd]
    rw [hI]
    exact moves_one _ _ _

theorem moves_rowN (t : T) (B : Frames G) (b : Pts G) (hb : IsBase t B b) (j : ℕ) (h1 : 1 ≤ j) (hm : j ≤ D.R.m) :
    Moves _ (b j) (G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN G j) fun _ => True := by
  by_cases hj : j ∈ idx D
  · exact moves_idx t B b hb j hj
  rw [hb.2.2 j (by omega) hj]
  by_cases hjm : j < D.R.m
  · have hc : D.R.m - 1 - j = 0 := by
      have : ¬ (1 ≤ j ∧ j < 1 + (D.R.m - 2)) := fun h => hj (List.mem_range'_1.2 h)
      omega
    have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN
      rw [dif_pos hjm, lat_grid G j h1 hjm]
      congr 1
      funext p
      exact absurd p.2 (by omega)
    rw [hN]
    exact moves_one _ _ _
  · have hN : GlobalTheory.RowShape.rowN G j = G.Λ (.grid D.R.m j) := by
      unfold GlobalTheory.RowShape.rowN; rw [dif_neg hjm]
    rw [hN]
    exact moves_one _ _ _

end Main

theorem base_moves_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, 1 ≤ j → j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t b hb j h1 hm
  exact moves_rowN t ch.S.B b hb j h1 hm

end GlobalTheory.BaseTiltMove
