import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLatticeStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem rowsLift_mem_orth {U : Submodule E S.V} {x : S.V} :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem rowsLift_fix_span {ι : Type} (v : ι → S.V) (s : Set ι) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ a, n (v a) = v a) : ∀ x ∈ Submodule.span E (v '' s), n x = x := by
  intro x hx
  have hle : Submodule.span E (v '' s) ≤ LinearMap.eqLocus (n : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simpa using hn a
  have h := hle hx
  rw [LinearMap.mem_eqLocus] at h
  simpa using h

theorem rowsLift_map_eq (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hn : ∀ x ∈ U, n x = x) :
    U.map (n : S.V →ₗ[E] S.V) = U := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hn x hx]
  · intro hy
    exact ⟨y, hy, hn y hy⟩

theorem rowsLift_orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  have hi' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hi
  rw [rowsLift_mem_orth, rowsLift_mem_orth]
  refine forall₂_congr fun y hy => ?_
  have h := hi' y x
  rw [hn y hy] at h
  rw [h]

theorem rowsLift_Lsub_gmap (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  ext y
  unfold Lsub Lrep
  constructor
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨ha1, haO⟩ := Submodule.mem_inf.mp ha
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp ha1
    have hlO : l ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn l).mp haO
    have hd : n l - l ∈ Xsp F := hq l hlO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨l, Submodule.mem_inf.mpr ⟨hl, hlO⟩, (n l - l) + b, (toO S (Xsp F)).add_mem hd hb, ?_⟩, hyO⟩
    show l + (n l - l + b) = n l + b
    abel
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨hl, haO⟩ := Submodule.mem_inf.mp ha
    have hnO : n a ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn a).mpr haO
    have hd : n a - a ∈ Xsp F := hq a haO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨n a, Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨a, hl, rfl⟩, hnO⟩, b - (n a - a),
        (toO S (Xsp F)).sub_mem hb hd, ?_⟩, hyO⟩
    abel

theorem rowsLift_cancel (X W : Submodule E S.V) (hXW : ∀ x ∈ X, x ∈ W → x = 0)
    (A B : Submodule (𝓞 E) S.V) (h : (A ⊓ toO S W) ⊔ toO S X = (B ⊓ toO S W) ⊔ toO S X) :
    A ⊓ toO S W ≤ B ⊓ toO S W := by
  intro y hy
  have h1 : y ∈ (A ⊓ toO S W) ⊔ toO S X := Submodule.mem_sup_left hy
  rw [h] at h1
  obtain ⟨b, hb, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
  have hxW : x ∈ W := by
    have h2 : b + x - b ∈ W := W.sub_mem (Submodule.mem_inf.mp hy).2 (Submodule.mem_inf.mp hb).2
    simpa using h2
  rw [hXW x hx hxW, add_zero]
  exact hb

end Generic

theorem rowsLift_X_inf_Wb (D : D7) (x : (hS D).V)
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) (hW : x ∈ Wb D) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).mp hx
  have hW' : (∑ i, c i • D.sp.hypE i) ∈ orth (hS D)
      (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF)) := hW
  have hc : ∀ j, c j = 0 := by
    intro j
    have h1 : (hS D).hT (D.sp.hypF j) (∑ i, c i • D.sp.hypE i) = 0 :=
      (rowsLift_mem_orth.mp hW') _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
    have hs : ∀ i, (hS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
      intro i
      rw [← (hS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
      split_ifs <;> simp
    rw [map_sum] at h1
    simpa [hs] using h1
  simp [hc]

theorem rowsLift_fixX {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {n : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hn : FixFr D (lf D F0) n) :
    (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z ∧ ∀ x ∈ F0.X, n x = x := by
  obtain ⟨-, hfr, -⟩ := hn
  have he : ∀ a, n (F0.e a) = F0.e a := by
    intro a
    have h := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, lf] using h
  have hz : n F0.z = F0.z := by
    have h := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, lf] using h
  refine ⟨he, hz, ?_⟩
  intro x hx
  rw [FlagG.X, ← Set.image_univ] at hx
  exact rowsLift_fix_span F0.e Set.univ n he x hx

theorem rowsLift : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  intro D u _ hT3 _ F0 he hz Λ₁ Λ₂ h₁ h₂ hL
  have hT1 : 1 ≤ Tu D u := by omega
  have hB : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨n₁, hf₁, hs₁, hr₁⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₁ hB h₁ hT1
  obtain ⟨n₂, hf₂, hs₂, hr₂⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₂ hB h₂ hT1
  have hfx₁ := rowsLift_fixX hf₁
  have hfx₂ := rowsLift_fixX hf₂
  have hLs : ∀ (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) (Λ : LatV D), FixFr D (lf D F0) n →
      Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    intro n Λ hf
    have hX := (rowsLift_fixX hf).2.2
    obtain ⟨hi, -, hq⟩ := hf
    exact rowsLift_Lsub_gmap (lf D F0) Λ n hi hX hq
  have hW : ∀ Λ : LatV D, IsRowLat D F0 Λ → IsSplit D F0 Λ →
      Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := fun Λ hr hs =>
    ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ hT1 hB hr).1 hs).2
  have heq : (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X =
      (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X :=
    (hW _ hr₁ hs₁).symm.trans
      (((hLs n₁ Λ₁ hf₁).trans (hL.trans (hLs n₂ Λ₂ hf₂).symm)).trans (hW _ hr₂ hs₂))
  have hXW : ∀ x ∈ F0.X, x ∈ Wb D → x = 0 := fun x hx hw =>
    rowsLift_X_inf_Wb D x (by rw [← he]; exact hx) hw
  have hM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D) = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D) :=
    le_antisymm (rowsLift_cancel _ _ hXW _ _ heq) (rowsLift_cancel _ _ hXW _ _ heq.symm)
  have e₁ : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₁
  have e₂ : Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₂
  have hMM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ := by
    rw [e₁, e₂, hM]
  have hfix : ∀ v, n₁ v = v → n₂ v = v → (n₁.trans n₂.symm) v = v := by
    intro v h1 h2
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_eq, h2]
  obtain ⟨hi₁, -, hq₁⟩ := hf₁
  obtain ⟨hi₂, -, hq₂⟩ := hf₂
  have hmem : n₁.trans n₂.symm ∈ stabF D F0 := by
    simp only [stabF, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi₂) hi₁
    · intro j
      exact rowsLift_map_eq (F0.Xa j) (n₁.trans n₂.symm) (fun x hx =>
        rowsLift_fix_span F0.e _ _ (fun a => hfix _ (hfx₁.1 a) (hfx₂.1 a)) x hx)
    · exact hfix _ hfx₁.2.1 hfx₂.2.1
  refine ⟨n₁.trans n₂.symm, hmem, ?_, ?_⟩
  · intro x hx
    have hy : n₁ x ∈ orth (hS D) F0.X := (rowsLift_orth_iff F0.X n₁ hi₁ hfx₁.2.2 x).mpr hx
    obtain ⟨w, hw⟩ : ∃ w, w = n₂.symm (n₁ x) := ⟨_, rfl⟩
    have hnw : n₂ w = n₁ x := by rw [hw, LinearEquiv.apply_symm_apply]
    have hwO : w ∈ orth (hS D) F0.X :=
      (rowsLift_orth_iff F0.X n₂ hi₂ hfx₂.2.2 w).mp (by rw [hnw]; exact hy)
    have h1 : n₁ x - x ∈ F0.X := hq₁ x hx
    have h2 : n₂ w - w ∈ F0.X := hq₂ w hwO
    rw [hnw] at h2
    have h3 : (n₁.trans n₂.symm) x - x = (n₁ x - x) - (n₁ x - w) := by
      rw [LinearEquiv.trans_apply, ← hw]
      abel
    rw [h3]
    exact F0.X.sub_mem h1 h2
  · have hcomp : Formalism.HermitianLatticesTheory.gmap (n₁.trans n₂.symm) Λ₁ =
        Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁) := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    have hback : Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂) = Λ₂ := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    rw [hcomp, hMM, hback]

end GlobalTheory.LoopC

end
