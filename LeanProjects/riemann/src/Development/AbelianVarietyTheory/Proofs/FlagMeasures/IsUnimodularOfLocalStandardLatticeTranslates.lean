import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.StdDual

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel

section Form

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_zero_right (x : V) : H.h x 0 = 0 := by
  have := h_smul_right H 0 x 0
  simpa using this

theorem h_neg_left (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

theorem h_neg_right (x y : V) : H.h x (-y) = - H.h x y := by
  have := h_smul_right H (-1) x y
  simpa using this

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [sub_eq_add_neg, h_add_right, h_neg_right, ← sub_eq_add_neg]

theorem h_sum_left {ι : Type*} (s : Finset ι) (c : ι → E) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, c i * H.h (u i) y := by
  refine Finset.induction_on s ?_ ?_
  · simpa using H.h_zero_left y
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_sum_right {ι : Type*} (s : Finset ι) (c : ι → E) (u : ι → V) (x : V) :
    H.h x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, M.L.cj (c i) * H.h x (u i) := by
  refine Finset.induction_on s ?_ ?_
  · simpa using h_zero_right H x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_right, h_smul_right, ih]

theorem int_span_right (x : V) (S : Set V) (hS : ∀ y ∈ S, H.h x y ∈ M.L.O) :
    ∀ y ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hS y h
  | zero => rw [h_zero_right]; exact M.L.O.zero_mem
  | add y z _ _ h1 h2 => rw [h_add_right]; exact M.L.O.add_mem h1 h2
  | smul c y _ h =>
    rw [show (c • y : V) = (c : E) • y from rfl, h_smul_right]
    exact M.L.O.mul_mem (cj_mem c.2) h

theorem int_span_left (S : Set V) (y : V) (hS : ∀ x ∈ S, H.h x y ∈ M.L.O) :
    ∀ x ∈ Submodule.span M.L.O S, H.h x y ∈ M.L.O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hS x h
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x z _ _ h1 h2 => rw [H.h_add_left]; exact M.L.O.add_mem h1 h2
  | smul c x _ h =>
    rw [show (c • x : V) = (c : E) • x from rfl, H.h_smul_left]
    exact M.L.O.mul_mem c.2 h

end Form

section Frame

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : LocNG.FrameD H r)

theorem h_e_e (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)

theorem h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

theorem h_es_e (a b : Fin r) : H.h (Fr.es b) (Fr.e a) = if a = b then 1 else 0 := by
  rw [H.h_herm, h_e_es]; split_ifs <;> simp

theorem h_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp [h_e_e, h_es_e]

theorem h_prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp [h_e_es, Fr.h_ss]

theorem h_e_prF (v : V) (b : Fin r) : H.h (Fr.e b) (Fr.prF v) = 0 := by
  rw [H.h_herm, h_prF_e, map_zero]

theorem h_es_prF (v : V) (b : Fin r) : H.h (Fr.es b) (Fr.prF v) = 0 := by
  rw [H.h_herm, h_prF_es, map_zero]

theorem decomp (v : V) :
    v = ∑ a, H.h v (Fr.es a) • Fr.e a + Fr.prF v + ∑ a, H.h v (Fr.e a) • Fr.es a := by
  unfold FrameD.prF; abel

theorem h_left_prF (v u : V) : H.h v (Fr.prF u) = H.h (Fr.prF v) (Fr.prF u) := by
  conv_lhs => rw [decomp Fr v]
  rw [H.h_add_left, H.h_add_left, h_sum_left, h_sum_left]
  simp [h_e_prF, h_es_prF]

theorem h_prF_right (w y : V) (h1 : ∀ a, H.h w (Fr.e a) = 0) (h2 : ∀ a, H.h w (Fr.es a) = 0) :
    H.h w (Fr.prF y) = H.h w y := by
  unfold FrameD.prF
  rw [h_sub_right, h_sub_right, h_sum_right, h_sum_right]
  simp [h1, h2]

theorem h_expand (v u : V) : H.h v u = ∑ a, M.L.cj (H.h u (Fr.es a)) * H.h v (Fr.e a) +
    H.h v (Fr.prF u) + ∑ a, M.L.cj (H.h u (Fr.e a)) * H.h v (Fr.es a) := by
  conv_lhs => rw [decomp Fr u]
  rw [h_add_right, h_add_right, h_sum_right, h_sum_right]

theorem prF_mem_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨a, rfl⟩ := h; exact h_prF_e Fr v a
  | zero => exact h_zero_right H _
  | add x z _ _ h1 h2 => rw [h_add_right, h1, h2, add_zero]
  | smul c x _ h => rw [h_smul_right, h, mul_zero]

theorem prF_prF (v : V) : Fr.prF (Fr.prF v) = Fr.prF v := by
  show Fr.prF v - ∑ a, H.h (Fr.prF v) (Fr.es a) • Fr.e a - ∑ a, H.h (Fr.prF v) (Fr.e a) • Fr.es a = Fr.prF v
  simp [h_prF_e, h_prF_es]

def gen (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

theorem lamStd_eq (L : Submodule M.L.O (H.Wb Fr.f)) : Fr.LamStd L = Submodule.span M.L.O (gen Fr L) := rfl

theorem e_mem (L : Submodule M.L.O (H.Wb Fr.f)) (j : Fin r) : Fr.e j ∈ gen Fr L := by
  have hp : Fr.prF (Fr.e j) = 0 := by
    unfold FrameD.prF
    simp [h_e_es, h_e_e]
  refine ⟨fun a => ?_, fun a => ?_, 0, by simp [hp], by simp⟩
  · rw [h_e_es]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [h_e_e]; exact M.L.O.zero_mem

theorem es_mem (L : Submodule M.L.O (H.Wb Fr.f)) (j : Fin r) : Fr.es j ∈ gen Fr L := by
  have hp : Fr.prF (Fr.es j) = 0 := by
    unfold FrameD.prF
    simp [h_es_e, Fr.h_ss]
  refine ⟨fun a => ?_, fun a => ?_, 0, by simp [hp], by simp⟩
  · rw [Fr.h_ss]; exact M.L.O.zero_mem
  · rw [h_es_e]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem

theorem prF_gen (L : Submodule M.L.O (H.Wb Fr.f)) (y : ↥(H.perp (H.X Fr.f))) (hy : H.mkW Fr.f y ∈ L) :
    Fr.prF y ∈ gen Fr L := by
  have hy0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => y.2 _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF y, prF_mem_perp Fr y⟩, (prF_prF Fr y).symm, ?_⟩
  · rw [h_prF_es]; exact M.L.O.zero_mem
  · rw [h_prF_e]; exact M.L.O.zero_mem
  · have hd : Fr.prF (y : V) - y = -(∑ a, H.h y (Fr.es a) • Fr.e a) := by
      unfold FrameD.prF
      simp [hy0]
    have heq : H.mkW Fr.f ⟨Fr.prF y, prF_mem_perp Fr y⟩ = H.mkW Fr.f y := by
      unfold HermSp.mkW
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      show Fr.prF (y : V) - y ∈ H.X Fr.f
      rw [hd]
      exact neg_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    rw [heq]; exact hy

end Frame

section SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : LocNG.FrameD H r)

theorem gen_pair (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) {v u : V}
    (hv : v ∈ gen Fr L) (hu : u ∈ gen Fr L) : H.h v u ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hu1, hu2, wu, hwu, hwuL⟩ := hu
  rw [h_expand Fr, h_left_prF, ← hwv, ← hwu]
  refine M.L.O.add_mem (M.L.O.add_mem ?_ ((hL.2.1 wv).1 hwvL wu hwuL)) ?_
  · exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (cj_mem (hu1 a)) (hv2 a)
  · exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (cj_mem (hu2 a)) (hv1 a)

theorem lamStd_selfDual (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (x : V) :
    x ∈ Fr.LamStd L ↔ ∀ y ∈ Fr.LamStd L, H.h x y ∈ M.L.O := by
  rw [lamStd_eq]
  constructor
  · intro hx y hy
    refine int_span_left H _ y ?_ x hx
    intro x' hx'
    exact int_span_right H x' _ (fun y' hy' => gen_pair Fr L hL hx' hy') y hy
  · intro h
    apply Submodule.subset_span
    refine ⟨fun a => h _ (Submodule.subset_span (es_mem Fr L a)),
      fun a => h _ (Submodule.subset_span (e_mem Fr L a)), ⟨Fr.prF x, prF_mem_perp Fr x⟩, rfl, ?_⟩
    rw [hL.2.1]
    intro y hy
    have := h _ (Submodule.subset_span (prF_gen Fr L y hy))
    rwa [h_left_prF, h_prF_right Fr _ _ (h_prF_e Fr x) (h_prF_es Fr x)] at this

theorem img_selfDual (g : V ≃ₗ[E] V) (hg : IsUnitary H g) (Λ : Submodule M.L.O V)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, H.h x y ∈ M.L.O) (x : V) :
    x ∈ img g Λ ↔ ∀ y ∈ img g Λ, H.h x y ∈ M.L.O := by
  have hm : ∀ z, z ∈ img g Λ ↔ g.symm z ∈ Λ := by
    intro z
    unfold img
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hz
      exact ⟨g.symm z, hz, by simp⟩
  rw [hm, hΛ]
  constructor
  · intro h y hy
    rw [hm] at hy
    have := h _ hy
    rwa [← hg, g.apply_symm_apply, g.apply_symm_apply] at this
  · intro h y hy
    rw [← hg (g.symm x) y, g.apply_symm_apply]
    exact h (g y) (by rw [hm]; simpa using hy)

theorem N_unitary {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : IsUnitary H g := by
  induction hg using Subgroup.closure_induction with
  | mem g h => exact h.1
  | one => intro x y; rfl
  | mul a b _ _ ha hb =>
    intro x y
    show H.h (a (b x)) (a (b y)) = H.h x y
    rw [ha, hb]
  | inv a _ ha =>
    intro x y
    show H.h (a.symm x) (a.symm y) = H.h x y
    rw [← ha (a.symm x) (a.symm y)]
    simp

theorem img_lamStd_selfDual {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (x : V) :
    x ∈ img n (Fr.LamStd L) ↔ ∀ y ∈ img n (Fr.LamStd L), H.h x y ∈ M.L.O :=
  img_selfDual n (N_unitary Fr hn) _ (lamStd_selfDual Fr L hL) x

end SelfDual

section Global

variable {D : D7}

theorem mem_iff_local (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    x ∈ Λ ↔ ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ := by
  have r := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) (LatLoc.isLattice_map _ _ hΛ)).1
    (LatLoc.cE D x)
  simp only [← LatLoc.localLattice_eq, ← LatLoc.baseChange_eq] at r
  refine Iff.trans ?_ r
  unfold LatLoc.cL
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := (LatLoc.cE D).injective hyx
    rwa [← this]

theorem unimodular_of_local : ∀ (D : D7) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS) (Λ : LV D), Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  intro D Z A Λ hΛ hloc
  have hsd : ∀ p x, x ∈ lattice₂ D Z.M p Λ ↔ ∀ y ∈ lattice₂ D Z.M p Λ, LocFacts₂ Z.M p x y ∈ (Z.M p).L.O := by
    intro p
    obtain ⟨n, hn, L, hL, he⟩ := hloc p
    rw [he]
    exact img_lamStd_selfDual (A p) hn L hL
  have hsub : ∀ p, ∀ x ∈ Λ, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ := fun p x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  have hform : ∀ p x y, LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  constructor
  · intro hx
    rw [mem_iff_local Z Λ hΛ]
    intro p
    rw [hsd]
    refine int_span_right (locH Z p) _ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := hx y hy
    show LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p y) ∈ _
    rw [hform, ← ho]
    exact GlobalTheory.HL.PlacesRec.int_mem (GlobalTheory.HL.placesOf Z) p o
  · intro hx y hy
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (GlobalTheory.HL.placesOf Z)).1 ((VS D).hT y x)).1
      (fun p => by
        have := (hsd p (baseChange₂ D p x)).1 (hsub p x hx) (baseChange₂ D p y) (hsub p y hy)
        rwa [hform] at this)
    exact ⟨o, ho⟩

end Global

end GlobalTheory.Unfold.StdDual
