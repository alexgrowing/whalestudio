import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

noncomputable section

namespace GlobalTheory.Cusp.FlagCocompact

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem exists_adapted_set {K M : Type} [Field K] [AddCommGroup M] [Module K M] (X : ℕ → Submodule K M)
    (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ s : Set M, LinearIndepOn K id s ∧ s ⊆ X k ∧ ∀ i ≤ k, X i ≤ Submodule.span K (s ∩ X i) := by
  induction k with
  | zero => exact ⟨∅, linearIndepOn_empty _ _, Set.empty_subset _, fun i hi => by
      rw [Nat.le_zero.1 hi, h0]; exact bot_le⟩
  | succ k ih =>
    obtain ⟨s, hs, h1, h2⟩ := ih
    have h3 : s ⊆ X (k + 1) := h1.trans (hX k.le_succ)
    refine ⟨hs.extend h3, hs.linearIndepOn_extend h3, hs.extend_subset h3, fun i hi => ?_⟩
    rcases Nat.le_succ_iff.1 hi with h | rfl
    · exact (h2 i h).trans (Submodule.span_mono (Set.inter_subset_inter_left _ (hs.subset_extend h3)))
    · rw [Set.inter_eq_left.2 (hs.extend_subset h3)]
      exact hs.subset_span_extend h3

theorem exists_adapted_basis {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (X : ℕ → Submodule K M) (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ (r : ℕ) (e : Fin r → M) (d : Fin r → ℕ), LinearIndependent K e ∧ (∀ j, d j < k) ∧
      ∀ i ≤ k, X i = Submodule.span K (e '' {j | d j < i}) := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := exists_adapted_set X hX h0 k
  have hf : Finite s := LinearIndependent.finite (R := K) hs
  obtain ⟨r, ⟨q⟩⟩ := Finite.exists_equiv_fin s
  let e : Fin r → M := fun j => (q.symm j).1
  have he : LinearIndependent K e := LinearIndependent.comp hs q.symm q.symm.injective
  have hex : ∀ j, ∃ i, e j ∈ X (i + 1) := fun j => ⟨k, hX k.le_succ (h1 (q.symm j).2)⟩
  have hd : ∀ j i, Nat.find (hex j) < i ↔ e j ∈ X i := fun j i => by
    refine ⟨fun h => hX (Nat.succ_le_of_lt h) (Nat.find_spec (hex j)), fun h => ?_⟩
    cases i with
    | zero => rw [h0] at h; exact absurd h (he.ne_zero j)
    | succ i => exact Nat.lt_succ_of_le (Nat.find_min' _ h)
  refine ⟨r, e, fun j => Nat.find (hex j), he, fun j => (hd j k).2 (h1 (q.symm j).2), fun i hi => le_antisymm
    ((h2 i hi).trans (Submodule.span_mono ?_)) (Submodule.span_le.2 ?_)⟩
  · rintro x ⟨hx, hx'⟩
    have : e (q ⟨x, hx⟩) = x := by simp [e]
    exact ⟨q ⟨x, hx⟩, (hd _ _).2 (this.symm ▸ hx'), this⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (hd _ _).1 hj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E}

omit [NumberField F] in

theorem mem_extSub_span_depth {R : Type} [CommRing R] [Algebra F R] {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) E}
    (d : Fin r → ℕ) (i : ℕ) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i})) ↔
      ∃ a : Fin r → R ⊗[F] E, (∀ j, i ≤ d j → a j = 0) ∧ y = (C.map (inclR (F := F) R)).mulVec a := by
  let C' : Matrix (Fin V.rank) (Fin r) E := fun a j => if d j < i then C a j else 0
  have e : Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i}) = colSpan V C' := by
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, congrArg (vecOf V) (funext fun a => if_pos hj)⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : d j < i
      · exact Submodule.subset_span ⟨j, hj, congrArg (vecOf V) (funext fun a => (if_pos hj).symm)⟩
      · have : C'ᵀ j = 0 := funext fun a => if_neg hj
        simp [this, vecOf]
  rw [e, AutFunCompare.mem_extSub_colSpan]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j => if d j < i then a j else 0, fun j hj => if_neg (not_lt.2 hj), funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i <;> simp [C', hj]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i
    · simp [C', hj]
    · rw [ha j (not_lt.1 hj), mul_zero, mul_zero]

theorem exists_adapted_frame (𝔉 : IsoFlag V) : ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ),
    LinearIndependent E Cᵀ ∧ (∀ j, d j < 𝔉.k) ∧
      ∀ i, 𝔉.X i = Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i.val}) := by
  have : Module.Finite E V.V := Module.Finite.of_basis V.frame
  obtain ⟨r, e, d, he, hd, hX⟩ := exists_adapted_basis (K := E)
    (fun i => 𝔉.X ⟨min i 𝔉.k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun a b h => 𝔉.strictMono.monotone (Fin.mk_le_mk.2 (min_le_min_right _ h)))
    (by rw [← 𝔉.zero]; congr 1) 𝔉.k
  refine ⟨r, Matrix.of fun a j => V.frame.repr (e j) a, d, he.map' V.frame.equivFun.toLinearMap (LinearEquiv.ker _),
    hd, fun i => ?_⟩
  have e1 : (fun k => vecOf V ((Matrix.of fun a j => V.frame.repr (e j) a)ᵀ k)) = e :=
    funext fun k => V.frame.equivFun.symm_apply_apply (e k)
  rw [e1, ← hX i (Nat.lt_succ_iff.1 i.2)]
  congr 1
  ext
  simp [Nat.lt_succ_iff.1 i.2]

theorem unip_cocompact (hc : CMData F E) (𝔉 : IsoFlag V) : Cocompact (ratPts hc V) (𝔉.unip hc (AF F)) := by
  obtain ⟨r, C, d, hC, hd, hX⟩ := exists_adapted_frame 𝔉
  have ht : 𝔉.top = colSpan V C := (hX _).trans (congrArg (Submodule.span _) (by
    rw [← Set.image_univ]; congr 1; exact Set.eq_univ_of_forall fun j => hd j))
  have h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0 := by
    have h := 𝔉.iso
    change 𝔉.top ≤ perp V 𝔉.top at h
    rw [ht] at h
    ext a k
    have := (mem_perp_colSpan hc V C _).1 (h (Submodule.subset_span ⟨k, rfl⟩))
    simp only [repr_vecOf] at this
    exact congrFun this a
  have hm : ∀ (g : GA hc V) (x : Fin V.rank → E),
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
      act hc V g (coordR V _ (vecOf V x)) - coordR V _ (vecOf V x) := fun g x => by
    have : coordR (F := F) V (AF F) (vecOf V x) = fun i => inclR (F := F) (AF F) (x i) :=
      funext fun i => by rw [coordR, repr_vecOf]
    rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  have e : 𝔉.unip hc (AF F) = Subgroup.closure (Mem.UnipCocompact.radSet hc V C d) := by
    rw [← Subgroup.closure_eq (𝔉.unip hc (AF F))]
    congr 1
    ext g
    refine IsoFlag.mem_unip_iff.trans
      (and_congr ⟨fun h i => ?_, fun h i x hx => ?_⟩ ⟨fun h x hx => ?_, fun h x hx => ?_⟩)
    · have := h ⟨d i, hd i⟩ (vecOf V (Cᵀ i)) (by
        rw [hX]; exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
      rw [hX, ← hm] at this
      exact (mem_extSub_span_depth d _ _).1 this
    · rw [hX] at hx ⊢
      refine act_sub_mem_of_mem_span ?_ hx
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨a, ha, h'⟩ := h j
      exact (mem_extSub_span_depth d _ _).2
        ⟨a, fun l hl => ha l (Nat.le_trans (Nat.lt_succ_iff.1 hj) hl), (hm g _).symm.trans h'⟩
    · rw [ht] at h
      rw [hm]
      exact (mem_extSub_colSpan V _ C _).1 (h _ ((mem_perp_colSpan hc V C _).2 (by simpa only [repr_vecOf] using hx)))
    · rw [ht] at hx ⊢
      have := h _ ((mem_perp_colSpan hc V C _).1 hx)
      rw [hm, show vecOf V (fun i => V.frame.repr x i) = x from V.frame.equivFun.symm_apply_apply x] at this
      exact (mem_extSub_colSpan V _ C _).2 this
  rw [e]
  obtain ⟨K, hK, h⟩ := Mem.UnipCocompact.closure_radSet_cocompact hc V C hC h0 d
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h n
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

end GlobalTheory.Cusp.FlagCocompact

namespace GlobalTheory.Cusp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cocompact_flag : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V), Cocompact (GQ V) (NA 𝔉) := fun D V 𝔉 => by
  rw [AutFunCompare.GQ_eq]
  exact FlagCocompact.unip_cocompact D.sp.cm 𝔉

end GlobalTheory.Cusp

end
