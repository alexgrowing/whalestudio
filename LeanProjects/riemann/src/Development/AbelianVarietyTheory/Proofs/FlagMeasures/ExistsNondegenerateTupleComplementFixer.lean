import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.FrameTuple

section Alg
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}

def tup (t : E) (g g' : Fin m → V) : Fin m ⊕ Fin m → V := Sum.elim g fun b => t • (g' b - g b)

theorem tup_indep {t θ : E} (h : θ * t = 1) {g g' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) : LinearIndependent E (tup t g g') := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have key := hli (Sum.elim (fun a => c (Sum.inl a) - t * c (Sum.inr a)) fun b => t * c (Sum.inr b))
    (by
      rw [← hc]
      simp only [Fintype.sum_sum_type, tup, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [sub_smul, smul_sub, smul_smul, mul_comm t]
      abel)
  have h2 : ∀ b, c (Sum.inr b) = 0 := fun b => by
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    linear_combination θ * this - c (Sum.inr b) * h
  rintro (a | b)
  · have := key (Sum.inl a)
    simpa [h2] using this
  · exact h2 b

theorem tup_span {t θ : E} (h : θ * t = 1) (g g' : Fin m → V) :
    Submodule.span E (Set.range (tup t g g')) = Submodule.span E (Set.range (Sum.elim g g')) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl b, rfl⟩))
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have : Sum.elim g g' (Sum.inr b) = tup t g g' (Sum.inl b) + θ • tup t g g' (Sum.inr b) := by
        simp [tup, smul_smul, h]
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))

theorem tup_change (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by
  rcases j with j | j
  · simp [tup, Fintype.sum_sum_type, hp]
  · simp only [tup, Fintype.sum_sum_type, hp, hp', Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.smul_sum, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    module

theorem det_uni (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) :
    s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem comb_mul (g : Fin m → V) (s A : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    ∑ i, A i j • ∑ l, s l i • g l = ∑ l, (s * A) l j • g l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem gram_unit (L : LocE F E) [IsArtinianRing E] {n m : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) (x : Fin m → Fin n → E) (hli : LinearIndependent E x)
    (hd : Disjoint (Submodule.span E (Set.range x)) (perp L H (Submodule.span E (Set.range x)))) :
    IsUnit (gramT L H x).det := by
  have hinj : Function.Injective (Matrix.toLin' (gramT L H x)) := by
    rw [injective_iff_map_eq_zero]
    intro α hα
    have h1 : ∑ i, α i • x i = 0 := by
      refine Submodule.disjoint_def.1 hd _ ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩) ?_
      rw [FrameBasic.mem_perp_span L h]
      intro j
      change FrameBasic.hfL L H (x j) _ = 0
      rw [map_sum]
      refine Eq.trans ?_ (congrFun hα j)
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gramT, Matrix.of_apply, map_smul,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h1 i
  have hb := IsArtinian.bijective_of_injective_endomorphism _ hinj
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_toLin'_iff]
  exact (Module.End.isUnit_iff _).2 hb

theorem isLat_std (L : LocE F E) (n : ℕ) :
    IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin n → E))) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := FrameOnto.unipotent_onto L r k S
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (2 * r + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have hθ : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hspan : Submodule.span E (Set.range (tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm)) = S.ME := by
    rw [e.symm.surjective.range_comp, tup_span hθ, hME]
  refine ⟨tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm, ?_, hspan, rfl, isLat_std L _, fun _ => rfl, ?_⟩
  · refine gram_unit L S.herm.1 _ ((tup_indep hθ hli).comp _ e.symm.injective) ?_
    rw [hspan]
    exact hco.disjoint
  · rintro C ⟨n, hn, n', hn', rfl⟩ p ⟨A, A', -, -, h0, h1, -, hp, hp'⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hN n hn
    obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := hN' n' hn'
    simp only [hs, hs', comb_mul] at hp hp'
    refine ⟨tup (algebraMap F E S.th⁻¹) p.1 p.2 ∘ e.symm,
      (Matrix.fromBlocks (s * A) (algebraMap F E S.th⁻¹ • (s' * A' - s * A)) 0 (s' * A')).submatrix
        e.symm e.symm, ?_, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul,
        det_uni s hs0 hs1, det_uni s' hs0' hs1', det_uni A (fun i j h => (h0 i j h).1) fun i => (h1 i).1,
        det_uni A' (fun i j h => (h0 i j h).2) fun i => (h1 i).2]
      simp
    · funext j
      rw [Function.comp_apply, tup_change _ S.f S.f' p.1 p.2 _ _ hp hp', rmul]
      exact (e.symm.sum_comp _).symm
    · rw [e.symm.surjective.range_comp, tup, Set.Sum.elim_range]
      rfl

end GlobalTheory.HL.FrameTuple
