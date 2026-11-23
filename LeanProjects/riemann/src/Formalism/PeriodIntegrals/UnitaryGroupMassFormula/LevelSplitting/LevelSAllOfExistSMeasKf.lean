import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan

noncomputable section

namespace PI.LevelKSplit.W.Split

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem stab_of (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (ΛX ΛW ΛY : Set (Fin n → E)) (hA : Adapted F E σ n J P ΛX ΛW ΛY)
    (k g : HA (Af F) σ J) (hk : k ∈ Hsub (Af F) σ J P) (hg : g ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY))
    (hgk : ∀ w ∈ ΛW, lin (Af F) σ J g (ratV (F := F) (Af F) w) -
      lin (Af F) σ J k (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∀ x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY),
      Matrix.mulVec ((compV v (incAf σ J k) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY) := by
  have hgv := (mem_Kf _ g).1 hg v
  have hL : latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY) = Submodule.span (v.adicCompletionIntegers F)
      (ratV (F := F) (Fv F v) '' ΛX ∪ ratV (F := F) (Fv F v) '' ΛW ∪
        ratV (F := F) (Fv F v) '' ΛY) := by
    rw [latLoc, Set.image_union, Set.image_union]
  have hXfix : ∀ x ∈ ΛX, lin (Af F) σ J k (ratV (F := F) (Af F) x) = ratV (F := F) (Af F) x :=
    fun x hx => lin_fix_span k P.e (H_fix_e P k hk) _ (ratV_mem_span P.e x (hA.1 x hx))
  have hYfix : ∀ x ∈ ΛY, lin (Af F) σ J k (ratV (F := F) (Af F) x) = ratV (F := F) (Af F) x :=
    fun x hx => lin_fix_span k P.f (H_fix_f P k hk) _ (ratV_mem_span P.f x (hA.2.1 x hx))
  intro x hx
  rw [hL] at hx ⊢
  refine Loc.mulVec_span_stable _ _ ?_ x hx
  rintro _ ((⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
  · rw [← phiV_ratV v l, compV_mulVec, hXfix l hl, phiV_ratV]
    exact Submodule.subset_span (Or.inl (Or.inl ⟨l, hl, rfl⟩))
  · have hy : Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (ratV (F := F) (Fv F v) l) ∈
          Submodule.span (v.adicCompletionIntegers F)
            (ratV (F := F) (Fv F v) '' ΛX ∪ ratV (F := F) (Fv F v) '' ΛW ∪
              ratV (F := F) (Fv F v) '' ΛY) := by
      rw [← hL]
      refine (hgv _).1 ?_
      rw [hL]
      exact Submodule.subset_span (Or.inl (Or.inr ⟨l, hl, rfl⟩))
    refine Loc.sep (fun a => ratV (F := F) (Fv F v) (P.e a))
      (fun a => ratV (F := F) (Fv F v) (P.f a)) (fun b => covR (Fv F v) σ J (P.e b))
      (fun b => covR (Fv F v) σ J (P.f b)) ?_ ?_ ?_ _ _ _ ?_ ?_ ?_ _ _ ?_ hy ?_
    · intro a b
      rw [covR_ratV, hP.1 b a, map_zero]
    · intro a b
      rw [covR_ratV, hP.2.2.1 b a]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
    · intro a b
      rw [covR_ratV, hE_swap hJ hinv, hP.2.2.1 a b]
      split_ifs <;> simp
    · rintro _ ⟨x, hx, rfl⟩
      exact ratV_mem_span P.e x (hA.1 x hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact ratV_mem_span P.f x (hA.2.1 x hx)
    · rintro _ ⟨w, hw, rfl⟩ b
      rw [covR_ratV, covR_ratV, (hA.2.2 w hw b).1, (hA.2.2 w hw b).2, map_zero]
      simp
    · intro b
      rw [← phiV_ratV v l, compV_mulVec, ← phiV_cov, ← phiV_cov,
        (H_perp P k hk l (hA.2.2 l hl) b).1, (H_perp P k hk l (hA.2.2 l hl) b).2, map_zero]
      simp
    · rw [← phiV_ratV v l, compV_mulVec, compV_mulVec]
      have : ((fun i => phiV v (lin (Af F) σ J k (ratV (F := F) (Af F) l) i)) -
          fun i => phiV v (lin (Af F) σ J g (ratV (F := F) (Af F) l) i)) =
          fun i => phiV v ((lin (Af F) σ J k (ratV (F := F) (Af F) l) -
            lin (Af F) σ J g (ratV (F := F) (Af F) l)) i) := by
        funext i; simp
      rw [this]
      apply phiV_span
      rw [← neg_sub]
      exact Submodule.neg_mem _ (hgk l hl)
  · rw [← phiV_ratV v l, compV_mulVec, hYfix l hl, phiV_ratV]
    exact Submodule.subset_span (Or.inr ⟨l, hl, rfl⟩)

theorem splitK_level : SplitK F E σ n J := by
  intro hJ hinv r P T hP ΛX ΛW ΛY hA m h hm hh hmh
  have hNm : ∀ m' : HA (Af F) σ J, m' ∈ Nsub (Af F) σ J P → ∀ y, InXperp (Af F) σ J P y →
      lin (Af F) σ J m' y - y ∈ spanR (F := F) (Af F) P.e Set.univ :=
    fun m' hm' y hy => hm'.2 y hy
  have hperp : ∀ w ∈ ΛW, ∀ k : HA (Af F) σ J, k ∈ Hsub (Af F) σ J P →
      InXperp (Af F) σ J P (lin (Af F) σ J k (ratV (F := F) (Af F) w)) := by
    intro w hw k hk a
    rw [hR_ratV_left]
    exact (H_perp P k hk w (hA.2.2 w hw) a).1
  have h1 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h) (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [lin_mul]
    exact hNm m hm _ (hperp w hw h hh)
  have h2 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h)⁻¹ (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h⁻¹ (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [mul_inv_rev, lin_mul, ← map_sub]
    have hp := hperp w hw 1 (Subgroup.one_mem _)
    rw [lin_one] at hp
    have hx := hNm m⁻¹ (Subgroup.inv_mem _ hm) _ hp
    rw [lin_fix_span h⁻¹ P.e (H_fix_e P _ (Subgroup.inv_mem _ hh)) _ (by rwa [spanR_univ] at hx)]
    exact hx
  rw [mem_Kf]
  intro v x
  have s1 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h (m * h) hh hmh h1 v
  have s2 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h⁻¹ (m * h)⁻¹ (Subgroup.inv_mem _ hh)
    (Subgroup.inv_mem _ hmh) h2 v
  constructor
  · exact s1 x
  · intro hx
    have := s2 _ hx
    rwa [map_inv, map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem level_split_all : SplitKAll := by
  intro F E _ _ _ _ _ σ _ M J _
  exact splitK_level

theorem levelSAll_of_existS_measKf (h1 : ExistSAll) (h2 : MeasKfAll) : LevelSAll :=
  levelSAll_of h1 h2 level_split_all

end PI.LevelKSplit.W.Split
