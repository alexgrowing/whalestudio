import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfC

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : D7} (Z : LocDat D) (p : PlF D)

def lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g : Fin (D.R.rS + 1) → (VS D).V) (Tn T'n : ℕ) :
    Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := sF Z p a • baseChange₂ D p (f a)
  f' b := sF' Z p b • baseChange₂ D p (g b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

structure GFacts (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop where
  iso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y
  lam : ∀ v ∈ Λ, β v ∈ Λ
  lam' : ∀ v ∈ Λ, β.symm v ∈ Λ
  xmap : ∀ a : Fin D.R.rS, β (g1 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  xmap' : ∀ a : Fin D.R.rS, β.symm (g2 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g1 b.castSucc)
  zmap : β (g1 (Fin.last _)) - g2 (Fin.last _) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  fiso : ∀ a b : Fin D.R.rS, (VS D).hT (f a.castSucc) (f b.castSucc) = 0
  g2iso : ∀ a b : Fin D.R.rS, (VS D).hT (g2 a.castSucc) (g2 b.castSucc) = 0
  proj : ∀ y, ∃ u ∈ Submodule.span D.host.E (Set.range (Sum.elim f g1)),
    ∀ i, (VS D).hT (Sum.elim f g1 i) (y - u) = 0
  gram : (Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k)).det ≠ 0
  theta : ∀ x1, (∀ i, (VS D).hT (Sum.elim f g1 i) x1 = 0) → ∃ x2, (∀ i, (VS D).hT (Sum.elim f g2 i) x2 = 0) ∧
    x1 - x2 ∈ Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc) ∧
    β x1 - x2 ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  ratio : GDl f g1 D.R.rS * GDl f g2 (D.R.rS + 1) = GDl f g2 D.R.rS * GDl f g1 (D.R.rS + 1)
  omp : GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2 ∈
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc)
  om : star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) - star (GDl f g1 (D.R.rS + 1)) • Gom f g2 ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)

theorem hermitian_base_change_smul (a : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (a • baseChange₂ D p x) (baseChange₂ D p y) = a * (D.s.atP p).ιE (brS (VS D) x y) := by
  have := h_bcP Z p a 1 x y
  rwa [one_smul, map_one, mul_one] at this

theorem h_zero_of_smul {c : (D.s.atP p).Ep} (hc : IsUnit c) {w y : Vp D p}
    (h : (locH Z p).h w (c • y) = 0) : (locH Z p).h w y = 0 := by
  rw [h_smul_right] at h
  exact (hc.map (Z.M p).L.cj).mul_right_eq_zero.1 h

theorem baseChange_mem_span {ι : Type} (v : ι → (VS D).V) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range v)) :
    baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (v i)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem mem_orthogonal_frame_iff (u v : Fin (D.R.rS + 1) → Vp D p) (w : Vp D p) :
    w ∈ (locH Z p).W0 u v ↔ (∀ a, (locH Z p).h w (u a) = 0) ∧ ∀ b, (locH Z p).h w (v b) = 0 := by
  unfold Loc.HermSp.W0 Loc.HermSp.Xp
  rw [← Submodule.span_union, mem_perp_span]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), fun b => h _ (Or.inr ⟨b, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact h1 a
    · exact h2 b

theorem scalar_frame_w_zero_exists (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) {w : Vp D p}
    (hw : w ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))) :
    ∃ w₂ ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)),
      w - w₂ ∈ (locH Z p).X (fun a => sF Z p a • baseChange₂ D p (f a)) ∧
      betaP p β w - w₂ ∈ (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  rw [mem_orthogonal_frame_iff] at hw
  have hperp : ∀ i, (locH Z p).h w (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    rintro (a | b)
    · exact h_zero_of_smul Z p (isUnit_sF Z p a) (hw.1 a)
    · exact h_zero_of_smul Z p (isUnit_sF' Z p b) (hw.2 b)
  choose u hu hpu using fun j => hG.proj ((VS D).frame j)

  set U : Vp D p := ∑ j, w j • baseChange₂ D p (u j) with hU
  set Hh : Vp D p := ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j) with hHh
  have hw_eq : w = U + Hh := by
    conv_lhs => rw [vp_eq_sum p w]
    rw [hU, hHh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add, ← map_add, add_sub_cancel]
  have hHperp : ∀ i, (locH Z p).h Hh (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    rw [hHh, h_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hermitian_base_change_smul, brS, hpu j i, map_zero, mul_zero]
  have hUperp : ∀ i, (locH Z p).h U (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    have e : U = w - Hh := by rw [hw_eq]; abel
    rw [e, h_sub_left, hperp i, hHperp i, sub_zero]
  have hUspan : U ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (Sum.elim f g1 i)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (baseChange_mem_span p _ (hu j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hUspan
  have hU0 : U = 0 := by
    set G0 := Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k) with hG0
    have hvm : Matrix.vecMul c ((D.s.atP p).ιE.mapMatrix G0) = 0 := by
      funext k
      have := hUperp k
      rw [← hc, h_sum_left] at this
      simp only [hermitian_base_change_smul] at this
      simpa [Matrix.vecMul, dotProduct, hG0] using this
    have hdet : IsUnit ((D.s.atP p).ιE.mapMatrix G0).det := by
      rw [← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 hG.gram).map _
    have hc0 : c = 0 := by
      have h1 := congrArg (fun v => Matrix.vecMul v ((D.s.atP p).ιE.mapMatrix G0)⁻¹) hvm
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] at h1
      exact h1
    rw [← hc, hc0]
    simp
  have hw' : w = Hh := by rw [hw_eq, hU0, zero_add]
  have hperp1 : ∀ j, ∀ i, (VS D).hT (Sum.elim f g1 i) ((VS D).frame j - u j) = 0 := fun j i => hpu j i
  choose x2 hx2 using fun j => hG.theta ((VS D).frame j - u j) (hperp1 j)
  refine ⟨∑ j, w j • baseChange₂ D p (x2 j), ?_, ?_, ?_⟩
  · rw [mem_orthogonal_frame_iff]
    constructor
    · intro a
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (f a) (x2 j) = 0 from (hx2 j).1 (Sum.inl a), map_zero, mul_zero]
    · intro b
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (g2 b) (x2 j) = 0 from (hx2 j).1 (Sum.inr b), map_zero, mul_zero]
  · have e : w - ∑ j, w j • baseChange₂ D p (x2 j) = ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j - x2 j) := by
      nth_rewrite 1 [hw']
      rw [hHh, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) (hx2 j).2.1)
  · have e : betaP p β w - ∑ j, w j • baseChange₂ D p (x2 j) =
        ∑ j, w j • baseChange₂ D p (β ((VS D).frame j - u j) - x2 j) := by
      nth_rewrite 1 [hw']
      rw [hHh, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) (hx2 j).2.2)

end Assembly

end Formalism.L2.SG.Pf.ScalarFramePf
