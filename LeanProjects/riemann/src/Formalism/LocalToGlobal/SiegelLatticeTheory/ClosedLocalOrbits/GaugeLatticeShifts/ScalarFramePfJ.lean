import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfI

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scal

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_left_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)

theorem span_right_le (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range F₁.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

theorem Xsp_le_span (F : LFlag (VS D) D.R.rS T) :
    Xsp F ≤ Submodule.span D.host.E (Set.range F.fl.fvec) := by
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, fvec_castSucc _ _⟩

theorem Xsp_eq_Xs (F : LFlag (VS D) D.R.rS T) : Xsp F = Xs (S := VS D) F.fl.fvec := (Xs_fvec F.fl).symm

theorem z_mem_span (F : LFlag (VS D) D.R.rS T) :
    F.fl.z ∈ Submodule.span D.host.E (Set.range F.fl.fvec) :=
  Submodule.subset_span ⟨Fin.last _, fvec_last _⟩

theorem Gom'_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom' u v ∈ Submodule.span D.host.E (Set.range v) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem Gom_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom u v ∈ Submodule.span D.host.E (Set.range u) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem scal_dir (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T')
    (hz : F.zt = F.fl.z) (hz₁ : F₁.zt = F₁.fl.z) (hz₂ : F₂.zt = F₂.fl.z) (hT0 : T ≠ 0)
    (hU2 : UUE Λ F F₂ = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₂.fl.fvec)))
    (htr : ∀ y ∈ UUE Λ F F₂, y ∈ orth (VS D) (Xplus F) → y ∈ UUE Λ F F₁)
    (hsc : ∀ y, y ∈ Ylift Λ F F₁ → y ∈ Ylift Λ F F₂ → ∀ α α', SgRel F F₂ y 0 α α' → SgRel F F₁ y 0 α α')
    (hind : LinearIndependent D.host.E F₁.fl.fvec)
    (hD1 : GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) ≠ 0) :
    (∃ x ∈ Xsp F, GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) • Gom' F.fl.fvec F₁.fl.fvec =
      GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) • (Gom' F.fl.fvec F₂.fl.fvec - x)) ∧
    GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₂.fl.fvec D.R.rS =
      GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₁.fl.fvec D.R.rS := by
  set f := F.fl.fvec with hf
  set f1 := F₁.fl.fvec with hf1
  set f2 := F₂.fl.fvec with hf2
  set D1 := GDl f f1 (D.R.rS + 1) with hD1def
  set D2 := GDl f f2 (D.R.rS + 1) with hD2def
  set R1 := GDl f f1 D.R.rS with hR1def
  set R2 := GDl f f2 D.R.rS with hR2def
  set om1 := Gom' f f1 with hom1
  set om2 := Gom' f f2 with hom2
  have hfl : f (Fin.last _) = F.fl.z := fvec_last _
  have hfc : ∀ a : Fin D.R.rS, f a.castSucc = F.fl.e a := fun a => fvec_castSucc _ a
  have p1 : ∀ a, (VS D).hT (f a) om1 = if a = Fin.last _ then D1 else 0 := om'_pair f f1
  have p2 : ∀ a, (VS D).hT (f a) om2 = if a = Fin.last _ then D2 else 0 := om'_pair f f2
  have hzz : (VS D).hT F.fl.z F.fl.z = -T := F.fl.z_norm
  set u2 := om2 + (D2 / T) • F.fl.z with hu2
  have hu2U : u2 ∈ UUE Λ F F₂ := by
    rw [hU2]
    exact Submodule.add_mem _ (span_right_le F F₂ (Gom'_mem f f2))
      (Submodule.smul_mem _ _ (span_left_le F F₂ (z_mem_span F)))
  have hu2o : u2 ∈ orth (VS D) (Xplus F) := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := p2 a.castSucc
      rw [if_neg (Fin.castSucc_ne_last a), hfc] at h1
      rw [hu2, map_add, map_smul, h1, F.fl.z_orth a, smul_zero, add_zero]
    · have h1 := p2 (Fin.last _)
      rw [if_pos rfl, hfl] at h1
      rw [hu2, map_add, map_smul, h1, hzz, smul_eq_mul]
      field_simp
      ring
  have hu2U1 := htr u2 hu2U hu2o
  have hx2 : om2 - R2 • F₂.fl.z ∈ Xsp F₂ := by
    rw [Xsp_eq_Xs, ← fvec_last F₂.fl]
    exact om'_decomp f f2
  have hsg : SgRel F F₂ u2 0 (D2 / T) R2 :=
    ⟨0, Submodule.zero_mem _, om2 - R2 • F₂.fl.z, hx2, by rw [hz, hz₂, hu2]; abel⟩
  obtain ⟨x, hx, x1, hx1, heq⟩ := hsc u2 (Submodule.mem_inf.2 ⟨hu2U1, hu2o⟩)
    (Submodule.mem_inf.2 ⟨hu2U, hu2o⟩) _ _ hsg
  rw [hz, hz₁, hu2, sub_zero] at heq
  have hp : R2 • F₁.fl.z + x1 = om2 - x := by
    have : om2 - x = (om2 + (D2 / T) • F.fl.z) - (D2 / T) • F.fl.z - x := by abel
    rw [this, heq]
    abel
  have hpspan : om2 - x ∈ Submodule.span D.host.E (Set.range f1) := by
    rw [← hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (z_mem_span F₁)) (Xsp_le_span F₁ hx1)
  have hxX : x ∈ F.fl.X := hx
  have hq0 : D1 • (om2 - x) - D2 • om1 = 0 := by
    refine lemB f f1 hD1 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom'_mem f f1))) fun a => ?_
    rw [map_sub, map_smul, map_smul, map_sub, p1, p2, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | last =>
      rw [if_pos rfl, if_pos rfl, hfl, hT_z_X F.fl hxX]
      ring
    | cast a =>
      rw [if_neg (Fin.castSucc_ne_last a), if_neg (Fin.castSucc_ne_last a), hfc,
        hT_X_X F.fl (Submodule.subset_span ⟨a, rfl⟩) hxX]
      ring
  refine ⟨⟨x, hx, (sub_eq_zero.1 hq0).symm⟩, ?_⟩
  have hy1 : om1 - R1 • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := om'_decomp f f1
  have hx1' : x1 ∈ Xs (S := VS D) f1 := by rw [← Xsp_eq_Xs]; exact hx1
  have hlast1 : f1 (Fin.last _) = F₁.fl.z := fvec_last _
  have e : (D1 * R2 - D2 * R1) • f1 (Fin.last _) =
      D2 • (om1 - R1 • f1 (Fin.last _)) - D1 • x1 + (D1 • (om2 - x) - D2 • om1) := by
    rw [← hp, hlast1]
    module
  rw [hq0, add_zero] at e
  have hmem : (D1 * R2 - D2 * R1) • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := by
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hx1')
  have hc := lemC f1 hind hmem
  linear_combination hc

end Scal

end Formalism.L2.SG.Pf.ScalarFramePf
