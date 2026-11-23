import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Translate

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem J_translate (ψ : AddChar k Circle) (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ)
    (hV : ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
        (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (L₀ : Subgroup (GL (Fin N) k)) (hL₀U : L₀ ≤ unipU k d hd) (hc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hO : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀)
    (hθ : ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1)
    (F : IndSp (stdBlocks d hd) ρ) (hF : F ∈ openFns d hd ρ) (v : W)
    (hF1 : ∀ u ∈ L₀, F.1.1 (pm k (wOpen d hd) * u) = v)
    (hF0 : ∀ u ∈ unipU k d hd, u ∉ L₀ → F.1.1 (pm k (wOpen d hd) * u) = 0)
    (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    (haU : ∀ u ∈ unipU k d hd, a * u * a⁻¹ ∈ unipU k d hd)
    (haU' : ∀ u ∈ unipU k d hd, a⁻¹ * u * a ∈ unipU k d hd)
    (hstab : ∀ u ∈ L₀, a * u * a⁻¹ ∈ L₀) :
    (J ⟨F, hF⟩ = (vol L₀ : ℂ) • v) ∧
    ∃ hm : parInd (stdBlocks d hd) ρ a F ∈ openFns d hd ρ,
      J ⟨parInd (stdBlocks d hd) ρ a F, hm⟩ = (vol (L₀.map (MulAut.conj a).toMonoidHom) : ℂ) •
        ((deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v) := by
  have hcont : Continuous fun g : GL (Fin N) k => a * g * a⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem1 : ∀ x : GL (Fin N) k, x ∈ L₀.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L₀ := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : a⁻¹ * ((MulAut.conj a).toMonoidHom y) * a = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hy']
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hback : ∀ x : GL (Fin N) k, x = a * (a⁻¹ * x * a) * a⁻¹ := fun x => by group
  refine ⟨?_, PositivityTheory.RgUd.CellA.translate_mem_openFns d hd ρ a l hl haB hF, ?_⟩
  · refine (hV L₀ hL₀U hc hO).2 ⟨F, hF⟩ v ?_ hF0
    intro u hb hu
    rw [hθ u hb hu]
    simpa using hF1 u hu
  · have hL₁U : L₀.map (MulAut.conj a).toMonoidHom ≤ unipU k d hd := by
      intro x hx
      rw [hmem1] at hx
      rw [hback x]
      exact haU _ (hL₀U hx)
    have hL₁c : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) := by
      rw [Subgroup.coe_map]
      exact hc.image hcont
    have hL₁O : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        (L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) := by
      obtain ⟨O, hOo, hOeq⟩ := hO
      have hc2 : Continuous fun g : GL (Fin N) k => a⁻¹ * g * a :=
        (continuous_const.mul continuous_id).mul continuous_const
      refine ⟨(fun g : GL (Fin N) k => a⁻¹ * g * a) ⁻¹' O, hOo.preimage hc2, ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
      rw [hmem1]
      constructor
      · rintro ⟨hxO, hxU⟩
        have : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := ⟨hxO, haU' x hxU⟩
        rw [hOeq] at this
        exact this
      · intro hx
        have hx' : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
          rw [hOeq]
          exact hx
        refine ⟨hx'.1, ?_⟩
        rw [hback x]
        exact haU _ hx'.2
    refine (hV _ hL₁U hL₁c hL₁O).2 _ _ ?_ ?_
    · intro u hb hu
      have hu0 : a⁻¹ * u * a ∈ L₀ := (hmem1 u).1 hu
      have huL₀ : u ∈ L₀ := by
        rw [hback u]
        exact hstab _ hu0
      have key : ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) =
          (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v := by
        rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u, hF1 _ hu0]
      rw [hθ u hb huL₀]
      simpa using key
    · intro u hu hnot
      show ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) = 0
      rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u]
      have hn : a⁻¹ * u * a ∉ L₀ := fun h => hnot ((hmem1 u).2 h)
      rw [hF0 _ (haU' u hu) hn, map_zero, smul_zero]

end PositivityTheory.RgUd.CellA
