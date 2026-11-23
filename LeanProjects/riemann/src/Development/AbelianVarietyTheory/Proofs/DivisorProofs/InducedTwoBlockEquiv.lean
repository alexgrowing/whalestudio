import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

noncomputable section

open Filter Topology
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

namespace GlobalTheory.IndEq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem place_zero (b : Fin 2 → ℕ) (i : Fin (b 0)) :
    pairPlace b rfl ⟨0, i⟩ = finSumFinEquiv (Sum.inl i : Fin (b 0) ⊕ Fin (b 1)) := by
  ext; simp [pairPlace]

theorem place_one (b : Fin 2 → ℕ) (i : Fin (b 1)) :
    pairPlace b rfl ⟨1, i⟩ = finSumFinEquiv (Sum.inr i : Fin (b 0) ⊕ Fin (b 1)) := by
  ext; simp [pairPlace]

theorem char_val (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (m : Levi k (fun j : Fin 2 => Fin (b j))) :
    (deltaHalf k _ m : ℂ) * (pairChar k b χ m : ℂ) =
      (χ 0 (gdet (m 0)) : ℂ) * χ 1 (gdet (m 1)) * apow (gdet (m 0)) ((b 1 : ℂ) / 2) *
        apow (gdet (m 1)) (-(b 0 : ℂ) / 2) := by
  have e0 : modExp (fun j : Fin 2 => Fin (b j)) 0 = b 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have e1 : modExp (fun j : Fin 2 => Fin (b j)) 1 = -(b 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  rw [deltaHalf_apply, pairChar, MonoidHom.finsetProd_apply, Fin.prod_univ_two, Fin.prod_univ_two, e0, e1]
  simp only [Units.val_mul, val_absPow, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply, apow,
    Int.cast_neg, Int.cast_natCast, gdet]
  ring

def funOf (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) :
    IndSp (pairPlace b rfl) (ofChar (pairChar k b χ)) →ₗ[ℂ] (GL (Fin (b 0 + b 1)) k → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem funOf_injective (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Function.Injective (funOf b χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem range_funOf (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) :
    LinearMap.range (funOf b χ) = indSp (b 0) (b 1) (χ 0) (χ 1) := by
  ext f
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨fun g A D N hg h => ?_, ?_⟩
    · have hp : g ∈ parab k (pairPlace b rfl) := by
        rw [mem_parab_iff]
        intro x y i j hlt
        fin_cases x <;> fin_cases y
        · exact absurd hlt (by decide)
        · exact absurd hlt (by decide)
        · exact (congrArg₂ g.val (place_one b i) (place_zero b j)).trans
            (congrFun (congrFun hg (Sum.inr i)) (Sum.inl j))
        · exact absurd hlt (by decide)
      have hA : leviProj k (pairPlace b rfl) ⟨g, hp⟩ 0 = A := by
        ext i j
        exact (congrArg₂ g.val (place_zero b i) (place_zero b j)).trans
            (congrFun (congrFun hg (Sum.inl i)) (Sum.inl j))
      have hD : leviProj k (pairPlace b rfl) ⟨g, hp⟩ 1 = D := by
        ext i j
        exact (congrArg₂ g.val (place_one b i) (place_one b j)).trans
            (congrFun (congrFun hg (Sum.inr i)) (Sum.inr j))
      have := parInd_law _ _ F ⟨g, hp⟩ h
      rw [ofChar_apply, smul_eq_mul, ← mul_assoc, char_val, hA, hD] at this
      exact this
    · have ho := isSmooth_parInd (pairPlace b rfl) (ofChar (pairChar k b χ)) F
      exact Filter.mem_of_superset (IsOpen.mem_nhds ho (by simp)) fun u hu h =>
        congrFun (congrArg (fun G => G.1.1) (show parInd _ _ u F = F from hu)) h
  · rintro ⟨h1, h2⟩
    refine ⟨⟨⟨f, fun p g => ?_⟩, mem_smoothPart_of_nhds (h2.mono fun u hu => Subtype.ext (funext hu))⟩, rfl⟩
    show f (p * g) = (deltaHalf k _ (leviProj k _ p) : ℂ) • ofChar (pairChar k b χ) (leviProj k _ p) (f g)
    rw [ofChar_apply, smul_eq_mul, ← mul_assoc, char_val]
    refine h1 p _ _ (fun i j => p.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) ?_ g
    ext (i | i) (j | j)
    · exact (congrArg₂ p.1.val (place_zero b i) (place_zero b j)).symm
    · rfl
    · exact (congrArg₂ p.1.val (place_one b i) (place_zero b j)).symm.trans
        (mem_parab_iff.1 p.2 1 0 i j (by decide))
    · exact (congrArg₂ p.1.val (place_one b i) (place_one b j)).symm

theorem indSp_equiv_indAA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ) :
    ∃ e : GlobalTheory.KSplit.indSp a a' α β ≃ₗ[ℂ] IndAA k a a' ![α, β],
      ∀ f x, (e f).1.1 x = (f : GL (Fin (a + a')) k → ℂ) x := by
  let e₀ := (LinearEquiv.ofInjective (funOf (k := k) ![a, a'] ![α, β]) (funOf_injective _ _)).trans
    (LinearEquiv.ofEq _ _ (range_funOf (k := k) ![a, a'] ![α, β]))
  refine ⟨e₀.symm, fun f x => ?_⟩
  have h := congrArg Subtype.val (e₀.apply_symm_apply f)
  exact congrFun h x

end GlobalTheory.IndEq

end
