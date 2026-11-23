import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharIffCoord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharTraceOfMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.HCChar

theorem sum_subgroup {G : Type} [Group G] [Fintype G] (P : Subgroup G) (Φ : P → ℂ) :
    ∑ p : P, Φ p = ∑ x : G, if h : x ∈ P then Φ ⟨x, h⟩ else 0 := by
  have e := Finset.sum_subtype (F := (inferInstance : Fintype P)) (Finset.univ.filter (· ∈ P)) (p := (· ∈ P))
    (by simp) (fun x => if h : x ∈ P then Φ ⟨x, h⟩ else 0)
  rw [Finset.sum_filter] at e
  refine (Eq.trans ?_ e.symm).trans ?_
  · apply Finset.sum_congr rfl; intro a _; simp [dif_pos a.2]
  · apply Finset.sum_congr rfl; intro x _; split_ifs <;> rfl

theorem toG_val {g m : ℕ} [Fact g.Prime] {M : Mt g m} (h : IsUnit M) : ((toG M : Gn g m) : Mt g m) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem card_ker_eq_sum {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) :
    (Nat.card π.ker : ℂ) = ∑ p : P, if π p = 1 then (1 : ℂ) else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

def blocks {g : ℕ} [Fact g.Prime] (a b n : ℕ) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n))
    (hunit : ∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n)))
    (hmul : ∀ x y : Mt g n, InPar a x → InPar a y →
      tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) :
    P →* Gn g a × Gn g b :=
  MonoidHom.mk' (fun p => (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n)))) (by
    intro p q
    have hp := (hP p).1 p.2
    have hq := (hP q).1 q.2
    have hpq := (hP (p * q)).1 (p * q).2
    have hm := hmul _ _ hp hq
    have e1 : (((p * q : P) : Gn g n) : Mt g n) = ((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n) := rfl
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · show ((toG (tl a (((p * q : P) : Gn g n) : Mt g n)) : Gn g a) : Mt g a) =
        ((toG (tl a ((p : Gn g n) : Mt g n)) * toG (tl a ((q : Gn g n) : Mt g n)) : Gn g a) : Mt g a)
      have hu : IsUnit (tl a (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.1]; exact (hunit _ hp).1.mul (hunit _ hq).1
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).1, toG_val (hunit _ hq).1, hm.1]
    · show ((toG (br a b (((p * q : P) : Gn g n) : Mt g n)) : Gn g b) : Mt g b) =
        ((toG (br a b ((p : Gn g n) : Mt g n)) * toG (br a b ((q : Gn g n) : Mt g n)) : Gn g b) : Mt g b)
      have hu : IsUnit (br a b (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.2]; exact (hunit _ hp).2.mul (hunit _ hq).2
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).2, toG_val (hunit _ hq).2, hm.2])

theorem hc_isChar_and_res_decomp : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b →
    (∀ (α : Gn g a → ℂ) (β : Gn g b → ℂ), IsChar α → IsChar β → IsChar (hc a b α β n)) ∧
    ∀ χ : Gn g n → ℂ, IsChar χ → ∃ L : List ((Gn g a → ℂ) × (Gn g b → ℂ)),
      (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, res a b χ x y = (L.map fun p => p.1 x * p.2 y).sum := by
  intro g _ a b n hn
  obtain ⟨⟨P, hP⟩, -, hunit, hmul, hcard, hPcard⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  obtain ⟨π, hπv⟩ : ∃ π : P →* Gn g a × Gn g b,
      ∀ p : P, π p = (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n))) :=
    ⟨blocks a b n P hP hunit hmul, fun _ => rfl⟩
  have hπ : ∀ (x : Gn g n) (hx : x ∈ P) (h₁ : Gn g a) (h₂ : Gn g b),
      π ⟨x, hx⟩ = (h₁, h₂) ↔ (tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂) := by
    intro x hx h₁ h₂
    have hu := hunit x ((hP x).1 hx)
    rw [hπv]
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
  have hsum : ∀ (f : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b),
      ∑ p : P, (if π p = (h₁, h₂) then f p else 0) =
        ∑ x : Gn g n, if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂ then f x else 0 := by
    intro f h₁ h₂
    rw [sum_subgroup]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ P
    · rw [dif_pos hx]
      have hx' := (hP x).1 hx
      by_cases h : tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂
      · rw [if_pos ((hπ x hx h₁ h₂).2 h), if_pos ⟨hx', h⟩]
      · rw [if_neg (fun e => h ((hπ x hx h₁ h₂).1 e)), if_neg (fun e => h e.2)]
    · rw [dif_neg hx, if_neg (fun e => hx ((hP x).2 e.1))]
  have hNP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x; simp [hP]
  refine ⟨?_, ?_⟩
  · intro α β hα hβ
    have hφ : IsChar (fun p : P => α (π p).1 * β (π p).2) :=
      GlobalTheory.GLm.isChar_comp_hom_and_mul.2 P _ _
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.fst _ _).comp π) α hα)
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.snd _ _).comp π) β hβ)
    obtain ⟨V, hV⟩ := GlobalTheory.GLm.IndChar.isChar_induced (Gn g n) P _ hφ
    refine ⟨V, fun x => (hV x).trans ?_⟩
    unfold hc hcT
    dsimp only
    rw [hNP]
    refine congrArg (fun t : ℂ => (((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹) * t) ?_
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y⁻¹ * x * y ∈ P
    · rw [dif_pos hy, if_pos ((hP _).1 hy), hπv]
    · rw [dif_neg hy, if_neg (fun e => hy ((hP _).2 e))]
  · intro χ hχ
    have hsurj : Function.Surjective π := by
      rintro ⟨h₁, h₂⟩
      have hpos : 0 < (Finset.univ.filter fun x : Gn g n =>
          InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card := by
        rw [hcard]; exact pow_pos (Fact.out : g.Prime).pos _
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter] at hx
      have hxP := (hP x).2 hx.2.1
      refine ⟨⟨x, hxP⟩, ?_⟩
      exact (hπ x hxP h₁ h₂).2 hx.2.2
    have hχP : IsChar (fun p : P => χ p) := GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ P.subtype χ hχ
    have hΨ := GlobalTheory.GLm.isChar_fibre_mean P (Gn g a × Gn g b) π _ hsurj hχP
    obtain ⟨L, hL, hLs⟩ := GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum (Gn g a) (Gn g b) _ hΨ
    refine ⟨L, hL, fun x y => ?_⟩
    rw [← hLs x y]
    have hker : (Nat.card π.ker : ℂ) = (g : ℂ) ^ (a * b) := by
      rw [card_ker_eq_sum, Prod.one_eq_mk]
      refine Eq.trans ?_ ((hsum (fun _ => 1) 1 1).trans ?_)
      · apply Finset.sum_congr rfl; intro p _; split_ifs <;> rfl
      rw [Finset.sum_boole, hcard 1 1]
      push_cast; rfl
    unfold res
    rw [hker]
    refine congrArg (fun t : ℂ => ((g : ℂ) ^ (a * b))⁻¹ * t) ?_
    convert (hsum χ x y).symm using 2
    split_ifs <;> rfl

end GlobalTheory.GLq.HCChar
