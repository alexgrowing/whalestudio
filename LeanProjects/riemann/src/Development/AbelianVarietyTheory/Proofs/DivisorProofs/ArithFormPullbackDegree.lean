import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
namespace GlobalTheory.VertForm.PullForm

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}

def fam (S : Finset (HermLB p)) (b : Fin S.card) : HermLB p := (S.equivFin.symm b : HermLB p)

theorem eq_sum_fam {S : Finset (HermLB p)} (x : Cl p) (hx : x.support ⊆ S) :
    x = ∑ b, x (fam S b) • cl (fam S b) := by
  calc x = ∑ L ∈ S, x L • cl L := by
        conv_lhs => rw [← Finsupp.sum_single x]
        rw [Finsupp.sum_of_support_subset x hx (fun L c => Finsupp.single L c) (by simp)]
        simp [cl, Finsupp.smul_single_one]
    _ = ∑ L : S, x L • cl (L : HermLB p) := (Finset.sum_coe_sort S (fun L => x L • cl L)).symm
    _ = _ := (Equiv.sum_comp S.equivFin.symm (fun L : S => x L • cl (L : HermLB p))).symm

def supp {D : ℕ} (v : Fin (D + 1) → Cl p) : Finset (HermLB p) := Finset.univ.biUnion fun j => (v j).support

theorem support_subset {D : ℕ} (v : Fin (D + 1) → Cl p) (j : Fin (D + 1)) : (v j).support ⊆ supp v :=
  Finset.subset_biUnion_of_mem (fun j => (v j).support) (Finset.mem_univ j)

theorem sub_mem_rad_of_isometric (hA : GlobalTheory.Published.ArCalc) [IsIntegral X] {D : ℕ} (hX : IsArithVar p D)
    {num : Form (Cl p) D} (hnum : IsArForm D num) {L M : HermLB p} (h : L.Isometric M) : cl L - cl M ∈ rad num := by
  intro v j
  let F := fam (supp v)
  let FL : Option (Fin (supp v).card) → HermLB p := fun o => o.elim L F
  let FM : Option (Fin (supp v).card) → HermLB p := fun o => o.elim M F
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 _ FL).1
  have hΦ' : IsArFun FM D Φ := ((hA.arIso k X p D hX).2 _ FL Φ hΦ).2.1 FM fun o => by
    cases o with
    | none => exact h
    | some b => exact HermLB.Isometric.refl _
  let a : Fin (D + 1) → Option (Fin (supp v).card) → ℝ := fun i o =>
    o.elim (if i = j then 1 else 0) fun b => if i = j then 0 else v i (F b)
  have key (N : HermLB p) (G : Option (Fin (supp v).card) → HermLB p) (hG : G = fun o => o.elim N F) :
      (fun i => ∑ o, a i o • cl (G o)) = Function.update v j (cl N) := by
    subst hG
    funext i
    rw [Fintype.sum_option]
    by_cases hi : i = j
    · subst hi
      simp [a]
    · simp only [a, hi, if_false, Option.elim, zero_smul, zero_add, Function.update_of_ne hi]
      exact (eq_sum_fam (v i) (support_subset v i)).symm
  have e₁ := hnum _ FL Φ hΦ a
  have e₂ := hnum _ FM Φ hΦ' a
  rw [key L FL rfl] at e₁
  rw [key M FM rfl] at e₂
  rw [num.map_update_sub, ← e₁, ← e₂, sub_self]

theorem isometric_pull_oneB (π : X' ⟶ X) (hπ : π ≫ p = q) : ((oneB p).pull π hπ).Isometric (oneB q) :=
  HermLB.isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g _ π (𝟙 X') x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun σ j y _ => by
      rw [show (((oneB p).pull π hπ).φ σ).φ j y = _ from Weight.pull_φ ((oneB p).φ σ) π hπ j y]
      rfl

theorem arForm_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q), π (genericPoint X') = genericPoint X → π.residueDegree (genericPoint X') ≠ 0 → ∀ (num : Form (Cl p) D) (num' : Form (Cl q) D), IsArForm D num → IsArForm D num' → (∀ v : Fin (D + 1) → Cl p, num' (fun j => pullCl π hπ (v j)) = (π.residueDegree (genericPoint X') : ℝ) * num v) ∧ pullCl π hπ (cl (oneB p)) - cl (oneB q) ∈ rad num' := by
  intro hA k _ X X' _ _ p q D hX hX' π hπ hg hd num num' hnum hnum'
  refine ⟨fun v => ?_, ?_⟩
  · let F := fam (supp v)
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 _ F).1
    have hΦ' := (hA.arProj k X X' p q D hX hX' π hπ hg hd).2 _ F Φ hΦ
    let a : Fin (D + 1) → Fin (supp v).card → ℝ := fun j b => v j (F b)
    have e₁ := hnum _ F Φ hΦ a
    have e₂ := hnum' _ _ _ hΦ' a
    have hv : (fun j => ∑ b, a j b • cl (F b)) = v :=
      funext fun j => (eq_sum_fam (v j) (support_subset v j)).symm
    have hv' : (fun j => ∑ b, a j b • cl ((F b).pull π hπ)) = fun j => pullCl π hπ (v j) := funext fun j => by
      conv_rhs => rw [eq_sum_fam (v j) (support_subset v j)]
      simp only [map_sum, LinearMap.map_smul, pullCl_cl, a, F]
    rw [hv] at e₁
    rw [hv'] at e₂
    rw [← e₂, ← e₁, LinearMap.smul_apply, smul_eq_mul]
  · have := sub_mem_rad_of_isometric hA hX' hnum' (isometric_pull_oneB (p := p) π hπ)
    rwa [pullCl_cl]

end GlobalTheory.VertForm.PullForm
