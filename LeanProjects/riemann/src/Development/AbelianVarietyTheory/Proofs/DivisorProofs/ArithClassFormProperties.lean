import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertForm

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem exists_finite_family {D : ℕ} (v : Fin (D + 1) → Cl p) :
    ∃ (N : ℕ) (e : Fin N → HermLB p) (b : Fin (D + 1) → Fin N → ℝ), ∀ j, v j = ∑ m, b j m • cl (e m) := by
  classical
  let S : Finset (HermLB p) := Finset.univ.biUnion fun j => (v j).support
  refine ⟨S.card, fun m => (S.equivFin.symm m : HermLB p), fun j m => v j (S.equivFin.symm m), fun j => ?_⟩
  have hsub : (v j).support ⊆ S := Finset.subset_biUnion_of_mem (fun j => (v j).support) (Finset.mem_univ j)
  have e1 := Equiv.sum_comp S.equivFin.symm (fun s : S => v j s • cl (s : HermLB p))
  have e2 := Finset.sum_coe_sort S (fun s => v j s • cl s)
  refine Eq.trans ?_ (e1.trans e2).symm
  conv_lhs => rw [← Finsupp.sum_single (v j)]
  rw [Finsupp.sum_of_support_subset _ hsub _ (fun _ _ => Finsupp.single_zero _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [cl, Finsupp.smul_single]

theorem sub_sum_mem_rad_of_isometric (hE : GlobalTheory.Published.ArExists) {D : ℕ} [IsIntegral X] (hX : IsArithVar p D)
    {num : Form (Cl p) D} (hnum : IsArForm D num) {κ : Type} [Fintype κ] (F : κ → HermLB p) (m : κ → ℤ)
    (B : HermLB p) (hB : (comb F m).Isometric B) :
    cl B - ∑ c, (m c : ℝ) • cl (F c) ∈ rad num := by
  classical
  intro v j
  obtain ⟨N, e, b, hv⟩ := exists_finite_family v
  let F' : κ ⊕ Fin N → HermLB p := Sum.elim F e
  obtain ⟨Φ, hΦ⟩ := ((hE k X p D hX).2 (κ ⊕ Fin N) F').1
  let G : Option (κ ⊕ Fin N) → HermLB p := fun o => o.elim B F'
  let A : Option (κ ⊕ Fin N) → κ ⊕ Fin N → ℤ := fun o => o.elim (Sum.elim m 0) fun c => Pi.single c 1
  have hA : ∀ o, (comb F' (A o)).Isometric (G o) := by
    rintro (_ | c)
    · refine HermLB.Isometric.trans (HermLB.icls_eq_iff.1 ?_) hB
      simp [A, F', ArInt.icls_comb, Fintype.sum_sum_type]
    · exact ArInt.isometric_comb_single F' c
  have hG := (((Published.arIso_holds k X p D hX).2 _ F' Φ hΦ).2.2 _ G A hA)
  let a : Fin (D + 1) → Option (κ ⊕ Fin N) → ℝ := fun i o =>
    if i = j then o.elim 1 (Sum.elim (fun c => -(m c : ℝ)) 0) else o.elim 0 (Sum.elim 0 (b i))
  have h1 := hnum _ G _ hG a
  have h2 : (fun i => ∑ o, a i o • cl (G o)) = Function.update v j (cl B - ∑ c, (m c : ℝ) • cl (F c)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [a, G, F', Fintype.sum_option, Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
    · simp [a, G, F', hi, Fintype.sum_option, Fintype.sum_sum_type, hv i]
  rw [← h2, ← h1]
  have h3 : aeval (fun o => lin fun c => (A o c : ℝ)) (lin (a j)) = 0 := by
    rw [ArInt.aeval_lin]
    have : (fun c : κ ⊕ Fin N => ∑ o, a j o * (A o c : ℝ)) = 0 := by
      funext c
      rcases c with c | c <;> simp [a, A, Fintype.sum_option, Fintype.sum_sum_type, Pi.single_apply]
    rw [this]
    simp [lin]
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) h3, map_zero]

theorem arForm_rad_rules : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num →
    (∀ L M : HermLB p, cl (L.tens M) - (cl L + cl M) ∈ rad num) ∧ (∀ L : HermLB p, cl L.dual + cl L ∈ rad num) ∧
    (∀ L M : HermLB p, L.Isometric M → cl L - cl M ∈ rad num) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      cl (ArInt.comb L n) - ∑ i, (n i : ℝ) • cl (L i) ∈ rad num := by
  intro hC k _ X _ p D hX num hnum
  have hE := hC.arExists
  refine ⟨fun L M => ?_, fun L => ?_, fun L M h => ?_,
    fun ι _ L n => sub_sum_mem_rad_of_isometric hE hX hnum L n _ (HermLB.Isometric.refl _)⟩
  · have := sub_sum_mem_rad_of_isometric hE hX hnum ![L, M] 1 (L.tens M)
      (HermLB.icls_eq_iff.1 (by simp [ArInt.icls_comb, HermLB.icls_tens, Fin.sum_univ_two]))
    simpa [Fin.sum_univ_two] using this
  · have := sub_sum_mem_rad_of_isometric hE hX hnum (fun _ : Unit => L) (-1) L.dual
      (HermLB.icls_eq_iff.1 (by simp [ArInt.icls_comb, HermLB.icls_dual]))
    simpa using this
  · have := sub_sum_mem_rad_of_isometric hE hX hnum (fun _ : Unit => M) 1 L
      (HermLB.Isometric.trans (HermLB.icls_eq_iff.1 (by simp [ArInt.icls_comb])) h.symm)
    simpa using this

end GlobalTheory.VertForm
