import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerticalCartierDivisorOfEquationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianBundleCanonicalOfVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOfTensorSectionAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleClassInRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOnOversOfCanonicalVerticalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

theorem sum_succ_sub_castSucc_eq : ∀ (N : ℕ) (f : Fin (N + 1) → ℝ),
    ∑ i : Fin N, (f i.succ - f i.castSucc) = f (Fin.last N) - f 0
  | 0, f => by simp
  | N + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have := sum_succ_sub_castSucc_eq N (fun j => f j.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this, Fin.succ_last, Fin.castSucc_zero]
    ring

section Loc

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_pow_of {x : X} {f : X.functionField} (h : UnitAt x f) : ∀ m : ℕ, UnitAt x (f ^ m)
  | 0 => by simpa using unitAt_one x
  | m + 1 => by rw [pow_succ]; exact (unitAt_pow_of h m).mul h

theorem vert_add {p : ℕ} {D E : CartierDiv X} (hD : Vert p D) (hE : Vert p E) : Vert p (D + E) :=
  fun x hx => by simpa using (hD x hx).add (hE x hx)

theorem vert_neg {p : ℕ} {D : CartierDiv X} (hD : Vert p D) : Vert p (-D) :=
  fun x hx => by simpa using (hD x hx).neg

theorem vert_sub {p : ℕ} {D E : CartierDiv X} (hD : Vert p D) (hE : Vert p E) : Vert p (D - E) := by
  rw [sub_eq_add_neg]; exact vert_add hD (vert_neg hE)

theorem vert_nsmul {p : ℕ} {D : CartierDiv X} (hD : Vert p D) (m : ℕ) : Vert p (m • D) :=
  fun x hx => by simpa using (hD x hx).nsmul m

theorem trivOn_pow {p : ℕ} {e b : X → X.functionField} (h : TrivOn p e b)
    (he : ∀ x, Ov p x → RegAt x (e x)) (m : ℕ) : TrivOn p e fun x => b x ^ m := by
  obtain ⟨t, ht⟩ := h
  refine ⟨fun x => t x ^ m, fun x hx => ⟨fun hn => ?_, (ht x hx).2.mono fun z hz hz' hn => ?_⟩⟩
  · have := unitAt_pow_of ((ht x hx).1 hn) m
    simpa [mul_pow] using this
  · have h1 := hz hz' hn
    by_cases h0 : e z = 0
    · simpa [h0] using regAt_zero z
    set u : X.functionField := (t x : X.functionField) / t z with hu
    have hu' : RegAt z u := by
      have e1 : u = ((u - 1) / e z) * e z + 1 := by rw [div_mul_cancel₀ _ h0, sub_add_cancel]
      rw [e1]
      exact (h1.mul (he z hz')).add (unitAt_one z).regAt
    have e2 : (((t x ^ m : X.functionFieldˣ) : X.functionField) / ((t z ^ m : X.functionFieldˣ) : X.functionField) - 1) / e z =
        ((u - 1) / e z) * ∑ i ∈ Finset.range m, u ^ i := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← div_pow, ← hu, ← geom_sum_mul, mul_comm, mul_div_right_comm]
    rw [e2]
    exact (loc z).mul_mem h1 ((loc z).sum_mem fun i _ => (loc z).pow_mem hu' i)

end Loc

section Num

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {n : ℕ}
  {num : Form (Cl q) (n + 1)}

theorem cl_sub_mem_rad_of_can (hP : Hypotheses2) (hX : IsArithVar q (n + 1)) (hF : IsArForm (n + 1) num)
    (hs : IsSymm num) {M M' : HermLB q} {E : CartierDiv X} (h : Can M E) (h' : Can M' E) :
    cl M - cl M' ∈ rad num := by
  have hR := GlobalTheory.T.arith_class_form_properties hP.p4 k X q (n + 1) hX num hF
  have hd : Can M'.dual (-E) := ((GlobalTheory.T.divisor_of_tensor_section_add k X q M' M').1 E E h' h').2
  have ht : Can (M.tens M'.dual) 0 := by
    have := ((GlobalTheory.T.divisor_of_tensor_section_add k X q M M'.dual).1 E (-E) h hd).1
    rwa [add_neg_cancel] at this
  have h1 := GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hF hs _ ht
  have h2 := hR.1 M M'.dual
  have h3 := hR.2.1 M'
  convert (rad num).sub_mem ((rad num).sub_mem h1 h2) h3 using 1
  abel

theorem cl_sub_nsmul_mem_rad_of_can (hP : Hypotheses2) (hX : IsArithVar q (n + 1)) (hF : IsArForm (n + 1) num)
    (hs : IsSymm num) {p : ℕ} (hp : p ≠ 0) {M : HermLB q} {E : CartierDiv X} (h : Can M E) (hV : Vert p E) :
    ∀ (m : ℕ) (M' : HermLB q), Can M' (m • E) → cl M' - (m : ℝ) • cl M ∈ rad num := by
  intro m
  induction m with
  | zero =>
    intro M' h'
    rw [zero_nsmul] at h'
    simpa using GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hF hs M' h'
  | succ m ih =>
    intro M' h'
    obtain ⟨Mm, hMm⟩ := GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp (m • E) (vert_nsmul hV m)
    have ht := ((GlobalTheory.T.divisor_of_tensor_section_add k X q Mm M).1 _ _ hMm h).1
    rw [← succ_nsmul] at ht
    have h1 := cl_sub_mem_rad_of_can hP hX hF hs h' ht
    have h2 := (GlobalTheory.T.arith_class_form_properties hP.p4 k X q (n + 1) hX num hF).1 Mm M
    have h3 := ih Mm hMm
    convert (rad num).add_mem ((rad num).add_mem h1 h2) h3 using 1
    rw [Nat.cast_succ, add_smul, one_smul]
    abel

end Num

theorem moves_of_link : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ),
    IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num →
    ∀ (G : Fin n → HermLB q) (p m N : ℕ), p.Prime → ∀ c c' : X → Fin N → X.functionFieldˣ, Link p c c' →
    Moves num G p m c c' := by
  intro hP k _ X _ q n hX num hF hs G p m N hp c c' hL
  obtain ⟨η, γ, hV, hO, hT⟩ := hL
  have hp0 : p ≠ 0 := hp.ne_zero
  have hR := GlobalTheory.T.arith_class_form_properties hP.p4 k X q (n + 1) hX num hF
  choose E hEV hEq using fun j : Fin (N + 1) => GlobalTheory.T.exists_vertical_cartier_divisor_of_equations X p (fun x => η x j) (hV j)
  choose H hH using fun j => GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp0 (E j) (hEV j)
  have hDV : ∀ i : Fin N, Vert p (E i.succ - E i.castSucc) := fun i => vert_sub (hEV _) (hEV _)
  choose Δ hΔ using fun i : Fin N => GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp0 _ (vert_nsmul (hDV i) m)
  choose K hK using fun i : Fin N => GlobalTheory.T.exists_hermitian_bundle_canonical_of_vertical k X q p hp0 _ (vert_neg (vert_nsmul (hEV i.castSucc) m))

  have hPc : ∀ i : Fin N, Can ((H i.succ).tens (H i.castSucc).dual) (E i.succ - E i.castSucc) := fun i => by
    have hd := ((GlobalTheory.T.divisor_of_tensor_section_add k X q (H i.castSucc) (H i.castSucc)).1 _ _ (hH _) (hH _)).2
    have := ((GlobalTheory.T.divisor_of_tensor_section_add k X q (H i.succ) (H i.castSucc).dual).1 _ _ (hH _) hd).1
    rwa [← sub_eq_add_neg] at this

  have hPr : ∀ i : Fin N, cl ((H i.succ).tens (H i.castSucc).dual) - (cl (H i.succ) - cl (H i.castSucc)) ∈ rad num := fun i => by
    convert (rad num).add_mem (hR.1 (H i.succ) (H i.castSucc).dual) (hR.2.1 (H i.castSucc)) using 1
    abel
  have hΔr : ∀ i : Fin N, cl (Δ i) - (m : ℝ) • (cl (H i.succ) - cl (H i.castSucc)) ∈ rad num := fun i => by
    have h1 := cl_sub_nsmul_mem_rad_of_can hP hX hF hs hp0 (hPc i) (hDV i) m (Δ i) (hΔ i)
    convert (rad num).add_mem h1 ((rad num).smul_mem (m : ℝ) (hPr i)) using 1
    simp only [smul_sub]
    abel

  have hKr : ∀ i : Fin N, cl (K i) + (m : ℝ) • cl (H i.castSucc) ∈ rad num := fun i => by
    have hd := ((GlobalTheory.T.divisor_of_tensor_section_add k X q (K i) (K i)).1 _ _ (hK i) (hK i)).2
    rw [neg_neg] at hd
    have h1 := cl_sub_nsmul_mem_rad_of_can hP hX hF hs hp0 (hH i.castSucc) (hEV _) m _ hd
    convert (rad num).sub_mem (hR.2.1 (K i)) h1 using 1
    abel

  have hlast : bil num (fun j => cl (G j)) (cl (H (Fin.last N))) (cl (H (Fin.last N))) = 0 := by
    obtain ⟨r, hr, hrd, -⟩ := hH (Fin.last N)
    refine GlobalTheory.T.trivial_on_overs_of_canonical_vertical hP k X q n hX num hF hs G p hp (H (Fin.last N)) (H (Fin.last N)) (E (Fin.last N))
      (fun x => η x (Fin.last N)) (fun x => η x (Fin.last N)) (hH _) (hEV _)
      (fun x hx => ⟨hEq _ x hx, (hV (Fin.last N) x hx).1⟩) ⟨r, hr, fun x hx => hrd ▸ hEq _ x hx⟩
      ⟨fun _ => γ⁻¹, fun x hx => ⟨fun _ => ?_, .of_forall fun z _ _ => by simpa using regAt_zero z⟩⟩
    have := (hO x hx).2.1
    rwa [Units.val_inv_eq_inv_val, inv_mul_eq_div]

  have h0 : bil num (fun j => cl (G j)) (cl (H 0)) (cl (H 0)) = 0 := by
    have hE0 : E 0 = 0 := CartierDiv.ext_of_isEqn fun x => ⟨1, ?_, CartierDiv.isEqn_zero x⟩
    · have h00 := hH 0
      rw [hE0] at h00
      exact bil_rad_left _ (GlobalTheory.T.canonical_bundle_class_in_radical hP k X q n hX num hF hs _ h00) _
    by_cases hx : Ov p x
    · exact (hEq 0 x hx).iff_unitAt.2 (by simpa using (hO x hx).1.inv)
    · exact hEV 0 x hx
  refine ⟨Δ, fun i => m • (E i.succ - E i.castSucc), fun i => ⟨hΔ i, vert_nsmul (hDV i) m, fun x hx => ?_⟩,
    fun L hL => ?_⟩
  · have h1 := ((hEq i.succ x hx).sub (hEq i.castSucc x hx)).nsmul m
    refine h1.iff_unitAt.2 ?_
    have := unitAt_pow_of ((hO x hx).2.2 i).2 m
    rw [div_pow] at this
    simpa only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] using this

  have hstep : ∀ i : Fin N, bil num (fun j => cl (G j)) (cl (H i.succ) - cl (H i.castSucc)) (cl (L i) - (m : ℝ) • cl (H i.castSucc)) = 0 := fun i => by
    obtain ⟨ρ, hρ, hρe⟩ := hL i
    obtain ⟨r, hr, hrd, -⟩ := hK i
    obtain ⟨s, hs', hsd⟩ := (GlobalTheory.T.divisor_of_tensor_section_add k X q (L i) (K i)).2 ρ hρ r hr
    have hz := GlobalTheory.T.trivial_on_overs_of_canonical_vertical hP k X q n hX num hF hs G p hp ((H i.succ).tens (H i.castSucc).dual) ((L i).tens (K i))
      (E i.succ - E i.castSucc) (fun x => η x i.succ / η x i.castSucc) (fun x => (c x i / η x i.castSucc) ^ m)
      (hPc i) (hDV i)
      (fun x hx => ⟨(hEq _ x hx).sub (hEq _ x hx), by
        simpa only [Units.val_div_eq_div_val] using ((hO x hx).2.2 i).1⟩)
      ⟨s, hs', fun x hx => by
        rw [hsd, hrd]
        have := (hρe x hx).add (((hEq i.castSucc x hx).nsmul m).neg)
        beta_reduce
        rwa [div_pow, div_eq_mul_inv]⟩
      (by
        have := trivOn_pow (hT i) (fun x hx => ((hO x hx).2.2 i).1) m
        simpa only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] using this)
    have hB : cl ((L i).tens (K i)) - (cl (L i) - (m : ℝ) • cl (H i.castSucc)) ∈ rad num := by
      convert (rad num).add_mem (hR.1 (L i) (K i)) (hKr i) using 1
      abel
    rwa [bil_congr _ hs (hPr i) hB] at hz

  have hkey : ∀ i : Fin N, bil num (fun j => cl (G j)) (cl (L i) + cl (Δ i)) (cl (L i) + cl (Δ i)) - bil num (fun j => cl (G j)) (cl (L i)) (cl (L i)) =
      (m : ℝ) ^ 2 * (bil num (fun j => cl (G j)) (cl (H i.succ)) (cl (H i.succ)) - bil num (fun j => cl (G j)) (cl (H i.castSucc)) (cl (H i.castSucc))) := fun i => by
    have hc : cl (L i) + cl (Δ i) - (cl (L i) + (m : ℝ) • (cl (H i.succ) - cl (H i.castSucc))) ∈ rad num := by
      convert hΔr i using 1; abel
    rw [bil_congr _ hs hc hc]
    have hb := hstep i
    have s1 := bil_symm (fun j => cl (G j)) hs (cl (H i.succ)) (cl (H i.castSucc))
    have s2 := bil_symm (fun j => cl (G j)) hs (cl (H i.succ)) (cl (L i))
    have s3 := bil_symm (fun j => cl (G j)) hs (cl (H i.castSucc)) (cl (L i))
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul] at hb ⊢
    linear_combination (2 * (m : ℝ)) * hb + (m : ℝ) ^ 2 * s1 - (m : ℝ) * s2 + (m : ℝ) * s3
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [hkey]
  rw [← Finset.mul_sum, sum_succ_sub_castSucc_eq N (fun j => bil num (fun j => cl (G j)) (cl (H j)) (cl (H j))), hlast, h0]
  ring

end GlobalTheory.LatChain
