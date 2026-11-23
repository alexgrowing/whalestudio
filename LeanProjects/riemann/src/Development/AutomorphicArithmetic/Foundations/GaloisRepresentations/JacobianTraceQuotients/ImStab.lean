import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.HeckeMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.JacNorm

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem exists_dom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ s : Fin n → kˣ, Dom s ∧ Dom (s * t) := by
  classical
  set c : Fin n → kˣ := fun i => if valuation k ((t i : kˣ) : k) ≤ 1 then (t i)⁻¹ else t i with hc
  have hv : ∀ u : kˣ, valuation k (u : k) ≠ 0 := fun u => by simp
  have hc1 : ∀ i, 1 ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩
    · exact le_of_lt (not_le.mp h)
  have hct : ∀ i, valuation k ((t i : kˣ) : k) ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact h.trans (one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩)
    · exact le_rfl
  have hct' : ∀ i, (valuation k ((t i : kˣ) : k))⁻¹ ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
    · exact (inv_le_one₀ (zero_lt_iff.mpr (hv _))).mpr (le_of_lt (not_le.mp h)) |>.trans
        (le_of_lt (not_le.mp h))
  set x : kˣ := ∏ i, c i with hx
  have hx1 : 1 ≤ valuation k (x : k) := by
    rw [hx, Units.coe_prod, map_prod]
    exact Finset.one_le_prod' (fun i _ => hc1 i)
  have hx2 : ∀ i j, i ≠ j →
      valuation k ((c i : kˣ) : k) * valuation k ((c j : kˣ) : k) ≤ valuation k (x : k) := by
    intro i j hij
    rw [hx, Units.coe_prod, map_prod,
      ← Finset.prod_pair (f := fun l => valuation k ((c l : kˣ) : k)) hij]
    exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _) (fun l _ _ => hc1 l)
  refine ⟨fun i => x ^ (i : ℕ), ?_, ?_⟩
  · intro i j hij
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right₀ hx1 (le_of_lt hij)
  · intro i j hij
    simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    have hle : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, pow_add, pow_add, pow_one, mul_assoc, mul_assoc]
    refine mul_le_mul_right ?_ _
    have h1 : valuation k (x : k) ≤ valuation k (x : k) ^ m * valuation k (x : k) :=
      le_mul_of_one_le_left' (one_le_pow₀ hx1)
    have h2 : valuation k ((t i : kˣ) : k) ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) := by
      have hne : i ≠ j := ne_of_lt hij
      calc valuation k ((t i : kˣ) : k)
          = valuation k ((t i : kˣ) : k) * ((valuation k ((t j : kˣ) : k))⁻¹ *
              valuation k ((t j : kˣ) : k)) := by rw [inv_mul_cancel₀ (hv _), mul_one]
        _ = (valuation k ((t i : kˣ) : k) * (valuation k ((t j : kˣ) : k))⁻¹) *
              valuation k ((t j : kˣ) : k) := by rw [mul_assoc]
        _ ≤ (valuation k ((c i : kˣ) : k) * valuation k ((c j : kˣ) : k)) *
              valuation k ((t j : kˣ) : k) :=
            mul_le_mul_left (mul_le_mul' (hct i) (hct' j)) _
        _ ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) :=
            mul_le_mul_left (hx2 i j hne) _
    calc valuation k ((t i : kˣ) : k)
        ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) := h2
      _ ≤ (valuation k (x : k) ^ m * valuation k (x : k)) * valuation k ((t j : kˣ) : k) :=
          mul_le_mul_left h1 _
      _ = valuation k (x : k) * (valuation k (x : k) ^ m * valuation k ((t j : kˣ) : k)) := by
          rw [mul_comm (valuation k (x : k) ^ m), mul_assoc]

theorem UpperTheory.Gal.Join.imStab :
    UpperTheory.Gal.Join.ImStab := by
  unfold UpperTheory.Gal.Join.ImStab UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π hπ K hK
  have hH0 := heckeMul
  have hJ0 := jacNorm
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep at hH0
  unfold UpperTheory.Gal.Join.JacNorm UpperTheory.Gal.Join.ForRep at hJ0
  have hH := hH0 k n V π
  have hJ := hJ0 k n V π
  beta_reduce at hH hJ
  have hco := hK.co
  have hco' : IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (K : Set (GL (Fin n) k)) := by
    unfold UpperTheory.ConvolutionTheory.C.CO at hco
    exact hco
  obtain ⟨e, he, hcomm⟩ := avgEx (GL (Fin n) k) V π hπ.1 K hco
  unfold UpperTheory.Gal.Join.imK
  haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hco'.2 hco'.1
  haveI hfd : FiniteDimensional ℂ
      (Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K)) :=
    Module.Finite.map _ _
  have hD : ∀ t : Fin n → kˣ, Dom t → ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ
      (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K) := by
    intro t ht y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    rw [← (hH K hK e he t ht v hv).2]
    exact Submodule.mem_map_of_mem (he.mem _)
  have key : ∀ (s : Fin n → kˣ) (z : Jacquet π (unipB k (Fin n))),
      jacBU π s⁻¹ (jacBU π s z) = z := fun s z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hU : ∀ t : Fin n → kˣ, ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ
      (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K) := by
    intro t y hy
    obtain ⟨s, hs, hst⟩ := exists_dom t
    let f := (jacBU π s).restrict (fun z hz => hD s hs z hz)
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h1 := congrArg (fun z => jacBU π s⁻¹ z) (congrArg Subtype.val hab)
      simpa [f, LinearMap.restrict_apply, key] using h1
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨z, hz⟩ := hsurj ⟨_, hD _ hst y hy⟩
    have hz' : jacBU π s z = jacBU π (s * t) y := by
      have := congrArg Subtype.val hz
      simpa [f, LinearMap.restrict_apply] using this
    have h2 : jacBU π s (jacBU π t y) = jacBU π s z := by
      rw [hz', map_mul, Module.End.mul_apply]
    have h3 : jacBU π t y = z := by
      have := congrArg (fun w => jacBU π s⁻¹ w) h2
      simpa [key] using this
    rw [h3]
    exact z.2
  refine ⟨hfd, ?_, ?_⟩
  · intro t y hy
    have hpos : (0 : ℝ) < √(deltaB t) := Real.sqrt_pos.mpr (deltaB_pos t)
    have hne : ((√(deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have h1 : jacB π t y = (((√(deltaB t) : ℝ) : ℂ))⁻¹ • jacBU π t y := by
      rw [hJ t y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (hU t y hy)
  · intro σ A hA hσ y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    have hinv : ∀ g : GL (Fin n) k, sg σ (sg σ.symm g) = g := by
      intro g
      ext i j
      rw [sg_val, sg_val, RingEquiv.apply_symm_apply]
    have hs1 : ∀ g ∈ K, sg σ g ∈ K := fun g hg => (hσ g).mpr hg
    have hs2 : ∀ g ∈ K, ∃ h ∈ K, sg σ h = g := by
      intro g hg
      refine ⟨sg σ.symm g, (hσ _).mp ?_, hinv g⟩
      rw [hinv]
      exact hg
    have hAe := hcomm (sg σ) A hA hs1 hs2 v
    have hev : e v = v := he.fix v hv
    unfold UpperTheory.Gal.LocD.jacA
    refine Submodule.mem_map.mpr ⟨A v, ?_, rfl⟩
    rw [← hev, hAe]
    exact he.mem _
