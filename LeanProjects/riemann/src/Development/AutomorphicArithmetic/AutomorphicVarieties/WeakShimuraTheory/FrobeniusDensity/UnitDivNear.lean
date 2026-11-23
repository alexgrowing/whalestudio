import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.MuChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusDensity.RootChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ Ω}

omit [IsAlgClosure ℚ Ω] in
private theorem res_mem (g : G K Ω) : resQ K g ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact g.commutes ⟨x, hx⟩

omit [IsAlgClosure ℚ Ω] in
private theorem val_agree {A B : ValuationSubring Ω} (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) {x : Ω} (hx : x ∈ K) :
    B.valuation x < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', h x hx, h _ (inv_mem hx)]

private theorem algClosure (K : IntermediateField ℚ Ω) : IsAlgClosure K Ω := by
  exact ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem conj_of_agree [NumberField K] {A B : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) : ∃ g : G K Ω, ∀ x, g x ∈ B ↔ x ∈ A := by
  haveI := algClosure K
  have hAT : A ≠ ⊤ := fun hT => ((places K Ω l A).2.1 hT).2 hA
  obtain ⟨v, hv⟩ := (places K Ω l A).1 hAT
  have hBv : IsPlaceOver B v := fun x => (val_agree h (SetLike.coe_mem (x : K))).trans (hv x)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv hBv
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show σ⁻¹ (σ x) ∈ A ↔ x ∈ A
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

private theorem differs [NumberField K] {A B B' : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1)
    (hD : Dec (F := ℚ) A ≤ K.fixingSubgroup) (h : ∀ x ∈ K, x ∈ B ↔ x ∈ A) {σ : G ℚ Ω} (hσ : σ ∉ K.fixingSubgroup)
    (hB : ∀ x, σ x ∈ B ↔ x ∈ B') : ∃ x ∈ K, ¬ (x ∈ B' ↔ x ∈ A) := by
  by_contra hne
  push_neg at hne
  obtain ⟨g, hg⟩ := conj_of_agree hA hne
  obtain ⟨g', hg'⟩ := conj_of_agree hA h
  set τ : G ℚ Ω := (resQ K g')⁻¹ * σ * resQ K g with hτ
  have key : ∀ y, τ y ∈ A ↔ y ∈ A := by
    intro y
    have e : g' (τ y) = σ (g y) := by
      show resQ K g' (((resQ K g')⁻¹ * σ * resQ K g) y) = σ (resQ K g y)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    calc τ y ∈ A ↔ g' (τ y) ∈ B := (hg' _).symm
      _ ↔ σ (g y) ∈ B := by rw [e]
      _ ↔ g y ∈ B' := hB _
      _ ↔ y ∈ A := hg y
  have hτD : τ ∈ Dec (F := ℚ) A := by
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← key]
    show τ (τ⁻¹ x) ∈ A ↔ x ∈ A
    rw [mul_inv_apply]
  have hτK := hD hτD
  apply hσ
  have e2 : σ = resQ K g' * τ * (resQ K g)⁻¹ := by
    rw [hτ]
    group
  rw [e2]
  exact K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem (res_mem g') hτK)
    (K.fixingSubgroup.inv_mem (res_mem g))

private theorem exists_lift [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ (σ : G ℚ Ω) (τ : K ≃+* K), σ ∉ K.fixingSubgroup ∧ IsLift τ σ.toRingEquiv := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK]
  haveI : Nontrivial Gal(K/ℚ) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(K/ℚ))
  let σ : G ℚ Ω := τ.liftNormal Ω
  have hlift : ∀ x : K, σ (x : Ω) = (τ x : Ω) := fun x => AlgEquiv.liftNormal_commutes τ Ω x
  refine ⟨σ, τ.toRingEquiv, ?_, fun x => hlift x⟩
  intro hmem
  apply hτ
  ext x
  have h1 := (IntermediateField.mem_fixingSubgroup_iff K σ).mp hmem x x.2
  rw [hlift] at h1
  exact h1

private theorem unit_div_near {a b : ℤ_[l]ˣ} (ha : ‖(a : ℤ_[l]) - 1‖ < 1) (hb : ‖(b : ℤ_[l]) - 1‖ < 1) :
    ‖((a / b : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  have hb1 : ‖((b⁻¹ : ℤ_[l]ˣ) : ℤ_[l])‖ = 1 := PadicInt.isUnit_iff.mp (Units.isUnit _)
  have e : ((a / b : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((a : ℤ_[l]) - b) * ((b⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e, norm_mul, hb1, mul_one]
  have e2 : (a : ℤ_[l]) - b = ((a : ℤ_[l]) - 1) + (1 - (b : ℤ_[l])) := by ring
  rw [e2]
  refine lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt ha ?_)
  rwa [norm_sub_rev]

private theorem exists_open [NumberField K] (f : G K Ω → PadicAlgCl l) (hf : Continuous f) (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    ∃ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) ∧ ∀ s ∈ U, f s ^ n = 1 → f s = 1 := by
  classical
  haveI := algClosure K
  let F : Set (PadicAlgCl l) := {z | z ^ n = 1 ∧ z ≠ 1}
  have hF : F.Finite := by
    apply (Polynomial.nthRoots n (1 : PadicAlgCl l)).toFinset.finite_toSet.subset
    intro z hz
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hz.1
  have hV : IsOpen (f ⁻¹' Fᶜ) := hF.isClosed.isOpen_compl.preimage hf
  have h1V : (1 : G K Ω) ∈ f ⁻¹' Fᶜ := by
    simp [F, h1]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1V
  refine ⟨H.toOpenSubgroup.toSubgroup, H.toOpenSubgroup.isOpen, fun s hs hsn => ?_⟩
  by_contra hne
  exact hH hs ⟨hsn, hne⟩

end SlopeTestRemainingChoices

private theorem padicInt_norm_units_mul_sub_one_lt_one {l : ℕ} [Fact l.Prime] {a b : ℤ_[l]ˣ} (ha : ‖(a : ℤ_[l]) - 1‖ < 1)
    (hb : ‖(b : ℤ_[l]) - 1‖ < 1) : ‖((a * b : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  have e : ((a * b : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((a : ℤ_[l]) - 1) * b + ((b : ℤ_[l]) - 1) := by
    rw [Units.val_mul]
    ring
  rw [e]
  refine lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt ?_ hb)
  rw [norm_mul]
  calc ‖(a : ℤ_[l]) - 1‖ * ‖(b : ℤ_[l])‖ ≤ ‖(a : ℤ_[l]) - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact ha

theorem UpperTheory.V.Ws.Tw.bt0 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ (t : G K Ω →* Multiplicative ℤ_[l]) (β : G K Ω →* (PadicAlgCl l)ˣ) (c₁ : Coef l), Continuous t ∧ t.ker ≤ β.ker ∧ Continuous β ∧ (∀ s, (β s : PadicAlgCl l) ∈ c₁.O ∧ ‖(β s : PadicAlgCl l) - 1‖ < 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → t s * t s' = 1) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → β s * β s' = 1) ∧ (∀ B : ValuationSubring Ω, ¬ B.valuation (l : Ω) < 1 → Ine (F := K) B ≤ t.ker) ∧ ∃ U : Subgroup (G K Ω), IsOpen (U : Set (G K Ω)) ∧ ∀ B : ValuationSubring Ω, (∀ x ∈ K, x ∈ B ↔ x ∈ A) → ∀ s ∈ U ⊓ Ine (F := K) B, (β s : PadicAlgCl l) ^ 2 = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ K Ω l s : ℤ_[l]) := by
  intro Ω _ _ _ l _ hl K _ _ hK A hA hD
  haveI := algClosure K
  obtain ⟨μ, n, hn, hμc, hμ1, hμconj, hμker⟩ := Tw.muChar Ω l hl K hK A hA hD
  obtain ⟨σ, τ, hσ, hlift⟩ := exists_lift hK
  have hσi : σ⁻¹ ∉ K.fixingSubgroup := fun h => hσ (by simpa using K.fixingSubgroup.inv_mem h)
  have hres : ∀ s, resQ K (conjGal hlift s) = σ⁻¹ * resQ K s * σ⁻¹⁻¹ := by
    intro s
    rw [inv_inv]
    ext x
    rfl
  have hconj : ∀ s, μ s * μ (conjGal hlift s) = cycZ K Ω l s ^ n :=
    fun s => hμconj σ⁻¹ hσi s _ (hres s)
  have hcyc : ∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ →
      cycZ K Ω l s' = cycZ K Ω l s := by
    intro c _ s s' h
    show cycZ ℚ Ω l (resQ K s') = cycZ ℚ Ω l (resQ K s)
    rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  let π : G K Ω →* ℤ_[l]ˣ :=
    { toFun := fun s => μ s ^ 2 / cycZ K Ω l s ^ n
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_pow]
        exact mul_div_mul_comm _ _ _ _ }
  have hπ : ∀ s, π s = μ s ^ 2 / cycZ K Ω l s ^ n := fun s => rfl
  have hπc : Continuous π := by
    show Continuous (fun s => μ s ^ 2 / cycZ K Ω l s ^ n)
    exact (hμc.pow 2).div' ((continuous_cycZ K Ω l).pow n)
  have hπ1 : ∀ s, ‖((π s : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
    intro s
    rw [hπ, ← hconj s, sq]
    exact unit_div_near (padicInt_norm_units_mul_sub_one_lt_one (hμ1 s) (hμ1 s)) (padicInt_norm_units_mul_sub_one_lt_one (hμ1 s) (hμ1 _))
  have hπconj : ∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ →
      π s * π s' = 1 := by
    intro c hc s s' h
    have e := hμconj c hc s s' h
    rw [hπ, hπ, hcyc c hc s s' h, div_mul_div_comm, div_eq_one]
    calc μ s ^ 2 * μ s' ^ 2 = (μ s * μ s') ^ 2 := (mul_pow _ _ _).symm
      _ = (cycZ K Ω l s ^ n) ^ 2 := by rw [e]
      _ = cycZ K Ω l s ^ n * cycZ K Ω l s ^ n := sq _
  obtain ⟨t, β, c₁, ht, hker, htβ, hβc, hβO, hβpow, hβconj⟩ :=
    Tw.rootChar l hl (G K Ω) π hπc hπ1 (2 * n) (by omega)
  let f : G K Ω → PadicAlgCl l := fun s => (β s : PadicAlgCl l) ^ 2 *
      algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have hf : Continuous f := by
    have hc : Continuous (fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x) := by
      have e : (fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x) =
          fun x : ℤ_[l] => algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) := by
        funext x
        exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l) x
      rw [e]
      exact (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
    exact ((Units.continuous_val.comp hβc).pow 2).mul
      (hc.comp (Units.continuous_val.comp ((continuous_cycZ K Ω l).inv)))
  have hf1 : f 1 = 1 := by simp [f]
  obtain ⟨U, hUo, hU⟩ := exists_open f hf hf1 hn
  refine ⟨t, β, c₁, ht, htβ, hβc, hβO, ?_, ?_, ?_, ?_⟩
  · intro c hc s s' h
    have hm : s * s' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      exact hπconj c hc s s' h
    rw [← hker] at hm
    rw [← map_mul]
    exact hm
  · intro c hc s s' h
    exact hβconj s s' (hπconj c hc s s' h)
  · intro B hB
    rw [hker]
    intro s hs
    have hdis : ∃ x ∈ K, ¬(x ∈ B ↔ x ∈ A) := by
      by_contra hne
      push_neg at hne
      exact hB ((val_agree hne (natCast_mem K l)).mpr hA)
    have h1 : μ s = 1 := hμker B hdis hs
    have h2 : cycZ K Ω l s = 1 := (places K Ω l B).2.2.2 hB hs
    rw [MonoidHom.mem_ker, hπ, h1, h2, one_pow, one_pow, div_one]
  · refine ⟨U, hUo, fun B hB s hs => ?_⟩
    obtain ⟨hsU, hsI⟩ := Subgroup.mem_inf.mp hs
    have hBB : ∀ x, σ x ∈ B ↔ x ∈ σ⁻¹ • B := by
      intro x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      rfl
    have hs' := conjGal_mem_Ine hlift (fun x => hBB x) hsI
    have hdis := differs hA hD hB hσ hBB
    have hμs' : μ (conjGal hlift s) = 1 := hμker _ hdis hs'
    have hμs : μ s = cycZ K Ω l s ^ n := by
      have e := hconj s
      rwa [hμs', mul_one] at e
    have hπs : π s = cycZ K Ω l s ^ n := by
      rw [hπ, hμs, div_eq_iff_eq_mul, sq]
    have hβ2n := hβpow s
    rw [hπs] at hβ2n
    have hab : algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l])) *
        algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hpow : f s ^ n = 1 := by
      show ((β s : PadicAlgCl l) ^ 2 *
        algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) ^ n = 1
      rw [mul_pow, ← pow_mul, hβ2n, Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hab, one_pow]
    have h1 := hU s hsU hpow
    change (β s : PadicAlgCl l) ^ 2 *
      algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 at h1
    calc (β s : PadicAlgCl l) ^ 2 = (β s : PadicAlgCl l) ^ 2 *
          (algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) *
            algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l]))) := by
          rw [mul_comm (algebraMap ℤ_[l] (PadicAlgCl l) (((cycZ K Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])), hab,
            mul_one]
      _ = algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ K Ω l s : ℤ_[l])) := by
          rw [← mul_assoc, h1, one_mul]
