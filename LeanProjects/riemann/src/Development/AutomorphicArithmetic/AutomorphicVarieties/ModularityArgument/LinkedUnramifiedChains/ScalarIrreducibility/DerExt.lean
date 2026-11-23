import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Cofinal

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

private theorem artinian_quot (j : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ j) := by
  have : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ j) := by
    refine Ring.krullDimLE_zero_iff.2 fun P hP => ?_
    have hc : (P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))).IsPrime := Ideal.comap_isPrime _ _
    have hle : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) := fun x hx => by
      refine hc.mem_of_pow_mem j ?_
      have : Ideal.Quotient.mk (maximalIdeal B ^ j) (x ^ j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx j)
      show Ideal.Quotient.mk _ (x ^ j) ∈ P
      rw [this]
      exact zero_mem _
    have he : P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = maximalIdeal B :=
      ((maximalIdeal.isMaximal B).eq_of_le hc.ne_top hle).symm
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hne
    have hc' : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) ≠ ⊤ := fun h =>
      hne (by rw [Ideal.eq_top_iff_one]; simpa using (Ideal.eq_top_iff_one _).1 h)
    have h1 : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) :=
      le_antisymm ((le_maximalIdeal hc').trans he.ge) (Ideal.comap_mono hJ.le)
    exact hJ.ne' (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem stab (I : ℕ → Ideal B) (hI : Antitone I) (j : ℕ) :
    ∃ e, ∀ N, e ≤ N → ∀ a ∈ I e, ∃ b ∈ I N, a - b ∈ maximalIdeal B ^ j := by
  haveI := artinian_quot (B := B) j
  let f : ℕ →o (Ideal (B ⧸ maximalIdeal B ^ j))ᵒᵈ :=
    ⟨fun N => OrderDual.toDual ((I N).map (Ideal.Quotient.mk _)), fun a b h => Ideal.map_mono (hI h)⟩
  obtain ⟨e, he⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨e, fun N hN a ha => ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal B ^ j) a ∈ (I N).map (Ideal.Quotient.mk _) := by
    have h2 : (I e).map (Ideal.Quotient.mk (maximalIdeal B ^ j)) = (I N).map (Ideal.Quotient.mk _) := he N hN
    rw [← h2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨b, hb, h3⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
  exact ⟨b, hb, Ideal.Quotient.eq.1 h3.symm⟩

private theorem cofinal [IsAdicComplete (maximalIdeal B) B] (I : ℕ → Ideal B) (hI : Antitone I)
    (h0 : ⨅ N, I N = ⊥) (k : ℕ) : ∃ N, I N ≤ maximalIdeal B ^ k := by
  by_contra hcon
  push_neg at hcon
  choose e he using fun j => stab I hI (k + j)

  let E : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup e + j
  have hE : Monotone E := monotone_nat_of_le_succ fun j =>
    Nat.add_le_add (Finset.sup_mono (Finset.range_mono (Nat.le_succ _))) (Nat.le_succ _)
  have hEe : ∀ j, e j ≤ E j := fun j =>
    le_trans (Finset.le_sup (f := e) (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hEj : ∀ j, j ≤ E j := fun j => Nat.le_add_left _ _
  let P : ℕ → B → Prop := fun j x => x ∈ I (E j) ∧ x ∉ maximalIdeal B ^ k
  have step : ∀ j x, P j x → ∃ y, P (j + 1) y ∧ x - y ∈ maximalIdeal B ^ (k + j) := by
    rintro j x ⟨h1, h2⟩
    obtain ⟨y, hy, hd⟩ := he j (E (j + 1)) ((hEe j).trans (hE (Nat.le_succ j))) x (hI (hEe j) h1)
    refine ⟨y, ⟨hy, fun h => h2 ?_⟩, hd⟩
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_add_right k j) hd) h
    rwa [sub_add_cancel] at this
  obtain ⟨x₀, h1, h2⟩ := SetLike.not_le_iff_exists.1 (hcon (E 0))
  let a : ∀ j, {x // P j x} := fun j => Nat.rec ⟨x₀, h1, h2⟩
    (fun j x => ⟨(step j x.1 x.2).choose, (step j x.1 x.2).choose_spec.1⟩) j
  have ha : ∀ j, (a j).1 - (a (j + 1)).1 ∈ maximalIdeal B ^ (k + j) := fun j =>
    (step j (a j).1 (a j).2).choose_spec.2
  have hchain : ∀ m n, m ≤ n → (a m).1 - (a n).1 ∈ maximalIdeal B ^ (k + m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn k) (ha n))
      rwa [sub_add_sub_cancel] at this
  have hsm : ∀ j : ℕ, (maximalIdeal B ^ j • ⊤ : Ideal B) = maximalIdeal B ^ j := fun j => by simp
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal B) (M := B) inferInstance
    (f := fun j => (a j).1) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      exact Ideal.pow_le_pow_right (Nat.le_add_left _ _) (hchain m n hmn))
  have hL' : ∀ j, (a j).1 - L ∈ maximalIdeal B ^ j := fun j => by
    have := SModEq.sub_mem.1 (hL j)
    simpa using this
  have hmem : ∀ N, L ∈ I N := by
    intro N
    by_cases hNt : I N = ⊤
    · simp [hNt]
    have hb : ⨅ i, maximalIdeal B ^ i • (⊤ : Submodule B (B ⧸ I N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top
    have : Ideal.Quotient.mk (I N) L ∈ (⊥ : Submodule B (B ⧸ I N)) := by
      rw [← hb]
      refine (Submodule.mem_iInf _).2 fun j => ?_
      have h3 : (a (max j N)).1 ∈ I N := hI ((le_max_right j N).trans (hEj _)) (a (max j N)).2.1
      have h4 := Ideal.pow_le_pow_right (le_max_left j N) (hL' (max j N))
      have h5 : Ideal.Quotient.mk (I N) L = ((a (max j N)).1 - L) • (-1 : B ⧸ I N) := by
        rw [Algebra.smul_def]
        have : Ideal.Quotient.mk (I N) (a (max j N)).1 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h3
        simp [Ideal.Quotient.algebraMap_eq, this]
      rw [h5]
      exact Submodule.smul_mem_smul h4 trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hz : L = 0 := by
    have : L ∈ ⨅ N, I N := (Submodule.mem_iInf _).2 hmem
    rwa [h0] at this
  have := hL' k
  rw [hz, sub_zero] at this
  have h6 := (a k).2.2
  exact h6 this

end Cofinal

section Der

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]

private theorem kill (A : Subalgebra O R) (ξ : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (s : Set R)
    (h : ∀ x ∈ s, ∃ hx : x ∈ A, D ⟨x, hx⟩ = 0) {x : R} (hx : x ∈ Algebra.adjoin O s) :
    ∃ h : x ∈ A, D ⟨x, h⟩ = 0 := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination (-1 : K) * this
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap a =>
    refine ⟨A.algebraMap_mem a, ?_⟩
    have : (⟨algebraMap O R a, A.algebraMap_mem a⟩ : A) = a • (1 : A) := by
      ext
      simp [Algebra.smul_def]
    rw [this, map_smul, h1, smul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have : (⟨x + y, add_mem a b⟩ : A) = ⟨x, a⟩ + ⟨y, b⟩ := rfl
    rw [this, map_add, ha, hb, add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨mul_mem a b, ?_⟩
    have : (⟨x * y, mul_mem a b⟩ : A) = ⟨x, a⟩ * ⟨y, b⟩ := rfl
    rw [this, hD, ha, hb, mul_zero, mul_zero, add_zero]

end Der

section Close

variable {O R K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [NormedField K] [Algebra O K]

private theorem close_zero (B : Subalgebra O R) [hB : IsCO O B]
    (hm : maximalIdeal B = (maximalIdeal R).comap (B.val : B →+* R)) (E : B →ₗ[O] K)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal B ^ k, ‖E a‖ ≤ ε) (T : Set B) (hT : ∀ t ∈ T, E t = 0)
    (hd : ∀ x : B, ∀ N : ℕ, ∃ t ∈ T, ((x - t : B) : R) ∈ maximalIdeal R ^ N) : E = 0 := by
  let I : ℕ → Ideal B := fun N => (maximalIdeal R ^ N).comap (B.val : B →+* R)
  have hI : Antitone I := fun a b h => Ideal.comap_mono (Ideal.pow_le_pow_right h)
  have h0 : ⨅ N, I N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : (x : R) ∈ ⨅ N : ℕ, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 fun N =>
      (Submodule.mem_iInf _).1 hx N
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot] at h1
    exact Subtype.ext h1
  ext x
  by_contra hne
  have hpos : 0 < ‖E x‖ / 2 := half_pos (norm_pos_iff.2 hne)
  obtain ⟨k, hk⟩ := hc _ hpos
  obtain ⟨N, hN⟩ := cofinal I hI h0 k
  obtain ⟨t, ht, hd'⟩ := hd x N
  have h2 := hk (x - t) (hN hd')
  rw [map_sub, hT t ht, sub_zero] at h2
  linarith

end Close

theorem UpperTheory.V.J.derExt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, ∀ D ∈ PtDer ξ (Qbar l), (∀ g i j, D (S.u.r g i j) = 0) → (∀ v i g, D (S.u.ψ v i g : S.A) = 0) → D = 0 := by
  intro l _ c _ F C₀ n hF hn S ξ D hD hr hψ
  obtain ⟨hco, hm⟩ := Fr.co_B hF hn S
  haveI := hco
  have hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f := hD

  have hs : ∀ x ∈ ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)} : Set S.R),
      ∃ hx : x ∈ S.A, D ⟨x, hx⟩ = 0 := by
    rintro x (⟨g, i, j, rfl⟩ | ⟨v, i, g, rfl⟩)
    · exact ⟨S.r_mem g i j, hr g i j⟩
    · exact ⟨S.B_le_A (S.ψ_mem v i g), hψ v i g⟩
  have hadj : Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤
      Algebra.adjoin c.O ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | hx)
    · refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin (Or.inl ⟨_, _, _, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr hx)

  have hB : D ∘ₗ S.inc.toLinearMap = 0 := by
    refine close_zero S.B (hm.trans rfl) _ (fun ε hε => ?_)
      {t | (t : S.R) ∈ Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})} (fun t ht => ?_)
      (fun x N => ?_)
    · have hDB : D ∘ₗ S.inc.toLinearMap ∈ PtDer (ξ.comp S.inc) (Qbar l) := fun f g => by
        simpa using hD (S.inc f) (S.inc g)
      obtain ⟨k, hk⟩ := derCont l c S.B (ξ.comp S.inc) _ hDB ε hε
      exact ⟨k, fun a ha => (hk a ha).1⟩
    · obtain ⟨_, h⟩ := kill S.A ξ D hD' _ hs (hadj ht)
      exact h
    · obtain ⟨y, hy, h⟩ := x.2 N
      exact ⟨⟨y, Fr.le_adicClosure _ hy⟩, hy, h⟩

  ext ⟨x, hx⟩
  obtain ⟨_, h⟩ := kill S.A ξ D hD' ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) (by
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact ⟨S.B_le_A hx, LinearMap.congr_fun hB ⟨x, hx⟩⟩
    · exact ⟨S.r_mem g i j, hr g i j⟩) hx
  exact h
