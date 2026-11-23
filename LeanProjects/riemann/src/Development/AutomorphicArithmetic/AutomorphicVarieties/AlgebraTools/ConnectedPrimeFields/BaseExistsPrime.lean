import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CorePowMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ExistsSystemOfParameters
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem base_exists_prime {R : Type} [CommRing R] (b : Ideal R)
    (h : 0 < ringKrullDim (R ⧸ b)) : ∃ P : Ideal R, P.IsPrime ∧ b ≤ P ∧ ¬ P.IsMaximal := by
  by_contra hc
  push Not at hc
  have hk : Ring.KrullDimLE 0 (R ⧸ b) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    have hs : Function.Surjective (Ideal.Quotient.mk b) := Ideal.Quotient.mk_surjective
    have h1 : (p.comap (Ideal.Quotient.mk b)).IsMaximal := by
      refine hc _ (Ideal.comap_isPrime _ _) ?_
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact p.zero_mem
    have h2 := Ideal.map_eq_top_or_isMaximal_of_surjective _ hs h1
    rw [Ideal.map_comap_of_surjective _ hs] at h2
    exact h2.resolve_left hp.ne_top
  rw [Ring.krullDimLE_iff] at hk
  exact absurd h (not_lt.2 (by simpa using hk))

private theorem base_exists_out {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [Algebra A R] [Module.Finite A R] (P : Ideal R) (hP : P.IsPrime) (hm : ¬ P.IsMaximal) :
    ∃ y ∈ maximalIdeal A, algebraMap A R y ∉ P := by
  by_contra hcon
  push_neg at hcon
  haveI := hP
  have hle : maximalIdeal A ≤ P.comap (algebraMap A R) := fun y hy => hcon y hy
  have hne : P.comap (algebraMap A R) ≠ ⊤ := (Ideal.comap_isPrime (algebraMap A R) P).ne_top
  have heq : P.comap (algebraMap A R) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le hne hle).symm
  have hmax : (P.comap (algebraMap A R)).IsMaximal := by
    rw [heq]
    exact maximalIdeal.isMaximal A
  exact hm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax)

private theorem base_ofList_le {A : Type} [CommRing A] {xs : List A} {I : Ideal A}
    (h : ∀ x ∈ xs, x ∈ I) : Ideal.ofList xs ≤ I :=
  Ideal.span_le.2 fun x hx => h x hx

private theorem base_mem_ofList {A : Type} [CommRing A] {xs : List A} {x : A}
    (h : x ∈ xs) : x ∈ Ideal.ofList xs :=
  Ideal.subset_span h

theorem UpperTheory.V.AlgebraTools.Conn.base :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R] [IsAdicComplete (maximalIdeal A) A], ReciprocityTheory.CA.IsCM A → ∀ (xs : List A) (b c : Ideal R),
      (∀ x ∈ xs, x ∈ maximalIdeal A) → ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → (b ⊔ c).radical = maximalIdeal R →
      0 < ringKrullDim (R ⧸ b) → 0 < ringKrullDim (R ⧸ c) → False := by
  intro A R _ _ _ _ _ _ _ _ _ _ hCM xs b c hxs hdim h2 hrad hsup hb hc
  haveI : IsNoetherianRing A := hCM.1
  have hIm : Ideal.ofList xs ≤ maximalIdeal A := base_ofList_le hxs
  have hIne : Ideal.ofList xs ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hIm
  haveI : IsAdicComplete (Ideal.ofList xs) A := cplFinite (A := A) (B := A) (Ideal.ofList xs) hIne
  obtain ⟨u, hu, v, hv, hreg⟩ := reg2 hCM xs hxs hdim h2
  obtain ⟨P, hP, hbP, hPm⟩ := base_exists_prime b hb
  obtain ⟨Q, hQ, hcQ, hQm⟩ := base_exists_prime c hc
  obtain ⟨y, hy, hyP⟩ := base_exists_out (A := A) P hP hPm
  obtain ⟨z, hz, hzQ⟩ := base_exists_out (A := A) Q hQ hQm
  have hcom : (maximalIdeal R).comap (algebraMap A R) = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (maximalIdeal R)
    exact IsLocalRing.eq_maximalIdeal this
  have hmem : ∀ a ∈ maximalIdeal A, algebraMap A R a ∈ (b ⊔ c).radical := by
    intro a ha
    rw [hsup, ← Ideal.mem_comap, hcom]
    exact ha
  have hmapI : ∀ {X : Ideal R}, X.IsPrime → b ⊓ c ≤ X →
      Ideal.map (algebraMap A R) (Ideal.ofList xs) ≤ X := by
    intro X hX hbc
    calc Ideal.map (algebraMap A R) (Ideal.ofList xs)
        ≤ (Ideal.map (algebraMap A R) (Ideal.ofList xs)).radical := Ideal.le_radical
      _ = (b ⊓ c).radical := hrad.symm
      _ ≤ X.radical := Ideal.radical_mono hbc
      _ = X := hX.radical
  refine core (Ideal.ofList xs) (fun m => Ideal.ofList (xs.map (fun x => x ^ (m + 1)))) u v b c P Q y z
    ?_ ?_ (fun m K => hreg m K) ?_ ?_ (hmem u hu) (hmem v hv) hP hQ hbP hcQ
    (hmapI hP (inf_le_left.trans hbP)) (hmapI hQ (inf_le_right.trans hcQ))
    (hmem y hy) (hmem z hz) hyP hzQ
  · intro m n hmn
    apply base_ofList_le
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    have he : x ^ (n + 1) = x ^ (n - m) * x ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    exact Ideal.mul_mem_left _ _ (base_mem_ofList (List.mem_map.2 ⟨x, hx, rfl⟩))
  · intro m
    apply base_ofList_le
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (Ideal.pow_mem_pow (base_mem_ofList hx) (m + 1))
  · intro m
    apply Ideal.exists_pow_le_of_le_radical_of_fg
    · apply base_ofList_le
      intro x hx
      exact ⟨m + 1, base_mem_ofList (List.mem_map.2 ⟨x, hx, rfl⟩)⟩
    · classical
      refine ⟨xs.toFinset, ?_⟩
      rw [List.coe_toFinset]
  · exact Ideal.mul_le_inf.trans (Ideal.le_radical.trans hrad.le)
