import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing UpperTheory.V.Alg

private theorem compl_of_nil {Q : Type} [CommRing Q] (J : Ideal Q) (N : ℕ) (h : J ^ N = ⊥) : IsAdicComplete J Q := by
  have smod : ∀ (K : Ideal Q) (x y : Q), (x ≡ y [SMOD K • (⊤ : Submodule Q Q)]) ↔ x - y ∈ K := by
    intro K x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have := (smod _ _ _).1 (hx N)
    rw [h, sub_zero, Ideal.mem_bot] at this
    exact this
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have := (smod _ _ _).1 (hf hn)
      rw [h, Ideal.mem_bot, sub_eq_zero] at this
      exact (smod _ _ _).2 (by rw [this, sub_self]; exact Ideal.zero_mem _)

private theorem mem_max {Λ R R' : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (h : R →ₐ[Λ] R') (n : ℕ) {y : R} (hy : y ∈ maximalIdeal R ^ n) :
    h y ∈ maximalIdeal R' ^ n := by
  have hle : (maximalIdeal R).map h ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, ← res_eq_zero_iff Λ R', res_map, res_eq_zero_iff]
    exact hz
  have := Ideal.mem_map_of_mem h hy
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle n this

private theorem co_pow {Λ A : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing A] [Algebra Λ A] [IsNoetherianRing A]
    (x : A →ₐ[Λ] ResidueField Λ) (I : Ideal A) [hI : I.IsMaximal] (hx : ∀ z, z ∈ I ↔ x z = 0) (n : ℕ) :
    ∃ _ : IsCO Λ (A ⧸ I ^ (n + 1)), maximalIdeal (A ⧸ I ^ (n + 1)) ^ (n + 1) = ⊥ ∧
      (res Λ (A ⧸ I ^ (n + 1))).comp (Ideal.Quotient.mkₐ Λ (I ^ (n + 1))) = x := by
  classical
  have hJle : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hunit : ∀ z : A, IsUnit (Ideal.Quotient.mk (I ^ (n + 1)) z) ↔ z ∉ I := by
    intro z
    constructor
    · intro hu hz
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (I ^ (n + 1))), Ideal.Quotient.eq] at hv
      have h1 : z * w - 1 ∈ I := hJle hv
      have h2 : z * w ∈ I := Ideal.mul_mem_right _ _ hz
      have h3 : (1 : A) ∈ I := by
        have := Ideal.sub_mem _ h2 h1
        rwa [sub_sub_cancel] at this
      exact hI.ne_top ((Ideal.eq_top_iff_one _).2 h3)
    · intro hz
      obtain ⟨w, i, hi, hwi⟩ := hI.exists_inv hz
      have hnil : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) i) :=
        ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi _⟩
      have e : Ideal.Quotient.mk (I ^ (n + 1)) z * Ideal.Quotient.mk (I ^ (n + 1)) w = 1 - Ideal.Quotient.mk (I ^ (n + 1)) i := by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (I ^ (n + 1))), ← map_sub]
        congr 1
        linear_combination hwi
      have hu := hnil.isUnit_one_sub
      rw [← e] at hu
      exact isUnit_of_mul_isUnit_left hu
  have hne : I ^ (n + 1) ≠ ⊤ := by
    intro ht
    rw [ht] at hJle
    exact hI.ne_top (top_le_iff.1 hJle)
  haveI : Nontrivial (A ⧸ I ^ (n + 1)) := ⟨⟨0, 1, fun h01 => hne ((Ideal.eq_top_iff_one _).2
    (Ideal.Quotient.eq_zero_iff_mem.1 ((map_one (Ideal.Quotient.mk (I ^ (n + 1)))).trans h01.symm)))⟩⟩
  have hnonunit : ∀ y : A ⧸ I ^ (n + 1), ¬IsUnit y ↔ y ∈ I.map (Ideal.Quotient.mk (I ^ (n + 1))) := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hunit, not_not, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', he⟩
      rw [Ideal.Quotient.eq] at he
      have := Ideal.sub_mem _ hz' (hJle he)
      rwa [sub_sub_cancel] at this
  haveI hloc : IsLocalRing (A ⧸ I ^ (n + 1)) := IsLocalRing.of_nonunits_add (by
    intro a b ha hb
    rw [mem_nonunits_iff] at ha hb ⊢
    rw [hnonunit] at ha hb ⊢
    exact Ideal.add_mem _ ha hb)
  have hmax : maximalIdeal (A ⧸ I ^ (n + 1)) = I.map (Ideal.Quotient.mk (I ^ (n + 1))) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnonunit]
  have hpow : maximalIdeal (A ⧸ I ^ (n + 1)) ^ (n + 1) = ⊥ := by
    rw [hmax, ← Ideal.map_pow, Ideal.map_quotient_self]
  have hres : ∀ z : A, ∃ a : Λ, z - algebraMap Λ A a ∈ I := by
    intro z
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x z)
    refine ⟨a, ?_⟩
    rw [hx, map_sub, AlgHom.commutes, ← ha]
    exact sub_eq_zero.2 rfl
  have halg : ∀ a : Λ, algebraMap Λ (A ⧸ I ^ (n + 1)) a = Ideal.Quotient.mk (I ^ (n + 1)) (algebraMap Λ A a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply Λ A (A ⧸ I ^ (n + 1)), Ideal.Quotient.algebraMap_eq]
  have hcompl : IsAdicComplete (maximalIdeal (A ⧸ I ^ (n + 1))) (A ⧸ I ^ (n + 1)) := compl_of_nil _ (n + 1) hpow
  have hlh : IsLocalHom (algebraMap Λ (A ⧸ I ^ (n + 1))) := ⟨fun a ha => by
    by_contra hna
    have ham : a ∈ maximalIdeal Λ := (IsLocalRing.mem_maximalIdeal a).2 hna
    have h0 : x (algebraMap Λ A a) = 0 := by
      rw [AlgHom.commutes]
      exact (IsLocalRing.residue_eq_zero_iff a).2 ham
    rw [← hx] at h0
    rw [halg, hunit] at ha
    exact ha h0⟩
  have hrs : ∀ y : A ⧸ I ^ (n + 1), ∃ a : Λ, y - algebraMap Λ _ a ∈ maximalIdeal (A ⧸ I ^ (n + 1)) := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres z
    refine ⟨a, ?_⟩
    rw [hmax, halg, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  haveI hco : IsCO Λ (A ⧸ I ^ (n + 1)) := IsCO.mk hcompl hlh hrs
  refine ⟨hco, hpow, ?_⟩
  apply AlgHom.ext
  intro z
  obtain ⟨a, ha⟩ := hres z
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have e1 : (res Λ (A ⧸ I ^ (n + 1))) (Ideal.Quotient.mk _ (z - algebraMap Λ A a)) = 0 := by
    rw [res_eq_zero_iff, hmax]
    exact Ideal.mem_map_of_mem _ ha
  have e2 : x (z - algebraMap Λ A a) = 0 := (hx _).1 ha
  rw [map_sub, map_sub, sub_eq_zero] at e1
  rw [map_sub, sub_eq_zero] at e2
  rw [e1, e2, ← halg]
  simp only [AlgHom.commutes]

theorem UpperTheory.V.Ws.fibCpl :
    ∀ {Λ A R : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing A] [Algebra Λ A] [IsNoetherianRing A] [CommRing R] [Algebra Λ R] [IsCO Λ R] [Algebra A R] [IsScalarTower Λ A R],
          (∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (g : A →ₐ[Λ] R'), (res Λ R').comp g = (res Λ R).comp (IsScalarTower.toAlgHom Λ A R) →
            ∃! h : R →ₐ[Λ] R', h.comp (IsScalarTower.toAlgHom Λ A R) = g) →
          ((maximalIdeal R).comap (algebraMap A R)).IsMaximal ∧ UpperTheory.V.CA.IsCplAt ((maximalIdeal R).comap (algebraMap A R)) R := by
  intro Λ A R _ _ _ _ _ _ _ _ _ _ H
  obtain ⟨P, hP⟩ : ∃ P, P = (maximalIdeal R).comap (algebraMap A R) := ⟨_, rfl⟩
  rw [← hP]
  let x : A →ₐ[Λ] ResidueField Λ := (res Λ R).comp (IsScalarTower.toAlgHom Λ A R)
  have hx : ∀ z, z ∈ P ↔ x z = 0 := by
    intro z
    rw [hP, Ideal.mem_comap, ← res_eq_zero_iff Λ R]
    exact Iff.rfl
  have hxsurj : Function.Surjective x := by
    intro k
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap Λ A a, by rw [AlgHom.commutes]; rfl⟩
  have hPker : P = RingHom.ker (x : A →+* ResidueField Λ) := by
    ext z
    rw [hx, RingHom.mem_ker]
    rfl
  haveI hPmax : P.IsMaximal := by
    rw [hPker]
    exact RingHom.ker_isMaximal_of_surjective _ hxsurj
  have hB : ∀ k : ℕ, ∃ _ : IsCO Λ (A ⧸ P ^ (k + 1)), maximalIdeal (A ⧸ P ^ (k + 1)) ^ (k + 1) = ⊥ ∧
      (res Λ (A ⧸ P ^ (k + 1))).comp (Ideal.Quotient.mkₐ Λ (P ^ (k + 1))) = x := fun k => co_pow x P hx k
  have hcp : ∀ n : ℕ, (maximalIdeal R ^ n).comap (algebraMap A R) = P ^ n := by
    intro n
    apply le_antisymm
    · intro z hz
      cases n with
      | zero => simp
      | succ k =>
        obtain ⟨hco, hpow, hres⟩ := hB k
        obtain ⟨h, hh, -⟩ := H (A ⧸ P ^ (k + 1)) (Ideal.Quotient.mkₐ Λ (P ^ (k + 1))) (by rw [hres])
        have h1 := mem_max h (k + 1) (Ideal.mem_comap.1 hz)
        rw [hpow, Ideal.mem_bot] at h1
        have h2 : h (algebraMap A R z) = Ideal.Quotient.mk (P ^ (k + 1)) z := by
          have := AlgHom.congr_fun hh z
          simpa using this
        rw [h2, Ideal.Quotient.eq_zero_iff_mem] at h1
        exact h1
    · rw [hP]
      exact Ideal.le_comap_pow (algebraMap A R) n
  have hdense : ∀ (n : ℕ) (r : R), ∃ c : A, r - algebraMap A R c ∈ maximalIdeal R ^ n := by
    intro n r
    cases n with
    | zero => exact ⟨0, by simp⟩
    | succ k =>
      obtain ⟨hco, hpow, hres⟩ := hB k
      obtain ⟨h, hh, -⟩ := H (A ⧸ P ^ (k + 1)) (Ideal.Quotient.mkₐ Λ (P ^ (k + 1))) (by rw [hres])
      have hne : maximalIdeal R ^ (k + 1) ≠ ⊤ := by
        intro ht
        have hle : maximalIdeal R ^ (k + 1) ≤ maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero k)
        rw [ht] at hle
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
      haveI : Nontrivial (R ⧸ maximalIdeal R ^ (k + 1)) := ⟨⟨0, 1, fun h01 => hne ((Ideal.eq_top_iff_one _).2
        (Ideal.Quotient.eq_zero_iff_mem.1 ((map_one (Ideal.Quotient.mk (maximalIdeal R ^ (k + 1)))).trans h01.symm)))⟩⟩
      haveI hcoQ : IsCO Λ (R ⧸ maximalIdeal R ^ (k + 1)) :=
        co_quot Λ R _ (Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (k + 1))) (Ideal.Quotient.mkₐ_surjective Λ _)
      let j : (A ⧸ P ^ (k + 1)) →ₐ[Λ] (R ⧸ maximalIdeal R ^ (k + 1)) :=
        Ideal.quotientMapₐ (maximalIdeal R ^ (k + 1)) (IsScalarTower.toAlgHom Λ A R) (fun z hz => (hcp (k + 1)).ge hz)
      obtain ⟨u, hu, huniq⟩ := H (R ⧸ maximalIdeal R ^ (k + 1))
        ((Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (k + 1))).comp (IsScalarTower.toAlgHom Λ A R)) (by
          apply AlgHom.ext
          intro z
          simp only [AlgHom.comp_apply]
          exact res_map _ _)
      have e1 : j.comp h = u := huniq _ (by
        show (j.comp h).comp (IsScalarTower.toAlgHom Λ A R) = _
        rw [AlgHom.comp_assoc, hh]
        apply AlgHom.ext
        intro z
        rfl)
      have e2 : Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (k + 1)) = u := huniq _ rfl
      have e3 : Ideal.Quotient.mkₐ Λ (maximalIdeal R ^ (k + 1)) r = j (h r) := by
        rw [e2, ← e1]
        rfl
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (h r)
      refine ⟨z, ?_⟩
      rw [← hz] at e3
      have e4 : j (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk (maximalIdeal R ^ (k + 1)) (algebraMap A R z) := rfl
      rw [e4, Ideal.Quotient.mkₐ_eq_mk] at e3
      exact Ideal.Quotient.eq.1 e3
  exact ⟨hPmax, ⟨inferInstance, IsCO.complete (O := Λ), hcp, hdense⟩⟩
