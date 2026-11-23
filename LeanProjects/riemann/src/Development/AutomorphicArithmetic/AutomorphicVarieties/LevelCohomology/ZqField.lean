import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem zq_unit {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact hx

private theorem zq_dvd {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x = 0) : (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  exact h

private theorem zq_cast {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (((PadicInt.toZModPow 1 x).val : ℕ) : ZMod l) = PadicInt.toZMod x := by
  have h : PadicInt.toZModPow 1 (x - (((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[l])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h
  exact h.symm

private theorem zq_four {l e : ℕ} (hl : 5 ≤ l) (he : Even e) (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) (ho : l % 2 = 1) :
    l % 4 = 1 ∧ l / 2 ∣ e := by
  obtain ⟨n, rfl⟩ : ∃ n, l = 2 * n + 1 := ⟨l / 2, by omega⟩
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : (2 * n + 1) / 2 = n := by omega
  rw [e1] at h1 h2
  rw [e2]
  obtain ⟨k, rfl⟩ : n ∣ e := Nat.dvd_of_mul_dvd_mul_left two_pos h1
  refine ⟨?_, dvd_mul_right _ _⟩
  rcases Nat.even_mul.1 he with ⟨j, hj⟩ | ⟨j, hj⟩
  · omega
  · exact absurd ⟨j, by rw [hj]; ring⟩ h2

private theorem zq_gen {l e : ℕ} [Fact l.Prime] (h2 : ¬ l - 1 ∣ e) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZMod (u : ℤ_[l]) ^ e ≠ 1 := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf b = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : PadicInt.toZMod (((b : ZMod l).val : ℕ) : ℤ_[l]) = b := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨u, hu⟩ := zq_unit _ (h0 ▸ b.ne_zero)
  refine ⟨u, fun h => h2 ?_⟩
  rw [hu, h0] at h
  rw [← ho, orderOf_dvd_iff_pow_eq_one]
  exact Units.ext (by simpa using h)

private theorem zq_root (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime]
    (h4 : l % 4 = 1) : ∃ s : Ω, s ^ 2 = (l : Ω) ∧ ∀ g : G ℚ Ω, (g s = s ∨ g s = -s) ∧
      (g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ (l / 2) = 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨hp.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨⟨s, hs⟩, h⟩ := CF.gauss Ω l ζ (by omega) hζ
  have hs2 : s ^ 2 = (l : Ω) := by
    rw [hs, CF.pStar, Even.neg_one_pow ⟨l / 4, by omega⟩]
    simp
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.out.ne_zero (by exact_mod_cast (hs2.symm.trans (by simp) : (l : Ω) = 0))
  refine ⟨s, hs2, fun g => ⟨?_, fun hg => ?_⟩⟩
  · refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, hs2, map_natCast]
  · have h1 := cyclotomicCharacter.spec l (n := 1) g.toRingEquiv ζ (by rw [pow_one, hζ.pow_eq_one])
    have h2 := (h s hs).2 g.toRingEquiv.toRingHom _ h1
    have h3 : s = _ := hg.symm.trans h2
    have h5 : legendreSym l ((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) = 1 := by
      have : (1 : Ω) * s = _ := (one_mul s).trans h3
      exact_mod_cast (mul_right_cancel₀ hs0 this).symm
    have h6 := legendreSym.eq_pow l (((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) : ℤ)
    rw [h5, Int.cast_natCast, zq_cast, Int.cast_one] at h6
    exact h6.symm

private theorem zq_hom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) (hp : l.Prime) (hl : 5 ≤ l) (hK : Module.finrank ℚ K = 2) (hd : discr K = l)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (h2 : ∀ m : M, 2 • m = 0 → m = 0)
    (φ : galOf ℚ K Ω → M) (hφ : φ ∈ Kum.XDual l (galOf ℚ K Ω) R M) (u : galOf ℚ K Ω) (hu : l • φ u = 0) : φ u = 0 := by
  rw [← Kum.pullOnto ℚ Ω K _ le_rfl l R M hp.ne_zero le_rfl (Or.inr h2)] at hφ
  obtain ⟨θ, hθ, rfl⟩ := hφ
  rw [Kum.clPull_apply] at hu ⊢
  generalize Kum.artCl K Ω (Kum.toGal K le_rfl u) = c at hu ⊢
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
    rw [hθ.1, ofAdd_add]
  have h1 : classNumber K • θ c = 0 := by
    have : θ' (c ^ classNumber K) = 1 := by rw [classNumber, pow_card_eq_one, map_one]
    rw [map_pow] at this
    exact this
  have hc : l.Coprime (classNumber K) :=
    (Nat.coprime_of_lt_prime (classNumber_pos K).ne' (hQuad K l hp hl hK hd) hp)
  have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hu) (addOrderOf_dvd_of_nsmul_eq_zero h1)
  rw [hc.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at this
  exact this

open IntermediateField in
private theorem zq_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hp : l.Prime) (h4 : l % 4 = 1)
    (s : Ω) (hs : s ^ 2 = (l : Ω)) (δ : G ℚ Ω) (hδ : δ s ≠ s) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (_ : IsAlgClosure K Ω),
      Module.finrank ℚ K = 2 ∧ discr K = l ∧ ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω ↔ g s = s := by
  have hi : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  haveI : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hi
  haveI : NumberField ℚ⟮s⟯ := NumberField.of_module_finite ℚ _
  refine ⟨ℚ⟮s⟯, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, fun g => ⟨fun h => ?_, fun h x => ?_⟩⟩
  · rw [adjoin.finrank hi]
    refine le_antisymm ?_ ((minpoly.two_le_natDegree_iff hi).2 ?_)
    · have := minpoly.min ℚ s (Polynomial.monic_X_pow_sub_C (l : ℚ) two_ne_zero) (by simp [hs])
      rw [Polynomial.degree_X_pow_sub_C two_pos] at this
      exact Polynomial.natDegree_le_of_degree_le this
    · rintro ⟨q, rfl⟩
      exact hδ (δ.commutes q)
  · refine Formalism.HF.quadDiscr _ l (AdjoinSimple.gen ℚ s) (Subtype.ext (by simpa using hs)) ?_
      (Int.squarefree_natCast.2 hp.squarefree) (by omega)
    exact lift_injective _ ((lift_adjoin_simple ℚ ℚ⟮s⟯ (AdjoinSimple.gen ℚ s)).trans (lift_top ℚ ℚ⟮s⟯).symm)
  · exact h (AdjoinSimple.gen ℚ s)
  · have : ℚ⟮s⟯ ≤ fixedField (Subgroup.zpowers g) := by
      rw [adjoin_simple_le_iff, mem_fixedField_iff]
      intro f hf
      exact (Subgroup.zpowers_le.2 (show g ∈ MulAction.stabilizer (G ℚ Ω) s from h)) hf
    exact (mem_fixedField_iff _ _).1 (this x.2) g (Subgroup.mem_zpowers g)

private theorem zq_main (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (hl : 5 ≤ l) (e : ℕ) (he : Even e)
    (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) : Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  obtain ⟨h4, hdv⟩ := zq_four hl he h1 h2 (hp.out.eq_two_or_odd.resolve_left (by omega))
  obtain ⟨u, hu⟩ := zq_gen h2
  obtain ⟨s, hs, hG⟩ := zq_root Ω l h4
  obtain ⟨A₀, hA₀⟩ := (B3.placesQ Ω).1 l hp.out
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ u
  have hpow : ∀ g : G ℚ Ω, g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1 := fun g hg => by
    obtain ⟨k, rfl⟩ := hdv
    rw [pow_mul, (hG g).2 hg, one_pow]
  have hδs : δ s ≠ s := fun h => hu (hδ ▸ hpow δ h)
  obtain ⟨K, _, _, _, _, hK, hd, hU⟩ := zq_field Ω l hp.out h4 s hs δ hδs
  set α : G ℚ Ω →* Oˣ := (1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)) with hα
  have hαg : ∀ g, α g = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ ℚ Ω l g ^ e)⁻¹ := fun g => by
    simp [hα, chiO]
  have hαs : ∀ g, (α g : O) - 1 = algebraMap ℤ_[l] O (-((cycZ ℚ Ω l g ^ e)⁻¹ : ℤ_[l]ˣ) * ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1)) :=
    fun g => by
      rw [hαg, ← Units.val_pow_eq_pow_val, mul_sub, neg_mul, Units.inv_mul, map_sub]
      simp [sub_eq_neg_add, add_comm]
  have hun : ∀ g, cycZ ℚ Ω l g = u → IsUnit ((α g : O) - 1) := fun g hg => by
    rw [hαs, hg]
    refine IsUnit.map _ ((Units.isUnit _).neg.mul (zq_unit _ ?_))
    rw [map_sub, map_pow, map_one]
    exact sub_ne_zero.2 hu
  have htr : ∀ g : G ℚ Ω, g s = s → ∀ m : QO l O, l • m = 0 → (α g : O) • m = m := fun g hg m hm => by
    obtain ⟨y, hy⟩ := zq_dvd ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1) (by rw [map_sub, map_pow, map_one, hpow g hg, sub_self])
    have : ((α g : O) - 1) • m = 0 := by
      rw [hαs, hy, mul_left_comm, map_mul, map_natCast, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hm, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hin : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1 := fun A hA g hg => by
    have : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    rw [hαg, this, one_pow, inv_one, map_one]
  have htwo : ∀ m : QO l O, 2 • m = 0 → m = 0 := fun m hm => by
    have h : IsUnit ((2 : ℕ) : O) := by
      rw [← map_natCast (algebraMap ℤ_[l] O)]
      refine IsUnit.map _ (zq_unit _ ?_)
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
    exact h.smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul _ _ _).trans hm)
  have key : ∀ a : O, ∀ c ∈ ShT (QO l O) α δ l a, l • c = 0 → c = 0 := by
    rintro a c ⟨⟨hlc, hc⟩, hcδ, -, hI, hD⟩ hcl
    have hcl' : ∀ g, l • c g = 0 := fun g => congrFun hcl g
    have hdec : ∀ A : ValuationSubring Ω, Over A l → ∀ g ∈ Dec (F := ℚ) A, g s = s → c g = 0 := fun A hA g hg hgs => by
      obtain ⟨m, -, hm⟩ := hD A hA
      obtain ⟨t, ht, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      have hlm : l • m = 0 := by
        refine (hun t htu).smul_eq_zero.1 ?_
        rw [smul_comm, sub_smul, one_smul, ← hm t (Ine_le_Dec (F := ℚ) A ht), hcl']
      rw [hm g hg, htr g hgs m hlm, sub_self]
    have hX : (fun v : galOf ℚ K Ω => c v) ∈ Kum.XDual l (galOf ℚ K Ω) O (QO l O) := by
      refine ⟨hlc.comp_continuous continuous_subtype_val, fun v w => ?_, fun A v hv => ?_, fun A hA v hv => ?_⟩
      · show c (v * w) = c v + c w
        rw [hc, htr v ((hU _).1 v.2) _ (hcl' _)]
      · by_cases hA : Over A l
        · exact hdec A hA v (Ine_le_Dec (F := ℚ) A hv) ((hU _).1 v.2)
        · exact hI A hA v hv
      · exact hdec A hA v hv ((hU _).1 v.2)
    have h0 : ∀ g : G ℚ Ω, g s = s → c g = 0 := fun g hg =>
      zq_hom Ω K l hp.out hl hK hd O (QO l O) htwo _ hX ⟨g, (hU g).2 hg⟩ (hcl' g)
    funext g
    rcases (hG g).1 with hg | hg
    · exact h0 g hg
    · have : (δ⁻¹ * g) s = s := by
        rw [AlgEquiv.mul_apply, hg]
        exact δ.symm_apply_eq.2 ((hG δ).1.resolve_left hδs).symm
      rw [← mul_inv_cancel_left δ g, hc, hcδ, h0 _ this, smul_zero, add_zero, Pi.zero_apply]
  refine nonpos_iff_eq_zero.1 (shaToShT Ω l O α δ (hun δ hδ) l hp.out.ne_zero hin (fun A h h' => absurd h h') 0 fun a ha => ?_)
  have hnu : ¬ IsUnit (l : O) := fun h => by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff] at h
    exact PadicInt.irreducible_p.not_isUnit h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∣ (l : O) ^ n := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
    refine ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd ?_ n)⟩
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hnu
  have hall : ∀ n : ℕ, ∀ c ∈ ShT (QO l O) α δ l a, l ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c _ h; simpa using h
    | succ n ih =>
      intro c hc h
      exact ih c hc (key a _ (nsmul_mem hc _) (by rw [smul_smul, ← pow_succ', h]))
  have : ShT (QO l O) α δ l a = ⊥ := by
    refine eq_bot_iff.2 fun c hc => hall n c hc (funext fun g => ?_)
    obtain ⟨y, hy⟩ := hn
    rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hy, mul_comm, mul_smul, hc.2.2.1 g, smul_zero, Pi.zero_apply]
  rw [this]
  simp

theorem UpperTheory.V.X.zQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 5 ≤ l → ∀ e : ℕ, Even e → l - 1 ∣ 2 * e → ¬ l - 1 ∣ e → Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  intro Ω _ inst _ l _ O _ _ _ _ _ hl e he h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact zq_main Ω l O hl e he h1 h2
