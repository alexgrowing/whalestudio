import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem one_of_pow {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.Oˣ} (hx : x ^ (l - 1) = 1)
    (h : (x : c.O) - 1 ∈ IsLocalRing.maximalIdeal c.O) : x = 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hu : IsUnit ((l - 1 : ℕ) : c.O) :=
    (dvrFacts l c.O).2.2.2.2.2.2.2.2 _ fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hx' : (x : c.O) ^ (l - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have h1 := mul_geom_sum (x : c.O) (l - 1)
  rw [hx', sub_self, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact Units.ext (sub_eq_zero.1 h1)
  · exfalso
    have h2 := congrArg (IsLocalRing.residue c.O) h1
    have h3 : IsLocalRing.residue c.O x = 1 := by
      rw [← sub_eq_zero, ← map_one (IsLocalRing.residue c.O), ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).2 h
    rw [map_sum, map_zero] at h2
    simp only [map_pow, h3, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h2
    have h4 := hu.map (IsLocalRing.residue c.O)
    rw [map_natCast, h2] at h4
    exact not_isUnit_zero h4

private theorem red_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (u v : ℤ_[l]ˣ) :
    algebraMap ℤ_[l] c.O u - algebraMap ℤ_[l] c.O v ∈ IsLocalRing.maximalIdeal c.O ↔
      KStar.TotallyRealRoots.red l u = KStar.TotallyRealRoots.red l v := by
  have := (dvrFacts l c.O).2.2.1
  rw [← map_sub, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero, Units.ext_iff]
  rfl

private theorem exists_strictHenselian_absolutely_closed_local_ring (l : ℕ) [Fact l.Prime] :
    ∃ T : ℤ_[l]ˣ →* ℤ_[l]ˣ, ∀ u, T u ^ (l - 1) = 1 ∧ KStar.TotallyRealRoots.red l (T u) = KStar.TotallyRealRoots.red l u := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hnd : ¬ l ∣ l - 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  choose t h1 h2 using KStar.TotallyRealRoots.exists_teich (l := l)
  refine ⟨MonoidHom.mk' t fun a b => ?_, fun u => ⟨(mem_rootsOfUnity _ _).1 (h1 u), h2 u⟩⟩
  rw [← mul_inv_eq_one]
  refine KStar.TotallyRealRoots.eq_one_of_mem_princ_one hnd (mul_mem (h1 _) (inv_mem (mul_mem (h1 _) (h1 _)))) ?_
  rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, h2, h2, h2, map_mul, mul_inv_cancel]

private theorem gen_pow {Γ M : Type} [Group Γ] [CommGroup M] {l : ℕ} [Fact l.Prime] {w : Γ →* M} {r : Γ →* (ZMod l)ˣ}
    (h : w.ker = r.ker) {σ : Γ} (hσ : ∀ x, x ∈ Subgroup.zpowers (r σ)) (j : ℕ) : w σ ^ j = 1 ↔ l - 1 ∣ j := by
  rw [← map_pow, ← MonoidHom.mem_ker, h, MonoidHom.mem_ker, map_pow, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_eq_card_of_forall_mem_zpowers hσ, Nat.card_eq_fintype_card, ZMod.card_units]

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem ker_red (c : Coef l) {w : G ℚ Ω →* c.Oˣ} (h : IsOmT c w) :
    w.ker = ((KStar.TotallyRealRoots.red l).comp (cycZ ℚ Ω l)).ker := by
  ext σ
  have h1 : ((w σ : c.Oˣ) : c.O) - algebraMap ℤ_[l] c.O (cycZ ℚ Ω l σ : ℤ_[l]ˣ) ∈ IsLocalRing.maximalIdeal c.O := h.2 σ
  have h2 := red_iff c (cycZ ℚ Ω l σ) 1
  rw [map_one, Units.val_one, map_one] at h2
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← h2]
  constructor
  · intro e
    rw [e, Units.val_one] at h1
    simpa using neg_mem h1
  · intro e
    refine one_of_pow c (DFunLike.congr_fun h.1 σ) ?_
    simpa using add_mem h1 e

private theorem cls_pow_one (σ : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) σ = cycMod ℚ Ω l 1 σ ∧ Chr.cls ℚ Ω (l ^ 1) σ = KStar.TotallyRealRoots.redPow l 1 (cycZ ℚ Ω l σ) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact ⟨(Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω σ) ζ hζ,
    (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ => cyclotomicCharacter.spec l σ.toRingEquiv ζ hζ⟩

private theorem cls_ker : (Chr.cls ℚ Ω (l ^ 1)).ker = (Chr.cls ℚ Ω l).ker := by
  ext σ
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω (l ^ 1)).2.1 l (pow_one l).symm.dvd) σ
  have h2 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω l).2.1 (l ^ 1) (pow_one l).dvd) σ
  rw [MonoidHom.comp_apply] at h1 h2
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => by rw [← h1, h, map_one], fun h => by rw [← h2, h, map_one]⟩

private theorem ker_cls (c : Coef l) {w : G ℚ Ω →* c.Oˣ} (h : IsOmT c w) : w.ker = (Chr.cls ℚ Ω (l ^ 1)).ker := by
  rw [ker_red c h]
  ext σ
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, (cls_pow_one σ).2, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    ← KStar.TotallyRealRoots.princ_one_eq_ker]
  rfl

end

theorem UpperTheory.V.HV.omT :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l), (∃! w : G ℚ Ω →* c.Oˣ, IsOmT c w) ∧ ∀ w : G ℚ Ω →* c.Oˣ, IsOmT c w →
      w.ker = (cycMod ℚ Ω l 1).ker ∧ w.ker = (Chr.cls ℚ Ω l).ker ∧ orderOf w = l - 1 ∧ IsOpen (w.ker : Set (G ℚ Ω)) ∧
      (∀ σ : G ℚ Ω, IsCC σ → l ≠ 2 → w σ = -1) ∧
      (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ w.ker) ∧
      (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ j : ℕ, Ine (F := ℚ) A ≤ (w ^ j).ker → l - 1 ∣ j) ∧
      ∀ θ : G ℚ Ω →* c.Oˣ, w.ker ≤ θ.ker → ∃ b < l - 1, θ = w ^ b := by
  intro Ω _ _ _ l hl c
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring l
    refine ⟨((Units.map (algebraMap ℤ_[l] c.O).toMonoidHom).comp T).comp (cycZ ℚ Ω l), ⟨?_, fun σ => ?_⟩, fun w hw => ?_⟩
    · refine MonoidHom.ext fun σ => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, (hT _).1, map_one, MonoidHom.one_apply]
    · exact (red_iff c _ _).2 (hT _).2
    · refine MonoidHom.ext fun σ => ?_
      rw [← mul_inv_eq_one]
      set y : c.Oˣ := (((Units.map (algebraMap ℤ_[l] c.O).toMonoidHom).comp T).comp (cycZ ℚ Ω l)) σ with hy
      have h1 : y ^ (l - 1) = 1 := by
        rw [hy, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, (hT _).1, map_one]
      have h2 : (y : c.O) - (chiO ℚ Ω l c.O σ : c.Oˣ) ∈ IsLocalRing.maximalIdeal c.O := (red_iff c _ _).2 (hT _).2
      have h3 : w σ ^ (l - 1) = 1 := DFunLike.congr_fun hw.1 σ
      refine one_of_pow c (by rw [mul_pow, inv_pow, h1, h3, inv_one, mul_one]) ?_
      have h4 := Ideal.mul_mem_right ((y⁻¹ : c.Oˣ) : c.O) _ (sub_mem (hw.2 σ) h2)
      rwa [sub_sub_sub_cancel_right, sub_mul, Units.mul_inv] at h4
  · have hk : w.ker = (Chr.cls ℚ Ω l).ker := (ker_cls c hw).trans cls_ker
    obtain ⟨f1, -, -, f4, f5⟩ := Chr.clsFacts ℚ Ω l
    obtain ⟨σ₀, hσ₀⟩ := (Chr.clsOnto Ω l).1 g
    have hp := gen_pow hk (σ := σ₀) (hσ₀ ▸ hg)
    refine ⟨?_, hk, ?_, hk ▸ f1, fun σ hσ h2 => ?_, fun A hA => hk ▸ f5 A hA, fun A hA j hj => ?_, fun θ hθ => ?_⟩
    · rw [ker_cls c hw, MonoidHom.ext fun σ => (cls_pow_one (l := l) σ).1]
    · exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hw.1)
        ((hp _).1 (DFunLike.congr_fun (pow_orderOf_eq_one w) σ₀))
    · have h1 : Chr.cls ℚ Ω l σ = -1 := f4 σ hσ
      have h3 : w σ ^ 2 = 1 := by
        rw [← map_pow, ← MonoidHom.mem_ker, hk, MonoidHom.mem_ker, map_pow, h1, neg_one_sq]
      have h4 : ((w σ : c.Oˣ) : c.O) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
      rcases sq_eq_one_iff.1 h4 with h5 | h5
      · exfalso
        have h6 : σ ∈ w.ker := Units.ext h5
        rw [hk, MonoidHom.mem_ker, h1] at h6
        have : Fact (2 < l) := ⟨by omega⟩
        exact ZMod.neg_one_ne_one (n := l) (congrArg Units.val h6)
      · exact Units.ext h5
    · obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.red_surjective (l := l) g
      obtain ⟨τ, hτ, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      refine (gen_pow (ker_red c hw) (σ := τ) ?_ j).1 (hj hτ)
      rw [MonoidHom.comp_apply, e, hu]
      exact hg
    · have : NeZero (l - 1) := ⟨by omega⟩
      have h1 : IsPrimitiveRoot (w σ₀) (l - 1) := ⟨(hp _).2 dvd_rfl, fun j => (hp j).1⟩
      have h2 : θ σ₀ ^ (l - 1) = 1 := by
        rw [← map_pow]
        exact hθ (by rw [MonoidHom.mem_ker, map_pow, h1.pow_eq_one])
      obtain ⟨b, hb, e⟩ := h1.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).2 h2)
      refine ⟨b, hb, MonoidHom.ext fun σ => ?_⟩
      obtain ⟨k, hk'⟩ := hg (Chr.cls ℚ Ω l σ)
      have h3 : σ * (σ₀ ^ k)⁻¹ ∈ w.ker := by
        rw [hk, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hσ₀, ← hk', mul_inv_cancel]
      have h4 := hθ h3
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3 h4
      rw [MonoidHom.pow_apply, h3, h4, ← e, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
