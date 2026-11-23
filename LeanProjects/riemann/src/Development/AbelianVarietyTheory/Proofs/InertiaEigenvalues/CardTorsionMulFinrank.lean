import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOntoOfUnramified

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.TorsionCard

variable {l : ℕ} [hl : Fact l.Prime]

noncomputable def red (l : ℕ) [Fact l.Prime] : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom

theorem red_val (x : ℤ_[l]ˣ) : (red l x : ZMod l) = PadicInt.toZMod (x : ℤ_[l]) := rfl

theorem eq_one_of_red (h2 : l ≠ 2) (x : ℤ_[l]ˣ) (hx : IsOfFinOrder x) (h1 : red l x = 1) :
    x = 1 := by
  have hpos : 0 < orderOf x := hx.orderOf_pos
  have hpow : ((x : ℤ_[l])) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hred : PadicInt.toZMod (x : ℤ_[l]) = 1 := by
    rw [← red_val, h1, Units.val_one]
  exact Units.ext (GlobalTheory.padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hpos.ne' hpow hred)

theorem exists_lift (h2 : l ≠ 2) (u : (ZMod l)ˣ) :
    ∃ x : ℤ_[l]ˣ, IsOfFinOrder x ∧ red l x = u := by
  classical
  have hl3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
  set a : ℤ_[l] := ((u : ZMod l).val : ℤ_[l]) with ha
  have hred_a : PadicInt.toZMod a = (u : ZMod l) := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have norm_of : ∀ y : ℤ_[l], PadicInt.toZMod y ≠ 0 → ‖y‖ = 1 := by
    intro y hy
    by_contra hne
    have hlt : ‖y‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one y) hne
    apply hy
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd]
    exact hlt
  have lt_of : ∀ y : ℤ_[l], PadicInt.toZMod y = 0 → ‖y‖ < 1 := by
    intro y hy
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hy
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have hF : PadicInt.toZMod (F.aeval a) = 0 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one, hred_a]
    rw [sub_eq_zero, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one]
  have hF' : PadicInt.toZMod (F.derivative.aeval a) ≠ 0 := by
    simp [F, hred_a, Polynomial.derivative_X_pow]
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [norm_of _ hF', one_pow]; exact lt_of _ hF
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma hnorm
  have hz1 : z ^ (l - 1) = 1 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one] at hz
    exact sub_eq_zero.mp hz
  have e : l - 1 = (l - 2) + 1 := by omega
  let x : ℤ_[l]ˣ := ⟨z, z ^ (l - 2), by rw [← pow_succ', ← e, hz1], by rw [← pow_succ, ← e, hz1]⟩
  refine ⟨x, ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l - 1, by omega, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact hz1
  · apply Units.ext
    rw [red_val, ← hred_a, ← sub_eq_zero, ← map_sub]
    by_contra hne
    have h1 := norm_of _ hne
    rw [norm_of _ hF'] at hza
    change ‖z - a‖ < 1 at hza
    linarith

theorem card_torsion (h2 : l ≠ 2) {Γ : Type} [Group Γ] (χ : Γ →* ℤ_[l]ˣ)
    (hχ : Function.Injective χ) (hk : ∀ x, red l x = 1 → x ∈ χ.range) :
    Nat.card {g : Γ // IsOfFinOrder g} = Nat.card ((red l).comp χ).range := by
  classical
  have hcomm : ∀ a b : Γ, a * b = b * a := fun a b => hχ (by rw [map_mul, map_mul, mul_comm])
  have hfin : ∀ g : Γ, IsOfFinOrder (χ g) ↔ IsOfFinOrder g := fun g => by
    rw [← orderOf_pos_iff, ← orderOf_pos_iff, orderOf_injective χ hχ g]
  let f : {g : Γ // IsOfFinOrder g} → ((red l).comp χ).range := fun g => ⟨red l (χ g.1), g.1, rfl⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : red l (χ a) = red l (χ b) := congrArg Subtype.val hab
    have hc : Commute a b⁻¹ := hcomm a b⁻¹
    have ht : IsOfFinOrder (χ (a * b⁻¹)) := (hfin _).mpr (hc.isOfFinOrder_mul ha hb.inv)
    have h1 : red l (χ (a * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv, hab', mul_inv_cancel]
    have h3 := eq_one_of_red h2 _ ht h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact Subtype.ext (hχ h3)
  · rintro ⟨u, g, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_lift h2 (red l (χ g))
    have hr : red l (x⁻¹ * χ g) = 1 := by rw [map_mul, map_inv, hxu, inv_mul_cancel]
    obtain ⟨k, hk'⟩ := hk _ hr
    have hgk : χ (g * k⁻¹) = x := by
      rw [map_mul, map_inv, hk', mul_inv_rev, inv_inv, mul_inv_cancel_left]
    refine ⟨⟨g * k⁻¹, (hfin _).mp (hgk ▸ hx)⟩, Subtype.ext ?_⟩
    change red l (χ (g * k⁻¹)) = red l (χ g)
    rw [hgk, hxu]

theorem exists_chi (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by
  have hn := GlobalTheory.Cyc.IsCyc.norm_eq_one P.χQ_cyc
  refine ⟨{ toFun := fun g => PadicInt.mkUnits (hn g), map_one' := ?_, map_mul' := ?_ },
    fun g => PadicInt.mkUnits_eq (hn g)⟩
  · apply Units.ext; apply PadicInt.ext
    simp
  · intro a b; apply Units.ext; apply PadicInt.ext
    simp only [Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, map_mul]

theorem finrank_eq_relIndex (K : FinExt l) :
    Module.finrank ↥(K0 K) ↥K.1 = (GK K).relIndex (K0 K).fixingSubgroup := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have : FiniteDimensional ℚ_[l] (K0 K) := FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  have h1 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) K.1
  have h2 := IntermediateField.finrank_eq_fixingSubgroup_index (E' := Om l) (K0 K)
  have h3 := Subgroup.relIndex_mul_index (IntermediateField.fixingSubgroup_le hle)
  have h4 := Module.finrank_mul_finrank ℚ_[l] (K0 K) K.1
  have hpos : 0 < Module.finrank ℚ_[l] (K0 K) := Module.finrank_pos
  unfold GK
  rw [← h1, ← h2] at h3
  rw [← h4, mul_comm] at h3
  exact (Nat.eq_of_mul_eq_mul_left hpos h3).symm

set_option maxHeartbeats 800000 in

theorem card_torsion_mul_finrank : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), l ≠ 2 → K.1 ≤ Ks K 1 → W.DelF.card * Module.finrank ↥(K0 K) ↥K.1 = l - 1 := by
  intro l _ P K LL n W h2 hK
  classical
  obtain ⟨χ, hχ⟩ := exists_chi P
  have hle : K0 K ≤ K.1 := inf_le_left
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  have hval : ∀ g : ↥(GK K), ((χK g : ℤ_[l]) : ℚ_[l]) = ((P.PD K).χ g : ℚ_[l]) := by
    intro g
    rw [P.PD_χ K g]
    exact hχ g
  have hO : Function.Injective (algebraMap (OL LL) LL.1) := Subtype.val_injective
  have hkey : ∀ g : ↥(GK K), W.resΓ g = 1 ↔ χK g = 1 := by
    intro g
    have hr := W.χΓ_res g
    constructor
    · intro h
      rw [h, map_one, Units.val_one, map_one] at hr
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 :=
        (algebraMap ℚ_[l] LL.1).injective (by rw [← hr, map_one])
      apply Units.ext
      apply PadicInt.ext
      rw [hval, h1]
      simp
    · intro h
      have h1 : (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
        rw [← hval, h]
        simp
      rw [h1, map_one] at hr
      have h3 : ((W.χΓ (W.resΓ g) : (OL LL)ˣ) : OL LL) = 1 := hO (by rw [hr, map_one])
      apply W.χΓ_inj
      rw [map_one]
      exact Units.ext h3
  let ψ : W.Gam →* ℤ_[l]ˣ :=
    W.resΓ.liftOfRightInverse (Function.surjInv W.resΓ_onto)
      (Function.rightInverse_surjInv W.resΓ_onto)
      ⟨χK, fun g hg => MonoidHom.mem_ker.mpr ((hkey g).mp (MonoidHom.mem_ker.mp hg))⟩
  have hψ : ∀ g : ↥(GK K), ψ (W.resΓ g) = χK g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr fun γ hγ => ?_
    obtain ⟨g, rfl⟩ := W.resΓ_onto γ
    rw [hψ] at hγ
    exact (hkey g).mpr hγ
  have hfix : ∀ g : GQ l, g ∈ (K0 K).fixingSubgroup → red l (χ g) = 1 → g ∈ GK K := by
    intro g hg hr
    have hz : PadicInt.toZMod ((χ g : ℤ_[l]) - 1) = 0 := by
      rw [map_sub, ← red_val, hr, Units.val_one, map_one, sub_self]
    have hd : (l : ℤ_[l]) ^ 1 ∣ (χ g : ℤ_[l]) - 1 := by
      rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact hz
    have hnorm : ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [← hχ g]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (Ideal.mem_span_singleton.mpr hd)
      simpa [PadicInt.norm_def] using this
    have hζ := (GlobalTheory.Cyc.IsCyc.fix_iff P.χQ_cyc g 1).mpr hnorm
    have hadj : g ∈ (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ 1 = 1}).fixingSubgroup :=
      (GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff _ g).mpr fun x hx => hζ x hx
    have hKs : g ∈ (Ks K 1).fixingSubgroup := by
      unfold Ks
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hg, hadj⟩
    exact IntermediateField.fixingSubgroup_le hK hKs
  have hfd0 : FiniteDimensional ℚ_[l] (K0 K) := by
    have : FiniteDimensional ℚ_[l] K.1 := K.2
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  let K0' : FinExt l := ⟨K0 K, hfd0⟩
  have honto : ∀ c : ℤ_[l]ˣ, ∃ g ∈ (K0 K).fixingSubgroup, χ g = c := by
    intro c
    obtain ⟨g, hg, hgc⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K0' inf_le_right c
    exact ⟨g, hg, Units.ext (PadicInt.ext (by rw [hχ g, hgc]))⟩
  have hk : ∀ x : ℤ_[l]ˣ, red l x = 1 → x ∈ ψ.range := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := honto x
    exact ⟨W.resΓ ⟨g, hfix g hg hx⟩, by rw [hψ]; rfl⟩
  have hct := card_torsion h2 ψ hψinj hk
  have hdel : W.DelF.card = Nat.card {γ : W.Gam // IsOfFinOrder γ} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => by
      rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one])
  let G0 := (K0 K).fixingSubgroup
  let F : ↥G0 →* (ZMod l)ˣ := (red l).comp (χ.comp G0.subtype)
  have hF : Function.Surjective F := by
    intro u
    obtain ⟨x, -, hxu⟩ := exists_lift h2 u
    obtain ⟨g, hg, hgx⟩ := honto x
    exact ⟨⟨g, hg⟩, by simp [F, hgx, hxu]⟩
  let H0 := (GK K).subgroupOf G0
  have hkerF : F.ker ≤ H0 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    exact Subgroup.mem_subgroupOf.mpr (hfix g g.2 hg)
  have hidx : H0.index = (H0.map F).index := by
    rw [← Subgroup.index_comap_of_surjective _ hF, Subgroup.comap_map_eq_self hkerF]
  have hmap : H0.map F = ((red l).comp ψ).range := by
    ext u
    constructor
    · rintro ⟨g0, hg0, rfl⟩
      refine ⟨W.resΓ ⟨g0, Subgroup.mem_subgroupOf.mp hg0⟩, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
    · rintro ⟨γ, rfl⟩
      obtain ⟨g, rfl⟩ := W.resΓ_onto γ
      refine ⟨⟨g, IntermediateField.fixingSubgroup_le hle g.2⟩, Subgroup.mem_subgroupOf.mpr g.2, ?_⟩
      simp only [MonoidHom.comp_apply, hψ]
      rfl
  have hcard := Subgroup.card_mul_index (H0.map F)
  rw [Nat.card_eq_fintype_card (α := (ZMod l)ˣ), ZMod.card_units] at hcard
  rw [finrank_eq_relIndex, hdel, hct, ← hmap]
  change _ * H0.index = _
  rw [hidx]
  exact hcard

end GlobalTheory.TorsionCard
