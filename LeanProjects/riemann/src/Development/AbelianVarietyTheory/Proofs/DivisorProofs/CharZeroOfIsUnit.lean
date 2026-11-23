import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupSchemes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRightMulActionLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false

namespace GlobalTheory.UPel.HT.ES.KerUPart

theorem exists_elt {O : Type} [CommRing O] (I J : Ideal O) (q : O) (h : IsCoprime I J)
    (hq : I * J ≤ Ideal.span {q}) (E : ℕ) :
    ∃ α : O, (∀ a ∈ I ^ E, ∃ u v, a = u * α + v * q ^ E) ∧ ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ v, α = a + v * q ^ E := by
  have hm : ∀ a ∈ I ^ E, ∀ b ∈ J ^ E, ∃ v, a * b = v * q ^ E := fun a ha b hb => by
    have h1 : a * b ∈ (I * J) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hq E h1
    rw [Ideal.span_singleton_pow] at h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨v, hv.symm⟩
  have hc : ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ b ∈ J ^ E, a + b = 1 := fun e =>
    Ideal.isCoprime_iff_exists.1 (h.pow (m := e) (n := E))
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hc E
  refine ⟨α, fun a ha => ?_, fun e => ?_⟩
  · obtain ⟨v, hv⟩ := hm a ha β hβ
    exact ⟨a, v, by linear_combination hv - a * hαβ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hc e
    obtain ⟨v, hv⟩ := hm α hα b hb
    exact ⟨α * a, Ideal.mul_mem_left _ _ ha, v, by linear_combination hv - α * hab⟩

theorem exists_conj {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤)
    (hu : uIdeal D r ≤ w) :
    ∃ J : Ideal (𝓞 D.F), IsCoprime (uIdeal D r) J ∧ uIdeal D r * J ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hM : (D.ω - r) * (D.bar D.ω - r) = ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination hnm - r * htr
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hn
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hn
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, ← hM, Int.cast_one, Int.cast_natCast] at h
    refine hw ((Ideal.eq_top_iff_one w).2 (h ▸ w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r)))
      (w.mul_mem_left _ (w.mul_mem_right _ (hu (sub_mem_uIdeal D r))))))
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Int.cast_mul, Int.cast_natCast] at hM
  refine ⟨Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 D.disc_p
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    push_cast at h
    refine Ideal.isCoprime_iff_exists.2 ⟨x * p + y * (D.ω - D.bar D.ω) * (D.ω - r),
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ (p_mem_uIdeal D r)) (Ideal.mul_mem_left _ _ (sub_mem_uIdeal D r)),
      -(y * (D.ω - D.bar D.ω)) * (D.bar D.ω - r),
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    linear_combination h + y * (D.ω + D.bar D.ω + D.tr) * htr - 4 * y * hnm
  · rw [uIdeal, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro z (rfl | rfl | rfl | rfl)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    · exact Ideal.mem_span_singleton.2 (hM ▸ dvd_mul_right _ _)

section Grp

variable {S : Scheme.{0}}

theorem comp_mulN {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) : x ≫ mulN A n = x ^ n := by
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem exists_zeroLocus {B Z : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (g : Z ⟶ B) (hg : g ^ n = 1) :
    ∃ (Y : Over S) (j : Y ⟶ Z), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ Z), (∃ z, z ≫ j = y) ↔ y ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B hn
  have hsec := GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion B n).hom _
    (Over.w (GlobalTheory.HTTorsRep.torsEta (A := B) n))
  have := GlobalTheory.HTTorsRep.mono_of_unit (GlobalTheory.HTTorsRep.torsEta (A := B) n)
  have := GlobalTheory.HTTorsRep.mono_ι (A := B) n
  let g' : Z ⟶ torsion B n := pullback.lift g (toUnit Z) (by rw [comp_mulN, hg]; rfl)
  have hg' : g' ≫ torsion.ι B n = g := pullback.lift_fst _ _ _
  have hP := (IsPullback.of_hasPullback g' (GlobalTheory.HTTorsRep.torsEta n)).map (Over.forget S)
  refine ⟨pullback g' (GlobalTheory.HTTorsRep.torsEta n), pullback.fst _ _, inferInstance,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2, fun W y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [← hg', Category.assoc, ← Category.assoc (pullback.fst g' _), pullback.condition, Category.assoc,
      GlobalTheory.HTTorsRep.torsEta_ι, ← Category.assoc, toUnit_unique (z ≫ pullback.snd g' _) (toUnit W)]
    rfl
  · refine ⟨pullback.lift y (toUnit W) ?_, pullback.lift_fst _ _ _⟩
    rw [← cancel_mono (torsion.ι B n), Category.assoc, hg', h, Category.assoc, GlobalTheory.HTTorsRep.torsEta_ι]
    rfl

theorem exists_subgroup {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hC : IsAbelianScheme C) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g] :
    ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧
      ∀ (T : Over S) (x : T ⟶ A), InSub i x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  have := GlobalTheory.HTTorsRep.mono_ι (A := A) n
  have h0 : torsion.ι A n ^ n = 1 := by rw [← comp_mulN, GlobalTheory.HTTorsRep.ι_mulN]; rfl
  obtain ⟨Y, j, hj, hjo, hjc, hY⟩ := exists_zeroLocus hB hn (torsion.ι A n ≫ f)
    (by rw [← MonObj.pow_comp, h0, MonObj.one_comp])
  obtain ⟨K, k, hk, hko, hkc, hK⟩ := exists_zeroLocus hC hn (j ≫ torsion.ι A n ≫ g)
    (by rw [← MonObj.comp_pow, ← MonObj.pow_comp, h0, MonObj.one_comp, MonObj.comp_one])
  have hpts : ∀ (T : Over S) (x : T ⟶ A),
      InSub (k ≫ j ≫ torsion.ι A n) x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
    intro T x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← MonObj.comp_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, h0]
        simp only [MonObj.comp_one]
      · simpa only [Category.assoc] using (hY T (z ≫ k ≫ j)).1 ⟨z ≫ k, Category.assoc _ _ _⟩
      · simpa only [Category.assoc] using (hK T (z ≫ k)).1 ⟨z, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      let y : T ⟶ torsion A n := pullback.lift x (toUnit T) (by rw [comp_mulN, h1]; rfl)
      have hy : y ≫ torsion.ι A n = x := pullback.lift_fst _ _ _
      obtain ⟨z, hz⟩ := (hY T y).2 (by rw [← Category.assoc, hy, h2])
      obtain ⟨u, hu⟩ := (hK T z).2 (by rw [← Category.assoc, hz, ← Category.assoc, hy, h3])
      exact ⟨u, by rw [← Category.assoc, hu, ← Category.assoc, hz, hy]⟩
  have hm : Mono (k ≫ j ≫ torsion.ι A n) := inferInstance
  have hfin : IsFinite K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  have het : Etale K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  generalize k ≫ j ≫ torsion.ι A n = i at hpts hm
  obtain ⟨i1, i2, i3⟩ := (hpts K i).1 ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨G, hG⟩ := GlobalTheory.overScheme_grpObj_of_mono_factor S A K i hm
    (by
      have e : (i ⊗ₘ i) ≫ μ[A] = (fst K K ≫ i) * (snd K K ≫ i) := by
        rw [Hom.mul_def]; congr 1
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, i1]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i2]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i3]; simp)
    (by
      have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [e]
      exact (hpts _ _).2 ⟨one_pow _, MonObj.one_comp _, MonObj.one_comp _⟩)
    (by
      have e : i ≫ ι[A] = i⁻¹ := rfl
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [inv_pow, i1, inv_one]
      · rw [GrpObj.inv_comp, i2, inv_one]
      · rw [GrpObj.inv_comp, i3, inv_one])
  exact ⟨K, G, i, hG, hm, hfin, het, hpts⟩

end Grp

theorem charZero_of_isUnit {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : Γ(S, ⊤))) (k : Type) [Field k] (x : Sp k ⟶ S) :
    CharZero k := by
  have hpk : (p : k) ≠ 0 := by
    have := hp.map (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    rw [map_natCast] at this
    exact this.ne_zero
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    by_cases h : ringChar k = p
    · exact hpk (h ▸ h0)
    · have := (b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)).map β
      rw [map_natCast, h0] at this
      exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

theorem exists_kerUPart : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) ∧ IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N _ _ hm r w j c hw hu _ _ S _ s hp o o' ψ hψ hT
  obtain ⟨⟨E, rfl⟩, hψh, hlin, -, -, ψ', hψ'h, hψψ', -⟩ := hψ
  obtain ⟨J, hJ, hJp⟩ := exists_conj D r w hw.ne_top hu
  obtain ⟨α, hα1, hα2⟩ := exists_elt _ _ _ hJ hJp E
  have hc : IsUnit ((p ^ E : ℕ) : Γ(S, ⊤)) := by rw [Nat.cast_pow]; exact hp.pow E
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : ∀ a, IsMonHom (o'.act.act a) := o'.act.hom
  obtain ⟨K, G, i, hG, hi, hfin, het, hpts⟩ :=
    exists_subgroup o.ab o'.ab o.ab hc ψ (o.act.act (algebraMap (𝓞 D.F) D.O α))
  have hnat : ∀ k : ℕ, o.act.act (k : D.O) = 𝟙 o.A ^ k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  have hcomb : ∀ {T : Over S} (x : T ⟶ o.A) (a u v : 𝓞 D.F), x ^ (p ^ E) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O (u * a + v * (p : 𝓞 D.F) ^ E)) = 1 := by
    intro T x a u v h1 h2
    rw [map_add, map_mul, map_mul, ← Nat.cast_pow, map_natCast, o.act.add, o.act.mul, o.act.mul, hnat,
      MonObj.comp_mul, ← Category.assoc, ← Category.assoc, h2, MonObj.comp_pow, Category.comp_id, h1,
      MonObj.one_comp, MonObj.one_comp, _root_.mul_one]
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      (x ≫ ψ = 1 ∧ ∃ e : ℕ, ES.KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
    intro T x
    rw [hpts]
    constructor
    · rintro ⟨h1, e, he⟩
      have h0 : x ^ (p ^ E) = 1 := by
        have : x ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, h1, MonObj.one_comp]
        rwa [hψψ', MonObj.comp_pow, Category.comp_id] at this
      obtain ⟨a, ha, v, hv⟩ := hα2 e
      refine ⟨h0, h1, ?_⟩
      rw [hv, ← _root_.one_mul a]
      exact hcomb x a 1 v h0 (he a ha)
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h1, E, fun a ha => ?_⟩
      obtain ⟨u, v, rfl⟩ := hα1 a ha
      exact hcomb x α u v h0 h2
  refine ⟨K, G, i, hG, hi, hfin, het, fun a => ?_, ?_, key⟩
  · obtain ⟨h1, e, he⟩ := (key K i).2 ⟨𝟙 _, Category.id_comp _⟩
    refine (key K _).1 ⟨?_, e, fun z hz => ?_⟩
    · rw [Category.assoc, hlin, ← Category.assoc, h1, MonObj.one_comp]
    · rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, he z hz, MonObj.one_comp]
  · refine GlobalTheory.FinEtRank.isIsogDeg_of_card o.A K i hi hfin het _ ?_ fun k _ _ t => ?_
    · refine Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => ?_)
      have h := hu (p_mem_uIdeal D r)
      rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at h
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
    · haveI := charZero_of_isUnit b s hp k t
      obtain ⟨h1, h2⟩ := hT k t
      rw [hm, Nat.one_mul] at h2
      rw [← h2]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      rw [← key]
      exact ⟨fun h => ⟨h.1, h1 g h.1 h.2⟩, fun h => ⟨h.1, 1, fun a ha => h.2 a (hu (by rwa [pow_one] at ha))⟩⟩

end GlobalTheory.UPel.HT.ES.KerUPart
