import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj

private theorem val_alg {E : Type} [Field E] [NumberField E] (u : Plc E) (c : 𝓞 E) :
    Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) = u.valuation E (c : E) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 E) E (u.adicCompletion E)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _

private theorem alg_int {E : Type} [Field E] [NumberField E] (u : Plc E) (c : 𝓞 E) :
    algebraMap (𝓞 E) (u.adicCompletion E) c ∈ u.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_alg]
  exact HeightOneSpectrum.valuation_le_one u c

private theorem lt_one_le {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [WithZero.exp_le_exp]
    have : WithZero.log x < 0 := by
      rwa [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    omega

private theorem split_at {E : Type} [Field E] [NumberField E] (w u : Plc E) (a b : 𝓞 E)
    (hab : Ideal.span {a} ⊔ Ideal.span {b} = w.asIdeal) (y : u.adicCompletion E)
    (hy : y ∈ u.adicCompletionIntegers E) (hw : u = w → Valued.v y < 1) :
    ∃ c ∈ u.adicCompletionIntegers E, ∃ d ∈ u.adicCompletionIntegers E,
      y = algebraMap (𝓞 E) (u.adicCompletion E) a * c + algebraMap (𝓞 E) (u.adicCompletion E) b * d := by
  have key : ∃ e ∈ w.asIdeal, e ≠ 0 ∧ Valued.v y ≤ u.valuation E ((e : 𝓞 E) : E) := by
    by_cases huw : u = w
    · subst huw
      obtain ⟨π, hπ⟩ := HeightOneSpectrum.intValuation_exists_uniformizer u
      have hv : u.valuation E ((π : 𝓞 E) : E) = WithZero.exp (-1 : ℤ) := by
        rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap u π
      refine ⟨π, (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u π).1 ?_, ?_, ?_⟩
      · refine lt_of_eq_of_lt hv ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
      · rintro rfl
        simp at hv
        exact WithZero.exp_ne_zero hv.symm
      · rw [hv]; exact lt_one_le (hw rfl)
    · have : ¬ w.asIdeal ≤ u.asIdeal := fun hle => huw
        (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm)
      obtain ⟨e, he, heu⟩ := SetLike.not_le_iff_exists.1 this
      refine ⟨e, he, fun h => heu (h ▸ zero_mem _), ?_⟩
      have : u.valuation E ((e : 𝓞 E) : E) = 1 :=
        le_antisymm (HeightOneSpectrum.valuation_le_one u e)
          (not_lt.1 fun h => heu ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u e).1 h))
      rw [this]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E u).1 hy
  obtain ⟨e, he, he0, hle⟩ := key
  rw [← hab, ← Ideal.span_union, Set.singleton_union, Ideal.mem_span_pair] at he
  obtain ⟨α, β, hαβ⟩ := he
  have hve : Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) e) ≠ 0 := by
    rw [val_alg]
    simpa using he0
  have he' : algebraMap (𝓞 E) (u.adicCompletion E) e ≠ 0 := fun h => hve (by rw [h, map_zero])
  have hz : y / algebraMap (𝓞 E) (u.adicCompletion E) e ∈ u.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    rw [div_le_one₀ (zero_lt_iff.2 hve), val_alg]
    exact hle
  refine ⟨_, mul_mem (alg_int u α) hz, _, mul_mem (alg_int u β) hz, ?_⟩
  have : algebraMap (𝓞 E) (u.adicCompletion E) a * (algebraMap (𝓞 E) (u.adicCompletion E) α * (y / algebraMap (𝓞 E) (u.adicCompletion E) e)) +
      algebraMap (𝓞 E) (u.adicCompletion E) b * (algebraMap (𝓞 E) (u.adicCompletion E) β * (y / algebraMap (𝓞 E) (u.adicCompletion E) e)) =
      algebraMap (𝓞 E) (u.adicCompletion E) (α * a + β * b) * (y / algebraMap (𝓞 E) (u.adicCompletion E) e) := by
    rw [map_add, map_mul, map_mul]; ring
  rw [this, hαβ, mul_div_cancel₀ _ he']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private theorem mem_idHat (F : Frame S) (w : Plc E) {v} (hv : v ∈ LaHat S.D)
    (hw : ∀ k, Valued.v (F.vec w v k) < 1) : v ∈ idHat S.D w.asIdeal := by
  classical
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq
    ((Ideal.span_singleton_le_iff_mem _).2 ha) (by simpa using ha0)
  have hs : ∀ (u : Plc E) (hu : (p : 𝓞 E) ∉ u.asIdeal) (k : Fin n), ∃ c ∈ u.adicCompletionIntegers E, ∃ d ∈ u.adicCompletionIntegers E,
      F.vec u v k = algebraMap (𝓞 E) (u.adicCompletion E) a * c + algebraMap (𝓞 E) (u.adicCompletion E) b * d :=
    fun u hu k => split_at w u a b hb _ ((F.vec_hat v).1 hv u hu k) (fun h => by subst h; exact hw k)
  choose c hc d hd e using hs
  obtain ⟨v₁, h₁⟩ := F.vec_surj (fun u k => if hu : (p : 𝓞 E) ∉ u.asIdeal then c u hu k else 0)
    (fun u k => by split_ifs with hu; exacts [zero_mem _, hc u hu k])
  obtain ⟨v₂, h₂⟩ := F.vec_surj (fun u k => if hu : (p : 𝓞 E) ∉ u.asIdeal then d u hu k else 0)
    (fun u k => by split_ifs with hu; exacts [zero_mem _, hd u hu k])
  have m₁ : v₁ ∈ LaHat S.D := (F.vec_hat _).2 fun u hu k => by
    rw [h₁ u hu]; simpa [hu] using hc u hu k
  have m₂ : v₂ ∈ LaHat S.D := (F.vec_hat _).2 fun u hu k => by
    rw [h₂ u hu]; simpa [hu] using hd u hu k
  have hv' : v = mulF S.D a v₁ + mulF S.D b v₂ := by
    rw [← sub_eq_zero]
    refine F.vec_inj _ fun u hu => ?_
    rw [map_sub, map_add, F.vec_mul u hu, F.vec_mul u hu, h₁ u hu, h₂ u hu]
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, dif_pos hu, e u hu k, sub_self]
  rw [hv']
  refine add_mem (AddSubgroup.subset_closure ⟨a, ha, v₁, m₁, rfl⟩)
    (AddSubgroup.subset_closure ⟨b, ?_, v₂, m₂, rfl⟩)
  rw [← hb]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)

end UpperTheory.Gal.Int.Geo.Pl.Tj

namespace UpperTheory.Gal.Int.Geo.Pl.Tj

open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private theorem mulVec_int (u : Plc E) {M : Matrix (Fin n) (Fin n) (u.adicCompletion E)} {y : Fin n → u.adicCompletion E}
    (hM : ∀ i k, M i k ∈ u.adicCompletionIntegers E) (hy : ∀ k, y k ∈ u.adicCompletionIntegers E) (k : Fin n) :
    (M *ᵥ y) k ∈ u.adicCompletionIntegers E :=
  sum_mem fun l _ => mul_mem (hM k l) (hy l)

private theorem mulVec_lt (u : Plc E) {M : Matrix (Fin n) (Fin n) (u.adicCompletion E)} {y : Fin n → u.adicCompletion E}
    (hM : ∀ i k, M i k ∈ u.adicCompletionIntegers E) (hy : ∀ k, Valued.v (y k) < 1) (k : Fin n) :
    Valued.v ((M *ᵥ y) k) < 1 := by
  change Valued.v (∑ l, M k l * y l) < 1
  refine (Valued.v : Valuation (u.adicCompletion E) _).map_sum_lt (one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0) fun l _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E u).1 (hM k l))) (hy l)

private theorem res_zero (u : Plc E) (x : u.adicCompletionIntegers E) :
    IsLocalRing.residue (u.adicCompletionIntegers E) x = 0 ↔ Valued.v (x : u.adicCompletion E) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (u.adicCompletion E) _)

private theorem card_core (F : Frame S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal)
    (haI : ∀ i j, (F.a w).val i j ∈ w.adicCompletionIntegers E)
    (haJ : ∀ i j, ((F.a w)⁻¹).val i j ∈ w.adicCompletionIntegers E)
    (i : ℕ) (hi : i ≤ n) (g : GUf E n) (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ < 1)
    (ht : (comp w g).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) :
    (((LaHat S.D).map (S.L.actG (F.j g)).toAddMonoidHom) ⊔ idHat S.D w.asIdeal).relIndex (LaHat S.D) =
      Ideal.absNorm w.asIdeal ^ i := by
  classical
  set c : AfP p ⊗[ℚ] VQ S.D → (Fin n → w.adicCompletion E) := fun v => ((F.a w)⁻¹).val *ᵥ F.vec w v with hc
  have inv_a : ((F.a w)⁻¹).val * (F.a w).val = 1 := by rw [← Units.val_mul]; simp
  have a_inv : (F.a w).val * ((F.a w)⁻¹).val = 1 := by rw [← Units.val_mul]; simp
  have c_add : ∀ v v', c (v + v') = c v + c v' := fun v v' => by simp [hc, Matrix.mulVec_add]
  have c_sub : ∀ v v', c (v - v') = c v - c v' := fun v v' => by simp [hc, Matrix.mulVec_sub]
  have c_neg : ∀ v, c (-v) = - c v := fun v => by simp [hc, Matrix.mulVec_neg]
  have c_zero : c 0 = 0 := by simp [hc]
  have vec_c : ∀ v, F.vec w v = (F.a w).val *ᵥ c v := fun v => by
    simp only [hc, Matrix.mulVec_mulVec, a_inv, Matrix.one_mulVec]
  have c_int : ∀ v ∈ LaHat S.D, ∀ k, c v k ∈ w.adicCompletionIntegers E := fun v hv k =>
    mulVec_int w haJ ((F.vec_hat v).1 hv w hp) k
  have c_act : ∀ v, c (S.L.actG (F.j g) v) = (comp w g).val *ᵥ c v := fun v => by
    simp only [hc]
    have e : ((F.a w)⁻¹).val * (F.a w * comp w g * (F.a w)⁻¹).val = (comp w g).val * ((F.a w)⁻¹).val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [F.vec_act w hp g v, Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
  have hit : ∀ y : Fin n → w.adicCompletion E, (∀ k, y k ∈ w.adicCompletionIntegers E) →
      ∃ v ∈ LaHat S.D, c v = y ∧ ∀ u : Plc E, u ≠ w → (p : 𝓞 E) ∉ u.asIdeal → F.vec u v = 0 := by
    intro y hy
    obtain ⟨v, hv⟩ := F.vec_surj (Pi.single w ((F.a w).val *ᵥ y)) (fun u k => by
      by_cases h : u = w
      · subst h
        rw [Pi.single_eq_same]
        exact mulVec_int u haI hy k
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _)
    refine ⟨v, (F.vec_hat v).2 fun u hu k => ?_, ?_, fun u h hu => ?_⟩
    · rw [hv u hu]
      by_cases h : u = w
      · subst h
        rw [Pi.single_eq_same]
        exact mulVec_int u haI hy k
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    · simp only [hc]
      rw [hv w hp, Pi.single_eq_same, Matrix.mulVec_mulVec, inv_a, Matrix.one_mulVec]
    · rw [hv u hu, Pi.single_eq_of_ne h]
  let ψ : LaHat S.D →+ (Fin i → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
    AddMonoidHom.mk' (fun v j => IsLocalRing.residue (w.adicCompletionIntegers E)
      ⟨c v.1 (Fin.castLE hi j), c_int v.1 v.2 _⟩) (fun v v' => by
        funext j
        rw [Pi.add_apply, ← map_add]
        congr 1
        apply Subtype.ext
        simp [c_add])
  have hψ : ∀ v : LaHat S.D, ψ v = 0 ↔ ∀ j : Fin i, Valued.v (c v.1 (Fin.castLE hi j)) < 1 := fun v => by
    rw [funext_iff]
    exact forall_congr' fun j => res_zero w _
  let C : AddSubgroup (AfP p ⊗[ℚ] VQ S.D) :=
    { carrier := {v | ∀ j : Fin i, Valued.v (c v (Fin.castLE hi j)) < 1}
      add_mem' := fun {v v'} h h' j => by
        rw [c_add, Pi.add_apply]
        exact Valuation.map_add_lt _ (h j) (h' j)
      zero_mem' := fun j => by simp [c_zero]
      neg_mem' := fun {v} h j => by
        rw [c_neg, Pi.neg_apply, Valuation.map_neg]
        exact h j }
  have hle : ((LaHat S.D).map (S.L.actG (F.j g)).toAddMonoidHom) ⊔ idHat S.D w.asIdeal ≤ C := by
    refine sup_le ?_ ((AddSubgroup.closure_le _).2 ?_)
    · rintro _ ⟨v, hv, rfl⟩ j
      change Valued.v (c (S.L.actG (F.j g) v) (Fin.castLE hi j)) < 1
      rw [c_act, ht, Matrix.mulVec_diagonal, if_pos (by simp), map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (c_int v hv _))) hϖ
    · rintro _ ⟨x, hx, v, hv, rfl⟩ j
      change Valued.v (c (mulF S.D x v) (Fin.castLE hi j)) < 1
      simp only [hc]
      have e : F.vec w (mulF S.D x v) = algebraMap (𝓞 E) (w.adicCompletion E) x • F.vec w v := F.vec_mul w hp x v
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (c_int v hv _))) ?_
      exact lt_of_eq_of_lt (val_alg w x) ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w x).2 hx)
  have hker : (((LaHat S.D).map (S.L.actG (F.j g)).toAddMonoidHom) ⊔ idHat S.D w.asIdeal).addSubgroupOf (LaHat S.D) = ψ.ker := by
    ext v
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hψ]
    refine ⟨fun h => hle h, fun h => ?_⟩
    obtain ⟨v', hv', hcv', hoff⟩ := hit (fun k : Fin n => if (k : ℕ) < i then 0 else c v.1 k) (fun k => by
      split_ifs
      exacts [zero_mem _, c_int v.1 v.2 k])
    have hfc : c (S.L.actG (F.j g) v') = fun k : Fin n => if (k : ℕ) < i then 0 else c v.1 k := by
      rw [c_act, ht, hcv']
      funext k
      rw [Matrix.mulVec_diagonal]
      split_ifs <;> simp
    have hfm : S.L.actG (F.j g) v' ∈ LaHat S.D := (F.vec_hat _).2 fun u hu k => by
      by_cases huw : u = w
      · subst huw
        rw [vec_c, hfc]
        refine mulVec_int u haI (fun k => ?_) k
        split_ifs
        exacts [zero_mem _, c_int v.1 v.2 k]
      · rw [F.vec_act u hu, hoff u huw hu, Matrix.mulVec_zero]
        exact zero_mem _
    have hr : v.1 - S.L.actG (F.j g) v' ∈ idHat S.D w.asIdeal := by
      refine mem_idHat F w (sub_mem v.2 hfm) fun k => ?_
      rw [vec_c]
      refine mulVec_lt w haI (fun k => ?_) k
      rw [c_sub, hfc, Pi.sub_apply]
      by_cases hk : (k : ℕ) < i
      · rw [if_pos hk, sub_zero]
        exact h ⟨k, hk⟩
      · rw [if_neg hk, sub_self, map_zero]
        exact zero_lt_one
    have : v.1 = S.L.actG (F.j g) v' + (v.1 - S.L.actG (F.j g) v') := by abel
    rw [this]
    exact add_mem (AddSubgroup.mem_sup_left ⟨v', hv', rfl⟩) (AddSubgroup.mem_sup_right hr)
  have hsurj : Function.Surjective ψ := by
    intro z
    choose z' hz' using fun j => IsLocalRing.residue_surjective (z j)
    obtain ⟨v, hv, hcv, -⟩ := hit (fun k : Fin n => if h : (k : ℕ) < i then (z' ⟨k, h⟩ : w.adicCompletion E) else 0) (fun k => by
      split_ifs
      exacts [(z' _).2, zero_mem _])
    refine ⟨⟨v, hv⟩, ?_⟩
    funext j
    rw [← hz' j]
    change IsLocalRing.residue _ _ = _
    congr 1
    apply Subtype.ext
    simp [hcv]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, GroundTheory.Global.natCard_residueField_adicCompletionIntegers]
  simp

end UpperTheory.Gal.Int.Geo.Pl.Tj

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tCard :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TCard := by
  intro hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg
  have hq : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hp : (p : 𝓞 E) ∉ w.asIdeal := fun hp => by
    have hcop : Nat.Coprime σ.q p :=
      (Nat.coprime_primes σ.atp.prime (Fact.out : p.Prime)).2 σ.atp.ne
    obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : ((a : 𝓞 E)) * (σ.q : 𝓞 E) + (b : 𝓞 E) * (p : 𝓞 E) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) h
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (h1 ▸ add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hp)))
  obtain ⟨haI, haJ⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (F.a_int w σ.q σ.atp.prime σ.good hq)
  obtain ⟨ϖ, hϖ, ht⟩ := hg.at_w
  refine card_core F w hp haI haJ i hi g ϖ ?_ ht
  rw [Formalism.UG.IsUnifV] at hϖ
  rw [hϖ]
  exact WithZero.coe_lt_one.2 (by decide)
