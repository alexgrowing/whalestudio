import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivCoeffOptionEquivLeft
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowVal GlobalTheory.RowVal.EndCalc ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.CocyclePow

open MvPowerSeries

section Alg

variable {C R : Type} [Field C] [CommRing R] [Algebra C R]

theorem coeff_pow_mem (S : Subring R) (G : PowerSeries R) (j : ℕ) (h : ∀ i ≤ j, PowerSeries.coeff i G ∈ S) (k : ℕ) :
    ∀ i ≤ j, PowerSeries.coeff i (G ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ k ih =>
    intro i hi
    rw [pow_succ, PowerSeries.coeff_mul]
    refine sum_mem fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    exact mul_mem (ih _ (by omega)) (h _ (by omega))

theorem exp_coeff_split (G : PowerSeries R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff (n + 1) ((PowerSeries.X * G) ^ k) =
      ∑ k ∈ Finset.range n, (((k + 2).factorial : C))⁻¹ • PowerSeries.coeff (n - (k + 1)) (G ^ (k + 2)) +
        PowerSeries.coeff n G := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, smul_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  congr 3
  omega

theorem exp_low [CharZero C] (S : Subring R) {l : ℕ} (hl : l.Prime)
    (hS : ∀ u : ℕ, ¬ l ∣ u → ∀ x ∈ S, (u : C)⁻¹ • x ∈ S) (G : PowerSeries R) (h0 : PowerSeries.constantCoeff G = 0)
    (hA : ∀ n, ∑ k ∈ Finset.range (n + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff n (G ^ k) ∈ S) :
    PowerSeries.coeff 1 G ∈ S ∧
      ∃ s ∈ S, PowerSeries.coeff 1 G ^ l - (l : C) • PowerSeries.coeff l G = (l : C) • s := by
  obtain ⟨G, rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  have hfac : ∀ k < l, ¬ l ∣ k.factorial := fun k hk h => absurd ((hl.dvd_factorial).1 h) (by omega)
  have low : ∀ n, n + 1 < l → PowerSeries.coeff n G ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h := hA (n + 1)
      rw [exp_coeff_split] at h
      refine (add_mem_cancel_left (sum_mem fun k hk => ?_)).1 h
      have hk' := Finset.mem_range.1 hk
      exact hS _ (hfac _ (by omega)) _
        (coeff_pow_mem S G (n - (k + 1)) (fun i hi => ih i (by omega) (by omega)) _ _ le_rfl)
  have e1 : PowerSeries.coeff 0 G ∈ S := by
    have h := hA (0 + 1)
    rw [exp_coeff_split] at h
    simpa using h
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  have h := hA (m + 1 + 1)
  rw [exp_coeff_split, Finset.sum_range_succ, add_assoc] at h
  have h2 := (add_mem_cancel_left (sum_mem fun k hk => by
    have hk' := Finset.mem_range.1 hk
    exact hS _ (hfac _ (by omega)) _
      (coeff_pow_mem S G (m + 1 - (k + 1)) (fun i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact e1
        · exact low i (by omega)) _ _ le_rfl))).1 h
  rw [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h2
  have c1 : PowerSeries.coeff 1 (PowerSeries.X * G) = PowerSeries.constantCoeff G := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact PowerSeries.coeff_succ_X_mul 0 G
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at e1
  rw [c1, PowerSeries.coeff_succ_X_mul]
  refine ⟨e1, ?_⟩
  obtain ⟨w, hw⟩ : m + 2 ∣ (m + 1).factorial + 1 := by
    haveI := Fact.mk hl
    rw [← ZMod.natCast_eq_zero_iff]
    have := ZMod.wilsons_lemma (m + 2)
    push_cast
    rw [show m + 2 - 1 = m + 1 from rfl] at this
    rw [this]; ring
  have hwC : ((m + 1).factorial : C) + 1 = ((m + 2 : ℕ) : C) * w := by exact_mod_cast hw
  refine ⟨_, sub_mem (nsmul_mem (hS _ (hfac (m + 1) (by omega)) _ (pow_mem e1 (m + 2))) w) h2, ?_⟩
  have hu : ((m + 1).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hl0 : ((m + 2 : ℕ) : C) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hf : ((m + 2).factorial : C) = ((m + 2 : ℕ) : C) * (m + 1).factorial := by
    rw [Nat.factorial_succ (m + 1)]; push_cast; ring
  rw [← Nat.cast_smul_eq_nsmul C, smul_sub, smul_add, smul_smul, smul_smul, smul_smul, hf]
  have k1 : ((m + 2 : ℕ) : C) * w * ((m + 1).factorial : C)⁻¹ =
      1 + ((m + 2 : ℕ) : C) * (((m + 2 : ℕ) : C) * (m + 1).factorial)⁻¹ := by
    rw [← hwC]; field_simp
  rw [k1, add_smul, one_smul]
  abel

end Alg

variable {C : Type} [Field C]

open scoped MvPowerSeries.WithPiTopology in
theorem ext_cont [UniformSpace C] [DiscreteUniformity C] {σ : Type} (L M : MvPowerSeries σ C → C)
    (hL : Continuous L) (hM : Continuous M) (aL : ∀ f g, L (f + g) = L f + L g) (aM : ∀ f g, M (f + g) = M f + M g)
    (h : ∀ e c, L (monomial e c) = M (monomial e c)) (f : MvPowerSeries σ C) : L f = M f := by
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := C)).equalizer hL hM (by
    funext p
    induction p using MvPolynomial.induction_on' with
    | monomial e c => simpa [MvPolynomial.coe_monomial] using h e c
    | add p q hp hq =>
      simp only [Function.comp] at hp hq ⊢
      rw [MvPolynomial.coe_add, aL, aM, hp, hq])
  exact congrFun this f

theorem split_bij {ρ κ β : Type} [Finite κ] [Finite β] {j0 : κ → ρ} {j1 : β → ρ}
    (hj : Function.Bijective (Sum.elim j0 j1)) :
    Function.Bijective fun p : (κ →₀ ℕ) × (β →₀ ℕ) => p.1.mapDomain j0 + p.2.mapDomain j1 := by
  have i0 : Function.Injective j0 := fun a b h => Sum.inl_injective (hj.1 (a₁ := Sum.inl a) (a₂ := Sum.inl b) h)
  have i1 : Function.Injective j1 := fun a b h => Sum.inr_injective (hj.1 (a₁ := Sum.inr a) (a₂ := Sum.inr b) h)
  have dj : ∀ a b, j0 a ≠ j1 b := fun a b h => Sum.inl_ne_inr (hj.1 (a₁ := Sum.inl a) (a₂ := Sum.inr b) h)
  have v0 : ∀ (ν : κ →₀ ℕ) (μ : β →₀ ℕ) a, (ν.mapDomain j0 + μ.mapDomain j1) (j0 a) = ν a := by
    intro ν μ a
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply i0, Finsupp.mapDomain_notin_range, add_zero]
    rintro ⟨b, hb⟩; exact dj a b hb.symm
  have v1 : ∀ (ν : κ →₀ ℕ) (μ : β →₀ ℕ) b, (ν.mapDomain j0 + μ.mapDomain j1) (j1 b) = μ b := by
    intro ν μ b
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply i1, Finsupp.mapDomain_notin_range, zero_add]
    rintro ⟨a, ha⟩; exact dj a b ha
  constructor
  · rintro ⟨ν, μ⟩ ⟨ν', μ'⟩ h
    simp only at h
    ext a
    · rw [← v0 ν μ, ← v0 ν' μ', h]
    · rw [← v1 ν μ, ← v1 ν' μ', h]
  · intro e
    refine ⟨(Finsupp.equivFunOnFinite.symm fun a => e (j0 a), Finsupp.equivFunOnFinite.symm fun b => e (j1 b)), ?_⟩
    ext r
    obtain ⟨x, rfl⟩ := hj.2 r
    rcases x with a | b
    · exact v0 _ _ a
    · exact v1 _ _ b

def row {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (μ : β →₀ ℕ) (P : MvPowerSeries ρ C) : MvPowerSeries κ C :=
  fun ν => coeff (ν.mapDomain j0 + μ.mapDomain j1) P

theorem coeff_row {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (μ : β →₀ ℕ) (P : MvPowerSeries ρ C) (ν : κ →₀ ℕ) :
    coeff ν (row j0 j1 μ P) = coeff (ν.mapDomain j0 + μ.mapDomain j1) P := rfl

def slice {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (γ : κ → PowerSeries C) (n : ℕ) (P : MvPowerSeries ρ C) :
    MvPowerSeries β C :=
  fun μ => PowerSeries.coeff n (alongCv γ (row j0 j1 μ P))

theorem coeff_slice {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (γ : κ → PowerSeries C) (n : ℕ) (P : MvPowerSeries ρ C)
    (μ : β →₀ ℕ) : coeff μ (slice j0 j1 γ n P) = PowerSeries.coeff n (subst γ (row j0 j1 μ P)) := rfl

open scoped MvPowerSeries.WithPiTopology in
theorem jet_subst {ρ κ β τ : Type} [Finite ρ] [Finite κ] [Finite β] [Finite τ] {j0 : κ → ρ} {j1 : β → ρ}
    (hj : Function.Bijective (Sum.elim j0 j1)) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {a : β → MvPowerSeries τ C} (ha : ∀ b, constantCoeff (a b) = 0)
    {s : ρ → MvPowerSeries (Option τ) C} (hs : ∀ r, constantCoeff (s r) = 0)
    (s0 : ∀ i, s (j0 i) = CurveJet.inT τ (γ i)) (s1 : ∀ b, s (j1 b) = rename some (a b)) (n : ℕ)
    (P : MvPowerSeries ρ C) :
    PowerSeries.coeff n (optionEquivLeft τ C (subst s P)) = subst a (slice j0 j1 γ n P) := by
  classical
  letI : UniformSpace C := ⊥
  have Hs := hasSubst_of_constantCoeff_zero hs
  have Ha := hasSubst_of_constantCoeff_zero ha
  have Hγ : HasSubst γ := hasSubst_of_constantCoeff_zero hγ
  ext x
  refine ext_cont (fun P => coeff x (PowerSeries.coeff n (optionEquivLeft τ C (subst s P))))
    (fun P => coeff x (subst a (slice j0 j1 γ n P))) ?_ ?_ ?_ ?_ ?_ P
  · simp only [coeff_coeff_optionEquivLeft]
    exact (WithPiTopology.continuous_coeff C _).comp (continuous_subst Hs)
  · refine (WithPiTopology.continuous_coeff C _).comp ((continuous_subst Ha).comp ?_)
    refine continuous_pi fun μ => ?_
    refine (WithPiTopology.continuous_coeff C (Finsupp.single () n)).comp ((continuous_subst Hγ).comp ?_)
    exact continuous_pi fun ν => WithPiTopology.continuous_coeff C _
  · intro f g
    simp only [subst_add Hs, map_add]
  · intro f g
    have : slice j0 j1 γ n (f + g) = slice j0 j1 γ n f + slice j0 j1 γ n g := by
      ext μ
      rw [map_add, coeff_slice, coeff_slice, coeff_slice, ← map_add, ← subst_add Hγ]
      rfl
    simp only [this, subst_add Ha, map_add]
  · intro e c
    obtain ⟨⟨ν0, μ0⟩, rfl⟩ := (split_bij hj).2 e
    have hsl : slice j0 j1 γ n (monomial (ν0.mapDomain j0 + μ0.mapDomain j1) c) =
        monomial μ0 (c * PowerSeries.coeff n (ν0.prod fun i k => γ i ^ k)) := by
      ext μ
      rw [coeff_slice]
      by_cases hμ : μ = μ0
      · subst hμ
        have : row j0 j1 μ (monomial (ν0.mapDomain j0 + μ.mapDomain j1) c) = monomial ν0 c := by
          ext ν
          rw [coeff_row, coeff_monomial, coeff_monomial]
          refine if_congr ⟨fun h => ?_, fun h => by rw [h]⟩ rfl rfl
          exact congrArg Prod.fst ((split_bij hj).1 (a₁ := (ν, μ)) (a₂ := (ν0, μ)) h)
        rw [this, subst_monomial Hγ, coeff_monomial_same, ← Algebra.smul_def]
        rfl
      · have : row j0 j1 μ (monomial (ν0.mapDomain j0 + μ0.mapDomain j1) c) = 0 := by
          ext ν
          rw [coeff_row, coeff_monomial, if_neg, map_zero]
          exact fun h => hμ (congrArg Prod.snd ((split_bij hj).1 (a₁ := (ν, μ)) (a₂ := (ν0, μ0)) h))
        rw [this, ← coe_substAlgHom Hγ, map_zero, map_zero, coeff_monomial_ne hμ]
    simp only
    rw [hsl, subst_monomial Hs, subst_monomial Ha,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have p0 : optionEquivLeft τ C (ν0.prod fun i k => s (j0 i) ^ k) =
        PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries τ C) (ν0.prod fun i k => γ i ^ k) := by
      simp only [map_finsuppProd, map_pow, s0, CurveJet.optionEquivLeft_inT]
    have p1 : optionEquivLeft τ C (μ0.prod fun b k => s (j1 b) ^ k) =
        PowerSeries.C (μ0.prod fun b k => a b ^ k) := by
      simp only [map_finsuppProd, map_pow, s1, CurveJet.optionEquivLeft_rename_some]
    rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_mul, p0, p1, PowerSeries.coeff_smul,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_map, mul_smul, ← smul_eq_C_mul]

theorem coeff_one_subst {κ : Type} [Fintype κ] {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (f : MvPowerSeries κ C) :
    PowerSeries.coeff 1 (subst γ f : PowerSeries C) =
      ∑ i, PowerSeries.coeff 1 (γ i) * coeff (Finsupp.single i 1) f := by
  have e : ∀ g : PowerSeries C, PowerSeries.coeff 1 g = constantCoeff (pderiv C () g) := by
    intro g
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [PowerSeries.coeff]
  rw [e, ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (a := γ) hγ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, cc_subst (a := γ) hγ, e, mul_comm, ← coeff_zero_eq_constantCoeff_apply (pderiv C i f), coeff_pderiv]
  simp

theorem v_nat (V : VF C) {u : ℕ} (hu : ¬ V.l ∣ u) : V.v (u : C) = 0 := by
  refine PlaceProj.v_eq_zero_of_not_mm (VF.ge_natCast u) fun h => PlaceProj.not_mm_one (V := V) ?_
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (((Nat.Prime.coprime_iff_not_dvd V.l_prime).2 hu).symm) V.l_prime.one_lt
  have h1 : (1 : C) = (m : C) * u - (V.l : C) * ((u * m / V.l : ℕ) : C) := by
    have := congrArg (Nat.cast : ℕ → C) (Nat.mod_add_div (u * m) V.l)
    rw [hm] at this
    push_cast at this
    linear_combination this
  rw [h1]
  exact PlaceProj.mm_sub (PlaceProj.mm_mul (VF.ge_natCast m) h) (PlaceProj.mm_l_mul (VF.ge_natCast _))

theorem coeff_option_exp {σ : Type} {F : MvPowerSeries (Option σ) C} (hc : constantCoeff F = 0)
    (h0 : PowerSeries.constantCoeff (optionEquivLeft σ C F) = 0) (n : ℕ) :
    PowerSeries.coeff n (optionEquivLeft σ C (mvExp F)) =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff n (optionEquivLeft σ C F ^ k) := by
  ext x
  rw [coeff_coeff_optionEquivLeft, map_sum]
  show (∑ k ∈ Finset.range ((x.optionElim n).degree + 1), coeff (x.optionElim n) (F ^ k) / (k.factorial : C)) = _
  have hle : n ≤ (x.optionElim n).degree := by
    simpa using Finsupp.le_degree none (x.optionElim n)
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← map_pow, coeff_coeff_optionEquivLeft, smul_eq_mul, div_eq_inv_mul]
  · intro k _ hk
    have hk' : n < k := by simpa using hk
    rw [← coeff_coeff_optionEquivLeft, map_pow,
      PowerSeries.X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 h0) k) n hk', map_zero, zero_div]

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem bij_two : Function.Bijective (Sum.elim (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x))) := by
  constructor
  · rintro (a | a) (b | b) h <;> simp_all
  · rintro ⟨j, x⟩
    fin_cases j
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩

theorem bij_three : Function.Bijective
    (Sum.elim (fun x : κ => ((0 : Fin 3), x)) (fun p : Fin 2 × κ => (p.1.succ, p.2))) := by
  constructor
  · rintro (a | ⟨i, a⟩) (b | ⟨j, b⟩) h <;> simp_all [(Fin.succ_ne_zero _).symm]
  · rintro ⟨j, x⟩
    refine Fin.cases ⟨Sum.inl x, rfl⟩ (fun j => ⟨Sum.inr (j, x), rfl⟩) j

theorem jet_hAt {τ : Type} [Finite τ] {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    {a : κ → MvPowerSeries τ C} (ha : ∀ b, constantCoeff (a b) = 0) (n : ℕ) :
    PowerSeries.coeff n (optionEquivLeft τ C (hAt X (fun i => CurveJet.inT τ (γ i)) (fun i => rename some (a i)))) =
      subst a (hCoef X γ n) := by
  have e : hCoef X γ n = slice (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x)) γ n X.h := by
    funext μ
    unfold hCoef slice row
    rfl
  rw [e]
  unfold hAt
  refine jet_subst bij_two hγ ha (fun p => ?_) (fun _ => if_pos rfl) (fun _ => if_neg (by simp)) n X.h
  split_ifs
  · exact CurveJet.constantCoeff_inT τ (hγ _)
  · rw [constantCoeff_rename, ha]

theorem hCoef_zero (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) :
    hCoef X γ 0 = 0 := by
  ext μ
  show PowerSeries.coeff 0 (subst γ (row (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x)) μ X.h)) = 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine (cc_subst (a := γ) hγ _).trans ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_row]
  refine H.axes 0 _ fun s hs => ?_
  rw [Finsupp.mapDomain_zero, zero_add] at hs
  classical
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hs)
  simp

theorem cob_smul (H : RLaw X V) (c : C) (b : MvPowerSeries κ C) : cob X (c • b) = c • cob X b := by
  unfold cob
  rw [subst_smul (hasSubst_of_constantCoeff_zero (formalAdd_constantCoeff H (gp_cc 0) (gp_cc 1))),
    subst_smul (hasSubst_of_constantCoeff_zero (gp_cc 0)), subst_smul (hasSubst_of_constantCoeff_zero (gp_cc 1)),
    smul_sub, smul_sub]

theorem exists_series [CharZero C] (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) :
    ∃ F : MvPowerSeries (Option (Fin 2 × κ)) C, constantCoeff F = 0 ∧ IntS V (mvExp F) ∧
      (∀ n, PowerSeries.coeff n (optionEquivLeft _ C F) = - cob X (hCoef X γ n)) ∧
      PowerSeries.coeff 1 (optionEquivLeft _ C F) = c2 X fun i => PowerSeries.coeff 1 (γ i) := by
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  let P : Fin 3 → κ → MvPowerSeries (Option (Fin 2 × κ)) C :=
    Fin.cons (fun i => CurveJet.inT _ (γ i)) (fun j i => rename some (gp C κ j i))
  have hP : ∀ j s, constantCoeff (P j s) = 0 := by
    intro j s
    refine Fin.cases (CurveJet.constantCoeff_inT _ (hγ0 s)) (fun j => ?_) j
    show constantCoeff (rename some (gp C κ j s)) = 0
    rw [constantCoeff_rename, gp_cc]
  have hI : ∀ j s, IntS V (P j s) := by
    intro j s
    refine Fin.cases ?_ (fun j => ?_) j
    · exact intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X _)
        (GlobalTheory.RowLaw.AddCurve.intS_iff.2 (hγ s).2)
    · show IntS V (rename some (MvPowerSeries.X (j, s)))
      rw [rename_X]; exact intS_X _
  have hb : ∀ p : Fin 3 × κ, constantCoeff (P p.1 p.2) = 0 := fun p => hP p.1 p.2
  have hs := hasSubst_of_constantCoeff_zero hb
  have hadd := formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (1 : Fin 3)) (gp_cc 2)
  have hΦ : constantCoeff (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
      hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2))) = 0 := by
    rw [map_sub, map_add, hAt_cc H (gp_cc 0) (gp_cc 1), hAt_cc H (gp_cc 0) (gp_cc 2), hAt_cc H (gp_cc 0) hadd]
    simp
  have h := logInt_subst hb (fun p => hI p.1 p.2) (mem_logInt.2 ⟨hΦ, H.ph2⟩)
  refine ⟨_, h.1, h.2, fun n => ?_, ?_⟩
  · have ea : (fun s => subst (fun p : Fin 3 × κ => P p.1 p.2) (addP X (gp C κ 1) (gp C κ 2) s)) =
        fun s => rename some (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) s) := by
      funext s
      rw [subst_addP H (gp_cc 1) (gp_cc 2) hb, subst_gp hP, subst_gp hP, rename_eq_subst,
        subst_addP (b := MvPowerSeries.X ∘ some) H (gp_cc 0) (gp_cc 1) (fun _ => constantCoeff_X _)]
      simp only [← rename_eq_subst]
      rfl
    rw [subst_sub hs, subst_add hs, subst_hAt (gp_cc 0) (gp_cc 1) hb, subst_hAt (gp_cc 0) (gp_cc 2) hb,
      subst_hAt (gp_cc 0) hadd hb, ea, subst_gp hP, subst_gp hP, subst_gp hP, map_sub, map_add, map_sub, map_add]
    have e0 := jet_hAt (X := X) hγ0 (gp_cc (C := C) (κ := κ) (0 : Fin 2)) n
    have e1 := jet_hAt (X := X) hγ0 (gp_cc (C := C) (κ := κ) (1 : Fin 2)) n
    have e2 := jet_hAt (X := X) hγ0 (formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (0 : Fin 2)) (gp_cc 1)) n
    unfold cob
    rw [← e0, ← e1, ← e2, sub_sub, neg_sub]
    rfl
  · rw [jet_subst bij_three hγ0 (a := MvPowerSeries.X) (fun _ => constantCoeff_X _) hb (fun _ => rfl) (fun _ => rfl),
      subst_self, id]
    ext μ
    rw [coeff_slice, coeff_one_subst hγ0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_row, Finsupp.mapDomain_single, add_comm]

theorem cocycle_pow_coboundary : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V (c2 X fun i => PowerSeries.coeff 1 (γ i)) ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ ((c2 X fun i => PowerSeries.coeff 1 (γ i)) ^ V.l + cob X ((V.l : C) • hCoef X γ V.l))) := by
  intro C _ V d _ I _ κ _ X H γ hγ _
  haveI := H.charZero
  obtain ⟨F, hc, hF, he, h1⟩ := exists_series H hγ
  have h0 : PowerSeries.constantCoeff (optionEquivLeft _ C F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he, hCoef_zero H fun i => (hγ i).1,
      ← zero_smul C (0 : MvPowerSeries κ C), cob_smul H, zero_smul, neg_zero]
  obtain ⟨a, s, hs, e⟩ := exp_low (C := C) (Ig (GaugeCocycle.valRing V) C (Fin 2 × κ)) V.l_prime (by
    intro u hu x hx
    rw [← GaugeCocycle.intS_iff_ig] at hx ⊢
    intro μ
    have hu0 : (u : C) ≠ 0 := by
      rw [Nat.cast_ne_zero]; rintro rfl; exact hu (dvd_zero _)
    refine PlaceProj.ge_of_unit_mul (v_nat V hu) ?_
    rw [map_smul, smul_eq_mul, mul_inv_cancel_left₀ hu0]
    exact hx μ) _ h0 (by
    intro n
    rw [← coeff_option_exp hc h0, ← GaugeCocycle.intS_iff_ig]
    intro μ
    rw [coeff_coeff_optionEquivLeft]
    exact hF _)
  rw [h1] at a e
  rw [he, smul_neg, sub_neg_eq_add, ← cob_smul H] at e
  refine ⟨(GaugeCocycle.intS_iff_ig V _).2 a, fun μ => ?_⟩
  rw [e, map_smul, smul_eq_mul]
  exact PlaceProj.mm_l_mul ((GaugeCocycle.intS_iff_ig V _).2 hs μ)

end GlobalTheory.CocyclePow
