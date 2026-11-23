import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnivNormUnramOfOrderOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA.TameUnr

open GlobalTheory.KA.UnivNorm

theorem mem_of_fibre_sums {l : ℕ} [Fact l.Prime] {X : ℕ → Type} [∀ r, Group (X r)] [∀ r, Fintype (X r)] (u : ∀ r, X r) (M : ℕ)
    (hu : ∀ k : ℕ, ∃ r, l ^ k ∣ orderOf (u r ^ M)) (Wo : Submodule (Qbar l) (Fin 2 → Qbar l))
    (T : Matrix (Fin 2) (Fin 2) (Qbar l)) (hT : ∀ w ∈ Wo, T *ᵥ w ∈ Wo) (b : Fin 2 → Qbar l)
    (a : ∀ r, X r → Fin 2 → Qbar l) (F : ∀ r, X r → Prop) [∀ r, DecidablePred (F r)]
    (hF : ∀ r z, F r (z * u r ^ M) ↔ F r z) (ha : ∀ r z i, ‖a r z i‖ ≤ 1)
    (hrel : ∀ r z, a r (z * u r) - T *ᵥ a r z ∈ Wo) (hb : ∀ r, b - ∑ z, (if F r z then a r z else 0) ∈ Wo) : b ∈ Wo := by
  classical
  let S : Module.End (Qbar l) ((Fin 2 → Qbar l) ⧸ Wo) := Wo.mapQ Wo (Matrix.toLin' T) fun w hw => hT w hw
  obtain ⟨E, hE, hfix⟩ := exists_pow_fix S
  have h1 : ∀ r n x, Wo.mkQ (a r (x * u r ^ n)) = (S ^ n) (Wo.mkQ (a r x)) := fun r n x => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, pow_succ', Module.End.mul_apply, ← ih]
      exact (Submodule.Quotient.eq Wo).2 (hrel r _)
  have h2 : ∀ r x, Wo.mkQ (a r (x * u r ^ E)) = Wo.mkQ (a r x) := fun r x => by
    rw [h1]
    refine hfix (orderOf (u r)) (orderOf_pos _) _ ?_
    rw [← h1, pow_orderOf_eq_one, mul_one]
  have h2a : ∀ r m x, Wo.mkQ (a r (x * (u r ^ E) ^ m)) = Wo.mkQ (a r x) := fun r m x => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, h2, ih]
  have h2b : ∀ r m x, F r (x * (u r ^ M) ^ m) ↔ F r x := fun r m x => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, hF, ih]
  set a' : ∀ r, X r → Fin 2 → Qbar l := fun r z => if F r z then a r z else 0 with ha'
  have h2c : ∀ r x, Wo.mkQ (a' r (x * (u r ^ M) ^ E)) = Wo.mkQ (a' r x) := fun r x => by
    simp only [ha', h2b]
    split_ifs
    · rw [← pow_mul, mul_comm M, pow_mul, h2a]
    · rfl
  have ha1 : ∀ r z i, ‖a' r z i‖ ≤ 1 := fun r z i => by
    simp only [ha']
    split_ifs
    · exact ha r z i
    · simp
  have hE0 : 0 < ‖(E : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hE.ne')
  refine (isClosed_submodule Wo).closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hE0 hε) (norm_l_lt_one (l := l))
  obtain ⟨r, hr⟩ := hu k
  let : Fintype (X r ⧸ Subgroup.zpowers ((u r ^ M) ^ E)) := Fintype.ofFinite _
  have h3 := sum_eq_orderOf_smul ((u r ^ M) ^ E) (fun x => Wo.mkQ (a' r x)) (h2c r)
  set o := orderOf ((u r ^ M) ^ E) with ho
  set y := ∑ ω : X r ⧸ Subgroup.zpowers ((u r ^ M) ^ E), a' r ω.out with hy
  have h4 : l ^ k ∣ E * o := hr.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one]))
  have h5 : ‖(o : Qbar l)‖ < ε := by
    obtain ⟨m, hm⟩ := h4
    have : ‖(E : Qbar l)‖ * ‖(o : Qbar l)‖ ≤ ‖(l : Qbar l)‖ ^ k := by
      rw [← norm_mul, ← Nat.cast_mul, hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ m)
    exact lt_of_mul_lt_mul_left (this.trans_lt hk) hE0.le
  refine ⟨b - o • y, ?_, ?_⟩
  · rw [← map_sum, ← map_sum, ← map_nsmul] at h3
    have := Wo.add_mem (hb r) ((Submodule.Quotient.eq Wo).1 h3)
    rwa [sub_add_sub_cancel] at this
  · rw [dist_eq_norm, sub_sub_cancel, ← Nat.cast_smul_eq_nsmul (Qbar l), norm_smul]
    refine (mul_le_of_le_one_right (norm_nonneg _) ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)).trans_lt h5
    rw [hy, Finset.sum_apply]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ω _ => ha1 r _ i

theorem exists_cob_of_limit {l : ℕ} [Fact l.Prime] {ι : Type} (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (f : ι → Fin 2 → Qbar l) (P : ℕ → Fin 2 → Qbar l)
    (h : ∀ r s i, ‖f s i - (M s *ᵥ P r - P r) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) : ∃ v, ∀ s, f s = M s *ᵥ v - v := by
  let row : ι × Fin 2 → (Fin 2 → Qbar l) × Qbar l := fun p => ((M p.1 - 1) p.2, f p.1 p.2)
  have hlim : ∀ w ∈ Submodule.span (Qbar l) (Set.range row),
      Filter.Tendsto (fun r => w.2 - w.1 ⬝ᵥ P r) Filter.atTop (nhds 0) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨s, i⟩, rfl⟩ := hx
      refine squeeze_zero_norm (a := fun r => ‖((l : ℕ) : Qbar l)‖ ^ r) (fun r => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt_one)
      have := h r s i
      rw [norm_pow, ← Matrix.one_mulVec (P r), Matrix.mulVec_mulVec, mul_one, ← Matrix.sub_mulVec] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy =>
      have := hx.add hy
      rw [add_zero] at this
      refine this.congr fun r => ?_
      rw [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
    | smul a x _ hx =>
      have := hx.const_mul a
      rw [mul_zero] at this
      refine this.congr fun r => ?_
      rw [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hn : ((0, 1) : (Fin 2 → Qbar l) × Qbar l) ∉ Submodule.span (Qbar l) (Set.range row) := fun hm => by
    simpa using hlim _ hm
  obtain ⟨g, hg, hk⟩ := Submodule.exists_le_ker_of_notMem hn
  refine ⟨fun k => -(g (Pi.single k 1, 0) / g (0, 1)), fun s => funext fun i => ?_⟩
  have h0 : g (row (s, i)) = 0 := hk (Submodule.subset_span ⟨_, rfl⟩)
  have e : row (s, i) = (M s - 1) i 0 • ((Pi.single 0 1, 0) : (Fin 2 → Qbar l) × Qbar l) +
      (M s - 1) i 1 • ((Pi.single 1 1, 0) : (Fin 2 → Qbar l) × Qbar l) + f s i • ((0, 1) : (Fin 2 → Qbar l) × Qbar l) := by
    refine Prod.ext (funext fun k => ?_) (by simp [row])
    fin_cases k <;> simp [row]
  rw [e, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h0
  conv_rhs => rw [← Matrix.one_mulVec (fun k => -(g (Pi.single k 1, 0) / g (0, 1))), Matrix.mulVec_mulVec, mul_one, ← Matrix.sub_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  linear_combination h0

theorem sum_ite_fibre {X Y M : Type} [Fintype X] [Fintype Y] [DecidableEq X] [AddCommMonoid M] (π : Y → X) (p : X → Prop)
    [DecidablePred p] (f : Y → M) :
    ∑ x, (if p x then ∑ y ∈ Finset.univ.filter (fun y => π y = x), f y else 0) = ∑ y, if p (π y) then f y else 0 := by
  rw [← Finset.sum_fiberwise Finset.univ π]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl fun y hy => (by rw [(Finset.mem_filter.1 hy).2] : (if p (π y) then f y else 0) = if p x then f y else 0)]
  split_ifs <;> simp

def red (l : ℕ) {a b : ℕ} (h : a ≤ b) : (ZMod (l ^ b))ˣ →* (ZMod (l ^ a))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ a))).toMonoidHom

theorem red_self (l a : ℕ) (x : (ZMod (l ^ a))ˣ) : red l (le_refl a) x = x := by
  ext; simp [red]

theorem red_red (l : ℕ) {a b d : ℕ} (h : a ≤ b) (h' : b ≤ d) (x : (ZMod (l ^ d))ˣ) :
    red l h (red l h' x) = red l (h.trans h') x :=
  Units.ext (DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow l h) (pow_dvd_pow l h')) (x : ZMod (l ^ d)))

theorem red_cycMod {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] {a b : ℕ} (h : a ≤ b) (s : G ℚ Ω) :
    red l h (cycMod ℚ Ω l b s) = cycMod ℚ Ω l a s :=
  Units.ext (DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow a b h) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]))

theorem sum_fibre_level {l : ℕ} [Fact l.Prime] {Γ A M : Type} [Group Γ] [Fintype A] [DecidableEq A] [AddCommMonoid M]
    (Y : ∀ r : ℕ, Γ → A × (ZMod (l ^ r))ˣ → M)
    (h : ∀ r s, Y r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Y (r + 1)) s)
    (r : ℕ) (z₀ : A × (ZMod (l ^ r))ˣ) (j : ℕ) (s : Γ) :
    Y r s z₀ = ∑ z : A × (ZMod (l ^ (r + j)))ˣ, if (z.1, red l (Nat.le_add_right r j) z.2) = z₀ then Y (r + j) s z else 0 := by
  induction j with
  | zero =>
    show _ = ∑ z : A × (ZMod (l ^ r))ˣ, if (z.1, red l (le_refl r) z.2) = z₀ then Y r s z else 0
    simp [red_self]
  | succ j ih =>
    rw [ih, h (r + j) s]
    refine (sum_ite_fibre _ (fun z : A × (ZMod (l ^ (r + j)))ˣ => (z.1, red l (Nat.le_add_right r j) z.2) = z₀) _).trans
      (Finset.sum_congr rfl fun z _ => if_congr ?_ rfl rfl)
    rw [← red_red l (Nat.le_add_right r j) (Nat.le_succ (r + j))]
    rfl

theorem slice_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  ∀ r z, ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Yw r s z = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c n θ ρ ψ Yw q B hq hB hI hW hWO hWρ hSh hYc hYO hpush r₀ z₀
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨-, hJn, hJcop, -, ⟨γ, hγ⟩, hrel⟩ := GlobalTheory.Published.TameQuotient_holds ℚ Ω l B q hB hq
  obtain ⟨-, hcj, -⟩ := hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec B hγ.1⟩ hφ hγ
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := ℚ) B l
  have hγI := hγ.1
  have hgen := hγ.2
  set J := GlobalTheory.TameQuot.ineKer ℚ B l with hJ
  have hc1 : ∀ j ∈ J, φ * j * φ⁻¹ ∈ J := fun j hj =>
    hJn.conj_mem ⟨j, Ine_le_Dec B (hJI hj)⟩ hj ⟨φ, hφ.1⟩
  have hc2 : ∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ normV q * j :=
    ⟨(γ ^ normV q)⁻¹ * (φ * γ * φ⁻¹), by simpa using hcj, by rw [mul_inv_cancel_left]⟩
  have hκ : ∀ r, ∀ s ∈ Ine (F := ℚ) B, (ψ.prod (cycMod ℚ Ω l r)⁻¹) s = 1 := fun r s hs => by
    rw [MonoidHom.prod_apply, MonoidHom.inv_apply, (hI s hs).1, GlobalTheory.StringRepresentationDecomposition.cycMod_eq_one_of_mem_Ine r hq hB hs, inv_one]
    rfl
  have hu : ∀ r, ((cycMod ℚ Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = (normV q : ZMod (l ^ r)) := fun r => by
    change PadicInt.toZModPow r ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = _
    rw [cycZ_of_isFrob hq hB hφ, map_natCast]
  have hW1 : ∀ s i k, ‖mat W s i k‖ ≤ 1 := fun s i k => norm_le_one_of_mem_coefO c ⟨_, hWO s i k⟩
  have hY1 : ∀ r s x i, ‖Yw r s x i‖ ≤ 1 := fun r s x i => norm_le_one_of_mem_coefO c ⟨_, hYO r s x i⟩
  have hWc : ∀ i k, Continuous fun s => mat W s i k := fun i k =>
    Continuous.matrix_elem (A := fun s => mat W s) (Units.continuous_val.comp hW) i k
  have hWmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by
    simp only [mat, map_mul, Units.val_mul]
  have hρ : ∀ s, ρ s = (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) • mat W s := fun s => by
    rw [hWρ, smul_smul, Units.inv_mul, one_smul]
  have hmul : ∀ s t, ρ (s * t) = ρ s * ρ t := fun s t => by
    rw [hρ, hρ, hρ, hWmul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]
  have hρI : ∀ s ∈ Ine (F := ℚ) B, ρ s = mat W s := fun s hs => by
    rw [hWρ, (hI s hs).2, Units.val_one, one_smul]
  let R : G ℚ Ω →* GL (Fin 2) (Qbar l) := MonoidHom.toHomUnits
    { toFun := ρ
      map_one' := by rw [hρI 1 (one_mem _)]; simp [mat]
      map_mul' := hmul }
  have hcoc : ∀ r x, ∀ s ∈ Ine (F := ℚ) B, ∀ t, Yw r (s * t) x = Yw r s x + mat W s *ᵥ Yw r t x := fun r x s hs t => by
    rw [hSh r s t x, hκ r s hs, mul_one, hρI s hs]
  choose v hv1 hv' using fun r x => exists_cob_of_coprime (G ℚ Ω) l W (fun s => Yw r s x) J hJcop hWc hW1 (hYc r x)
    (fun s i => hY1 r s x i) (fun s hs t _ => hcoc r x s (hJI hs) t)
  have hv : ∀ r x, ∀ j ∈ J, Yw r j x = ρ j *ᵥ v r x - v r x := fun r x j hj => by
    rw [hρI j (hJI hj)]; exact hv' r x j hj
  set M := orderOf ((ψ.prod (cycMod ℚ Ω l r₀)⁻¹) φ) with hM
  have hM0 : 0 < M := orderOf_pos _
  have hM1 : ψ φ ^ M = 1 ∧ (cycMod ℚ Ω l r₀ φ)⁻¹ ^ M = 1 :=
    Prod.ext_iff.1 (pow_orderOf_eq_one ((ψ.prod (cycMod ℚ Ω l r₀)⁻¹) φ))
  have hb : Yw r₀ γ z₀ - (ρ γ *ᵥ v r₀ z₀ - v r₀ z₀) ∈ cobSp ρ J γ := by
    refine mem_of_fibre_sums (X := fun j => Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ)
      (fun j => (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ) M (fun k => ?_) _
      (ρ φ⁻¹ * ∑ i ∈ Finset.range (normV q), ρ γ ^ i) ?_ _
      (fun j x => Yw (r₀ + j) γ x - (ρ γ *ᵥ v (r₀ + j) x - v (r₀ + j) x))
      (fun j z => (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀) ?_ ?_ ?_ ?_
    · obtain ⟨r, hr⟩ := exists_pow_dvd_orderOf l (normV q ^ M)
        (Nat.one_lt_pow hM0.ne' (GlobalTheory.WeilDeligne.one_lt_normV q)) (fun r => cycMod ℚ Ω l r φ ^ M)
        (fun r => by rw [Units.val_pow_eq_pow_val, hu, Nat.cast_pow]) k
      refine ⟨r, hr.trans ?_⟩
      have e : cycMod ℚ Ω l r φ ^ M = ((red l (Nat.le_add_left r r₀)).comp (MonoidHom.snd _ _))
          (((ψ.prod (cycMod ℚ Ω l (r₀ + r))⁻¹) φ ^ M)⁻¹) := by
        rw [map_inv, map_pow, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.coe_snd, MonoidHom.inv_apply, map_inv,
          red_cycMod, inv_pow, inv_inv]
      rw [e]
      exact (orderOf_map_dvd _ _).trans (orderOf_inv _).dvd
    · rintro _ ⟨u, hu', rfl⟩
      refine ⟨ρ φ⁻¹ *ᵥ u, fun j hj => ?_, frob_mulVec_cob (G ℚ Ω) (Qbar l) R J γ φ _ hc2 u hu'⟩
      have e : j * φ⁻¹ = φ⁻¹ * (φ * j * φ⁻¹) := by group
      rw [Matrix.mulVec_mulVec, ← hmul, e, hmul, ← Matrix.mulVec_mulVec, hu' _ (hc1 j hj)]
    · intro j z
      rw [MonoidHom.prod_apply, MonoidHom.inv_apply, Prod.pow_mk, Prod.fst_mul, Prod.snd_mul, map_mul, map_pow, map_inv,
        red_cycMod, hM1.1, hM1.2, mul_one, mul_one]
    · intro r x i
      rw [hρI γ hγI]
      exact norm_sub_le_one (hY1 _ γ x i) (norm_sub_le_one (norm_mulVec_le (hW1 γ) (hv1 _ x) i) (hv1 _ x i))
    · intro j x
      obtain ⟨v', h1, h2⟩ := exists_conj_norm (G ℚ Ω) (Qbar l) _ R _ (Yw (r₀ + j)) (Ine (F := ℚ) B) J γ φ (normV q) x
        (v _ x) (hSh _) (hκ _) hJI hγI hc1 hc2 (hv _ x)
      have h3 := sub_mem_cobSp (ρ := ρ) (γ := γ) (Yw (r₀ + j) γ (x * (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ))
        (fun j' hj => (hv (r₀ + j) (x * (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ) j' hj).symm.trans (h1 j' hj))
      erw [h2] at h3
      exact h3
    · intro j
      have hs := sum_fibre_level Yw hpush r₀ z₀ j
      set V := ∑ z : Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ,
        if (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀ then v (r₀ + j) z else 0 with hV
      have e : ∀ s, Yw r₀ s z₀ - (ρ s *ᵥ V - V) = ∑ z : Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ,
          if (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀ then
            Yw (r₀ + j) s z - (ρ s *ᵥ v (r₀ + j) z - v (r₀ + j) z) else 0 := fun s => by
        rw [hs s, hV, Matrix.mulVec_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> simp
      rw [← e]
      refine sub_mem_cobSp _ fun j' hj => ?_
      rw [← hv r₀ z₀ j' hj, ← sub_eq_zero, e]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [← hv _ z j' hj, sub_self, ite_self]
  obtain ⟨w, hw, hb⟩ := hb
  rw [hρI γ hγI] at hb
  refine ⟨v r₀ z₀ + w, fun s hs => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_gen (G ℚ Ω) l W (fun s => Yw r₀ s z₀ - (mat W s *ᵥ (v r₀ z₀ + w) - (v r₀ z₀ + w))) (Ine (F := ℚ) B) J γ
    (isClosed_Ine B) hJI hγI (fun i => ?_) (fun s hs t _ => ?_) ?_ (fun j hj => ?_) hgen s hs
  · show Continuous fun s => Yw r₀ s z₀ i - (∑ k, mat W s i k * (v r₀ z₀ + w) k - (v r₀ z₀ + w) i)
    exact (hYc r₀ z₀ i).sub ((continuous_finset_sum _ fun k _ => (hWc i k).mul continuous_const).sub continuous_const)
  · show _ = _ + mat W s *ᵥ _
    rw [hcoc r₀ z₀ s hs t, hWmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub]; abel
  · show Yw r₀ γ z₀ - _ = 0
    rw [eq_add_of_sub_eq hb, Matrix.mulVec_add]; abel
  · show Yw r₀ j z₀ - _ = 0
    rw [hv r₀ z₀ j hj, ← hρI j (hJI hj), Matrix.mulVec_add, hw j hj]; abel

theorem tame_limit_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  intro l _ Ω _ _ _ W c n e χ θ ρ ψ Yw Yt q B hq hB hI hW hWO hWρ _ _ hSh hYc hYO hpush hspec
  choose V hV using slice_unram l Ω W c n θ ρ ψ Yw q B hq hB hI hW hWO hWρ hSh hYc hYO hpush
  have key : ∀ a, ∃ v : Fin 2 → Qbar l, ∀ s : Ine (F := ℚ) B, Yt s a = mat W s *ᵥ v - v := fun a => by
    refine exists_cob_of_limit (fun s : Ine (F := ℚ) B => mat W s) (fun s => Yt s a)
      (fun r => ∑ x : (ZMod (l ^ r))ˣ, (((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) • V r (a, x)) fun r s i => ?_
    refine le_of_eq_of_le ?_ (hspec r s a i)
    refine congrArg (fun w : Fin 2 → Qbar l => ‖Yt s a i - w i‖) ?_
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mulVec_smul, ← smul_sub, ← hV r (a, x) s s.2]
  choose v hv using key
  exact ⟨v, fun s hs a => hv a ⟨s, hs⟩⟩

end GlobalTheory.KA.TameUnr

end
