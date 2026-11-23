import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Core

variable {H E : Type} [Group H] [Field E]

private theorem cob (κ z : H → E) (hz : ∀ g h, z (g * h) = z g + κ g * z h) (g0 : H) (hκ : κ g0 ≠ 1)
    (hc : ∀ g, z (g0 * g * g0⁻¹ * g⁻¹) = 0 ∧ κ (g0 * g * g0⁻¹ * g⁻¹) = 1) (g : H) :
    z g = (1 - κ g) * (z g0 / (1 - κ g0)) := by
  have h1 := hz (g0 * g * g0⁻¹ * g⁻¹) (g * g0)
  rw [(hc g).1, (hc g).2, show g0 * g * g0⁻¹ * g⁻¹ * (g * g0) = g0 * g by group, hz, hz] at h1
  have h2 : 1 - κ g0 ≠ 0 := sub_ne_zero.2 hκ.symm
  field_simp
  linear_combination -h1

private theorem pow_add_char (κ z : H → E) (hz : ∀ g h, z (g * h) = z g + κ g * z h) (s : H) (hs : κ s = 1)
    (h1 : z 1 = 0) (m : ℕ) : z (s ^ m) = m * z s := by
  induction m with
  | zero => simpa using h1
  | succ m ih => rw [pow_succ', hz, ih, hs]; push_cast; ring

private theorem sgn_sq (i : Fin 4) : sgn i * sgn i = 1 := by revert i; decide

private theorem adj_mul (χ : Fin 4 → E) (θ : E) (γ : M4 E) (r : M4 (DualNumber E))
    (hf : ∀ a b, (r a b).fst = if a = b then χ a else 0) (hs : ∀ a b, (r a b).snd = γ a b * χ b)
    (hθ : ∀ a, χ a.rev * χ a = θ) (i j : Fin 4) :
    ((adj r * r) i j).fst = (if i = j then θ else 0) ∧
      ((adj r * r) i j).snd = χ i.rev * χ j * (γ i j + adj γ i j) := by
  constructor
  · rw [Matrix.mul_apply, TrivSqZeroExt.fst_sum, Finset.sum_eq_single j]
    · rw [TrivSqZeroExt.fst_mul, adj_apply, TrivSqZeroExt.fst_smul, hf, hf]
      by_cases h : i = j
      · subst h
        simp [sgn_sq, hθ]
      · simp [h, Ne.symm h]
    · intro b _ hb
      simp [hf, hb]
    · simp
  · rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
    simp only [DualNumber.snd_mul, adj_apply, TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, hf, hs,
      Finset.sum_add_distrib, Fin.rev_inj, smul_ite, ite_mul, mul_ite, smul_zero, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [sgn_sq, one_smul, zsmul_eq_mul]
    push_cast
    ring

private theorem gsp_iff (χ : Fin 4 → E) (θ : E) (γ : M4 E) (r : M4 (DualNumber E)) (h0 : ∀ a, χ a ≠ 0)
    (hf : ∀ a b, (r a b).fst = if a = b then χ a else 0) (hs : ∀ a b, (r a b).snd = γ a b * χ b)
    (hθ : ∀ a, χ a.rev * χ a = θ) :
    IsGSp (TrivSqZeroExt.inl θ) r ↔ γ ∈ sp4 E := by
  show adj r * r = _ ↔ adj γ = -γ
  rw [← Matrix.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [TrivSqZeroExt.ext_iff, (adj_mul χ θ γ r hf hs hθ i j).1, (adj_mul χ θ γ r hf hs hθ i j).2, Matrix.neg_apply,
    eq_neg_iff_add_eq_zero, add_comm (adj γ i j)]
  by_cases h : i = j
  · subst h
    simp [h0]
  · simp [h0, h]

private theorem core [CharZero E] (χ : Fin 4 → H →* Eˣ) (θ : H → E) (I N : H → Prop) (γ : H → M4 E)
    (r : H →* M4 (DualNumber E))
    (hf : ∀ g a b, (r g a b).fst = if a = b then (χ a g : E) else 0)
    (hs : ∀ g a b, (r g a b).snd = γ g a b * χ b g)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hNI : ∀ g, N g → I g) (hN : ∀ g, N g → ∀ a, χ a g = 1)
    (hfin : ∀ s, I s → ∃ m : ℕ, m ≠ 0 ∧ N (s ^ m))
    (hab : ∀ a b, a ≠ b → ∃ g0, χ a g0 ≠ χ b g0 ∧ ∀ g, N (g0 * g * g0⁻¹ * g⁻¹) ∨
      (I (g0 * g * g0⁻¹ * g⁻¹) ∧ ∀ s, I s → χ a s = χ b s)) :
    ((∀ g, IsGSp (TrivSqZeroExt.inl (θ g)) (r g)) ∧ ∀ g, N g → r g = 1) ↔
      (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, a ≠ b →
        γ g a b = (1 - ((χ a g * (χ b g)⁻¹ : Eˣ) : E)) * X a b) ∧ ∀ s, I s → ∀ a, γ s a a = 0 := by
  have hg : ∀ g, IsGSp (TrivSqZeroExt.inl (θ g)) (r g) ↔ γ g ∈ sp4 E := fun g =>
    gsp_iff (fun a => (χ a g : E)) (θ g) (γ g) (r g) (fun a => Units.ne_zero _) (hf g) (hs g) (hθ g)
  have h1 : ∀ g, N g → (r g = 1 ↔ ∀ a b, γ g a b = 0) := fun g hn => by
    rw [← Matrix.ext_iff]
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [TrivSqZeroExt.ext_iff, hf, hs, hN g hn, hN g hn]
    by_cases h : a = b
    · subst h
      simp
    · simp [h]
  have hz : ∀ a b g h, γ (g * h) a b = γ g a b + ((χ a g * (χ b g)⁻¹ : Eˣ) : E) * γ h a b := fun a b g h => by
    have e := hs (g * h) a b
    rw [map_mul r, Matrix.mul_apply, TrivSqZeroExt.snd_sum] at e
    simp only [DualNumber.snd_mul, hf, hs, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, Units.val_mul] at e
    have u1 := Units.ne_zero (χ b g)
    have u2 := Units.ne_zero (χ b h)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    apply mul_right_cancel₀ u2
    linear_combination -e
  rw [forall_congr' hg]
  refine and_congr_right fun hsp => ⟨fun hn => ?_, fun ⟨⟨X, _, hX⟩, hd⟩ g hn => (h1 g hn).2 fun a b => ?_⟩
  · have hn' : ∀ g, N g → ∀ a b, γ g a b = 0 := fun g h => (h1 g h).1 (hn g h)
    have hI : ∀ a b s, I s → χ a s = χ b s → γ s a b = 0 := fun a b s hsI e => by
      obtain ⟨m, hm, hmN⟩ := hfin s hsI
      have h2 : γ 1 a b = 0 := by simpa using hz a b 1 1
      have h3 := pow_add_char (fun g => ((χ a g * (χ b g)⁻¹ : Eˣ) : E)) (fun g => γ g a b) (hz a b) s
        (by simp [e]) h2 m
      rw [hn' _ hmN] at h3
      exact (mul_eq_zero.1 h3.symm).resolve_left (Nat.cast_ne_zero.2 hm)
    refine ⟨?_, fun s hsI a => hI a a s hsI rfl⟩
    have hx : ∀ a b, ∃ x : E, (a = b → x = 0) ∧
        (a ≠ b → ∀ g, γ g a b = (1 - ((χ a g * (χ b g)⁻¹ : Eˣ) : E)) * x) := fun a b => by
      by_cases h : a = b
      · exact ⟨0, fun _ => rfl, fun h' => (h' h).elim⟩
      obtain ⟨g0, h2, h3⟩ := hab a b h
      refine ⟨_, fun h' => (h h').elim, fun _ => cob (fun g => ((χ a g * (χ b g)⁻¹ : Eˣ) : E)) (fun g => γ g a b)
        (hz a b) g0 (fun e => h2 (mul_inv_eq_one.1 (Units.val_eq_one.1 e))) fun g => ⟨?_, ?_⟩⟩
      · rcases h3 g with h4 | h4
        · exact hn' _ h4 a b
        · exact hI a b _ h4.1 (h4.2 _ h4.1)
      · simp [mul_right_comm]
    choose X hX0 hX using hx
    refine ⟨Matrix.of X, ?_, fun g a b h => hX a b h g⟩
    show adj _ = -_
    ext a b
    rw [adj_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply]
    by_cases h : a = b
    · subst h
      rw [hX0 _ _ rfl, hX0 _ _ rfl, smul_zero, neg_zero]
    obtain ⟨g0, h2, -⟩ := hab a b h
    have h3 : adj (γ g0) a b = -γ g0 a b := congrFun (congrFun (hsp g0) a) b
    have h4 : χ b.rev g0 * (χ a.rev g0)⁻¹ = χ a g0 * (χ b g0)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, mul_comm (χ a g0)]
      exact Units.ext ((hθ g0 b).trans (hθ g0 a).symm)
    rw [adj_apply, hX a b h, hX _ _ (fun e => h (Fin.rev_inj.1 e).symm), h4, ← mul_smul_comm, ← mul_neg] at h3
    exact mul_left_cancel₀ (sub_ne_zero.2 fun e => h2 (mul_inv_eq_one.1 (Units.val_eq_one.1 e.symm))) h3
  · by_cases h : a = b
    · subst h
      exact hd g (hNI g hn) a
    · rw [hX g a b h, hN g hn, hN g hn]
      simp

end Core

section Loc

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

omit [IsAlgClosure ℚ Ω] in
private theorem comm_ine {A : ValuationSubring Ω} {q : ℕ} {σ g : G ℚ Ω} (hσ : IsFrob (F := ℚ) A q σ)
    (hg : g ∈ Dec (F := ℚ) A) : σ * g * σ⁻¹ * g⁻¹ ∈ Ine (F := ℚ) A := by
  have hle : ∀ {k : G ℚ Ω}, k ∈ Dec (F := ℚ) A → ∀ {x : Ω}, A.valuation x ≤ 1 → A.valuation (k x) ≤ 1 :=
    fun hk x hx => (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hk x).2 ((A.valuation_le_one_iff _).1 hx))
  have hlt : ∀ {x : Ω}, A.valuation x < 1 → A.valuation (g x) < 1 := fun {x} hx => by
    rw [valuation_lt_one_iff'] at hx ⊢
    refine ⟨(apply_mem_iff_of_mem_Dec hg x).2 hx.1, hx.2.imp (fun h => by rw [h, map_zero]) fun h h' => h ?_⟩
    rw [← map_inv₀] at h'
    exact (apply_mem_iff_of_mem_Dec hg _).1 h'
  refine ⟨mul_mem (mul_mem (mul_mem hσ.1 hg) (inv_mem hσ.1)) (inv_mem hg), fun x hx => ?_⟩
  have hy := hle (inv_mem hσ.1) (hle (inv_mem hg) hx)
  have h1 := hσ.2 _ (hle hg hy)
  have h2 := hlt (hσ.2 _ hy)
  have e : σ (σ⁻¹ (g⁻¹ x)) = g⁻¹ x := σ.apply_symm_apply _
  have e' : g (g⁻¹ x) = x := g.apply_symm_apply _
  rw [e, map_sub, map_pow, e'] at h2
  have h3 := Valuation.map_sub_lt A.valuation h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  exact h3

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem chi_ine (hD : D.Good) {q : ℕ} (hq : q ∈ D.Sb) {s : G ℚ Ω} (hs : s ∈ D.Ip q) :
    chiO ℚ Ω l c.O s = 1 := by
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hq
  have hp := hD.S_prime q h1
  have hA : ¬ (D.pl q).valuation (l : Ω) < 1 := fun h => by
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 h2)
    have hi : ∀ n : ℤ, (D.pl q).valuation (n : Ω) ≤ 1 := fun n =>
      ((D.pl q).valuation_le_one_iff _).mpr (intCast_mem _ n)
    have h3 : (D.pl q).valuation ((a : Ω) * (q : Ω) + (b : Ω) * (l : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi a)) (hD.pl_over q hp)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi b)) h
    have h4 : (a : Ω) * (q : Ω) + (b : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h4, map_one] at h3
    exact lt_irrefl _ h3
  show Units.map _ (cycZ ℚ Ω l s) = 1
  rw [MonoidHom.mem_ker.1 ((places ℚ Ω l _).2.2.2 hA hs), map_one]

private theorem al_ine (hD : D.Good) {q : ℕ} (hq : q ∈ D.Sb) {s : G ℚ Ω} (hs : s ∈ D.Ip q) : D.al s = 1 := by
  have hl : l.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, -, -, hu⟩ := dvrFacts l c.O
  have h1 : residue c.O (D.om s : c.O) = 1 := by
    have := hD.om_bar s
    simp only [Raw.bar] at this
    rw [this, chi_ine hD hq hs, Units.val_one, map_one]
  have h2 : (D.om s : c.O) ^ (l - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hD.om_pow]; rfl
  have h3 := geom_sum_mul (D.om s : c.O) (l - 1)
  rw [h2, sub_self] at h3
  have h4 : D.om s = 1 := by
    refine Units.ext (sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left fun h => ?_))
    have h5 := congrArg (residue c.O) h
    simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_one, map_zero] at h5
    have h6 := (hu (l - 1) (Nat.not_dvd_of_pos_of_lt (by have := hl.two_le; omega)
      (by have := hl.two_le; omega))).map (residue c.O)
    rw [map_natCast, h5] at h6
    exact not_isUnit_zero h6
  have h7 : D.ξ s = 1 := hD.xi_unrT q (Finset.mem_insert_of_mem hq) hs
  show chiO ℚ Ω l c.O s * (D.om s)⁻¹ * D.ξ s = 1
  rw [chi_ine hD hq hs, h4, h7]; simp

private theorem ps_ine (hD : D.Good) {q : ℕ} (hq : q ∈ D.Sb) {s : G ℚ Ω} (hs : s ∈ D.Ip q) (a : Fin 4) :
    D.ps a s = ![D.ψ s, D.ψ s, 1, 1] a := by
  have h1 : D.Psi s = D.ψ s := by
    rw [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, chi_ine hD hq hs, one_pow, one_mul]
  have h2 := al_ine hD hq hs
  fin_cases a <;> simp [Raw.ps, Raw.th, h1, h2]

private theorem al_sg (hD : D.Good) {q : ℕ} (hq : q ∈ D.Sb) : D.al (D.sg q) ≠ 1 := fun h => by
  refine hD.condD q (Finset.mem_insert_of_mem hq) 0 ?_
  have h1 : chiO ℚ Ω l c.O (D.sg q) * D.ξ (D.sg q) = D.om (D.sg q) := by
    rw [← mul_inv_eq_one, mul_right_comm]; exact h
  have h2 := congrArg (fun u : c.Oˣ => residue c.O (u : c.O)) h1
  have h3 := hD.om_bar (D.sg q)
  simp only [Raw.bar, Units.val_mul, map_mul] at h2 h3
  rw [← h3] at h2
  have h4 : residue c.O (D.om (D.sg q) : c.O) ≠ 0 := ((D.om (D.sg q)).isUnit.map _).ne_zero
  simpa [Raw.bar] using (mul_eq_left₀ h4).1 h2

private theorem ex_psi {q : ℕ} (hq : q ∈ D.Sb) : ∃ s ∈ D.Ip q, D.ψ s ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨-, -, h3⟩ := Finset.mem_filter.1 hq
  rw [(Subgroup.map_eq_bot_iff _).2 h, Subgroup.card_bot] at h3
  exact (Fact.out : l.Prime).not_dvd_one h3

end Loc

theorem UpperTheory.V.Loc.spTanP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (q : ℕ), q ∈ D.Sb → ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (γ : D.Gp q → M4 E) (r' : D.Gp q →* M4 (DualNumber E)), IsFirstOrderDeformationOfRZero D q γ r' → (∀ a b, QCont l fun g => γ g a b) → (EqP D q r' ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ (g : D.Gp q) a b, a ≠ b → γ g a b = (1 - algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O)) * X a b) ∧ ∀ s : D.Gp q, (s : G ℚ Ω) ∈ D.Ip q → ∀ a, γ s a a = 0) := by
  intro Ω _ _ _ l _ c D hD q hq E _ _ _ _ _ _ _ _ γ r' hr _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  haveI : IsGalois ℚ Ω := {}
  let ι : c.Oˣ →* Eˣ := Units.map (algebraMap c.O E).toMonoidHom
  have hι : Function.Injective ι := Units.map_injective (IsFractionRing.injective c.O E)
  let χ : Fin 4 → D.Gp q →* Eˣ := fun a => ι.comp ((D.ps a).comp (D.Gp q).subtype)
  have hχ : ∀ a g, χ a g = ι (D.ps a g) := fun _ _ => rfl
  have hχ' : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.Oˣ) := fun _ _ => rfl
  have hr0 : ∀ g : D.Gp q, D.r0At q g = Matrix.diagonal fun a => ((D.ps a g : c.Oˣ) : c.O) := fun _ => rfl
  have key := core χ (fun g => algebraMap c.O E (D.th g)) (fun g => (g : G ℚ Ω) ∈ D.Ip q)
    (fun g => (g : G ℚ Ω) ∈ D.Ip q ⊓ D.ψ.ker) γ r' ?_ ?_ ?_ (fun g h => h.1) ?_ ?_ ?_
  · simp only [hχ, ← map_inv ι, ← map_mul ι] at key
    exact key
  · intro g a b
    rw [hr g a b, hr0, hχ']
    show algebraMap c.O E _ = _
    rw [Matrix.diagonal_apply]
    split_ifs <;> simp
  · intro g a b
    rw [hr g a b, hr0, hχ', Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal]
    rfl
  · intro g a
    rw [hχ', hχ', ← map_mul, ← Units.val_mul]
    congr 2
    fin_cases a <;> simp [Raw.ps, Raw.th, mul_comm]
  · intro g hg a
    rw [hχ, ps_ine hD hq hg.1, MonoidHom.mem_ker.1 hg.2]
    fin_cases a <;> simp
  · intro s hs
    haveI := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
    haveI : D.ψ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact ⟨D.ψ.ker.index, Subgroup.FiniteIndex.index_ne_zero, pow_mem hs _, D.ψ.ker.pow_index_mem _⟩
  · intro a b hab
    have hσ := hD.sg_frob q (Finset.mem_insert_of_mem hq)
    by_cases h : ∀ s : D.Gp q, (s : G ℚ Ω) ∈ D.Ip q → χ a s = χ b s
    · refine ⟨⟨D.sg q, hσ.1⟩, fun e => ?_, fun g => Or.inr ⟨comm_ine hσ g.2, h⟩⟩
      obtain ⟨s, hs, hs1⟩ := ex_psi hq
      have h1 := hι (h ⟨s, Ine_le_Dec _ hs⟩ hs)
      have h2 := hι e
      have h3 := al_sg hD hq
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1 h2
      rw [ps_ine hD hq hs, ps_ine hD hq hs] at h1
      fin_cases a <;> fin_cases b <;> simp [Raw.ps, Raw.th, hs1, hs1.symm, h3, h3.symm] at hab h1 h2
    · push Not at h
      obtain ⟨s, hs, hne⟩ := h
      refine ⟨s, hne, fun g => Or.inl ⟨?_, ?_⟩⟩
      · have hn : ((D.Ip q).subgroupOf (D.Gp q)).Normal := inferInstance
        have h1 : s ∈ (D.Ip q).subgroupOf (D.Gp q) := hs
        have h2 := mul_mem h1 (hn.conj_mem _ (inv_mem h1) g)
        rw [← mul_assoc, ← mul_assoc] at h2
        exact h2
      · simp [MonoidHom.mem_ker, mul_right_comm]
