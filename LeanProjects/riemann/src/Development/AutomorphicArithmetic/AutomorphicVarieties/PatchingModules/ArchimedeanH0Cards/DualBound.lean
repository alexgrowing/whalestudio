import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section SlopeTestRemainingChoices

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}

private theorem od_iff (Y : Matrix (Fin n) (Fin n) X) :
    Y ∈ Od A X n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Y i j = 0 :=
  ⟨fun h i j e => (Submodule.mem_bot A).1 ((h i j).1 e),
    fun h i j => ⟨fun e => (Submodule.mem_bot A).2 (h i j e), fun _ => Submodule.mem_top⟩⟩

private theorem ev_iff (Y : Matrix (Fin n) (Fin n) X) :
    Y ∈ Ev A X n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Y i j = 0 :=
  ⟨fun h i j e => (Submodule.mem_bot A).1 ((h i j).2 e),
    fun h i j => ⟨fun _ => Submodule.mem_top, fun e => (Submodule.mem_bot A).2 (h i j e)⟩⟩

private theorem ev_mul_od {E Y : Matrix (Fin n) (Fin n) X} (hE : E ∈ Ev A X n a) (hY : Y ∈ Od A X n a) :
    E * Y ∈ Od A X n a := by
  rw [od_iff] at hY ⊢
  rw [ev_iff] at hE
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [hY k j (h.symm.trans e), mul_zero]
  · rw [hE i k h, zero_mul]

private theorem od_mul_ev {E Y : Matrix (Fin n) (Fin n) X} (hE : E ∈ Ev A X n a) (hY : Y ∈ Od A X n a) :
    Y * E ∈ Od A X n a := by
  rw [od_iff] at hY ⊢
  rw [ev_iff] at hE
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ((k : ℕ) < a) ↔ ((j : ℕ) < a)
  · rw [hY i k (e.trans h.symm), zero_mul]
  · rw [hE k j h, mul_zero]

private theorem ev_map {E : Matrix (Fin n) (Fin n) A} (hE : E ∈ Ev A A n a) :
    E.map (algebraMap A X) ∈ Ev A X n a := by
  rw [ev_iff] at hE ⊢
  intro i j h
  simp [Matrix.map_apply, hE i j h]

private theorem comm_span {M : Type} [AddCommGroup M] (φ : Od A X n a →+ M) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ E ∈ S, E ∈ Ev A A n a ∧ ∀ Y Y₁ Y₂ : Od A X n a,
      (Y₁ : Matrix (Fin n) (Fin n) X) = E.map (algebraMap A X) * Y →
      (Y₂ : Matrix (Fin n) (Fin n) X) = Y * E.map (algebraMap A X) → φ Y₁ = φ Y₂)
    (R : Matrix (Fin n) (Fin n) A) (hR : R ∈ Submodule.span A S) :
    R ∈ Ev A A n a ∧ ∀ Y Y₁ Y₂ : Od A X n a,
      (Y₁ : Matrix (Fin n) (Fin n) X) = R.map (algebraMap A X) * Y →
      (Y₂ : Matrix (Fin n) (Fin n) X) = Y * R.map (algebraMap A X) → φ Y₁ = φ Y₂ := by
  induction hR using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨Submodule.zero_mem _, fun Y Y₁ Y₂ h₁ h₂ => ?_⟩
    have e₁ : Y₁ = 0 := Subtype.ext (by rw [h₁]; simp)
    have e₂ : Y₂ = 0 := Subtype.ext (by rw [h₂]; simp)
    rw [e₁, e₂]
  | add x y _ _ hx hy =>
    refine ⟨Submodule.add_mem _ hx.1 hy.1, fun Y Y₁ Y₂ h₁ h₂ => ?_⟩
    let P : Od A X n a := ⟨x.map (algebraMap A X) * Y, ev_mul_od (ev_map hx.1) Y.2⟩
    let Q : Od A X n a := ⟨y.map (algebraMap A X) * Y, ev_mul_od (ev_map hy.1) Y.2⟩
    let P' : Od A X n a := ⟨Y * x.map (algebraMap A X), od_mul_ev (ev_map hx.1) Y.2⟩
    let Q' : Od A X n a := ⟨Y * y.map (algebraMap A X), od_mul_ev (ev_map hy.1) Y.2⟩
    have hmap : (x + y).map (algebraMap A X) = x.map (algebraMap A X) + y.map (algebraMap A X) := by
      ext i j
      simp
    have e₁ : Y₁ = P + Q := Subtype.ext (by rw [h₁, hmap, add_mul]; rfl)
    have e₂ : Y₂ = P' + Q' := Subtype.ext (by rw [h₂, hmap, mul_add]; rfl)
    rw [e₁, e₂, map_add, map_add, hx.2 Y P P' rfl rfl, hy.2 Y Q Q' rfl rfl]
  | smul c x _ hx =>
    refine ⟨Submodule.smul_mem _ c hx.1, fun Y Y₁ Y₂ h₁ h₂ => ?_⟩
    apply hx.2 (c • Y) Y₁ Y₂
    · rw [h₁]
      ext i j
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Submodule.coe_smul, smul_eq_mul,
        map_mul]
      simp only [Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · rw [h₂]
      ext i j
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Submodule.coe_smul, smul_eq_mul,
        map_mul]
      simp only [Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring

private def e1 (R : Type) [CommRing R] (n a : ℕ) : Matrix (Fin n) (Fin n) R :=
  diagonal fun i => if (i : ℕ) < a then 1 else 0

private theorem first_raising_mem_equivariant : e1 X n a ∈ Ev A X n a := by
  rw [ev_iff]
  intro i j h
  have hij : i ≠ j := by
    rintro rfl
    exact h Iff.rfl
  simp [e1, Matrix.diagonal_apply_ne _ hij]

private theorem kill {M : Type} [AddCommGroup M] (φ : Od A X n a →+ M) (c : A)
    (h : ∀ Y Y₁ Y₂ : Od A X n a,
      (Y₁ : Matrix (Fin n) (Fin n) X) = (c • e1 A n a).map (algebraMap A X) * Y →
      (Y₂ : Matrix (Fin n) (Fin n) X) = Y * (c • e1 A n a).map (algebraMap A X) → φ Y₁ = φ Y₂)
    (Y : Od A X n a) : φ (c • Y) = 0 := by
  have hY := (od_iff (Y : Matrix (Fin n) (Fin n) X)).1 Y.2
  let U : Od A X n a := ⟨e1 X n a * Y, ev_mul_od (first_raising_mem_equivariant (A := A)) Y.2⟩
  let W : Od A X n a := ⟨Y * e1 X n a, od_mul_ev (first_raising_mem_equivariant (A := A)) Y.2⟩
  let dc : Matrix (Fin n) (Fin n) X := diagonal fun i : Fin n => if (i : ℕ) < a then algebraMap A X c else 0
  have hm : (c • e1 A n a).map (algebraMap A X) = dc := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : (i : ℕ) < a <;> simp [dc, e1, hi]
    · simp [dc, e1, Matrix.diagonal_apply_ne _ hij]
  have hdec : Y = U + W := by
    apply Subtype.ext
    ext i j
    show Y.1 i j = (e1 X n a * Y.1) i j + (Y.1 * e1 X n a) i j
    rw [e1, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · simp [hi, hj, hY i j (iff_of_true hi hj)]
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [hi, hj, hY i j (iff_of_false hi hj)]
  have hU : φ (c • U) = 0 := by
    have := h U (c • U) 0 ?_ ?_
    · rw [this, map_zero]
    · rw [hm]
      ext i j
      show c • (e1 X n a * Y.1) i j = (dc * (e1 X n a * Y.1)) i j
      rw [Matrix.diagonal_mul, e1, Matrix.diagonal_mul]
      by_cases hi : (i : ℕ) < a <;> simp [hi, Algebra.smul_def]
    · rw [hm]
      ext i j
      show (0 : X) = (e1 X n a * Y.1 * dc) i j
      rw [Matrix.mul_diagonal, e1, Matrix.diagonal_mul]
      by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
      · simp [hi, hj, hY i j (iff_of_true hi hj)]
      · simp [hi, hj]
      · simp [hi, hj]
      · simp [hi, hj]
  have hW : φ (c • W) = 0 := by
    have := h W 0 (c • W) ?_ ?_
    · rw [← this, map_zero]
    · rw [hm]
      ext i j
      show (0 : X) = (dc * (Y.1 * e1 X n a)) i j
      rw [Matrix.diagonal_mul, e1, Matrix.mul_diagonal]
      by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
      · simp [hi, hj, hY i j (iff_of_true hi hj)]
      · simp [hi, hj]
      · simp [hi, hj]
      · simp [hi, hj]
    · rw [hm]
      ext i j
      show c • (Y.1 * e1 X n a) i j = (Y.1 * e1 X n a * dc) i j
      rw [Matrix.mul_diagonal, e1, Matrix.mul_diagonal]
      by_cases hj : (j : ℕ) < a <;> simp [hj, Algebra.smul_def, mul_comm]
  rw [hdec, smul_add, map_add, hU, hW, add_zero]

private noncomputable def pol {K : Type} [Field K] {s : ℕ} (c : Fin s → K) : PowerSeries K :=
  PowerSeries.mk fun k => if h : k < s then c ⟨k, h⟩ else 0

private theorem pol_spec {K : Type} [Field K] (s : ℕ) (b : PowerSeries K) :
    ∃ (c : Fin s → K) (d : PowerSeries K), b = pol c + PowerSeries.X ^ s * d := by
  refine ⟨fun k => PowerSeries.coeff (k : ℕ) b, PowerSeries.mk fun k => PowerSeries.coeff (k + s) b, ?_⟩
  ext k
  rw [map_add, PowerSeries.coeff_X_pow_mul', pol, PowerSeries.coeff_mk]
  by_cases hk : k < s
  · simp [hk, Nat.not_le.mpr hk]
  · have hle : s ≤ k := Nat.le_of_not_lt hk
    simp [hk, hle, PowerSeries.coeff_mk, Nat.sub_add_cancel hle]

private def odOf (a : ℕ) (Z : Fin n → Fin n → A) : Od A X n a :=
  ⟨Matrix.of fun i j => if (((i : ℕ) < a) ↔ ((j : ℕ) < a)) then 0 else algebraMap A X (Z i j),
    (od_iff _).2 fun i j e => by simp [e]⟩

private theorem od_dec {K : Type} [Field K] {X : Type} [CommRing X] [Algebra (PowerSeries K) X]
    (hX : Function.Surjective (algebraMap (PowerSeries K) X)) (s : ℕ) (Y : Od (PowerSeries K) X n a) :
    ∃ (c : Fin n → Fin n → Fin s → K) (Y' : Od (PowerSeries K) X n a),
      Y = odOf a (fun i j => pol (c i j)) + (PowerSeries.X : PowerSeries K) ^ s • Y' := by
  choose b hb using fun i j => hX ((Y : Matrix (Fin n) (Fin n) X) i j)
  choose c d hcd using fun i j => pol_spec (K := K) s (b i j)
  refine ⟨c, odOf (A := PowerSeries K) (X := X) a d, ?_⟩
  apply Subtype.ext
  ext i j
  simp only [odOf, Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
  by_cases hij : ((i : ℕ) < a ↔ (j : ℕ) < a)
  · simp [hij, (od_iff _).1 Y.2 i j hij]
  · simp only [hij, if_false]
    rw [← hb i j, hcd i j, map_add, Algebra.smul_def, map_mul]

end SlopeTestRemainingChoices

private theorem card_zmod_nsmul_eq_zero_le (l : ℕ) [Fact l.Prime] (N : ℕ) (hN : 0 < N) :
    Nat.card {y : ZMod l // N • y = 0} ≤ N := by
  by_cases hd : (N : ZMod l) = 0
  · have hdvd : l ∣ N := (ZMod.natCast_eq_zero_iff N l).mp hd
    calc Nat.card {y : ZMod l // N • y = 0} ≤ Nat.card (ZMod l) := Finite.card_subtype_le _
      _ = l := Nat.card_zmod l
      _ ≤ N := Nat.le_of_dvd hN hdvd
  · have hsub : Subsingleton {y : ZMod l // N • y = 0} := by
      constructor
      rintro ⟨y, hy⟩ ⟨z, hz⟩
      rw [nsmul_eq_mul] at hy hz
      have hy0 := (mul_eq_zero.mp hy).resolve_left hd
      have hz0 := (mul_eq_zero.mp hz).resolve_left hd
      exact Subtype.ext (hy0.trans hz0.symm)
    exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans hN

private theorem f_symm_eq_of_left_right_mul_mat {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (hom : G.Hom G0) {n : ℕ}
    (x : NP G0.frame n) (e : ℕ) (D : Dat x.A (plOf G)) (hD : IsOd hom x (x.Am e) D)
    (f : D.M.X →+ ZMod l)
    (hf : ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m)
    (g' : G0.frame.G₀) (hg' : g' ∈ G0.frame.G') (Y Y₁ Y₂ : Od x.A (x.Am e) n x.a)
    (h₁ : (Y₁ : Matrix (Fin n) (Fin n) (x.Am e)) = (mat x.ρ g').map (algebraMap x.A (x.Am e)) * Y)
    (h₂ : (Y₂ : Matrix (Fin n) (Fin n) (x.Am e)) = Y * (mat x.ρ g').map (algebraMap x.A (x.Am e))) :
    f (hD.e.symm Y₁) = f (hD.e.symm Y₂) := by
  obtain ⟨γ, hγ⟩ := hom.surj (g' : G0.Γ)
  have hγk : γ ∈ G.η.ker := by
    rw [MonoidHom.mem_ker, ← hom.η, hγ]
    exact g'.2
  let g : G.G₀ := ⟨γ, hγk⟩
  have hpg : hom.p₀ g = g' := Subtype.ext hγ
  have hε : G.ε γ = 1 := by
    rw [← hom.ε, hγ]
    exact hg'
  have hinv : (mat x.ρ g').map (algebraMap x.A (x.Am e)) * x.ρX (x.Am e) g'⁻¹ = 1 := by
    simp only [NP.ρX]
    rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hρ : x.ρX (x.Am e) g' = (mat x.ρ g').map (algebraMap x.A (x.Am e)) := rfl
  have hf' := hf γ (hD.e.symm Y₂)
  rw [hε] at hf'
  simp only [Units.val_one, map_one, one_mul] at hf'
  have hY : hD.e.symm Y₁ = D.M.ρ γ (hD.e.symm Y₂) := by
    apply hD.e.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    have := hD.act g (hD.e.symm Y₂)
    rw [this, LinearEquiv.apply_symm_apply, map_inv, hpg, h₁, h₂, hρ, mul_assoc, mul_assoc, hinv, mul_one]
  rw [hY, hf']

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Pa.B2.dualBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n), ∃ C : ℕ, ∀ (G : Glob l L) (h : G.Hom G0) (e : ℕ) (D : Dat x.A (plOf G)), IsOd h x (x.Am e) D → Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} ≤ Nat.card x.K ^ C := by
  intro l _ L G0 n x
  obtain ⟨s, hs⟩ := x.span (e1 x.A n x.a) first_raising_mem_equivariant
  refine ⟨Nat.card x.K * (n * n * s), ?_⟩
  intro G hom e D hD
  let Ψ : (Fin n × Fin n × Fin s → x.K) →+ Od x.A (x.Am e) n x.a :=
    { toFun := fun c => odOf x.a (fun i j => pol (fun k => c (i, j, k)))
      map_zero' := by
        apply Subtype.ext
        ext i j
        simp only [odOf, Matrix.of_apply, Submodule.coe_zero, Matrix.zero_apply]
        split_ifs
        · rfl
        · have : pol (s := s) (fun _ => (0 : x.K)) = 0 := by
            ext k
            simp [pol, PowerSeries.coeff_mk]
          exact (congrArg (algebraMap x.A (x.Am e)) this).trans (map_zero _)
      map_add' := fun c c' => by
        apply Subtype.ext
        ext i j
        simp only [odOf, Matrix.of_apply, Submodule.coe_add, Matrix.add_apply]
        split_ifs
        · simp
        · have : pol (fun k => (c + c') (i, j, k)) = pol (fun k => c (i, j, k)) + pol (fun k => c' (i, j, k)) := by
            ext k
            simp only [pol, PowerSeries.coeff_mk, map_add, Pi.add_apply]
            split_ifs <;> simp
          rw [this, map_add] }
  have hkill : ∀ f : {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m},
      ∀ Y : Od x.A (x.Am e) n x.a, f.1 (hD.e.symm ((PowerSeries.X : x.A) ^ s • Y)) = 0 := by
    intro f Y
    let φ : Od x.A (x.Am e) n x.a →+ ZMod l := f.1.comp hD.e.symm.toLinearMap.toAddMonoidHom
    have hS : ∀ E ∈ mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀), E ∈ Ev x.A x.A n x.a ∧
        ∀ Y Y₁ Y₂ : Od x.A (x.Am e) n x.a,
          (Y₁ : Matrix (Fin n) (Fin n) (x.Am e)) = E.map (algebraMap x.A (x.Am e)) * Y →
          (Y₂ : Matrix (Fin n) (Fin n) (x.Am e)) = Y * E.map (algebraMap x.A (x.Am e)) → φ Y₁ = φ Y₂ := by
      rintro E ⟨g', hg', rfl⟩
      exact ⟨x.blk g', fun Y Y₁ Y₂ h₁ h₂ => f_symm_eq_of_left_right_mul_mat hom x e D hD f.1 f.2 g' hg' Y Y₁ Y₂ h₁ h₂⟩
    have hcs := comm_span (A := x.A) (X := x.Am e) φ _ hS _ hs
    exact kill φ (PowerSeries.X ^ s) hcs.2 Y
  have hK : 0 < Nat.card x.K := Nat.card_pos
  have hsmul0 : ∀ v : (Fin n × Fin n × Fin s → x.K), Nat.card x.K • v = 0 := by
    intro v
    ext t
    simp only [Pi.smul_apply, Pi.zero_apply]
    exact card_nsmul_eq_zero'
  let Φ : {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} →
      (Fin n × Fin n × Fin s → x.K → {y : ZMod l // Nat.card x.K • y = 0}) :=
    fun f t v => ⟨f.1 (hD.e.symm (Ψ (Pi.single t v))), by
      rw [← map_nsmul, ← map_nsmul, ← map_nsmul, hsmul0, map_zero, map_zero, map_zero]⟩
  have hinj : Function.Injective Φ := by
    intro f f' hff
    apply Subtype.ext
    ext m
    obtain ⟨c, Y', hY⟩ := od_dec (K := x.K) (X := x.Am e) (n := n) (a := x.a)
      (fun y => Ideal.Quotient.mk_surjective y) s (hD.e m)
    have key : ∀ f : {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m},
        f.1 m = ∑ t, (Φ f t (c t.1 t.2.1 t.2.2)).1 := by
      intro f
      have hm : m = hD.e.symm (Ψ (fun t => c t.1 t.2.1 t.2.2))
          + hD.e.symm ((PowerSeries.X : x.A) ^ s • Y') := by
        rw [← map_add]
        apply hD.e.injective
        rw [LinearEquiv.apply_symm_apply, hY]
        rfl
      conv_lhs => rw [hm]
      have hsum : (fun t => c t.1 t.2.1 t.2.2 : Fin n × Fin n × Fin s → x.K)
          = ∑ t, Pi.single t (c t.1 t.2.1 t.2.2) := (Finset.univ_sum_single _).symm
      rw [map_add, hkill f Y', add_zero, hsum, map_sum, map_sum, map_sum]
    rw [key f, key f', hff]
  calc _ ≤ Nat.card (Fin n × Fin n × Fin s → x.K → {y : ZMod l // Nat.card x.K • y = 0}) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = (Nat.card {y : ZMod l // Nat.card x.K • y = 0} ^ Nat.card x.K) ^ (n * n * s) := by
        rw [Nat.card_fun, Nat.card_fun]
        simp [Nat.card_prod, mul_assoc]
    _ ≤ (Nat.card x.K ^ Nat.card x.K) ^ (n * n * s) :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left (card_zmod_nsmul_eq_zero_le l _ hK) _) _
    _ = Nat.card x.K ^ (Nat.card x.K * (n * n * s)) := by rw [← pow_mul]
