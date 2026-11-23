import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem lc_wcomp_mul (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add, h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add, h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

private theorem lc_wcomp_self (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) : wcomp O wt w e = e := by
  ext n
  rw [coeff_wcomp]
  split_ifs with h
  · rfl
  · exact (he n h).symm

private theorem lc_inv {E τ ι : Type} [CommRing E] [Fintype ι] [DecidableEq ι] (w : τ → ℤ) (u : ι → ℤ)
    (A B : Matrix ι ι (MvPowerSeries τ E)) (h1 : A * B = 1) (h2 : B * A = 1)
    (hA : ∀ a b, A a b ∈ wtPart E w (u a - u b)) (a b : ι) : B a b ∈ wtPart E w (u a - u b) := by
  let B' : Matrix ι ι (MvPowerSeries τ E) := Matrix.of fun a b => wcomp E w (u a - u b) (B a b)
  have h3 : B' * A = 1 := by
    ext1 a c
    have e : (B' * A) a c = wcomp E w (u a - u c) ((B * A) a c) := by
      rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lc_wcomp_mul E w (hA b c)]
      have : u a - u c - (u b - u c) = u a - u b := by ring
      rw [this]; rfl
    rw [e, h2]
    by_cases hac : a = c
    · subst hac
      rw [Matrix.one_apply_eq, sub_self]
      exact lc_wcomp_self E w (one_mem_wtPart E w)
    · rw [Matrix.one_apply_ne hac, map_zero]
  have h4 : B' = B := by
    rw [← Matrix.mul_one B', ← h1, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [← h4]
  exact wcomp_mem E w _ _

private theorem lc_JMJ {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem lc_emb {E τ : Type} [CommRing E] (w : τ → ℤ) (x : GG 3 (MvPowerSeries τ E))
    (hx : ∀ a b, x.mat a b ∈ wtPart E w (wt a b)) (a b : Fin 3 ⊕ Fin 3) :
    emb x a b ∈ wtPart E w (wt6 a - wt6 b) := by
  have hθ : ∀ a b, (theta x.left : Matrix (Fin 3) (Fin 3) (MvPowerSeries τ E)) a b ∈ wtPart E w (wt1 a - wt1 b) := by
    intro a b
    rw [theta_val, lc_JMJ]
    have := lc_inv w wt1 x.mat ((x.left⁻¹ : GL (Fin 3) _) : Matrix (Fin 3) (Fin 3) (MvPowerSeries τ E))
      (Units.mul_inv x.left) (Units.inv_mul x.left) hx b.rev a.rev
    have e : ∀ a b : Fin 3, wt1 b.rev - wt1 a.rev = wt1 a - wt1 b := by decide
    rwa [e] at this
  rw [emb_apply]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact hx a b
    | exact hθ a b
    | exact zero_mem _

private theorem lc_order {K τ : Type} [CommRing K] (n : ℕ) :
    ∀ g ∈ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries τ K →+* K) ^ n, (n : ℕ∞) ≤ g.order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      exact add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 hb)
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

private theorem lc_graded {O E σ τ : Type} [CommRing O] [CommRing E] [Algebra O E] [Finite σ] (v : σ → ℤ) (w : τ → ℤ)
    (Φ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E)
    (h0 : ∀ s, MvPowerSeries.constantCoeff (Φ (MvPowerSeries.X s)) = 0)
    (h1 : ∀ s, Φ (MvPowerSeries.X s) ∈ wtPart E w (v s)) (j : ℤ) (F : MvPowerSeries σ O) (hF : F ∈ wtPart O v j) :
    Φ F ∈ wtPart E w j := by
  intro d hd
  obtain ⟨y, hy, hm⟩ := approx v Φ (RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries τ E →+* E))
    (fun j => (wtPart E w j).restrictScalars O) (one_mem_wtPart E w)
    (fun i j a ha b hb => mul_mem_wtPart E w ha hb) h0 h1 j F hF (d.degree + 1)
  have h2 : MvPowerSeries.coeff d (Φ F - y) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (lc_order _ _ hm))
    exact_mod_cast Nat.lt_succ_self _
  rwa [map_sub, hy d hd, sub_zero] at h2

theorem UpperTheory.exists_origin_and_chart_of_isLocPres :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {H : Type} [Group H] [TopologicalSpace H] {η : H →* ℤˣ} {Ψ : H →* Oˣ}
          (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (x : U.R →ₐ[O] O) {τ : Type} [Fintype τ] (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O))
          (WB : WPres O ℤ (U.R ⧸ I)), IsBase η Ψ U.r.hom x → LocChart U I x w φ → IsLocPres U I WB →
          ∃ hB : WB.HasOrigin, (WB.origin hB).comp (Ideal.Quotient.mkₐ O I) = x ∧
            ∃ φb : (U.R ⧸ I) →ₐ[O] MvPowerSeries τ (FractionRing O), IsChart WB.part (WB.origin hB) w φb := by
  intro O _ _ _ H _ _ η Ψ U I x τ _ w φ WB hx hφ hW
  have hφI : ∀ f ∈ I, φ f = 0 := fun f hf => by rw [← hφ.ker] at hf; exact hf
  have hxI : ∀ f ∈ I, x f = 0 := fun f hf => by
    apply IsFractionRing.injective O (FractionRing O)
    rw [← hφ.const, hφI f hf, map_zero, map_zero]
  let xb : (U.R ⧸ I) →ₐ[O] O := Ideal.Quotient.liftₐ I x hxI
  let φb : (U.R ⧸ I) →ₐ[O] MvPowerSeries τ (FractionRing O) := Ideal.Quotient.liftₐ I φ hφI
  have hxb : ∀ f, xb (Ideal.Quotient.mkₐ O I f) = x f := fun f => rfl
  have hφb : ∀ f, φb (Ideal.Quotient.mkₐ O I f) = φ f := fun f => rfl
  have hz : ∀ s, ∃ g a b, WB.wt s = wt6 a - wt6 b ∧ WB.z s =
      Ideal.Quotient.mkₐ O I (emb (U.r.hom g) a b - algebraMap O U.R (emb (r0 η Ψ g) a b)) := fun s => by
    obtain ⟨g, a, b, h1, h2⟩ := hW.1 s
    exact ⟨g, a, b, h1, by rw [h2, emb_push, map_sub, AlgHom.commutes]⟩
  have hz0 : ∀ s, xb (WB.z s) = 0 := fun s => by
    obtain ⟨g, a, b, -, h2⟩ := hz s
    rw [h2, hxb]
    exact base_coord hx g a b
  have hconst : ∀ f, MvPowerSeries.constantCoeff (φb f) = algebraMap O (FractionRing O) (xb f) := fun f => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I f
    rw [hφb, hxb, hφ.const]
  obtain ⟨hB, hO⟩ := origin_of WB xb hz0
  refine ⟨hB, by rw [hO]; exact AlgHom.ext hxb, φb, ?_⟩
  rw [hO]
  refine ⟨?_, hconst, fun i => ?_, fun f hf0 hf1 => ?_⟩
  · rintro j _ ⟨F, hF, rfl⟩
    refine lc_graded WB.wt w (φb.comp WB.π) (fun s => ?_) (fun s => ?_) j F hF
    · show MvPowerSeries.constantCoeff (φb (WB.z s)) = 0
      rw [hconst, hz0, map_zero]
    · show φb (WB.z s) ∈ _
      obtain ⟨g, a, b, h1, h2⟩ := hz s
      rw [h2, hφb, h1, map_sub, AlgHom.commutes, ← emb_push]
      refine sub_mem (lc_emb w _ (fun a b => hφ.graded g a b) a b) ?_
      by_cases hab : wt6 a = wt6 b
      · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ _ (one_mem_wtPart _ w)
      · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab, map_zero]
        exact zero_mem _
  · obtain ⟨f, hf⟩ := hφ.onto i
    exact ⟨Ideal.Quotient.mkₐ O I f, hf⟩
  · obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I f
    obtain ⟨c, hc, hf⟩ := hφ.inj f hf0 hf1
    refine ⟨c, hc, ?_⟩
    rw [← map_smul]
    have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker xb ^ 2).comap (Ideal.Quotient.mkₐ O I) := by
      refine sup_le ?_ fun y hy => ?_
      · refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)
        exact hy
      · rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hy]
        exact zero_mem _
    exact hle hf
