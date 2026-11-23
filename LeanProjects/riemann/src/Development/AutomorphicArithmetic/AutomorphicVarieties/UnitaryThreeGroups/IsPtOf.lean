import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem ipo_mul {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  rcases eq_or_ne (f z) 0 with h0 | h0
  · simp [h0]
  have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr h0
  suffices hx : ‖f x‖ ≤ 1 by nlinarith [norm_nonneg (f x)]
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) hx
  have hmem : x ^ n * z ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hz
  have h1 := hf _ hmem
  rw [map_mul, map_pow, norm_mul, norm_pow] at h1
  have := (inv_lt_iff_one_lt_mul₀ hpos).mp hn
  linarith [mul_comm (‖f x‖ ^ n) ‖f z‖]

private theorem ipo_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  refine ⟨((s.sup fun g => ‖f g‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
  · have : (s.sup fun g => ‖f g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hgm : g ∈ maximalIdeal R := hs ▸ Ideal.subset_span hg
      have := hf g hgm
      exact_mod_cast this
    exact_mod_cast this
  · intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      have : ‖f x‖₊ ≤ s.sup fun g => ‖f g‖₊ := Finset.le_sup (f := fun g => ‖f g‖₊) hx
      exact_mod_cast this
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    | smul a x hx ihx =>
      rw [smul_eq_mul]
      refine (ipo_mul hf a ?_).trans ihx
      exact hs ▸ hx

private theorem ipo_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ipo_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [zero_add, pow_one] at hz ⊢
      exact hρ z hz
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (hρ b hb) (norm_nonneg _) (pow_nonneg hρ0 _)
      · intro x y hx hy
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨n + 1, fun z hz => (key n z hz).trans_lt ?_⟩
  calc ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ n)
    _ < ε := hn

private theorem ipo_cont {f : R →ₐ[O] K} (hf : IsLocPt f) {X : Type} [TopologicalSpace X] (u : X → R)
    (hu : AdicCont (maximalIdeal R) u) : Continuous fun g => f (u g) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ipo_pow hf hε
  have hopen := (hu n).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ n) (u g))
  filter_upwards [hopen.mem_nhds rfl] with g' hg'
  have heq : Ideal.Quotient.mk (maximalIdeal R ^ n) (u g') = Ideal.Quotient.mk (maximalIdeal R ^ n) (u g) := hg'
  rw [Ideal.Quotient.eq] at heq
  rw [dist_eq_norm, ← map_sub]
  exact hn _ heq

end SlopeTestRemainingChoices

private theorem ipo_le_one {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  haveI := c.dvr
  haveI : IsLocalHom (algebraMap c.O R) := IsCO.isLocalHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hm : algebraMap c.O R ϖ ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap c.O R) ϖ).mp hu)
  have hne : f (algebraMap c.O R ϖ) ≠ 0 := by
    rw [AlgHom.commutes]
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext (by simpa using h)
  have hpos : 0 < ‖f (algebraMap c.O R ϖ)‖ := norm_pos_iff.mpr hne
  have h := ipo_mul hf x hm
  rw [map_mul, norm_mul] at h
  nlinarith [norm_nonneg (f x)]

private theorem diagonal_rep_map_entries {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, MonoidHom.comp_apply]
  split_ifs
  · first
      | (rw [← map_zpow, Units.coe_map]; rfl)
      | (rw [← map_pow, Units.coe_map]; rfl)
  · simp

theorem UpperTheory.V.U3.isPt_push :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁),
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f → D.IsPt U g₁ (push f S.r.hom) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ S f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  have hm : ∀ g a b, (push f S.r.hom g).mat a b = f ((S.r.hom g).mat a b) := fun _ _ _ => rfl
  refine ⟨fun g => S.r.hasMult g, ?_, fun g a b => ipo_le_one hf _, fun g a b => ?_, ⟨?_, ?_, ?_⟩, fun g hg => ?_,
    f.comp φ, fun x hx => hf _ ?_, fun x hx => ?_, ?_⟩
  · exact continuous_matrix fun a b => ipo_cont hf _ (S.r.cont a b)
  · have h1 : (r0 D.η D.ΨQ g).mat a b = algebraMap c.O (PadicAlgCl l) ((r0 D.η D.Ψ g).mat a b) :=
      diagonal_rep_map_entries _ _ _ _ _ _
    rw [hm, h1, ← f.commutes, ← map_sub]
    refine hf _ ((res_eq_zero_iff c.O S.R _).1 ?_)
    have h2 : res c.O S.R ((S.r.hom g).mat a b) = (rbar c.O D.η D.Ψ g).mat a b :=
      congrArg (fun x : GG 3 (ResidueField c.O) => x.mat a b) (S.r.red g)
    have h3 : (rbar c.O D.η D.Ψ g).mat a b = residue c.O ((r0 D.η D.Ψ g).mat a b) := diagonal_rep_map_entries _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · show (S.r.hom D.cc).mat.map (f : S.R →+* PadicAlgCl l) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* PadicAlgCl l) (S.r.hom g) = 1
    rw [hk g hg, map_one]
  · show φ x ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff c.O, res_map, res_eq_zero_iff]
    exact hx
  · have : φ x = 0 := hI hx
    show f (φ x) = 0
    rw [this, map_zero]
  · have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    refine MonoidHom.ext fun g => ?_
    show GG.map (f : S.R →+* PadicAlgCl l) ((U.r.map φ).hom g) = _
    rw [h1]
    rfl
