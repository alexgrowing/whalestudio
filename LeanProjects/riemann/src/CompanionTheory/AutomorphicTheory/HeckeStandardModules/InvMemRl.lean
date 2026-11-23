import CompanionTheory.AutomorphicTheory.HeckeStandardModules.IntegralOfModule

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA

noncomputable section

namespace CompanionTheory.L3H

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

local notation3 "L⁺" => maximalRealSubfield L

theorem ent_mul (x y : GA L n) : ent (x * y) = ent x * ent y := rfl

theorem mat_mem {S : Subring (AL L)} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S)
    (i j : Fin n) : (A * B) i j ∈ S :=
  Matrix.mul_apply (M := A) (N := B) ▸ Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hA i a) (hB a j)

section R

variable (l : ℕ) [hl : Fact l.Prime]

instance span_prime : (Ideal.span {(l : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)

abbrev Rl : Subalgebra ℤ ℚ :=
  Localization.subalgebra.ofField ℚ (Ideal.span {(l : ℤ)}).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

variable {l}

theorem inv_mem_Rl {m : ℕ} (hm : ¬ l ∣ m) : ∃ r : Rl l, algebraMap (Rl l) ℂ r = (m : ℂ)⁻¹ := by
  have hS : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl := fun h =>
    hm (Int.natCast_dvd_natCast.1 (Ideal.mem_span_singleton.1 h))
  refine ⟨⟨(m : ℚ)⁻¹, 1, m, hS, by simp⟩, ?_⟩
  rw [IsScalarTower.algebraMap_apply (Rl l) ℚ ℂ]
  simp

end R

section Eig

variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem gq_ent {γ : GA L n} (hγ : γ ∈ GQ L n) : ∃ γ₀ : GL (Fin n) L, (γ : GL (Fin n) (AL L)) =
    Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀ := by
  obtain ⟨γ₀, -, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨γ₀, e.symm⟩

def M0 (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ) : Submodule (Rl l) ℂ :=
  Submodule.span (Rl l) (Set.range fun p : (L →+* ℂ) × Module.Free.ChooseBasisIndex ℤ (𝓞 L) =>
    p.1 (RingOfIntegers.basis L p.2 : L) / (c : ℂ) ^ 2)

theorem M0_fg (l : ℕ) [Fact l.Prime] (c : ℕ) : (M0 L l c).FG := Submodule.fg_span (Set.finite_range _)

theorem key_M0 {l : ℕ} [Fact l.Prime] {c : ℕ} (hc : c ≠ 0) (x : L)
    (hx : ∃ m : ℕ, ¬ l ∣ m ∧ ((m * c ^ 2 : ℕ) : AL L) * (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) ∈ ALint L)
    (τ : L →+* ℂ) : τ x ∈ M0 L l c := by
  obtain ⟨m, hm, h⟩ := hx
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun e => hm (e ▸ dvd_zero l)
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  have hint : IsIntegral ℤ (((m * c ^ 2 : ℕ) : L) * x) := by
    refine Formalism.UG.P.csGlob_int (F := maximalRealSubfield L) (E := L) _ ?_
    rw [← ALint_eq]
    convert h using 1
    show (((m * c ^ 2 : ℕ) : L) * x) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) = _
    rw [← one_mul (1 : AFplus L), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
  set y : 𝓞 L := ⟨_, hint⟩
  have hy := (RingOfIntegers.basis L).sum_repr y
  have hτ : τ (((m * c ^ 2 : ℕ) : L) * x) =
      ∑ r, ((RingOfIntegers.basis L).repr y r : ℂ) * τ (RingOfIntegers.basis L r : L) := by
    have := congrArg (τ.comp (algebraMap (𝓞 L) L)) hy
    rw [show τ (((m * c ^ 2 : ℕ) : L) * x) = (τ.comp (algebraMap (𝓞 L) L)) y from rfl, ← this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨r, hr⟩ := inv_mem_Rl hm
  have hx' : τ x = algebraMap (Rl l) ℂ r *
      ∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * (τ (RingOfIntegers.basis L i : L) / (c : ℂ) ^ 2) := by
    have e : ∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * (τ (RingOfIntegers.basis L i : L) / (c : ℂ) ^ 2) =
        (∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * τ (RingOfIntegers.basis L i : L)) / (c : ℂ) ^ 2 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hr, e, ← hτ, map_mul, map_natCast]
    push_cast
    field_simp
  rw [hx', ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (Submodule.sum_mem _ fun i _ => ?_)
  rw [← zsmul_eq_mul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(τ, i), rfl⟩)

theorem eig_int (alg : Formalism.AUTREP.IsAlgWeight L n ρ) (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {l : ℕ} [hl' : Fact l.Prime]
    (hsl : ¬ s.Above l) (d : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) {f : Formalism.AUTREP.GAf L n → W}
    (hf : f ∈ NG.TypeSp ρ J χ) (hf0 : f ≠ 0) (ν : ℂ)
    (hν : op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f = ν • f) : IsIntegral (Rl l) ν := by
  have hl := hl'.out
  letI : Module (Rl l) W := Module.compHom W (algebraMap (Rl l) ℂ)
  haveI : IsScalarTower (Rl l) ℂ W := ⟨fun r c w => by
    show (r • c) • w = algebraMap (Rl l) ℂ r • (c • w)
    rw [Algebra.smul_def r c, mul_smul]⟩
  haveI : IsNoetherianRing (Rl l) :=
    IsLocalization.isNoetherianRing (Ideal.span {(l : ℤ)}).primeCompl _ inferInstance
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := not_forall.1 fun h => hf0 (funext h)
  set Y : Set (GA L n) := {y | ∀ i j, ent y i j ∈ Sl L hl} with hYdef
  have hY1 : (1 : GA L n) ∈ Y := fun i j => ALint_le_Sl hl ((Umax L n).one_mem i j)
  have hYm : ∀ y ∈ Y, ∀ h, y * emb s n h ∈ Y := fun y hy h i j => by
    rw [ent_mul]
    exact mat_mem hy (ent_mem_Sl s hl hsl (emb_triv s h)) i j
  set N : Submodule (Rl l) W := Submodule.span _ ((fun y => f (g0 * y)) '' Y) with hNdef
  obtain ⟨S, hS⟩ := exists_sum (W := W) (emb s n) (comm_KL s) (dosetInd_mem s d)
  refine isIntegral_of_smul_mem_submodule N (fun h => hg0 ?_) ?_ ν fun w hw => ?_
  · have : f (g0 * 1) ∈ N := Submodule.subset_span ⟨1, hY1, rfl⟩
    rwa [h, Submodule.mem_bot, mul_one] at this
  ·
    obtain ⟨N', hN'0, hN'⟩ := hf.1.2
    obtain ⟨T, hT, hrep⟩ := reps (L := L) (n := n) (Nat.pos_iff_ne_zero.1 hN'0)
    haveI : Finite T := hT
    obtain ⟨c, hc0, hc⟩ := exists_den_fin ((hT.image (·⁻¹)).insert g0)
    obtain ⟨-, ι0, hι0, hdec, b, P, hP⟩ := alg
    choose Nt hNt hNt' using fun t : T => apply_fg (R := Rl l) b P (M0_fg (L := L) l c) (f t)
    refine Submodule.FG.of_le (Submodule.fg_iSup _ hNt) (Submodule.span_le.2 ?_)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hrep (g0 * y)
    obtain ⟨γ₀, hγ₀⟩ := gq_ent hγ
    have hfe : f (g0 * y) = ρ ⟨γ, hγ⟩ (f t) := by rw [e, hN' κ hκ, hf.1.1 ⟨γ, hγ⟩ t]
    show f (g0 * y) ∈ _
    rw [hfe]
    refine Submodule.mem_iSup_of_mem (⟨t, ht⟩ : T) (hNt' _ (ρ ⟨γ, hγ⟩) (fun p => p.1 (γ₀ p.2.1 p.2.2)) (fun p => ?_)
      (hP ⟨γ, hγ⟩ γ₀ (by rw [show ((⟨γ, hγ⟩ : GQ L n) : GA L n) = γ from rfl, hγ₀]; rfl)))

    have hγe : γ = g0 * y * κ⁻¹ * t⁻¹ := by rw [← mul_inv_eq_iff_eq_mul.2 e.symm]; group
    have hκU : κ⁻¹ ∈ Umax L n := (Umax L n).inv_mem hκ.1
    have hg0c : ∀ i j, (c : AL L) * ent g0 i j ∈ ALint L := hc g0 (Set.mem_insert _ _)
    have htc : ∀ i j, (c : AL L) * ent t⁻¹ i j ∈ ALint L := hc t⁻¹ (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩)
    have hmat : ((c : AL L) ^ 2) • ent γ = ((c : AL L) • ent g0) * ent y * ent κ⁻¹ * ((c : AL L) • ent t⁻¹) := by
      rw [hγe, ent_mul, ent_mul, ent_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        pow_two]
    have hS' : ((c : AL L) ^ 2) * ent γ p.2.1 p.2.2 ∈ Sl L hl := by
      have := congrArg (fun M : Matrix (Fin n) (Fin n) (AL L) => M p.2.1 p.2.2) hmat
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      rw [this]
      exact mat_mem (mat_mem (mat_mem (fun i j => ALint_le_Sl hl (by simpa using hg0c i j)) hy)
        (fun i j => ALint_le_Sl hl (hκU i j))) (fun i j => ALint_le_Sl hl (by simpa using htc i j)) _ _
    obtain ⟨m, hm, hmm⟩ := hS'
    refine key_M0 hc0 _ ⟨m, hm, ?_⟩ p.1
    have he : ent γ p.2.1 p.2.2 = γ₀ p.2.1 p.2.2 ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := by
      show ((γ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) p.2.1 p.2.2 = _
      rw [hγ₀]
      rfl
    rw [← he]
    convert hmm using 1
    push_cast
    ring
  ·
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [show ν • f (g0 * y) = (ν • f) (g0 * y) from rfl, ← hν, hS]
      refine Submodule.sum_mem _ fun c _ => ?_
      have hmem : f (g0 * y * emb s n c.out) ∈ N :=
        Submodule.subset_span ⟨y * emb s n c.out, hYm y hy _, by rw [mul_assoc]⟩
      unfold dosetInd
      by_cases h : c.out ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n)
      · rw [Set.indicator_of_mem h, Pi.one_apply, one_smul]
        exact hmem
      · rw [Set.indicator_of_notMem h, zero_smul]
        exact N.zero_mem
    | zero => rw [smul_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
    | smul r x _ hx =>
      have : ν • r • x = r • ν • x := by
        show ν • (algebraMap (Rl l) ℂ r • x) = algebraMap (Rl l) ℂ r • (ν • x)
        rw [smul_smul, smul_smul, mul_comm]
      rw [this]
      exact N.smul_mem r hx

end Eig

end CompanionTheory.L3H

namespace ReciprocityTheory.ChartRestriction.L3H

open CompanionTheory.L3H

theorem heckeStd : HeckeStdStatement := by
  intro L _ _ _ n W _ _ ρ alg J χ B hN hB s ϖ k hs hu hk1 hk2
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hu
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hex : ∃ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1 : ℤ) := ⟨ϖ, hϖ⟩
  set d := dg n s h0 k
  have hT : ∀ {f : Formalism.AUTREP.GAf L n → W}, f ∈ NG.TypeSp ρ J χ →
      tN J s ϖ k f = ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f := fun {f} hf => by
    show ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • NG.heckeD J (Formalism.AUTREP.tSet L n s ϖ k) f = _
    rw [heckeD_eq hB hs (inv_of_mem hB hs hf) d (tSet_iff s h0 k)]
  have hmem : ∀ {f : Formalism.AUTREP.GAf L n → W}, f ∈ NG.TypeSp ρ J χ → tN J s ϖ k f ∈ NG.TypeSp ρ J χ := fun hf => by
    rw [hT hf]
    exact Submodule.smul_mem _ _ (op_mem hB hs hex hN hf d)
  obtain ⟨S, hS⟩ := CompanionTheory.HeckeA.exists_sum (W := W) (emb s n) (comm_KL s) (dosetInd_mem s d)
  refine ⟨fun f hf => hmem hf, fun f hf f' hf' c => ?_, fun s' ϖ' k' hs' hu' hk1' hk2' f hf => ?_, fun f hf hf0 μ hμ l hl hsl => ?_⟩
  · rw [hT (Submodule.add_mem _ (Submodule.smul_mem _ c hf) hf'), hT hf, hT hf']
    funext g
    simp only [hS, Pi.add_apply, Pi.smul_apply, Finset.smul_sum, Finset.sum_add_distrib, smul_add, smul_comm c]
  · have hϖ' : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hu'
    have h0' : ϖ' ≠ 0 := fun e => by simp [e] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
    have hex' : ∃ ϖ : s'.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1 : ℤ) := ⟨ϖ', hϖ'⟩
    set d' := dg n s' h0' k'
    have hT' : ∀ {f : Formalism.AUTREP.GAf L n → W}, f ∈ NG.TypeSp ρ J χ →
        tN J s' ϖ' k' f = ((s'.q : ℂ) ^ (k' * (n - 1)))⁻¹ • op (emb s' n) (KL s' n) (dosetInd ℂ (KL s' n) d') f :=
      fun {f} hf => by
        show ((s'.q : ℂ) ^ (k' * (n - 1)))⁻¹ • NG.heckeD J (Formalism.AUTREP.tSet L n s' ϖ' k') f = _
        rw [heckeD_eq hB hs' (inv_of_mem hB hs' hf) d' (tSet_iff s' h0' k')]
    have hmem' : ∀ {f : Formalism.AUTREP.GAf L n → W}, f ∈ NG.TypeSp ρ J χ → tN J s' ϖ' k' f ∈ NG.TypeSp ρ J χ := fun hf => by
      rw [hT' hf]
      exact Submodule.smul_mem _ _ (op_mem hB hs' hex' hN hf d')
    obtain ⟨S', hS'⟩ := CompanionTheory.HeckeA.exists_sum (W := W) (emb s' n) (comm_KL s') (dosetInd_mem s' d')
    have sm : ∀ (c : ℂ) (f : Formalism.AUTREP.GAf L n → W),
        op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) (c • f) = c • op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f :=
      fun c f => funext fun g => by simp only [hS, Pi.smul_apply, Finset.smul_sum, smul_comm c]
    have sm' : ∀ (c : ℂ) (f : Formalism.AUTREP.GAf L n → W),
        op (emb s' n) (KL s' n) (dosetInd ℂ (KL s' n) d') (c • f) = c • op (emb s' n) (KL s' n) (dosetInd ℂ (KL s' n) d') f :=
      fun c f => funext fun g => by simp only [hS', Pi.smul_apply, Finset.smul_sum, smul_comm c]
    rw [hT (hmem' hf), hT' hf, hT' (hmem hf), hT hf, sm, sm', smul_comm ((s.q : ℂ) ^ (k * (n - 1)))⁻¹]
    congr 1
    congr 1
    by_cases hv : s'.v = s.v
    · obtain ⟨d'', hd''⟩ := tSet_same s s' hv h0' k'
      have e' : ∀ {f : Formalism.AUTREP.GAf L n → W}, CompanionTheory.HeckeA.Inv (emb s' n) (KL s' n) f →
          CompanionTheory.HeckeA.Inv (emb s n) (KL s n) f →
          op (emb s' n) (KL s' n) (dosetInd ℂ (KL s' n) d') f = op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d'') f :=
        fun {f} h1 h2 => by rw [← heckeD_eq hB hs' h1 d' (tSet_iff s' h0' k'), heckeD_eq hB hs h2 d'' hd'']
      have hc := Formalism.UG.Final.HeckeCommGL (maximalRealSubfield L) s.v n ℂ _ (dosetInd_mem s d) _ (dosetInd_mem s d'')
      have hop : op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f ∈ NG.TypeSp ρ J χ := op_mem hB hs hex hN hf d
      rw [e' (inv_of_mem hB hs' hf) (inv_of_mem hB hs hf), e' (inv_of_mem hB hs' hop) (inv_of_mem hB hs hop)]
      exact CompanionTheory.HeckeA.op_comm_same (emb s n) (comm_KL s) (dosetInd_mem s d) (dosetInd_mem s d'') hc
        (inv_of_mem hB hs hf)
    · funext g
      simp only [hS, hS', Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      rw [mul_comm, mul_assoc, mul_assoc, commute_of_ne hv (emb_triv s' _) (emb_triv s _)]
  ·
    haveI : Fact l.Prime := ⟨hl⟩
    obtain ⟨p, hp, hA, fq, hfq⟩ := exists_prime s
    have hlp : ¬ l ∣ s.q ^ (k * (n - 1)) := fun h => hsl (by
      rw [hfq, ← pow_mul] at h
      exact ((Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow h)) ▸ hA)
    have hq0 : ((s.q : ℂ) ^ (k * (n - 1))) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by rw [hfq]; exact pow_ne_zero _ hp.ne_zero))
    have hop : op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f = ((s.q : ℂ) ^ (k * (n - 1)) * μ) • f := by
      rw [← smul_smul, ← hμ, hT hf, smul_smul, mul_inv_cancel₀ hq0, one_smul]
    have hν := eig_int alg hB hs hsl d hf hf0 _ hop
    obtain ⟨r, hr⟩ := inv_mem_Rl (l := l) (m := s.q ^ (k * (n - 1))) hlp
    have hμR : IsIntegral (Rl l) μ := by
      have := (isIntegral_algebraMap (x := r)).mul hν
      rwa [hr, Nat.cast_pow, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul] at this
    haveI : IsScalarTower ℤ (Rl l) ℂ := IsScalarTower.of_algebraMap_eq fun _ => by simp
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Ideal.span {(l : ℤ)}).primeCompl μ hμR
    have hm' : ¬ l ∣ m.natAbs := fun h => hm (Ideal.mem_span_singleton.2 (Int.natCast_dvd.2 h))
    refine ⟨m.natAbs, hm', ?_⟩
    have e1 : (m • μ : ℂ) = (m : ℂ) * μ := zsmul_eq_mul μ m
    rw [Submonoid.mk_smul, e1] at hmi
    rcases Int.natAbs_eq m with h | h
    · rwa [h, Int.cast_natCast] at hmi
    · have := hmi.neg
      rwa [h, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this

end ReciprocityTheory.ChartRestriction.L3H
