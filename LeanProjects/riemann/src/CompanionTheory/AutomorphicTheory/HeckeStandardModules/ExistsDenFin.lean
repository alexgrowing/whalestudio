import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2

noncomputable section

namespace CompanionTheory.Split

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem ALint_eq : ALint L = tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺) := by
  rw [ALint, tensInt]
  congr 2 <;> ext x
  · exact ⟨fun ⟨y, h⟩ => ⟨⟨y, y, rfl⟩, h.symm⟩, fun ⟨⟨_, y, rfl⟩, h⟩ => ⟨y, h.symm⟩⟩
  · exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h.symm⟩, fun ⟨⟨a, ha⟩, h⟩ => ⟨a, ha, h.symm⟩⟩

theorem levelafC_nat (N : ℕ) : P.levelafC L (N : 𝓞 L⁺) = (N : AL L) := by
  rw [P.levelafC, map_natCast]
  exact map_natCast (Algebra.TensorProduct.includeRight (R := L⁺) (A := L) (B := AFplus L)) N

theorem exists_den (z : AL L) : ∃ c : ℕ, c ≠ 0 ∧ (c : AL L) * z ∈ ALint L := by
  obtain ⟨d, hd, h⟩ := P.levelaf_denom (F := L⁺) z
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), by simpa using hd, ?_⟩
  rw [← levelafC_nat, ← he, P.levelafC_mul, mul_assoc, ALint_eq]
  exact Subring.mul_mem _ (P.levelafC_mem e) h

theorem exists_den_fin {T : Set (GA L n)} (hT : T.Finite) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ t ∈ T, ∀ i j, (c : AL L) * ent t i j ∈ ALint L := by
  have := hT.fintype
  choose c h0 h using fun p : T × Fin n × Fin n => exists_den (ent p.1.1 p.2.1 p.2.2)
  refine ⟨∏ p, c p, Finset.prod_ne_zero_iff.2 fun p _ => h0 p, fun t ht i j => ?_⟩
  obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem c (Finset.mem_univ (⟨t, ht⟩, i, j))
  rw [he, mul_comm _ e, Nat.cast_mul, mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ e) (h (⟨t, ht⟩, i, j))

theorem mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) A) :
    g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ↔ g ∈ UGroup n σ hσ := by
  show cT σ (g : Matrix (Fin n) (Fin n) A) * 1 * g = 1 ↔ (g : Matrix (Fin n) (Fin n) A) * conjT σ g = 1
  rw [Matrix.mul_one]
  exact mul_eq_one_comm

theorem reps_Umax : ∃ T : Set (GA L n), T.Finite ∧ ∀ g, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ Umax L n, g = γ * t * κ := by
  let σ : L →ₐ[L⁺] L := (IsCMField.complexConj L).toAlgHom
  have hσ : ∀ τ : L →+* ℂ, τ.comp (σ : L →+* L) = (starRingEnd ℂ).comp τ := fun τ =>
    RingHom.ext fun x => IsCMField.complexEmbedding_complexConj L τ x
  obtain ⟨h1, h2, -⟩ := Final.StdFormDef L⁺ L (Fin n) σ hσ
    (fun e he => ⟨⟨e, (IsCMField.complexConj_eq_self_iff L e).1 he⟩, rfl⟩) inferInstance
  have hfin := Final.ClassSetFinite L⁺ L (Fin n) σ 1 hσ h1 (by simp) h2
  have hU : ∀ g, g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L) ↔ g ∈ GA L n := fun g => by
    rw [UPts, Matrix.map_one _ (map_zero _) (map_one _)]
    exact mem_UJ_one _ (conjAL_conjAL L) g
  let e : UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L) → GA L n := fun x => ⟨x, (hU x).1 x.2⟩
  refine ⟨Set.range fun q : ClassSet _ _ => e q.out, @Set.finite_range _ _ _ hfin, fun g => ?_⟩
  set q := DoubleCoset.mk ((ratPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)).subgroupOf _)
    ((levelAf σ 1).subgroupOf _) (⟨g, (hU g).2 g.2⟩ : UPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)) with hq
  obtain ⟨γ, κ, hγ, hκ, h⟩ := DoubleCoset.mk_out_eq_mul
    ((ratPts σ (1 : Matrix (Fin n) (Fin n) L) (AFplus L)).subgroupOf _) ((levelAf σ 1).subgroupOf _) ⟨g, (hU g).2 g.2⟩
  refine ⟨(e γ)⁻¹, (GQ L n).inv_mem ?_, e q.out, ⟨q, rfl⟩, (e κ)⁻¹, (Umax L n).inv_mem (show e κ ∈ Umax L n from fun i j => ?_), ?_⟩
  · obtain ⟨γ₀, h0, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    exact Subgroup.mem_subgroupOf.2 ⟨γ₀, (mem_UJ_one _ (complexConj_invol L) γ₀).1 h0, e0⟩
  · have := (Subgroup.mem_subgroupOf.1 hκ).2
    rw [Final.StabStd _ _ _ Subtype.val_injective] at this
    obtain ⟨a, ha⟩ := this
    rw [ALint_eq]
    have e1 := congrArg (fun M : GL (Fin n) (AL L) => (M : Matrix (Fin n) (Fin n) (AL L)) i j) ha
    refine (show ((κ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺) from ?_)
    rw [← e1]
    exact ((a : Matrix (Fin n) (Fin n) (tensInt (F := L⁺) (AFplus L) (intOE L) (intAd L⁺))) i j).2
  · have h' : (q.out : GL (Fin n) (AL L)) = γ * g * κ := congrArg Subtype.val h
    refine Subtype.ext ?_
    show (g : GL (Fin n) (AL L)) = ((γ : GL (Fin n) (AL L)))⁻¹ * q.out * ((κ : GL (Fin n) (AL L)))⁻¹
    rw [h']
    group

theorem reps_Cong {N : ℕ} (hN : N ≠ 0) :
    ∃ T : Set (GA L n), T.Finite ∧ ∀ u ∈ Umax L n, ∃ t ∈ T, NG.Cong L n N (t⁻¹ * u) := by
  have hfin : Finite (ALint L ⧸ Ideal.span {(N : ALint L)}) := by
    have := P.levelaf_finite_quot (F := L⁺) (E := L) (N : 𝓞 L⁺) (Nat.cast_ne_zero.2 hN) N
      (by rw [levelafC_nat]; rfl)
    rwa [← ALint_eq] at this
  let red : Umax L n → Fin n → Fin n → ALint L ⧸ Ideal.span {(N : ALint L)} := fun u i j =>
    Ideal.Quotient.mk _ ⟨_, u.2 i j⟩
  refine ⟨Set.range fun m => (Function.invFun red m : Umax L n), Set.finite_range _, fun u hu => ?_⟩
  set t := Function.invFun red (red ⟨u, hu⟩) with ht
  have e : red t = red ⟨u, hu⟩ := Function.invFun_eq ⟨_, rfl⟩
  refine ⟨t, ⟨_, rfl⟩, (Umax L n).mul_mem ((Umax L n).inv_mem t.2) hu, fun i j => ?_⟩
  choose y hy using fun a b => Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun e.symm a) b))
  refine ⟨∑ a, ent (t : GA L n)⁻¹ i a * y a j,
    Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((Umax L n).inv_mem t.2 i a) (y a j).2, ?_⟩
  have h1 : ent (t : GA L n)⁻¹ * ent (t : GA L n) = 1 := congrArg ent (inv_mul_cancel (t : GA L n))
  show (ent (t : GA L n)⁻¹ * ent u) i j - _ = _
  rw [← h1, ← Matrix.sub_apply, ← Matrix.mul_sub, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (y a j : AL L) * N = ent u a j - ent (t : GA L n) a j := congrArg Subtype.val (hy a j)
  rw [Matrix.sub_apply, ← this]
  ring

theorem reps {N : ℕ} (hN : N ≠ 0) :
    ∃ T : Set (GA L n), T.Finite ∧ ∀ g, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ, NG.Cong L n N κ ∧ g = γ * t * κ := by
  obtain ⟨T, hT, h⟩ := reps_Umax (L := L) (n := n)
  obtain ⟨T', hT', h'⟩ := reps_Cong (L := L) (n := n) hN
  refine ⟨Set.image2 (· * ·) T T', hT.image2 _ hT', fun g => ?_⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, rfl⟩ := h g
  obtain ⟨t', ht', hc⟩ := h' κ hκ
  exact ⟨γ, hγ, t * t', Set.mem_image2_of_mem ht ht', _, hc, by group⟩

variable (s : SplitPlace L)

theorem normaliser {ϖ : s.v.adicCompletion L⁺} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (t : GL (Fin n) (s.v.adicCompletion L⁺)) (ht : ∀ k ∈ KL s n, t * k * t⁻¹ ∈ KL s n) :
    ∃ u ∈ KL s n, ∀ h, t * h * t⁻¹ = u * h * u⁻¹ := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  obtain ⟨a, -, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp L⁺ s.v n ϖ
    (show Valued.v ϖ ≤ 1 by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) hϖ t
  obtain ⟨d, rfl⟩ : ∃ d, t = k₁ * d * k₂ := ⟨k₁⁻¹ * t * k₂⁻¹, by group⟩
  have hd : (d : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) = diagPow L⁺ s.v ϖ a := by
    rw [Units.val_mul, Units.val_mul] at e
    exact (Units.mul_right_inj k₁).1 ((Units.mul_left_inj k₂).1 e)
  have hle : ∀ i j, a j ≤ a i := fun i j => by
    rcases eq_or_ne i j with rfl | hij
    · exact le_rfl
    let E : GL (Fin n) (s.v.adicCompletion L⁺) := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]⟩
    have hE : ∀ c : s.v.adicCompletion L⁺, Valued.v c ≤ 1 → ∀ p q, Valued.v (Matrix.transvection i j c p q) ≤ 1 :=
      fun c hc p q => by
        rw [Matrix.transvection, Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.one_apply]; split_ifs <;> simp
        · rw [Matrix.single_apply]; split_ifs <;> simp [hc]
    have hEK : E ∈ KL s n := (mem_KL s).2 ⟨hE 1 (by simp), hE (-1) (by simp)⟩
    have hM : d * E * d⁻¹ ∈ KL s n := by
      have := (KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₁)
        (ht _ ((KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₂) hEK) h₂))) h₁
      rwa [show k₁⁻¹ * (k₁ * d * k₂ * (k₂⁻¹ * E * k₂) * (k₁ * d * k₂)⁻¹) * k₁ = d * E * d⁻¹ by group] at this
    have h3 := ((mem_KL s).1 hM).1 i j
    have h4' : ((d * E * d⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) *
        ((d : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) =
        ((d : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) *
          ((E : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺) => M i j) h4'
    simp only [hd, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul] at h4
    have h5 : ((E : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j = 1 := by
      simp [E, Matrix.transvection, hij]
    have h6 := mul_le_mul_left h3 (Valued.v (ϖ ^ a j))
    rw [← map_mul, h4, h5, mul_one, one_mul, map_zpow₀, map_zpow₀, hϖ, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      WithZero.exp_le_exp] at h6
    simpa using h6
  have hc : ∀ h, d * h = h * d := fun h => Units.ext (Matrix.ext fun i j => by
    rw [Units.val_mul, Units.val_mul, hd, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul,
      le_antisymm (hle j i) (hle i j), mul_comm])
  refine ⟨k₁ * k₂, (KL s n).mul_mem h₁ h₂, fun h => ?_⟩
  rw [show k₁ * d * k₂ * h * (k₁ * d * k₂)⁻¹ = k₁ * (d * (k₂ * h * k₂⁻¹)) * d⁻¹ * k₁⁻¹ by group, hc]
  group

theorem exists_prime : ∃ p : ℕ, p.Prime ∧ s.Above p ∧ ∃ f : ℕ, s.q = p ^ f := by
  have := s.v.isMaximal
  let _ : Field (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 L⁺ ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let _ : Fintype (𝓞 L⁺ ⧸ s.v.asIdeal) := Fintype.ofFinite _
  obtain ⟨p, hp, f, hpp, hf⟩ := FiniteField.card' (𝓞 L⁺ ⧸ s.v.asIdeal)
  refine ⟨p, hpp, Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_natCast, CharP.cast_eq_zero]), f, ?_⟩
  rw [SplitPlace.q, Nat.card_eq_fintype_card, hf]

theorem pow_mul_mem {p : ℕ} (hp : s.Above p) {z : AL L} (hz : ∀ w, w ≠ s.v → compAt L w z = 0) :
    ∃ a : ℕ, ((p ^ a : ℕ) : AL L) * z ∈ ALint L := by
  have hv : Valued.v (p : s.v.adicCompletion L⁺) < 1 := by
    have := (s.split_mem_ideal _).1 ((s.split_alg_mem p).2 hp)
    rwa [map_natCast, show (((p : 𝓞 L) : 𝓞 L) : L) = p from map_natCast (algebraMap (𝓞 L) L) p, map_natCast] at this
  have key : ∀ y : s.v.adicCompletion L⁺, ∃ a : ℕ, ∀ b, a ≤ b → Valued.v ((p : s.v.adicCompletion L⁺) ^ b * y) ≤ 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, fun _ _ => by simp⟩
    have hy' : Valued.v y ≠ 0 := (map_ne_zero _).2 hy
    obtain ⟨a, ha⟩ := exists_pow_lt₀ hv (Units.mk0 _ (inv_ne_zero hy'))
    refine ⟨a, fun b hb => ?_⟩
    rw [map_mul, map_pow, ← le_mul_inv_iff₀ (zero_lt_iff.2 hy'), one_mul]
    exact (pow_le_pow_right_of_le_one' hv.le hb).trans ha.le
  obtain ⟨a, ha⟩ := key (s.proj z)
  obtain ⟨b, hb⟩ := key (s.proj (conjAL L z))
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  refine ⟨a + b, GlobalTheory.mem_ALint_of_supported_at_split L s e he he' _ (fun w hw => by rw [map_mul, hz w hw, mul_zero]) ?_ ?_⟩
  · rw [map_mul, map_natCast, Nat.cast_pow]
    exact ha _ (Nat.le_add_right _ _)
  · rw [map_mul, map_mul, map_natCast, map_natCast, Nat.cast_pow]
    exact hb _ (Nat.le_add_left _ _)

def Sl (L : Type) [Field L] [NumberField L] [IsCMField L] {l : ℕ} (hl : l.Prime) : Subring (AL L) where
  carrier := {z | ∃ m : ℕ, ¬ l ∣ m ∧ (m : AL L) * z ∈ ALint L}
  mul_mem' := by
    rintro x y ⟨m, hm, h⟩ ⟨m', hm', h'⟩
    refine ⟨m * m', fun e => (hl.dvd_mul.1 e).elim hm hm', ?_⟩
    rw [Nat.cast_mul, mul_mul_mul_comm]
    exact Subring.mul_mem _ h h'
  add_mem' := by
    rintro x y ⟨m, hm, h⟩ ⟨m', hm', h'⟩
    refine ⟨m * m', fun e => (hl.dvd_mul.1 e).elim hm hm', ?_⟩
    rw [show ((m * m' : ℕ) : AL L) * (x + y) = m' * (m * x) + m * (m' * y) by push_cast; ring]
    exact Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ _) h) (Subring.mul_mem _ (natCast_mem _ _) h')
  one_mem' := ⟨1, hl.not_dvd_one, by simp⟩
  zero_mem' := ⟨1, hl.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [mul_neg]; exact Subring.neg_mem _ h⟩

theorem ALint_le_Sl {l : ℕ} (hl : l.Prime) : ALint L ≤ Sl L hl := fun z hz => ⟨1, hl.not_dvd_one, by simpa using hz⟩

theorem ent_mem_Sl {l : ℕ} (hl : l.Prime) (hs : ¬ s.Above l) {x : GA L n} (hx : TrivOutside {s.v} x) (i j : Fin n) :
    ent x i j ∈ Sl L hl := by
  obtain ⟨p, hp, hA, -⟩ := exists_prime s
  obtain ⟨a, ha⟩ := pow_mul_mem s hA fun w => sub_one_supp hx i j
  have h1 : ent x i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ Sl L hl :=
    ⟨p ^ a, fun e => hs (((Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow e)).symm ▸ hA), ha⟩
  have := add_mem h1 (ALint_le_Sl hl ((Umax L n).one_mem i j))
  rwa [show ((1 : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) = 1 from rfl, sub_add_cancel] at this

end CompanionTheory.Split
