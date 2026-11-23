import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.MatchA
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GaussBinomialTwistedSumIdentityStatement

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem card_res : Nat.card (IsLocalRing.ResidueField 𝒪) = qV K v :=
  GlobalTheory.SplitUnif.card_residueField v (algebraMap K (Cv v)) v (fun _ => rfl) fun x => by
    rw [← v.valuation_lt_one_iff_mem (K := K)]
    exact (congrArg (· < 1) (v.valuedAdicCompletion_eq_valuation' (x : K))).to_iff.symm

theorem cst (q j m : ℕ) : (((((q : ℝ)⁻¹ ^ j) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) =
    ((Real.sqrt q : ℂ) ^ m)⁻¹ ^ j := by
  have h : (((q : ℝ)⁻¹ ^ j) ^ ((m : ℝ) / 2) : ℝ) = (Real.sqrt q ^ m)⁻¹ ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity),
      Real.rpow_natCast, Real.inv_rpow (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast ((q : ℝ) ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul (by positivity)]
    congr 3
    ring
  rw [h]; push_cast; rfl

section Count

variable {l m j : ℕ} {α : GL (Fin m) (Cv v)} {ι : Type} {R : Finset ι}
  {ρ : ι → GL (Fin m) (Cv v)}

theorem cnt_zero {p : 𝒪} (hα : Hk 𝒪 p j α) (hR : Reps 𝒪 α R ρ) {y : Matrix (Fin l) (Fin m) (Cv v)}
    (hy : ¬ IntM 𝒪 (algebraMap 𝒪 (Cv v) p • y)) :
    Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * (ρ γ).1)} = 0 := by
  refine Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨γ, hγ, h⟩ => hy ?_⟩)
  obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 γ hγ
  have hk : Hk 𝒪 p j (ρ γ) := h4 ▸ hα.mul g₁ g₂
  have := h.mul hk.2.1
  rwa [Matrix.mul_smul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at this

theorem cnt_eq {p : 𝒪} (hp : Irreducible p) (hj : j ≤ m) (hα : Hk 𝒪 p j α) (hR : Reps 𝒪 α R ρ)
    {y : Matrix (Fin l) (Fin m) (Cv v)} {w : Matrix (Fin l) (Fin m) (IsLocalRing.ResidueField 𝒪)}
    (hy : IntM 𝒪 (y - yw (Cv v) p w)) :
    Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * (ρ γ).1)} = nKer j w := by
  rw [← GlobalTheory.SplitHecke.card_heckeCosetReps_integral_right_inversePrime hp hj hα hR w]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun hγ => ?_)
  obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 γ hγ
  have hk : Hk 𝒪 p j (ρ γ) := h4 ▸ hα.mul g₁ g₂
  have h1 := hy.mul hk.1
  rw [Matrix.sub_mul] at h1
  exact ⟨fun h => by simpa using h.sub h1, fun h => by simpa using h1.add h⟩

end Count

theorem heckeVec_sum_left {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    (hJ : IsCommensurated J) (ρ : Representation ℂ G V) (s : Finset ι) (a : ι → ℂ)
    (f : ι → G → ℂ) (hf : ∀ i, f i ∈ Hecke ℂ J) (x : V) :
    heckeVec ρ J (∑ i ∈ s, a i • f i) x = ∑ i ∈ s, a i • heckeVec ρ J (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heckeVec]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, heckeVec_add_left hJ
      (Submodule.smul_mem _ _ (hf i))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)), heckeVec_smul_left hJ (hf i), ih]

def Acts {m : ℕ} (f : GL (Fin m) (Cv v) → ℂ) (B : Multiset ℂˣ) (lam : ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V),
    IsSatVecGL v ρ x B → heckeVec ρ (KGL v m) f x = lam • x

def Mt (c t : ℕ) (f' : GL (Fin (c + t)) (Cv v) → ℂ) (f : GL (Fin c) (Cv v) → ℂ) : Prop :=
  f' ∈ Hecke ℂ (KGL v (c + t)) ∧ f ∈ Hecke ℂ (KGL v c) ∧
    heckeVec (rT v (c + t) c) (KGL v (c + t)) f' (phi0 v (c + t) c) =
      heckeVec (rS v (c + t) c) (KGL v c) f (phi0 v (c + t) c) ∧
    ∀ B : Multiset ℂˣ, B.card = c → ∃ lam, Acts f B lam ∧ Acts f' (B + seg v 1 t) lam

variable (v) in

def mtSub (c t : ℕ) : Submodule ℂ (GL (Fin (c + t)) (Cv v) → ℂ) where
  carrier := {f' | ∃ f, Mt c t f' f}
  zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp [heckeVec], fun B _ =>
    ⟨0, fun V _ _ ρ x _ => by simp [heckeVec], fun V _ _ ρ x _ => by simp [heckeVec]⟩⟩
  add_mem' := by
    rintro f' g' ⟨f, a1, a2, a3, a4⟩ ⟨g, b1, b2, b3, b4⟩
    have hK := Final.GLintComm K v c
    have hK' := Final.GLintComm K v (c + t)
    refine ⟨f + g, add_mem a1 b1, add_mem a2 b2, by
      rw [heckeVec_add_left hK' a1 b1, heckeVec_add_left hK a2 b2, a3, b3], fun B hB => ?_⟩
    obtain ⟨l, l1, l2⟩ := a4 B hB
    obtain ⟨l', m1, m2⟩ := b4 B hB
    exact ⟨l + l', fun V _ _ ρ x hx => by
      rw [heckeVec_add_left hK a2 b2, l1 V ρ x hx, m1 V ρ x hx, add_smul], fun V _ _ ρ x hx => by
      rw [heckeVec_add_left hK' a1 b1, l2 V ρ x hx, m2 V ρ x hx, add_smul]⟩
  smul_mem' := by
    rintro z f' ⟨f, a1, a2, a3, a4⟩
    have hK := Final.GLintComm K v c
    have hK' := Final.GLintComm K v (c + t)
    refine ⟨z • f, Submodule.smul_mem _ z a1, Submodule.smul_mem _ z a2, by
      rw [heckeVec_smul_left hK' a1, heckeVec_smul_left hK a2, a3], fun B hB => ?_⟩
    obtain ⟨l, l1, l2⟩ := a4 B hB
    exact ⟨z * l, fun V _ _ ρ x hx => by rw [heckeVec_smul_left hK a2, l1 V ρ x hx, mul_smul],
      fun V _ _ ρ x hx => by rw [heckeVec_smul_left hK' a1, l2 V ρ x hx, mul_smul]⟩

theorem conv_mem_mtSub {c t : ℕ} : ∀ f' ∈ mtSub v c t, ∀ g' ∈ mtSub v c t,
    conv (KGL v (c + t)) f' g' ∈ mtSub v c t := by
  rintro f' ⟨f, a1, a2, a3, a4⟩ g' ⟨g, b1, b2, b3, b4⟩
  have hK : IsCommensurated (KGL v c) := Final.GLintComm K v c
  have hK' : IsCommensurated (KGL v (c + t)) := Final.GLintComm K v (c + t)
  refine ⟨conv (KGL v c) g f, Final.HeckeConvMem _ _ ℂ hK' _ a1 _ b1,
    Final.HeckeConvMem _ _ ℂ hK _ b2 _ a2, ?_, fun B hB => ?_⟩
  · rw [heckeVec_conv hK' a1 b1 (sphericalVector_fixed_left _ _), heckeVec_conv hK b2 a2 (sphericalVector_fixed_right _ _), b3,
      ← a3]
    have e1 : ∀ Ψ, heckeVec (rS v (c + t) c) (KGL v c) g
        (heckeVec (rT v (c + t) c) (KGL v (c + t)) f' Ψ) =
        heckeVec (rT v (c + t) c) (KGL v (c + t)) f' (heckeVec (rS v (c + t) c) (KGL v c) g Ψ) :=
      fun Ψ => map_heckeVec hK' a1 (heckeLin hK b2 (rS v (c + t) c))
        (fun z y => (map_heckeVec hK b2 (rT v (c + t) c z)
          (fun g y => (rS_rT g z y).symm) y).symm) Ψ
    rw [e1]
  · obtain ⟨l, l1, l2⟩ := a4 B hB
    obtain ⟨l', m1, m2⟩ := b4 B hB
    exact ⟨l * l', fun V _ _ ρ x hx => by
      rw [heckeVec_conv hK b2 a2 hx.2.1, l1 V ρ x hx, heckeVec_smul hK b2, m1 V ρ x hx, mul_smul],
      fun V _ _ ρ x hx => by
      rw [heckeVec_conv hK' a1 b1 hx.2.1, m2 V ρ x hx, heckeVec_smul hK' a1, l2 V ρ x hx,
        mul_comm, mul_smul]⟩

set_option maxHeartbeats 1000000 in
theorem Tj_mem_mtSub {c t : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (d : ℕ) (hd : d ≤ c + t) :
    Tj ℂ (c + t) (Ov K v) ϖ d ∈ mtSub v c t := by
  classical
  have hK : IsCommensurated (KGL v c) := Final.GLintComm K v c
  obtain ⟨p, rfl⟩ : ∃ p : 𝒪, (p : Cv v) = ϖ := ⟨⟨ϖ, mem_Ov_of_isUnifV hu⟩, rfl⟩
  have h0 := ne_zero_of_isUnifV hu
  have hp : Irreducible p := GlobalTheory.SplitUnif.irreducible_of_valued v p hu
  set q := qV K v with hq
  let a : ℕ → ℂ := fun j => (q : ℂ) ^ ((c - j) * (d - j)) * (Formalism.L2.Col.gaussBin q t (d - j) : ℂ) *
    ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d * ((Real.sqrt q : ℂ) ^ (c + t)) ^ j
  have hjc : ∀ j ∈ Finset.range (min d c + 1), j ≤ c := fun j hj => by
    have := Finset.mem_range.1 hj; omega
  refine ⟨∑ j ∈ Finset.range (min d c + 1), a j • Tj ℂ c (Ov K v) p j, Tj_mem_hecke hu d,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Tj_mem_hecke hu j), ?_,
    fun B hB => ⟨satEig q (c + t) (B + seg v 1 t) d, fun V _ _ ρ x hx => ?_,
      fun V _ _ ρ x hx => hx.2.2.2 _ hu d hd⟩⟩
  · rw [heckeVec_sum_left hK _ _ _ _ (Tj_mem_hecke hu)]
    funext y
    obtain ⟨RT, hRT, eT⟩ := Tj_count (X := Matrix (Fin (c + t)) (Fin c) (Cv v)) hd hu h0
    rw [eT _ _ _ y (fun z => IntM 𝒪 (yᵀ * z.1)) (fun z => by
      rw [rT_apply, characteristic_function_integral_apply, intM_tr_iff]), cst, Finset.sum_apply]
    have eS : ∀ j ∈ Finset.range (min d c + 1), ∀ N : ℕ,
        (∀ R : Finset (GL (Fin c) (Cv v) ⧸ KGL v c),
          Reps 𝒪 (tor h0 fun i : Fin c => if (i : ℕ) < j then 1 else 0) R Quotient.out →
          Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * γ.out.1)} = N) →
        (a j • heckeVec (rS v (c + t) c) (KGL v c) (Tj ℂ c (Ov K v) p j) (phi0 v (c + t) c)) y =
          ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d *
            ((q ^ ((c - j) * (d - j)) * Formalism.L2.Col.gaussBin q t (d - j) * N : ℕ) : ℂ) := by
      intro j hj N hN
      obtain ⟨R, hR, e⟩ := Tj_count (X := Matrix (Fin (c + t)) (Fin c) (Cv v)) (hjc j hj) hu h0
      have hs : ((Real.sqrt q : ℂ) ^ (c + t)) ≠ 0 := pow_ne_zero _ (by
        have : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (qV_ne_zero v)
        exact_mod_cast (Real.sqrt_pos.2 this).ne')
      rw [Pi.smul_apply, e _ _ _ y (fun g => IntM 𝒪 (y * g.1)) (fun g => by
        rw [rS_apply, characteristic_function_integral_apply]), cst, hN R hR, smul_eq_mul]
      rw [← hq]
      simp only [a]
      generalize (Real.sqrt q : ℂ) ^ (c + t) = u at hs ⊢
      generalize ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d = u'
      push_cast
      rw [inv_pow]
      field_simp
    by_cases hy : IntM 𝒪 (algebraMap 𝒪 (Cv v) p • y)
    · obtain ⟨w, hw, -⟩ := GlobalTheory.SplitHecke.existsUnique_yw hp hy
      haveI : Finite (IsLocalRing.ResidueField 𝒪) :=
        Nat.finite_of_card_ne_zero (card_res (v := v) ▸ qV_ne_zero v)
      rw [cnt_eq hp hd (hk_tor h0 hd) hRT (y := yᵀ) (w := wᵀ) hw.transpose,
        Finset.sum_congr rfl fun j hj => eS j hj (nKer j w) fun R hR =>
          cnt_eq hp (hjc j hj) (hk_tor h0 (hjc j hj)) hR hw,
        ← Finset.mul_sum, GlobalTheory.SplitHecke.nKer_eq_sum (t := t) rfl, card_res, Nat.cast_sum]
      rfl
    · rw [cnt_zero (hk_tor h0 hd) hRT (y := yᵀ) fun h => hy h.transpose,
        Finset.sum_congr rfl fun j hj => eS j hj 0 fun R hR =>
          cnt_zero (hk_tor h0 (hjc j hj)) hR hy]
      simp
  · have e := GlobalTheory.T.gaussBinomial_twisted_sum_identity v c t d B 1 1 hB hd
    simp only [Units.val_one, one_mul, inv_one, mul_one, Multiset.map_id'] at e
    rw [heckeVec_sum_left hK _ _ _ _ (Tj_mem_hecke hu),
      Finset.sum_congr rfl fun j hj => by rw [hx.2.2.2 _ hu j (hjc j hj), smul_smul],
      ← Finset.sum_smul]
    exact congrArg (· • x) e

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
