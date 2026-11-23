import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.NonemptyCoefficientFieldPrime

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.MainNotions.ModuliIntegralCharts NumberField

theorem nonempty_local_provision_degenerate (D : D7) : Nonempty (ModuliIntegralCharts.Prov D) := by
  exact ⟨{
    Dat := Empty
    rk := fun w => w.elim
    jj := fun w => w.elim
    jj_range := fun w => w.elim
    loc := fun w => w.elim
    ex := fun w => w.elim
    NgC := fun _ => Unit
    NgC_ne := fun _ => ⟨()⟩
    KF := fun _ _ => Unit
    kfNorm := fun _ _ => 1
    pbKF := fun w => w.elim
    levIn := fun _ _ => True
    Xg := fun _ => Unit
    bc := fun {w} => w.elim
    DivX := fun _ => Unit
    effD := fun _ => True
    noVertD := fun _ => True
    posBdD := fun _ => True
    ampleOnAbelianBase := fun _ _ _ => True
    Met := fun _ => Unit
    nefFib := fun _ => True
    ampleGen := fun _ => True
    limRA := fun _ => True }⟩

namespace LocalProvisionModel

section Form

variable (D : D7)

def cjO : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem cjO_coe (c : 𝓞 D.host.E) : ((cjO D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

theorem emb_conj (σ : D.host.E →ₐ[ℚ] ℂ) (x : D.host.E) : σ (D.host.conj x) = starRingEnd ℂ (σ x) := by
  exact (D.host.der.conj_iff (σ : D.host.E →+* ℂ) D.host.conj).mpr
    (D.host.gal.apply_symm_apply _) x

theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h : ∀ y, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    (D.host.der.conj_iff D.host.φ₀ D.host.conj).mpr (D.host.gal.apply_symm_apply _)
  apply D.host.φ₀.injective
  rw [h, h, Complex.conj_conj]

def beO : 𝓞 D.host.E →ₗ[ℤ] 𝓞 D.host.E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun a b => ((Algebra.trace ℤ (𝓞 D.host.E) (a * cjO D b) : ℤ) : ℝ))
    (by intro a a' b; rw [add_mul, map_add, Int.cast_add])
    (by intro c a b; rw [smul_mul_assoc, map_smul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])
    (by intro a b b'; rw [map_add, mul_add, map_add, Int.cast_add])
    (by intro c a b; rw [map_zsmul, mul_smul_comm, map_smul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])

theorem beO_apply (a b : 𝓞 D.host.E) :
    beO D a b = ((Algebra.trace ℤ (𝓞 D.host.E) (a * cjO D b) : ℤ) : ℝ) := rfl

theorem trC (x : 𝓞 D.host.E) :
    ((Algebra.trace ℤ (𝓞 D.host.E) x : ℤ) : ℂ) = ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ (x : D.host.E) := by
  have h1 := Algebra.coe_trace_int x
  have h2 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := D.host.E) (x := (x : D.host.E))
  rw [← h2, ← h1]
  simp

theorem beO_eq (a b : 𝓞 D.host.E) : ((beO D a b : ℝ) : ℂ) =
    ∑ σ : D.host.E →ₐ[ℚ] ℂ, σ (a : D.host.E) * starRingEnd ℂ (σ (b : D.host.E)) := by
  rw [beO_apply, Complex.ofReal_intCast, trC]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : ((a * cjO D b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * D.host.conj (b : D.host.E) := by
    rw [← cjO_coe]; norm_cast
  rw [e, map_mul, emb_conj]

theorem beO_symm (a b : 𝓞 D.host.E) : beO D a b = beO D b a := by
  apply Complex.ofReal_injective
  rw [← Complex.conj_ofReal (beO D a b : ℝ), beO_eq, beO_eq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem beO_bal (c c' : 𝓞 D.host.E) (h : (c' : D.host.E) = D.host.conj (c : D.host.E)) (a b : 𝓞 D.host.E) :
    beO D (c • a) b = beO D a (c' • b) := by
  apply Complex.ofReal_injective
  rw [beO_eq, beO_eq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : σ (c' : D.host.E) = starRingEnd ℂ (σ (c : D.host.E)) := by rw [h, emb_conj]
  have e1 : ((c • a : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * a := by
    rw [smul_eq_mul]; norm_cast
  have e2 : ((c' • b : 𝓞 D.host.E) : D.host.E) = (c' : D.host.E) * b := by
    rw [smul_eq_mul]; norm_cast
  rw [e1, e2, map_mul, map_mul, map_mul, hc, Complex.conj_conj]
  ring

theorem beO_self (a : 𝓞 D.host.E) : beO D a a = ∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (σ (a : D.host.E)) := by
  apply Complex.ofReal_injective
  rw [beO_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Complex.mul_conj]

theorem beO_nonneg (a : 𝓞 D.host.E) : 0 ≤ beO D a a := by
  rw [beO_self]
  exact Finset.sum_nonneg fun σ _ => Complex.normSq_nonneg _

theorem beO_pos (a : 𝓞 D.host.E) (h : a ≠ 0) : 0 < beO D a a := by
  rw [beO_self]
  let σ0 : D.host.E →ₐ[ℚ] ℂ := D.host.φ₀.toRatAlgHom
  have ha : (a : D.host.E) ≠ 0 := by exact_mod_cast h
  have hs : σ0 (a : D.host.E) ≠ 0 := (map_ne_zero σ0).mpr ha
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hs)
    (Finset.single_le_sum (f := fun σ : D.host.E →ₐ[ℚ] ℂ => Complex.normSq (σ (a : D.host.E)))
      (fun σ _ => Complex.normSq_nonneg _) (Finset.mem_univ σ0))

def beK (k : ℕ) : (Fin k → 𝓞 D.host.E) →ₗ[ℤ] (Fin k → 𝓞 D.host.E) →ₗ[ℤ] ℝ :=
  ∑ i, (beO D).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem beK_apply (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : beK D k a b = ∑ i, beO D (a i) (b i) := by
  simp [beK, LinearMap.sum_apply, LinearMap.compl₁₂_apply]

theorem beK_int (k : ℕ) (a b : Fin k → 𝓞 D.host.E) : ∃ z : ℤ, beK D k a b = z := by
  refine ⟨∑ i, Algebra.trace ℤ (𝓞 D.host.E) (a i * cjO D (b i)), ?_⟩
  rw [beK_apply, Int.cast_sum]
  rfl

theorem beK_pos (k : ℕ) (a : Fin k → 𝓞 D.host.E) (h : a ≠ 0) : 0 < beK D k a a := by
  rw [beK_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.sum_pos' (fun j _ => beO_nonneg D _) ⟨i, Finset.mem_univ _, beO_pos D _ hi⟩

theorem beO_sum {ι : Type} [Fintype ι] (a : ι → 𝓞 D.host.E) (c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * beO D (a i) (a j) =
      ∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i : D.host.E)) := by
  apply Complex.ofReal_injective
  calc ((∑ i, ∑ j, c i * c j * beO D (a i) (a j) : ℝ) : ℂ)
      = ∑ i, ∑ j, ∑ σ : D.host.E →ₐ[ℚ] ℂ,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [beO_eq, Finset.mul_sum]
    _ = ∑ i, ∑ σ : D.host.E →ₐ[ℚ] ℂ, ∑ j,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ σ : D.host.E →ₐ[ℚ] ℂ, ∑ i, ∑ j,
          (c i : ℂ) * c j * (σ (a i : D.host.E) * starRingEnd ℂ (σ (a j : D.host.E))) :=
        Finset.sum_comm
    _ = ((∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i : D.host.E)) : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Complex.conj_ofReal]
        ring

theorem beK_sum (k : ℕ) {ι : Type} [Fintype ι] (a : ι → Fin k → 𝓞 D.host.E) (c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * beK D k (a i) (a j) =
      ∑ m : Fin k, ∑ σ : D.host.E →ₐ[ℚ] ℂ, Complex.normSq (∑ i, (c i : ℂ) * σ (a i m : D.host.E)) := by
  simp only [beK_apply, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact beO_sum D (fun i => a i m) c

def bK (k : ℕ) : Module.Basis (Σ _ : Fin k, Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) ℤ (Fin k → 𝓞 D.host.E) :=
  Pi.basis fun _ => RingOfIntegers.basis D.host.E

theorem beK_posDef (k : ℕ) (c : (Σ _ : Fin k, Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * beK D k (bK D k i) (bK D k j) := by
  obtain ⟨⟨m0, t0⟩, h0⟩ := Function.ne_iff.mp hc
  have key : ∃ σ : D.host.E →ₐ[ℚ] ℂ,
      ∑ i, (c i : ℂ) * σ ((bK D k i m0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    by_contra hne
    push_neg at hne
    let B := NumberField.integralBasis D.host.E
    have hred : ∀ σ : D.host.E →ₐ[ℚ] ℂ, ∑ t, (c ⟨m0, t⟩ : ℂ) * σ (B t) = 0 := by
      intro σ
      have h := hne σ
      rw [Fintype.sum_sigma, Finset.sum_eq_single m0 (fun m' _ hm' => ?_) (by simp)] at h
      · rw [← h]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [B, bK, Pi.basis_apply, NumberField.integralBasis_apply]
      · refine Finset.sum_eq_zero fun t _ => ?_
        simp [bK, Pi.basis_apply, Pi.single_apply, Ne.symm hm']
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)) =
        Fintype.card (D.host.E →ₐ[ℚ] ℂ) := by
      rw [AlgHom.card, Module.finrank_eq_card_basis B]
    let e := Fintype.equivOfCardEq hcard
    have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ B e).det ≠ 0 := by
      intro hd
      have h2 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ B e
      rw [hd, zero_pow two_ne_zero, map_eq_zero_iff _ (algebraMap ℚ ℂ).injective] at h2
      exact Algebra.discr_not_zero_of_basis ℚ B h2
    have hv := Matrix.eq_zero_of_vecMul_eq_zero hdet (v := fun t => (c ⟨m0, t⟩ : ℂ)) (by
      funext j
      simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex,
        Algebra.embeddingsMatrix, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_apply,
        Equiv.symm_symm, Matrix.of_apply, Pi.zero_apply]
      exact hred (e j))
    have h1 := congrFun hv t0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h1
    exact h0 h1
  obtain ⟨σ, hσ⟩ := key
  rw [beK_sum]
  refine Finset.sum_pos' (fun m _ => Finset.sum_nonneg fun σ _ => Complex.normSq_nonneg _)
    ⟨m0, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
    ⟨σ, Finset.mem_univ _, Complex.normSq_pos.mpr hσ⟩

open Classical in

def rk01 (P : Prop) : ℕ := if P then 0 else 1

theorem rank_indicator_le_one (P : Prop) : rk01 P ≤ 1 := by
  unfold rk01
  split_ifs <;> omega

theorem finrank_copies (k : ℕ) : Module.finrank ℤ (Fin k → 𝓞 D.host.E) = 2 * D.R.f * k := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, NumberField.RingOfIntegers.rank, D.host.der.finrank_E]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem subsingleton_rank_indicator_iff (P : Prop) : Subsingleton (Fin (rk01 P) → 𝓞 D.host.E) ↔ P := by
  unfold rk01
  by_cases h : P
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => inferInstance⟩
  · rw [if_neg h]
    refine ⟨fun hs => ?_, fun hp => absurd hp h⟩
    exfalso
    have h1 := congrFun (hs.elim (fun _ => (0 : 𝓞 D.host.E)) (fun _ => 1)) 0
    exact zero_ne_one h1

def pmM (dg : PsiT D → ℕ → ℤ) (n : ℕ) : ℤ := ∑ t : D.what₂.Tau, ∑ k ∈ Finset.Icc 1 n, |dg (D.eTau t) k|

theorem pmM_nonneg (dg : PsiT D → ℕ → ℤ) (n : ℕ) : 0 ≤ pmM D dg n := by
  exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => abs_nonneg _

theorem abs_le_pmM (dg : PsiT D → ℕ → ℤ) (n : ℕ) (τ : PsiT D) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 n) :
    |∑ k ∈ s, dg τ k| ≤ pmM D dg n := by
  have h1 : |∑ k ∈ s, dg τ k| ≤ ∑ k ∈ s, |dg τ k| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ k ∈ s, |dg τ k| ≤ ∑ k ∈ Finset.Icc 1 n, |dg τ k| :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => abs_nonneg _)
  have h3 : ∑ k ∈ Finset.Icc 1 n, |dg τ k| ≤ pmM D dg n := by
    unfold pmM
    have := Finset.single_le_sum (f := fun t => ∑ k ∈ Finset.Icc 1 n, |dg (D.eTau t) k|)
      (fun t _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ (D.eTau.symm τ))
    simpa using this
  linarith

end Form

def nn (n : ℕ) : ℕ := if n = 0 then 1 else n

instance (n : ℕ) : NeZero (nn n) := ⟨by unfold nn; split_ifs <;> omega⟩

abbrev AtM (k n : ℕ) : Type := Fin k → ZMod (nn n)

theorem atM_tors (k n : ℕ) (x : AtM k n) : n • x = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  by_cases h : n = 0
  · simp [h]
  · have hn : nn n = n := if_neg h
    have : (n : ZMod (nn n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (nn n)) (nn n) n).mpr (by rw [hn])
    rw [this, zero_mul]

theorem atM_card (k n : ℕ) (h : 0 < n) : Fintype.card (AtM k n) = n ^ k := by
  have hn : nn n = n := if_neg (by omega)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hn]

macro "exists_prescribed_local_data" : tactic => `(tactic| (intros; first | trivial | rfl | exact Subsingleton.elim _ _ | simp))

structure MP (D : D7) (p : ℕ) where
  K : CF p
  Gn : Type
  fin : Finite Gn
  ne : Nonempty Gn
  ab : Gn → Prop
  Cv : Type
  dg : Cv → PsiT D → ℕ → ℤ

variable (D : D7) (r j p : ℕ) (M : MP D p)

@[reducible] def locM : Loc D r j p where
  Mdl := Unit
  Xm := ()
  YY := ()
  Xn := fun _ => ()
  Pt := fun _ => M.Gn
  fld := fun _ => M.K
  Ylat := fun y => Fin (rk01 (M.ab y)) → 𝓞 D.host.E
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := fun y => beK D (rk01 (M.ab y))
  be_symm := fun y a b => by rw [beK_apply, beK_apply]; exact Finset.sum_congr rfl fun i _ => beO_symm D _ _
  be_bal := fun y c c' h a b => by
    rw [beK_apply, beK_apply]; exact Finset.sum_congr rfl fun i _ => beO_bal D c c' h _ _
  be_posDef := fun y => ⟨_, inferInstance, bK D _, beK_posDef D _⟩
  yl_rank := fun y => ⟨rk01 (M.ab y), finrank_copies D _, fun h1 h2 => by
    have := rank_indicator_le_one (M.ab y); omega⟩
  Gen := fun _ => M.Gn
  abAt := fun η => M.ab η
  Sh := fun _ => Unit
  IsInv := fun _ => True
  IsLocFree := fun _ => True
  Sec := fun _ => PUnit
  secAdd := fun _ => inferInstance
  H0 := fun _ => ⊤
  nrm := fun _ _ _ => 0
  nrm_nonneg := by exists_prescribed_local_data
  norm_le_one_of_mem_sections := by exists_prescribed_local_data
  GIso := fun _ _ => Empty
  vrat := fun _ _ => 0
  Lb := fun _ => ()
  Lb_inv := by exists_prescribed_local_data
  nrmRef := fun _ _ _ => 0
  DVP := M.Gn
  dvRho := fun y => rk01 (M.ab y)
  Ext := fun _ => Unit
  Chart := fun _ _ _ => Empty
  chAt := fun _ => True
  chOpen := fun _ => True
  chAbExact := fun _ => True
  chModU := fun _ => True
  chConst := fun _ => True
  PL := Unit
  phiAt := fun _ _ _ => 0
  phiAt_zero := by exists_prescribed_local_data
  divGe := fun _ _ _ _ => True
  FJd := Unit
  Chr := fun _ => Unit
  fjN := fun _ _ _ _ => 0
  Unim := ℕ
  LBG := fun _ => Unit
  LBGq := fun _ => Unit
  resQ := fun _ => ()
  PPq := fun _ => ()
  symmG := fun _ => True
  rigG := fun _ => True
  LBGt := fun _ _ => Unit
  LBB := fun _ _ => Unit
  resGt := fun _ _ => ()
  prPull := fun _ => ()
  principal := fun _ => True
  psiV := fun _ _ => 0
  piPP := ()
  keySh := fun _ => ()
  latStd := fun n => n
  At := fun _ La n => AtM (2 * (D.R.f * r * La)) n
  atAdd := fun _ _ _ => inferInstance
  atFin := fun _ _ _ => inferInstance
  at_tors := fun _ _ _ x => atM_tors _ _ x
  at_card := fun _ _ _ h => atM_card _ _ h
  Th := fun _ La n => (M.K.C)ˣ × Multiplicative (AtM (2 * (D.R.f * r * La)) n)
  thGrp := fun _ _ _ => inferInstance
  ovr := fun _ _ _ => MonoidHom.snd _ _
  ovr_surj := fun _ _ _ x => ⟨(1, x), rfl⟩
  scal := fun _ _ _ => MonoidHom.inl _ _
  scal_inj := fun _ _ _ a b h => congrArg Prod.fst h
  scal_central := fun _ _ _ a g => by
    ext <;> simp [mul_comm]
  ker_ovr := fun _ _ _ g => ⟨fun h => ⟨g.1, Prod.ext rfl h.symm⟩, fun ⟨a, h⟩ => by rw [← h]; rfl⟩
  dl := fun _ _ _ => MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.inv _)
  dl_ovr := fun _ _ _ _ => rfl
  dl_scal := fun _ La n a => Prod.ext rfl (inv_one : (1 : Multiplicative (AtM (2 * (D.R.f * r * La)) n))⁻¹ = 1)
  dl_dl := fun _ _ _ g => by
    show (g.1, (g.2⁻¹)⁻¹) = g
    rw [inv_inv]
  Sn := fun _ _ _ => PUnit
  snAdd := fun _ _ _ => inferInstance
  snMod := fun _ _ _ => inferInstance
  act := fun _ _ _ => 1
  act_scal := by exists_prescribed_local_data
  vth := fun _ _ _ => 0
  Jet := fun _ _ _ _ => PUnit
  jAdd := fun _ _ _ _ => inferInstance
  jMod := fun _ _ _ _ => inferInstance
  intJet := fun _ _ _ _ => ⊤
  jet := fun _ _ _ _ => 0
  LieGt := fun _ _ => PUnit
  LieB := fun _ _ => PUnit
  LieT := fun _ _ => PUnit
  lgAdd := fun _ _ => inferInstance
  lbAdd := fun _ _ => inferInstance
  ltAdd := fun _ _ => inferInstance
  resB := fun _ _ => 0
  incT := fun _ _ => 0
  kapGt := fun _ _ _ _ => 0
  kapB := fun _ _ _ _ => 0
  Harm := fun _ => Unit
  SecP := fun _ => Unit
  evA := fun _ _ _ => 0
  evGt := fun _ _ _ => 0
  Tp := fun _ => PUnit
  tpAdd := fun _ => inferInstance
  OmV := fun _ => PUnit
  omAdd := fun _ => inferInstance
  omMod := fun _ => inferInstance
  om := fun _ => ⊤
  ht := fun _ => 0
  IsHTBlowup := fun _ _ => False
  eOmP := fun _ _ _ => ()
  SES := fun _ => Unit
  ExactMod := fun _ _ => True
  htSES := fun _ _ => ()
  nefHT := fun _ _ => True
  nefQ := fun _ => True
  descK := fun _ _ => True
  bdryLoci := fun _ => True
  BT := fun _ => Unit
  extA := fun _ => True
  compat := fun _ _ => True
  Crv := M.Cv
  eDeg := fun c => -∑ᶠ τ, ((∑ i ∈ Finset.Icc 1 j, M.dg c τ i) + -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i)
  Pm := fun c => pmM D (M.dg c) (r + j)
  Pm_nonneg := fun c => pmM_nonneg D _ _
  degLie := fun c τ b => if b then -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i else ∑ i ∈ Finset.Icc 1 j, M.dg c τ i
  degLdR := fun c μ => -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (M.dg c τ i : ℝ)

@[reducible] def extM : ExtA D (locM D r j p M) where
  FlagData := fun _ => Unit
  flagCl := fun _ _ => ()
  allFlags := ()
  YY_eq := rfl
  Idl := fun _ => Unit
  blowUp := fun _ _ => ()
  powP := fun _ => True
  pbPrinc := fun _ _ => True
  Corr := fun _ _ => Unit
  diagCl := fun _ _ _ => ()
  IvD := fun _ => Unit
  jIdl := fun _ _ => ()
  ZP := fun _ => M.Gn
  spz := fun _ _ => True
  abP := fun x => M.ab x
  inQ := fun _ => False
  isGenP := fun _ => False
  isGenP_ab := fun _ h => h.elim
  gpt := fun η => η
  abAt_iff := fun _ => Iff.rfl
  gpt_notQ := fun _ h => h
  genFin := fun _ => M.fin
  genNe := fun _ => M.ne
  redK := fun _ y => y
  dvRho_pos_iff := fun _ y => by
    show 0 < rk01 (M.ab y) ↔ ¬ M.ab y
    by_cases h : M.ab y <;> simp [rk01, h]
  genK := fun η => η
  redK_genK := fun _ => rfl
  imgM := fun χ => Empty.elim χ
  imgU := fun χ => Empty.elim χ
  img_spz := fun χ => Empty.elim χ
  imgU_inQ := fun χ => Empty.elim χ
  chAt_imgM := fun χ => Empty.elim χ
  chAbExact_imgU := fun χ => Empty.elim χ
  RFam := fun _ _ => Unit
  chFam := fun _ => ()
  ptK := fun _ y => y
  ptK_good := fun _ y => by
    show Subsingleton (Fin (rk01 (M.ab y)) → 𝓞 D.host.E) ↔ rk01 (M.ab y) = 0
    rw [subsingleton_rank_indicator_iff]
    by_cases h : M.ab y <;> simp [rk01, h]
  vpi := fun _ => 1
  vpi_pos := by exists_prescribed_local_data
  ordGe := fun _ _ _ _ => True
  yEta := fun η => η
  yEta_good := fun η => subsingleton_rank_indicator_iff D (M.ab η)
  homSh := fun _ _ => ()
  homSh_inv := by exists_prescribed_local_data
  isoSec := fun _ => 0
  nrm_isoSec := fun φ => Empty.elim φ
  isoSymm := fun φ => Empty.elim φ
  vrat_symm := fun φ => Empty.elim φ
  LieV := fun _ => PUnit
  lvAdd := fun _ => inferInstance
  lvMod := fun _ => inferInstance
  lieL := fun _ => ⊤
  eig := fun _ _ => ⊤
  Wst := fun _ _ _ => ⊤
  Wst_le := by exists_prescribed_local_data
  taut := fun _ _ _ => ⊤
  taut_eq := by exists_prescribed_local_data
  nrmIn := fun _ _ _ _ => 0
  nrmRef_def := by exists_prescribed_local_data
  nrm_Lb_def := by exists_prescribed_local_data
  om_smul := by exists_prescribed_local_data
  TC := fun _ => PUnit
  tcAdd := fun _ => inferInstance
  tcMod := fun _ => inferInstance
  iT := fun _ => 0
  iT_span := by exists_prescribed_local_data
  htC := fun _ => 0
  htC_iT := by exists_prescribed_local_data
  psiC := fun _ => 0
  lieGt1 := fun _ => ⊤
  eT := fun _ _ => 0
  HTn := fun _ => Empty
  htEval := fun h => Empty.elim h
  htIdl := fun _ => ()
  IsHTBlowup_def := fun n Z' _ => ⟨fun h => h.elim, fun ⟨h, _⟩ => Empty.elim h⟩
  wFib := fun _ _ _ => ⊤
  htFlags := fun _ => ()
  omSh := fun _ => ()
  omPat := fun _ => ⊤
  omPat_def := fun _ _ _ h => h.elim
  BPt := fun _ => Empty
  bfld := fun _ => M.K
  OmB := fun _ => PUnit
  obAdd := fun _ => inferInstance
  obMod := fun _ => inferInstance
  omB := fun _ => ⊤
  omPB := fun _ => ⊤
  eOmB := fun _ _ => ⊤
  eB := fun _ _ => 0
  YsP := fun _ => Empty
  ysBd := fun _ => True
  FlP := Unit
  hFl := fun _ => ()
  FlCl := Unit
  flMem := fun _ _ => True
  flDim := fun _ => 0
  Sum1 := Unit
  locus := fun _ => ()
  bdryLoci_def := fun _ => ⟨fun _ => ⟨∅, Set.finite_empty, fun x => Empty.elim x, by simp⟩, fun _ => trivial⟩
  CrvS := fun _ => Empty
  degGr := fun _ _ _ => 0
  nefHT_def := fun _ _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  CrvQ := Empty
  degGrQ := fun _ _ _ => 0
  nefQ_def := fun _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  degGrD := fun c => M.dg c
  degLdR_def := fun _ _ => rfl
  degLie_f := fun _ _ => rfl
  degLie_alt := fun _ _ => rfl
  eDeg_def := fun _ _ => rfl
  Pm_head := fun c τ i _ h2 => le_trans (le_abs_self _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc le_rfl (by omega)))
  Pm_tail := fun c τ i _ _ => le_trans (neg_le_abs _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc (by omega) (by omega)))

@[reducible] def provDegenerate (Dat : Type) (rk jj : Dat → ℕ) (h : ∀ w, 1 ≤ jj w ∧ jj w + 1 ≤ rk w)
    (M : ∀ (_ : Dat) (p : ℕ), MP D p) : ModuliIntegralCharts.Prov D where
  Dat := Dat
  rk := rk
  jj := jj
  jj_range := h
  loc := fun w p => locM D (rk w) (jj w) p (M w p)
  ex := fun w p => extM D (rk w) (jj w) p (M w p)
  NgC := fun _ => Unit
  NgC_ne := fun _ => ⟨()⟩
  KF := fun _ _ => Unit
  kfNorm := fun _ _ => 1
  pbKF := fun _ _ _ _ => 0
  levIn := fun _ _ => True
  Xg := fun _ => Unit
  bc := fun _ _ => ()
  DivX := fun _ => Unit
  effD := fun _ => True
  noVertD := fun _ => True
  posBdD := fun _ => True
  ampleOnAbelianBase := fun _ _ _ => True
  Met := fun _ => Unit
  nefFib := fun _ => True
  ampleGen := fun _ => True
  limRA := fun _ => True

def mpTrivialAb (K : CF p) : MP D p where
  K := K
  Gn := Unit
  fin := inferInstance
  ne := ⟨()⟩
  ab := fun _ => True
  Cv := Empty
  dg := fun c => c.elim

end LocalProvisionModel

open LocalProvisionModel

variable (D : D7)

theorem exists_full_local_provision :
    ∃ P : ModuliIntegralCharts.Prov D, ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j := by
  refine ⟨provDegenerate D {rj : ℕ × ℕ // 1 ≤ rj.2 ∧ rj.2 + 1 ≤ rj.1} (fun w => w.1.1) (fun w => w.1.2)
    (fun w => w.2) (fun _ p => mpTrivialAb D p (Classical.choice (nonempty_coefficient_field p))), ?_⟩
  intro r j hj hr
  exact ⟨⟨(r, j), hj, hr⟩, rfl, rfl⟩

end Formalism.MainNotions.DIV.Inh

end
