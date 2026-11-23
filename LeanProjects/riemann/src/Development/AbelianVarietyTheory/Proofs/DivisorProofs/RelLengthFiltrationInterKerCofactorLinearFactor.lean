import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {S : Type} [Fintype S] [DecidableEq S]
  (a : S → Int0 v) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a))

def compSpan (s : S) : Submodule C (Fin N → C) :=
  Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
    (eigQuot a Fil s : Set (Fin N → Int0 v)))

abbrev CompProd (τ : S) : Type := ∀ s : {s // s ≠ τ}, compSpan v a Fil s

def compMap (τ : S) : filKer a Fil τ →ₗ[Int0 v] CompProd v a Fil τ where
  toFun x s := ⟨fun i => ((ev a s.1 ((x : Fin N → RS a) i) : Int0 v) : C),
    Submodule.subset_span ⟨comp a N s.1 x, ⟨x, x.2.1, rfl⟩, rfl⟩⟩
  map_add' x y := by
    funext s; apply Subtype.ext; funext i; simp
  map_smul' c x := by
    funext s; apply Subtype.ext; funext i
    simp [Algebra.smul_def, ← AdjoinRoot.algebraMap_eq, AlgHom.commutes]
    exact Or.inl rfl

def diagMul (τ : S) : CompProd v a Fil τ →ₗ[C] CompProd v a Fil τ :=
  LinearMap.pi fun s => ((a s.1 : C) - (a τ : C)) • LinearMap.proj s

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem mulR_apply (r : RS a) (x : Fin N → RS a) : mulR a N r x = r • x := rfl

theorem mulR_mem_filKer (τ : S) {x : Fin N → RS a} (hx : x ∈ filKer a Fil τ) :
    mulR a N (lin a τ) x ∈ filKer a Fil τ := by
  rw [filKer, Submodule.mem_inf] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [mulR_apply]; exact Fil.smul_mem _ h1
  · rw [LinearMap.mem_ker] at h2 ⊢
    rw [mulR_apply] at h2
    rw [mulR_apply, mulR_apply, smul_smul, mul_comm, ← smul_smul, h2, smul_zero]

theorem compMap_mulR (τ : S) (x : Fin N → RS a) (hx : x ∈ filKer a Fil τ) :
    compMap v a Fil τ ⟨mulR a N (lin a τ) x, mulR_mem_filKer τ hx⟩ =
      diagMul v a Fil τ (compMap v a Fil τ ⟨x, hx⟩) := by
  funext s; apply Subtype.ext; funext i
  simp [compMap, diagMul, mulR_apply, ev_lin]

theorem det_diagMul (τ : S) :
    LinearMap.det (diagMul v a Fil τ) =
      ∏ s : {s // s ≠ τ}, ((a s.1 : C) - (a τ : C)) ^ eigRank v a Fil s.1 := by
  let bs : ∀ s : {s // s ≠ τ}, Basis (Fin (finrank C (compSpan v a Fil s.1))) C (compSpan v a Fil s.1) :=
    fun s => Module.finBasis C _
  let B := Pi.basis bs
  rw [← LinearMap.det_toMatrix B]
  have hM : LinearMap.toMatrix B B (diagMul v a Fil τ) =
      Matrix.diagonal (fun σ => (a σ.1.1 : C) - (a τ : C)) := by
    ext σ ρ
    rw [LinearMap.toMatrix_apply]
    have : diagMul v a Fil τ (B ρ) = ((a ρ.1.1 : C) - (a τ : C)) • B ρ := by
      funext s
      simp only [B, Pi.basis_apply, diagMul, LinearMap.pi_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, Pi.smul_apply]
      by_cases h : s = ρ.1
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [this, map_smul, B.repr_self, Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : ρ = σ
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hM, Matrix.det_diagonal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem lin_eq_mk (s : S) : lin a s = AdjoinRoot.mk _ (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem prod_lin : ∏ s, lin a s = 0 := by
  simp_rw [lin_eq_mk]
  rw [← map_prod]
  exact AdjoinRoot.mk_self

theorem cofac_mul_cofac {s τ : S} (h : s ≠ τ) : cofac a τ * cofac a s = 0 := by
  have h1 : lin a s * ∏ t ∈ (Finset.univ.erase τ).erase s, lin a t = cofac a τ :=
    Finset.mul_prod_erase _ (lin a) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ s⟩)
  have h2 : cofac a s * lin a s = ∏ t, lin a t :=
    Finset.prod_erase_mul _ (lin a) (Finset.mem_univ s)
  rw [← h1, mul_comm (lin a s), mul_assoc, mul_comm (lin a s), h2, prod_lin, mul_zero]

theorem ev_cofac (t s : S) : ev a t (cofac a s) = ∏ u ∈ Finset.univ.erase s, (a t - a u) := by
  simp [cofac, map_prod, ev_lin]

theorem ev_cofac_of_ne {t s : S} (h : t ≠ s) : ev a t (cofac a s) = 0 := by
  rw [ev_cofac]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ t⟩) (sub_self _)

theorem ev_cofac_self_ne_zero (ha : Function.Injective a) (s : S) : ev a s (cofac a s) ≠ 0 := by
  rw [ev_cofac]
  refine Finset.prod_ne_zero_iff.mpr fun u hu => sub_ne_zero.mpr fun h => ?_
  exact (Finset.mem_erase.mp hu).1 (ha h).symm

theorem ev_mk (s : S) (q : (Int0 v)[X]) : ev a s (AdjoinRoot.mk _ q) = q.eval (a s) := by
  simp [ev, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map]

theorem eq_zero_of_ev (ha : Function.Injective a) (r : RS a) (h : ∀ s, ev a s r = 0) : r = 0 := by
  have hmon : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
    monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _
  have hdeg : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).natDegree = Fintype.card S := by
    rw [natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C _)]; simp
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    have hmk : AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s))) p =
        AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s))) (p %ₘ ∏ s, (X - Polynomial.C (a s))) := by
      rw [AdjoinRoot.mk_eq_mk]
      refine ⟨p /ₘ ∏ s, (X - Polynomial.C (a s)), ?_⟩
      have := modByMonic_add_div p (∏ s, (X - Polynomial.C (a s)))
      linear_combination this.symm
    rw [hmk] at h ⊢
    have hev : ∀ s, (p %ₘ ∏ s, (X - Polynomial.C (a s))).eval (a s) = 0 := by
      intro s
      rw [← ev_mk]; exact h s
    by_cases hq : p %ₘ ∏ s, (X - Polynomial.C (a s)) = 0
    · rw [hq, map_zero]
    · have hlt : (p %ₘ ∏ s, (X - Polynomial.C (a s))).natDegree < Fintype.card S := by
        rw [← hdeg]
        exact natDegree_lt_natDegree hq (degree_modByMonic_lt _ hmon)
      rw [eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ha hev hlt, map_zero]

theorem eq_zero_of_cofac (ha : Function.Injective a) (τ : S) (r : RS a) (hP : cofac a τ * r = 0)
    (h : ∀ s, s ≠ τ → ev a s r = 0) : r = 0 := by
  refine eq_zero_of_ev ha r fun s => ?_
  by_cases hs : s = τ
  · subst hs
    have := congrArg (ev a s) hP
    rw [map_mul, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (ev_cofac_self_ne_zero ha s)
  · exact h s hs

theorem mem_filKer_iff (τ : S) (x : Fin N → RS a) :
    x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0 := by
  rw [filKer, Submodule.mem_inf, LinearMap.mem_ker]; rfl

theorem mulR_injOn (ha : Function.Injective a) (τ : S) {x : Fin N → RS a} (hx : x ∈ filKer a Fil τ)
    (h0 : mulR a N (lin a τ) x = 0) : x = 0 := by
  rw [mem_filKer_iff] at hx
  funext i
  refine eq_zero_of_cofac ha τ (x i) (congrFun hx.2 i) fun s hs => ?_
  have := congrArg (ev a s) (congrFun h0 i)
  rw [mulR_apply, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr fun h => hs (ha h))

theorem compMap_injective (ha : Function.Injective a) (τ : S) :
    Function.Injective (compMap v a Fil τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hx2 := ((mem_filKer_iff τ x.1).mp x.2).2
  apply Subtype.ext
  funext i
  refine eq_zero_of_cofac ha τ _ (congrFun hx2 i) fun s hs => ?_
  have := congrArg (fun p => ((p ⟨s, hs⟩ : compSpan v a Fil s) : Fin N → C) i) hx
  simpa [compMap] using this

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem filKer_finite_free (hsat : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil)
    (τ : S) : Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Free (Int0 v) (filKer a Fil τ) := by
  have hmon : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
    monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _
  haveI : Module.Finite (Int0 v) (RS a) := hmon.finite_adjoinRoot
  haveI : Module.Free (Int0 v) (RS a) := hmon.free_adjoinRoot
  haveI : Module.Free (Int0 v) (Fin N → RS a) := inferInstance
  haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) := Module.Free.instIsTorsionFree _ _
  have hsat' : GlobalTheory.IsSaturatedSubmodule (filKer a Fil τ) := by
    rw [GlobalTheory.isSaturatedSubmodule_iff]
    intro c hc x hx
    rw [mem_filKer_iff] at hx ⊢
    refine ⟨hsat c x hc hx.1, ?_⟩
    have h2 : c • (cofac a τ • x) = 0 := by rw [smul_comm]; exact hx.2
    exact (smul_eq_zero.mp h2).resolve_left hc
  exact ⟨hsat'.finite_of_valuationRing, hsat'.free_of_valuationRing⟩

theorem span_range_compMap (ha : Function.Injective a) (τ : S) :
    Submodule.span C (Set.range (compMap v a Fil τ)) = ⊤ := by
  set W := Submodule.span C (Set.range (compMap v a Fil τ)) with hW
  have key : ∀ (s : {s // s ≠ τ}) (y : Fin N → Int0 v) (hy : y ∈ eigQuot a Fil s.1)
      (hy' : (fun i => (y i : C)) ∈ compSpan v a Fil s.1),
      Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s ⟨fun i => (y i : C), hy'⟩ ∈ W := by
    intro s y hy hy'
    obtain ⟨x0, hx0, rfl⟩ := hy
    have hz : cofac a s.1 • x0 ∈ filKer a Fil τ := by
      rw [mem_filKer_iff]
      refine ⟨Fil.smul_mem _ hx0, ?_⟩
      rw [smul_smul, cofac_mul_cofac s.2, zero_smul]
    have hd : ((ev a s.1 (cofac a s.1) : Int0 v) : C) ≠ 0 := by
      rw [Ne, ZeroMemClass.coe_eq_zero]; exact ev_cofac_self_ne_zero ha s.1
    have hval : compMap v a Fil τ ⟨cofac a s.1 • x0, hz⟩ =
        ((ev a s.1 (cofac a s.1) : Int0 v) : C) •
          Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s
            ⟨fun i => ((comp a N s.1 x0) i : C), hy'⟩ := by
      funext t; apply Subtype.ext; funext i
      by_cases h : t = s
      · subst h; simp [compMap]; exact Or.inl rfl
      · have h' : t.1 ≠ s.1 := fun e => h (Subtype.ext e)
        simp [compMap, Pi.single_eq_of_ne h, ev_cofac_of_ne h']
    have : Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s
        ⟨fun i => ((comp a N s.1 x0) i : C), hy'⟩ =
        (((ev a s.1 (cofac a s.1) : Int0 v) : C))⁻¹ • compMap v a Fil τ ⟨cofac a s.1 • x0, hz⟩ := by
      rw [hval, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [this]
    exact W.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  have hsingle : ∀ (s : {s // s ≠ τ}) (w : compSpan v a Fil s.1),
      Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s w ∈ W := by
    intro s w
    obtain ⟨w, hw⟩ := w
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact key s y hy _
    | zero =>
      have : (⟨0, Submodule.zero_mem _⟩ : compSpan v a Fil s.1) = 0 := rfl
      rw [this, Pi.single_zero]; exact W.zero_mem
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, Submodule.add_mem _ hx hz⟩ : compSpan v a Fil s.1) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
      rw [this, Pi.single_add]; exact W.add_mem ihx ihz
    | smul c x hx ih =>
      have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : compSpan v a Fil s.1) = c • ⟨x, hx⟩ := rfl
      rw [this, Pi.single_smul]; exact W.smul_mem c ih
  rw [eq_top_iff]
  intro p _
  rw [← Finset.univ_sum_single p]
  exact W.sum_mem fun s _ => hsingle s (p s)

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore

theorem relLen_lin_filKer : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  intro C _ v S _ _ a ha N Fil hsat τ
  set K := filKer a Fil τ with hK
  obtain ⟨hfin, hfree⟩ := filKer_finite_free (v := v) (a := a) hsat τ
  let n := finrank (Int0 v) K
  let b : Basis (Fin n) (Int0 v) K := Module.finBasis _ _
  let T : K →ₗ[Int0 v] K := (mulR a N (lin a τ)).restrict (fun x hx => mulR_mem_filKer τ hx)
  have hT : ∀ x : K, (T x : Fin N → RS a) = mulR a N (lin a τ) x := fun x => rfl
  let g : K →ₗ[Int0 v] (Fin N → RS a) := (mulR a N (lin a τ)).comp K.subtype
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (mulR_injOn ha τ x.2 hx)
  have hrange : LinearMap.range g = K.map (mulR a N (lin a τ)) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : K ≃ₗ[Int0 v] K.map (mulR a N (lin a τ)) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  let A := LinearMap.toMatrix b b T

  let Φ := compMap v a Fil τ
  have hli : LinearIndependent C (Φ ∘ b) :=
    (LinearIndependent.iff_fractionRing (Int0 v) C).mp
      (b.linearIndependent.map' Φ (LinearMap.ker_eq_bot.mpr (compMap_injective ha τ)))
  have hsp : ⊤ ≤ Submodule.span C (Set.range (Φ ∘ b)) := by
    rw [← span_range_compMap (v := v) (Fil := Fil) ha τ, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, ← algebraMap_smul C]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let β : Basis (Fin n) C (CompProd v a Fil τ) := Basis.mk hli hsp
  have hmat : LinearMap.toMatrix β β (diagMul v a Fil τ) = A.map (algebraMap (Int0 v) C) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have h1 : diagMul v a Fil τ (β k) = ∑ j, (algebraMap (Int0 v) C (A j k)) • β j := by
      rw [Basis.mk_apply, Function.comp_apply]
      have := compMap_mulR (v := v) τ (b k : Fin N → RS a) (b k).2
      simp only [Subtype.coe_eta] at this
      rw [← this]
      have h2 : (⟨mulR a N (lin a τ) (b k), mulR_mem_filKer τ (b k).2⟩ : K) = ∑ j, A j k • b j := by
        show T (b k) = _
        conv_lhs => rw [← b.sum_repr (T (b k))]
        simp [A, LinearMap.toMatrix_apply]
      rw [h2, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, algebraMap_smul, Basis.mk_apply]
      rfl
    rw [h1, β.repr_sum_self]
  have hdetC : ((A.det : Int0 v) : C) = ∏ s : {s // s ≠ τ}, ((a s.1 : C) - (a τ : C)) ^ eigRank v a Fil s.1 := by
    rw [← det_diagMul, ← LinearMap.det_toMatrix β, hmat]
    exact RingHom.map_det (algebraMap (Int0 v) C) A
  have hne : ((A.det : Int0 v) : C) ≠ 0 := by
    rw [hdetC]
    refine Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro h
    exact s.2 (ha (Subtype.ext h))
  have hval : v ((A.det : Int0 v) : C) = yExp v a Fil τ := by
    have hprod : ∀ (ι : Type) (s : Finset ι) (f : ι → C), v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
      intro ι s f
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]
    rw [hdetC, hprod, yExp]
    rw [Finset.sum_subtype (Finset.univ.erase τ) (p := fun s => s ≠ τ) (by simp)
      (fun s => eigRank v a Fil s • v ((a s : C) - (a τ : C)))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddValuation.map_pow]
  have htop : v ((A.det : Int0 v) : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]; exact hne
  refine ⟨(v ((A.det : Int0 v) : C)).untop htop, by rw [WithTop.coe_untop, hval], n, b, b.map e, A, fun k => ?_, by rw [WithTop.coe_untop]⟩
  rw [Basis.map_apply]
  have : ((e (b k) : K.map (mulR a N (lin a τ))) : Fin N → RS a) = (T (b k) : Fin N → RS a) := rfl
  have h3 : T (b k) = ∑ i, A i k • b i := by
    conv_lhs => rw [← b.sum_repr (T (b k))]
    simp [A, LinearMap.toMatrix_apply]
  rw [this, h3, Submodule.coe_sum]
  simp

end GlobalTheory.HerbCore
