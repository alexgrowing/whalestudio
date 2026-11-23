import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)

variable {n : ℕ}

section maps
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fsb_pow_map (f : V →ₗ[ℂ] W) (T : Module.End ℂ V) (T' : Module.End ℂ W)
    (h : ∀ v, f (T v) = T' (f v)) : ∀ (k : ℕ) (v : V), f ((T ^ k) v) = (T' ^ k) (f v) := by
  intro k
  induction k with
  | zero => intro v; simp
  | succ k ih =>
    intro v
    rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

theorem fsb_ofFn_map (f : V →ₗ[ℂ] W) : ∀ (t : ℕ) (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ W),
    (∀ k v, f (g k v) = g' k (f v)) → ∀ v, f ((List.ofFn g).prod v) = (List.ofFn g').prod (f v) := by
  intro t
  induction t with
  | zero => intro g g' _ v; simp
  | succ t ih =>
    intro g g' hg v
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, hg,
      ih (fun i => g i.succ) (fun i => g' i.succ) (fun k w => hg k.succ w), List.ofFn_succ, List.prod_cons,
      Module.End.mul_apply]

theorem fsb_qdet_map {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (x : ℂ) (v : V) :
    f (qdet E x v) = qdet E' x (f v) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply,
    map_zsmul]
  congr 1
  refine fsb_ofFn_map f n _ _ (fun k w => ?_) v
  simp only [Formalism.REAL.Tm, LinearMap.add_apply, map_add, hf]
  split_ifs <;> simp

theorem fsb_glRel_surj {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hs : Function.Surjective f) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  have key := hE a b c d
  ext w
  obtain ⟨v, rfl⟩ := hs w
  have key' := congrArg (fun T => f (T v)) key
  split_ifs at key' ⊢ <;> simpa [hf] using key'

end maps

theorem fsb_hasChar_inj (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hi : Function.Injective f) (χ : Fin n → ℂ) (h : HasChar M2 χ) : HasChar M1 χ := by
  have hT : ∀ (u c : ℂ) (w : M1.V), f ((Formalism.REAL.qdet M1.E u - c • (1 : Module.End ℂ M1.V)) w) =
      (Formalism.REAL.qdet M2.E u - c • (1 : Module.End ℂ M2.V)) (f w) := by
    intro u c w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_qdet_map f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  ext v
  apply hi
  rw [fsb_pow_map f _ _ (hT _ _) k v, hk Y]
  simp

theorem fsb_hasChar_surj (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (hs : Function.Surjective f) (χ : Fin n → ℂ) (h : HasChar M1 χ) : HasChar M2 χ := by
  have hT : ∀ (u c : ℂ) (w : M1.V), f ((Formalism.REAL.qdet M1.E u - c • (1 : Module.End ℂ M1.V)) w) =
      (Formalism.REAL.qdet M2.E u - c • (1 : Module.End ℂ M2.V)) (f w) := by
    intro u c w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_qdet_map f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  ext w
  obtain ⟨v, rfl⟩ := hs w
  rw [← fsb_pow_map f _ _ (hT _ _) k v, hk Y]
  simp

theorem fsb_omD_apply (M : GMod n) (g : Fin n → M.V) (a : Fin n) : omD M g a = -∑ c, M.E a c (g c) := by
  simp only [omD, eeVd, LinearMap.pi_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem fsb_tensVd_apply (M : GMod n) (a b : Fin n) (g : Fin n → M.V) (d : Fin n) :
    tensVd M.E a b g d = M.E a b (g d) - if d = b then g a else 0 := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  split_ifs <;> simp

theorem fsb_omD_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (g : Fin n → M1.V) : f.compLeft (Fin n) (omD M1 g) = omD M2 (f.compLeft (Fin n) g) := by
  funext a
  simp only [LinearMap.compLeft_apply, Function.comp_apply, fsb_omD_apply, map_neg, map_sum, hf]

theorem fsb_aeval_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (p : Polynomial ℂ) (g : Fin n → M1.V) :
    f.compLeft (Fin n) (Polynomial.aeval (omD M1) p g) = Polynomial.aeval (omD M2) p (f.compLeft (Fin n) g) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      fsb_pow_map (f.compLeft (Fin n)) (omD M1) (omD M2) (fun v => fsb_omD_map M1 M2 f hf v) k g]

theorem fsb_gen_map (M1 M2 : GMod n) (f : M1.V →ₗ[ℂ] M2.V) (hf : ∀ a b v, f (M1.E a b v) = M2.E a b (f v))
    (μ : ℂ) (g : Fin n → M1.V) (hg : g ∈ (omD M1).maxGenEigenspace μ) :
    f.compLeft (Fin n) g ∈ (omD M2).maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at hg ⊢
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  have h1 : ∀ v, f.compLeft (Fin n) ((omD M1 - μ • 1) v) = (omD M2 - μ • 1) (f.compLeft (Fin n) v) := by
    intro v
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, fsb_omD_map M1 M2 f hf, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_smul]
  rw [← fsb_pow_map _ _ _ h1 k g, hk, map_zero]

def fsbQuot (M : GMod n) (Z : Submodule ℂ M.V) (hZ : ∀ a b, ∀ x ∈ Z, M.E a b x ∈ Z) : GMod n where
  V := M.V ⧸ Z
  E := fun a b => Z.mapQ Z (M.E a b) (fun x hx => hZ a b x hx)
  gl := fsb_glRel_surj Z.mkQ (Submodule.mkQ_surjective Z) (fun a b v => by simp) M.gl

private theorem exists_mem_backSub_compLeft_eq_of_surjective (hD : DualFacts) (S Q : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ)
    (hz : χ' s = z) (h1 : ∀ t, t ≠ s → χ' t ≠ z) (hS : HasChar S χ') (f : S.V →ₗ[ℂ] Q.V)
    (hs : Function.Surjective f) (hf : ∀ a b v, f (S.E a b v) = Q.E a b (f v)) (y : Fin n → Q.V)
    (hy : y ∈ backSub Q z) : ∃ x ∈ backSub S z, f.compLeft (Fin n) x = y := by
  obtain ⟨K, hK⟩ := (hD n S χ' hS).1
  have hP : Polynomial.aeval (omD S)
      ((List.ofFn fun t => (Polynomial.X - Polynomial.C (-χ' t - cn n))).prod ^ K) = 0 := by
    rw [map_pow, map_list_prod, List.map_ofFn]
    have hfun : (⇑(Polynomial.aeval (omD S)) ∘ fun t => Polynomial.X - Polynomial.C (-χ' t - cn n)) =
        fun t => omD S - (-χ' t - cn n) • 1 := by
      funext t
      rw [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [hfun]
    exact hK
  rw [List.prod_ofFn, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), hz, mul_pow] at hP
  have hcop : IsCoprime (Polynomial.X - Polynomial.C (-z - cn n))
      (∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (-χ' t - cn n))) := by
    apply IsCoprime.prod_right
    intro t ht
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply Ne.isUnit
    intro h0
    apply h1 t (Finset.ne_of_mem_erase ht)
    linear_combination h0
  generalize (∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (-χ' t - cn n))) = R at hP hcop
  have hy' := hy
  rw [backSub, Module.End.mem_maxGenEigenspace] at hy'
  obtain ⟨k, hk⟩ := hy'
  obtain ⟨A', B', hAB⟩ := hcop.pow (m := k) (n := K)
  choose x0 hx0 using fun d => hs (y d)
  have hx0' : f.compLeft (Fin n) x0 = y := by
    funext d
    rw [LinearMap.compLeft_apply, Function.comp_apply, hx0]
  refine ⟨Polynomial.aeval (omD S) (B' * R ^ K) x0, ?_, ?_⟩
  · rw [backSub, Module.End.mem_maxGenEigenspace]
    refine ⟨K, ?_⟩
    have e1 : (omD S - (-z - cn n) • 1) ^ K =
        Polynomial.aeval (omD S) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ K) := by
      rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul,
      show (Polynomial.X - Polynomial.C (-z - cn n)) ^ K * (B' * R ^ K) =
        B' * ((Polynomial.X - Polynomial.C (-z - cn n)) ^ K * R ^ K) by ring,
      map_mul, hP, mul_zero, LinearMap.zero_apply]
  · rw [fsb_aeval_map S Q f hf, hx0']
    have e3 : Polynomial.aeval (omD Q) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k) y = 0 := by
      have e4 : Polynomial.aeval (omD Q) ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k) =
          (omD Q - (-z - cn n) • 1) ^ k := by
        rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      rw [e4]
      exact hk
    calc Polynomial.aeval (omD Q) (B' * R ^ K) y
        = Polynomial.aeval (omD Q) (A' * (Polynomial.X - Polynomial.C (-z - cn n)) ^ k + B' * R ^ K) y := by
          rw [map_add, LinearMap.add_apply,
            map_mul (Polynomial.aeval (omD Q)) A' ((Polynomial.X - Polynomial.C (-z - cn n)) ^ k),
            Module.End.mul_apply, e3, map_zero, zero_add]
      _ = y := by rw [hAB, map_one, Module.End.one_apply]

private theorem apply_mem_of_mem_backSub_of_iso_simple (hD : DualFacts) (X S : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ)
    (hz : χ' s = z) (hX : IsSimple X) (hS : HasChar S χ') (h2 : ∀ r, χ' r ≠ z - 1)
    (hB : ∀ a b, ∀ x ∈ backSub S z, (tensD S).E a b x ∈ backSub S z)
    (hI : Iso (back S z hB) X) (Z : Submodule ℂ S.V) (hZ : ∀ a b, ∀ x ∈ Z, S.E a b x ∈ Z) (hZb : Z ≠ ⊥) :
    ∀ g ∈ backSub S z, ∀ d, g d ∈ Z := by
  obtain ⟨e, he⟩ := hI
  have hZc : HasChar (S.sub Z hZ) χ' :=
    fsb_hasChar_inj (S.sub Z hZ) S Z.subtype (fun a b v => rfl) Z.injective_subtype χ' hS
  haveI : Nontrivial (S.sub Z hZ).V := Submodule.nontrivial_iff_ne_bot.mpr hZb
  have hne := (hD n (S.sub Z hZ) χ' hZc).2.2 s inferInstance (fun r => by rw [hz]; exact h2 r)
  rw [hz] at hne
  obtain ⟨g0, hg0, hg0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hmem : Z.subtype.compLeft (Fin n) g0 ∈ backSub S z :=
    fsb_gen_map (S.sub Z hZ) S Z.subtype (fun a b v => rfl) _ g0 hg0
  let W : Submodule ℂ ↥(backSub S z) := (Submodule.pi Set.univ fun _ => Z).comap (backSub S z).subtype
  have hWmem : ∀ x : ↥(backSub S z), x ∈ W ↔ ∀ d, (x : Fin n → S.V) d ∈ Z := by
    intro x
    simp only [W, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.subtype_apply]
  have hWinv : ∀ a b, ∀ x ∈ W, (back S z hB).E a b x ∈ W := by
    intro a b x hx
    have hx : ∀ d, (x : Fin n → S.V) d ∈ Z := (hWmem x).mp hx
    refine (hWmem ((back S z hB).E a b x)).mpr fun d => ?_
    show (tensVd S.E a b (x : Fin n → S.V)) d ∈ Z
    rw [fsb_tensVd_apply S a b]
    split_ifs
    · exact Z.sub_mem (hZ a b _ (hx d)) (hx a)
    · simpa using hZ a b _ (hx d)
  let W' : Submodule ℂ X.V := W.comap (e.symm : X.V →ₗ[ℂ] (back S z hB).V)
  have hW'mem : ∀ x : X.V, x ∈ W' ↔ e.symm x ∈ W := fun x => Iff.rfl
  have key : ∀ a b (x : X.V), e.symm (X.E a b x) = (back S z hB).E a b (e.symm x) := by
    intro a b x
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hW'inv : ∀ a b, ∀ x ∈ W', X.E a b x ∈ W' := by
    intro a b x hx
    rw [hW'mem, key]
    exact hWinv a b _ hx
  rcases hX.2 W' hW'inv with h | h
  · exfalso
    apply hg0ne
    have hw : (⟨_, hmem⟩ : ↥(backSub S z)) ∈ W := by
      rw [hWmem]
      intro d
      exact (g0 d).2
    have hw' : e ⟨_, hmem⟩ ∈ W' :=
      (hW'mem _).mpr (Eq.mpr (congrArg (fun x => x ∈ W) (e.symm_apply_apply _)) hw)
    rw [h, Submodule.mem_bot] at hw'
    have hw0 : (⟨_, hmem⟩ : ↥(backSub S z)) = 0 := e.injective (hw'.trans (map_zero e).symm)
    funext d
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hw0) d
  · intro g hg d
    have hw' : e ⟨g, hg⟩ ∈ W' := by rw [h]; trivial
    have hw2 : (⟨g, hg⟩ : ↥(backSub S z)) ∈ W :=
      Eq.mp (congrArg (fun x => x ∈ W) (e.symm_apply_apply ⟨g, hg⟩)) ((hW'mem _).mp hw')
    exact (hWmem ⟨g, hg⟩).mp hw2 d

theorem fsb_simple_of_back (hD : DualFacts) (X S : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ) (hz : χ' s = z)
    (hX : IsSimple X) (hS : HasChar S χ') (h1 : ∀ t, t ≠ s → χ' t ≠ z) (h2 : ∀ r, χ' r ≠ z - 1)
    (hB : ∀ a b, ∀ x ∈ backSub S z, (tensD S).E a b x ∈ backSub S z)
    (hI : Iso (back S z hB) X) : IsSimple S := by
  haveI hnt : Nontrivial ↥(backSub S z) := by
    obtain ⟨e, -⟩ := hI
    haveI := hX.1
    exact e.symm.injective.nontrivial
  refine ⟨?_, fun Z hZ => ?_⟩
  · obtain ⟨⟨g, hg⟩, hne⟩ := exists_ne (0 : ↥(backSub S z))
    have hg0 : g ≠ 0 := fun h0 => hne (Subtype.ext h0)
    obtain ⟨d, hd⟩ := Function.ne_iff.mp hg0
    exact ⟨⟨g d, 0, hd⟩⟩
  · by_cases hZb : Z = ⊥
    · exact Or.inl hZb
    · right
      by_contra hZt
      have hA := apply_mem_of_mem_backSub_of_iso_simple hD X S χ' s z hz hX hS h2 hB hI Z hZ hZb
      have hQc : HasChar (fsbQuot S Z hZ) χ' :=
        fsb_hasChar_surj S (fsbQuot S Z hZ) Z.mkQ (fun a b v => rfl) (Submodule.mkQ_surjective Z) χ' hS
      obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hZt)
      haveI : Nontrivial (fsbQuot S Z hZ).V :=
        ⟨⟨Submodule.Quotient.mk v, 0, fun h0 => hv ((Submodule.Quotient.mk_eq_zero Z).mp h0)⟩⟩
      have hne := (hD n (fsbQuot S Z hZ) χ' hQc).2.2 s inferInstance (fun r => by rw [hz]; exact h2 r)
      rw [hz] at hne
      obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨x, hx, hxy⟩ := exists_mem_backSub_compLeft_eq_of_surjective hD S (fsbQuot S Z hZ) χ' s z hz h1 hS Z.mkQ
        (Submodule.mkQ_surjective Z) (fun a b v => rfl) y hy
      apply hyne
      rw [← hxy]
      funext d
      show Z.mkQ (x d) = 0
      exact (Submodule.Quotient.mk_eq_zero Z).mpr (hA x hx d)

theorem forward_simple_of_tensor_facts : QdetTens → BackStable → DualFacts → Unit → FwdSimple := by
  intro hQ hB hD hU n X χ s hX hSc h1 h2 h3
  have hXc : HasChar X χ := ⟨1, fun Y => by rw [pow_one, hSc Y, sub_self]⟩
  refine fsb_simple_of_back hD X (step X (χ s)) (χ + Pi.single s 1) s (χ s + 1) (by simp) hX
    (GlobalTheory.T.InfinitesimalCharacterStatement n X χ s hXc) ?_ ?_ (hB n _ _) (hU n X χ s hB hSc h1 h2 h3)
  · intro t ht
    simpa [Pi.single_apply, ht] using h1 t
  · intro r
    by_cases hr : r = s
    · subst hr
      simp
    · simpa [Pi.single_apply, hr] using h2 r hr

end CompanionTheory.RgExh.Hk
