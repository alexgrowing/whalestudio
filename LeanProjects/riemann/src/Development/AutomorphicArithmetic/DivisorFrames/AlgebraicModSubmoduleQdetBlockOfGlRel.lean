import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ULieDefs
import Development.AutomorphicArithmetic.DivisorFrames.ExistsQdetEqPowAddSumCoeffMemSpan
import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralEvalOfMonicMulIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ULie
open scoped TensorProduct

namespace UpperTheory.QuantumDeterminantBlockAnnihilators
open Formalism.REAL Polynomial

private theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (S : Subalgebra ℂ A)
    (E : Fin n → Fin n → A) (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => S.mul_mem (S.intCast_mem _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Tm
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  unfold qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp, Tm]
  split_ifs <;> simp

private theorem qdet_self_comm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (u w : ℂ) : qdet E u * qdet E w = qdet E w * qdet E u := by
  have h := qdet_mem (Subalgebra.centralizer ℂ {qdet E u}) E (fun a b => by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds A n E hE u a b) w
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h _ rfl

private def stab {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) :
    Subalgebra ℂ (Module.End ℂ V) where
  carrier := {a | ∀ x ∈ M, a x ∈ M}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => M.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => M.smul_mem c hx

private theorem exists_poly {A : Type} [Ring A] [Algebra ℂ A] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] A) {n : ℕ} (E : Fin n → Fin n → A) (h : ∀ u, qdet E u ∈ φ.range) :
    ∃ p : R[X], p.Monic ∧ ∀ u : ℂ, φ (p.eval (algebraMap ℂ R u)) = qdet E u := by
  obtain ⟨c, hc, hq⟩ := UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span A n E
  have hc' : ∀ k, ∃ d : R, φ d = c k := fun k => by
    have : Submodule.span ℂ (Set.range (qdet E)) ≤ Subalgebra.toSubmodule φ.range :=
      Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact h u)
    exact this (hc k)
  choose d hd using hc'
  refine ⟨X ^ n + ∑ k : Fin n, C (d k) * X ^ (k : ℕ), monic_X_pow_add (degree_sum_fin_lt _), fun u => ?_⟩
  rw [hq u, ← Fin.sum_univ_eq_sum_range (fun k => u ^ k • c k)]
  simp only [eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C, map_add, map_sum]
  congr 1
  · rw [← map_pow, AlgHom.commutes]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, hd]

private theorem factor_alg {V : Type} [AddCommGroup V] [Module ℂ V] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] Module.End ℂ V) (M : Submodule ℂ V) (hM : ∀ r : R, ∀ x ∈ M, φ r x ∈ M) (v : V)
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (h : ∀ u : ℂ, ∃ P : ℂ[X], P ≠ 0 ∧ aeval (φ ((p * q).eval (algebraMap ℂ R u))) P v ∈ M) (u : ℂ) :
    ∃ P : ℂ[X], P ≠ 0 ∧ aeval (φ (p.eval (algebraMap ℂ R u))) P v ∈ M := by
  let I : Ideal R :=
    { carrier := {a | φ a v ∈ M}
      add_mem' := fun {a b} ha hb => by
        show φ (a + b) v ∈ M
        rw [map_add]; exact M.add_mem ha hb
      zero_mem' := by
        show φ 0 v ∈ M
        rw [map_zero]; exact M.zero_mem
      smul_mem' := fun c a ha => by
        show φ (c * a) v ∈ M
        rw [map_mul]; exact hM c _ ha }
  have key : ∀ a : R, IsIntegral ℂ (Ideal.Quotient.mkₐ ℂ I a) ↔
      ∃ P : ℂ[X], P ≠ 0 ∧ aeval (φ a) P v ∈ M := by
    intro a
    rw [← isAlgebraic_iff_isIntegral]
    refine exists_congr fun P => and_congr_right fun _ => ?_
    rw [aeval_algHom_apply, aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  have hev : ∀ (f : R[X]) (w : ℂ), (f.map (Ideal.Quotient.mk I)).eval (algebraMap ℂ (R ⧸ I) w) =
      Ideal.Quotient.mkₐ ℂ I (f.eval (algebraMap ℂ R w)) := by
    intro f w
    have : algebraMap ℂ (R ⧸ I) w = Ideal.Quotient.mk I (algebraMap ℂ R w) := rfl
    rw [this, eval_map, eval₂_hom]; rfl
  rw [← key, ← hev]
  refine UpperTheory.isIntegral_eval_of_monic_mul_isIntegral (R ⧸ I) _ (q.map (Ideal.Quotient.mk I)) (hp.map _) (hq.map _) (fun w => ?_) u
  rw [← Polynomial.map_mul, hev, key]
  exact h w

private theorem aeval_congr {V : Type} [AddCommGroup V] [Module ℂ V] (W M : Submodule ℂ V)
    (c D : Module.End ℂ V) (hc : ∀ x ∈ W, c x ∈ W) (hD : ∀ x ∈ M, D x ∈ M)
    (h : ∀ x ∈ W, c x - D x ∈ M) (P : ℂ[X]) : ∀ v ∈ W, aeval c P v - aeval D P v ∈ M := by
  have hDn : ∀ n : ℕ, ∀ x ∈ M, (D ^ n) x ∈ M := fun n => (stab M).pow_mem (show D ∈ stab M from hD) n
  have hn : ∀ n : ℕ, ∀ v ∈ W, (c ^ n) v - (D ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      have e : (c ^ (n + 1)) v - (D ^ (n + 1)) v =
          ((c ^ n) (c v) - (D ^ n) (c v)) + (D ^ n) (c v - D v) := by
        rw [pow_succ, pow_succ, map_sub, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [e]
      exact M.add_mem (ih _ (hc v hv)) (hDn n _ (h v hv))
  intro v hv
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : aeval c (p + q) v - aeval D (p + q) v =
        (aeval c p v - aeval D p v) + (aeval c q v - aeval D q v) := by
      simp only [map_add, LinearMap.add_apply]; abel
    rw [e]; exact M.add_mem hp hq
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact M.smul_mem _ (hn n v hv)

private theorem two_factor {V : Type} [AddCommGroup V] [Module ℂ V] {r m : ℕ}
    (A : Fin r → Fin r → Module.End ℂ V) (B : Fin m → Fin m → Module.End ℂ V)
    (hA : GlRel A) (hB : GlRel B) (hAB : ∀ u w, qdet B u * qdet A w = qdet A w * qdet B u)
    (M : Submodule ℂ V) (hAM : ∀ p q, ∀ x ∈ M, A p q x ∈ M) (hBM : ∀ p q, ∀ x ∈ M, B p q x ∈ M)
    (v : V) (t : ℂ)
    (h : ∀ u : ℂ, ∃ P : ℂ[X], P ≠ 0 ∧ aeval (qdet B u * qdet A (u - t)) P v ∈ M) :
    (∀ u : ℂ, ∃ P : ℂ[X], P ≠ 0 ∧ aeval (qdet A u) P v ∈ M) ∧
      (∀ u : ℂ, ∃ P : ℂ[X], P ≠ 0 ∧ aeval (qdet B u) P v ∈ M) := by
  let s : Set (Module.End ℂ V) := Set.range (qdet A) ∪ Set.range (qdet B)
  have hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩) _ (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact qdet_self_comm A hA u w
    · exact (hAB w u).symm
    · exact hAB u w
    · exact qdet_self_comm B hB u w
  letI : CommRing (Algebra.adjoin ℂ s) :=
    { (inferInstance : Ring (Algebra.adjoin ℂ s)) with
      mul_comm := (Algebra.isMulCommutative_adjoin ℂ hs).is_comm.comm }
  let φ : Algebra.adjoin ℂ s →ₐ[ℂ] Module.End ℂ V := (Algebra.adjoin ℂ s).val
  have hle : Algebra.adjoin ℂ s ≤ stab M := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact qdet_mem (stab M) A hAM u
    · exact qdet_mem (stab M) B hBM u
  have hM : ∀ a : Algebra.adjoin ℂ s, ∀ x ∈ M, φ a x ∈ M := fun a => hle a.2
  obtain ⟨pA, mA, eA⟩ := exists_poly φ A fun u =>
    ⟨⟨_, Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩, rfl⟩
  obtain ⟨pB, mB, eB⟩ := exists_poly φ B fun u =>
    ⟨⟨_, Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩, rfl⟩
  have eA' : ∀ u : ℂ, φ ((pA.comp (X - C (algebraMap ℂ _ t))).eval (algebraMap ℂ _ u)) =
      qdet A (u - t) := by
    intro u
    rw [eval_comp, eval_sub, eval_X, eval_C, ← map_sub, eA]
  have mA' := mA.comp_X_sub_C (algebraMap ℂ _ t)
  have h1 : ∀ u : ℂ, ∃ P : ℂ[X], P ≠ 0 ∧
      aeval (φ ((pB * pA.comp (X - C (algebraMap ℂ _ t))).eval (algebraMap ℂ _ u))) P v ∈ M := by
    intro u
    rw [eval_mul, map_mul, eA', eB]
    exact h u
  refine ⟨fun u => ?_, fun u => ?_⟩
  · have := factor_alg φ M hM v _ _ mA' mB (by rw [mul_comm]; exact h1) (u + t)
    rwa [eA', add_sub_cancel_right] at this
  · have := factor_alg φ M hM v _ _ mB mA' h1 u
    rwa [eB] at this

private theorem block_congr {V : Type} [AddCommGroup V] [Module ℂ V] {r m : ℕ}
    (X : Fin (r + m) → Fin (r + m) → Module.End ℂ V) (hX : GlRel X) (W : Submodule ℂ V)
    (hW : ∀ p q, ∀ x ∈ W, X p q x ∈ W) (u : ℂ) (x : V) (hx : x ∈ W) :
    qdet X u x - (qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u *
      qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) (u - m)) x ∈
      Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m), ∃ x ∈ W,
        y = X (Fin.castAdd m p) (Fin.natAdd r q) x} := by
  let Y : Fin (r + m) → Fin (r + m) → stab W := fun p q => ⟨X p q, hW p q⟩
  have hY : GlRel Y := by
    intro a b c d
    apply Subtype.ext
    have := hX a b c d
    split_ifs at this ⊢ <;> simpa [Y] using this
  have h1 := GlobalTheory.CapHC.two_block Y hY u
  have h2 : ∀ y ∈ GlobalTheory.CapHC.upperSpan Y, (stab W).val y x ∈
      Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m), ∃ x ∈ W,
        y = X (Fin.castAdd m p) (Fin.natAdd r q) x} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, w, rfl⟩ := hy
      exact Submodule.subset_span ⟨p, q, w.1 x, w.2 x hx, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h3 := h2 _ h1
  rw [map_sub, map_mul, map_qdet, map_qdet, map_qdet] at h3
  exact h3

private theorem span_stable {V : Type} [AddCommGroup V] [Module ℂ V] {r m : ℕ}
    (X : Fin (r + m) → Fin (r + m) → Module.End ℂ V) (hX : GlRel X) (W : Submodule ℂ V)
    (hW : ∀ p q, ∀ x ∈ W, X p q x ∈ W) (a b : Fin (r + m))
    (hab : (∃ s t, a = Fin.castAdd m s ∧ b = Fin.castAdd m t) ∨
      ∃ s t, a = Fin.natAdd r s ∧ b = Fin.natAdd r t) :
    ∀ y ∈ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m), ∃ x ∈ W,
        y = X (Fin.castAdd m p) (Fin.natAdd r q) x}, X a b y ∈
      Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m), ∃ x ∈ W,
        y = X (Fin.castAdd m p) (Fin.natAdd r q) x} := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, x, hx, rfl⟩ := hy
    have h := LinearMap.congr_fun (hX a b (Fin.castAdd m p) (Fin.natAdd r q)) x
    rw [LinearMap.sub_apply, sub_eq_iff_eq_add, Module.End.mul_apply, Module.End.mul_apply] at h
    rw [h, LinearMap.sub_apply]
    have hne : ∀ (s : Fin r) (t : Fin m), Fin.natAdd r t ≠ Fin.castAdd m s := by
      intro s t h; have := congrArg Fin.val h; simp at this; omega
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_)
      (Submodule.subset_span ⟨p, q, _, hW _ _ _ hx, rfl⟩)
    · split_ifs with h1
      · rcases hab with ⟨s, t, rfl, rfl⟩ | ⟨s, t, rfl, rfl⟩
        · exact Submodule.subset_span ⟨s, q, x, hx, rfl⟩
        · exact absurd h1 (hne _ _)
      · exact Submodule.zero_mem _
    · split_ifs with h1
      · rcases hab with ⟨s, t, rfl, rfl⟩ | ⟨s, t, rfl, rfl⟩
        · exact absurd h1 (hne _ _)
        · exact Submodule.subset_span ⟨p, t, x, hx, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end UpperTheory.QuantumDeterminantBlockAnnihilators

open UpperTheory.QuantumDeterminantBlockAnnihilators in
theorem UpperTheory.algebraicModSubmodule_qdet_block_of_glRel :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (r m : ℕ) (X : Fin (r + m) → Fin (r + m) → Module.End ℂ V), Formalism.REAL.GlRel X →
        ∀ W N N' : Submodule ℂ V, (∀ p q, ∀ x ∈ W, X p q x ∈ W) → (∀ p q, ∀ x ∈ N, X p q x ∈ N) →
        N' = N ⊔ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m), ∃ x ∈ W, y = X (Fin.castAdd m p) (Fin.natAdd r q) x} →
        ∀ v ∈ W, (∀ u : ℂ, ∃ P : Polynomial ℂ, P ≠ 0 ∧ Polynomial.aeval (Formalism.REAL.qdet X u) P v ∈ N) →
        (∀ p q : Fin r, ∀ x ∈ N', X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ N') ∧
        (∀ u : ℂ, ∃ P : Polynomial ℂ, P ≠ 0 ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u) P v ∈ N') ∧
        (∀ u : ℂ, ∃ P : Polynomial ℂ, P ≠ 0 ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u) P v ∈ N') := by
  intro V _ _ r m X hX W N N' hW hN hN' v hv hc
  have hst : ∀ a b : Fin (r + m), ((∃ s t, a = Fin.castAdd m s ∧ b = Fin.castAdd m t) ∨
      ∃ s t, a = Fin.natAdd r s ∧ b = Fin.natAdd r t) → ∀ x ∈ N', X a b x ∈ N' := by
    intro a b hab x hx
    rw [hN'] at hx ⊢
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hN _ _ _ hy) (span_stable X hX W hW a b hab z hz)
  have hAM : ∀ p q : Fin r, ∀ x ∈ N', X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ N' :=
    fun p q => hst _ _ (Or.inl ⟨p, q, rfl, rfl⟩)
  have hBM : ∀ p q : Fin m, ∀ x ∈ N', X (Fin.natAdd r p) (Fin.natAdd r q) x ∈ N' :=
    fun p q => hst _ _ (Or.inr ⟨p, q, rfl, rfl⟩)
  refine ⟨hAM, two_factor _ _
    (GlobalTheory.CapHC.glRel_restrict hX _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)))
    (GlobalTheory.CapHC.glRel_restrict hX _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)))
    (fun u w => (GlobalTheory.CapHC.qdet_comm hX u w).eq) N' hAM hBM v m fun u => ?_⟩
  obtain ⟨P, hP, hPv⟩ := hc u
  refine ⟨P, hP, ?_⟩
  have h1 := aeval_congr W N' (Formalism.REAL.qdet X u) _ (qdet_mem (stab W) X hW u)
    ((stab N').mul_mem (qdet_mem (stab N') _ hBM u) (qdet_mem (stab N') _ hAM (u - m)))
    (fun x hx => hN' ▸ Submodule.mem_sup_right (block_congr X hX W hW u x hx)) P v hv
  have h2 : Polynomial.aeval (Formalism.REAL.qdet X u) P v ∈ N' := hN' ▸ Submodule.mem_sup_left hPv
  have h3 := N'.sub_mem h2 h1
  rwa [sub_sub_cancel] at h3
