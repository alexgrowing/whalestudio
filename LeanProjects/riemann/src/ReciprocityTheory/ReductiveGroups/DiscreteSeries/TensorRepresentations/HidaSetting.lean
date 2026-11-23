import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Resolvent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def tensF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    Fin n → Fin n → Module.End ℂ (Fin n → M) :=
  cond dual (tensVd E) (tensV E)

def eeF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (Fin n → M) :=
  cond dual (eeVd E) (eeV E)

def poleF (dual : Bool) (lam : Fin n → ℝ) : Fin n → ℂ := cond dual (poleVd lam) (poleV lam)

def ratioF (dual : Bool) (lam : Fin n → ℝ) : Fin n → ℝ := cond dual (ratioVd lam) (ratioV lam)

def shiftF (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) : Fin n → ℝ :=
  cond dual (lam - Pi.single s 1) (lam + Pi.single s 1)

def tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) : Submodule ℂ (Fin n → M) :=
  Submodule.pi Set.univ fun _ => S

theorem tset_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ tensSub S ↔ ∀ c, f c ∈ S := by
  simp [tensSub, Submodule.mem_pi]

theorem tset_genSub_E {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (V : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem tset_actM_single {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (r d : Fin n) : actM E (Matrix.single r d (1 : ℂ)) = E r d := by
  unfold actM
  simp [Matrix.single_apply, ite_smul, ite_and]

theorem tset_conj_single (k : Matrix (Fin n) (Fin n) ℂ) (r d a b : Fin n) :
    (k * Matrix.single r d (1 : ℂ) * kᴴ : Matrix (Fin n) (Fin n) ℂ) a b = k a r * star (k b d) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem tset_unit {k : Matrix (Fin n) (Fin n) ℂ} (hu : k * kᴴ = 1) (s b : Fin n) :
    ∑ d, k s d * star (k b d) = if s = b then 1 else 0 := by
  have h := congrFun (congrFun hu s) b
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply] using h

theorem tset_comb {H : Type*} [AddCommGroup H] [Module ℂ H] (k : Fin n → Fin n → ℂ)
    (hu : ∀ s b, ∑ d, k s d * star (k b d) = if s = b then 1 else 0) (X : Fin n → Fin n → Fin n → H)
    (s : Fin n) :
    ∑ d, k s d • ∑ r, ∑ a, ∑ b, (k a r * star (k b d)) • X a b r = ∑ r, ∑ a, k a r • X a s r := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have hb : ∀ b, ∑ d, (k s d * (k a r * star (k b d))) • X a b r =
      (k a r * if s = b then 1 else 0) • X a b r := by
    intro b
    rw [← Finset.sum_smul, ← hu s b, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [hb, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem tset_combd {H : Type*} [AddCommGroup H] [Module ℂ H] (k : Fin n → Fin n → ℂ)
    (hu : ∀ s b, ∑ d, k s d * star (k b d) = if s = b then 1 else 0) (X : Fin n → Fin n → Fin n → H)
    (r : Fin n) :
    ∑ d, star (k r d) • ∑ s, ∑ a, ∑ b, (k a d * star (k b s)) • X a b s =
      ∑ s, ∑ b, star (k b s) • X r b s := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  have ha : ∀ a, ∑ d, ∑ b, (star (k r d) * (k a d * star (k b s))) • X a b s =
      ∑ b, (star (k b s) * if a = r then 1 else 0) • X a b s := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul, ← hu a r, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [ha, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem tset_casVal_add (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam + Pi.single s 1) = casVal lam + 2 * lam s + 1 := by
  have key : ∀ a, (lam + Pi.single s (1 : ℝ) : Fin n → ℝ) a * (lam + Pi.single s (1 : ℝ) : Fin n → ℝ) a =
      lam a * lam a + (if a = s then 2 * lam s + 1 else 0) := by
    intro a
    by_cases h : a = s
    · subst h; rw [Pi.add_apply, Pi.single_eq_same, if_pos rfl]; ring
    · rw [Pi.add_apply, Pi.single_eq_of_ne h, if_neg h]; ring
  simp only [casVal, nsq, dot, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp <;> ring

theorem tset_casVal_sub (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam - Pi.single s 1) = casVal lam - 2 * lam s + 1 := by
  have key : ∀ a, (lam - Pi.single s (1 : ℝ) : Fin n → ℝ) a * (lam - Pi.single s (1 : ℝ) : Fin n → ℝ) a =
      lam a * lam a + (if a = s then -2 * lam s + 1 else 0) := by
    intro a
    by_cases h : a = s
    · subst h; rw [Pi.sub_apply, Pi.single_eq_same, if_pos rfl]; ring
    · rw [Pi.sub_apply, Pi.single_eq_of_ne h, if_neg h]; ring
  simp only [casVal, nsq, dot, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp <;> ring

section Ambient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kDiag (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (k : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • σ k (f d)

variable {D : Submodule ℂ H}

def IsGKEndo (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S : Submodule ℂ D) (A : Module.End ℂ (Fin n → D)) : Prop :=
  (∀ f ∈ tensSub S, A f ∈ tensSub S) ∧
    (∀ a b, ∀ f ∈ tensSub S, A (tensF dual E a b f) = tensF dual E a b (A f)) ∧
    ∀ k ∈ Kset ε, ∀ f ∈ tensSub S, ∀ f' ∈ tensSub S,
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
        (fun c => ((A f' c : D) : H)) = kDiag dual σ k (fun c => ((A f c : D) : H))

def IsGKEmb (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S S' : Submodule ℂ D) (ι : D →ₗ[ℂ] (Fin n → D)) : Prop :=
  (∀ x ∈ S', ι x ∈ tensSub S) ∧ (∀ x ∈ S', ι x = 0 → x = 0) ∧
    (∀ a b, ∀ x ∈ S', ι (E a b x) = tensF dual E a b (ι x)) ∧
    ∀ k ∈ Kset ε, ∀ x ∈ S', ∀ x' ∈ S', (x' : H) = σ k (x : H) →
      (fun c => ((ι x' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H))

theorem tset_kV {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f f' : Fin n → D)
    (h : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H))) :
    (fun c => ((eeF dual E f' c : D) : H)) = kDiag dual σ k (fun c => ((eeF dual E f c : D) : H)) := by
  have hu := tset_unit (rq_K_unit hk).2
  have hgen : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v : D), σ k ((actM E X v : D) : H) =
      ((actM E (k * X * kᴴ) ⟨σ k (v : H), hD.kStable k hk v v.2⟩ : D) : H) := by
    intro X v
    have h0 := rq_lin hD hk v (1 / 2) (-Complex.I / 2) (rq_main_G hσ hD hk (rq_inG_S ε X) v)
      (rq_main_G hσ hD hk (isInLieAlgebra_I_smul_add_conjTranspose ε X) v)
    have hX : (1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε) +
        (-Complex.I / 2) • (Complex.I • (X + Jm ε * Xᴴ * Jm ε)) = X := by
      rw [smul_smul, show -Complex.I / 2 * Complex.I = (1 / 2 : ℂ) by
          rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]; ring, ← smul_add,
        show X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X by rw [two_smul]; abel,
        smul_smul]
      norm_num
    rwa [hX] at h0
  let g : Fin n → D := fun d => ⟨σ k ((f d : D) : H), hD.kStable k hk _ (f d).2⟩
  have hsingle : ∀ x y z, σ k ((E x y (f z) : D) : H) =
      ((∑ a, ∑ b, (k a x * star (k b y)) • E a b (g z) : D) : H) := by
    intro x y z
    rw [← actM_single' E x y, hgen]
    congr 1
    unfold actM
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, tset_conj_single] <;> rfl
  cases dual
  · have hf' : ∀ r, f' r = ∑ d, k r d • g d := by
      intro r
      apply Subtype.ext
      have h1 := congrFun h r
      simp only [kDiag, cond_false] at h1
      rw [h1, Submodule.coe_sum]
      simp only [Submodule.coe_smul] <;> rfl
    funext s
    show ((eeV E f' s : D) : H) = ∑ d, k s d • σ k ((eeV E f d : D) : H)
    simp only [eeV_coord, hf', map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsingle]
    rw [tset_comb k hu (fun a b r => ((E a b (g r) : D) : H)) s, Finset.sum_comm]
  · have hf' : ∀ r, f' r = ∑ d, star (k r d) • g d := by
      intro r
      apply Subtype.ext
      have h1 := congrFun h r
      simp only [kDiag, cond_true] at h1
      rw [h1, Submodule.coe_sum]
      simp only [Submodule.coe_smul] <;> rfl
    funext r
    show ((eeVd E f' r : D) : H) = ∑ d, star (k r d) • σ k ((eeVd E f d : D) : H)
    simp only [eeVd_coord, hf', map_sum, map_smul, map_neg, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_neg, hsingle, smul_neg, Finset.sum_neg_distrib]
    rw [tset_combd k hu (fun a b s => ((E a b (g s) : D) : H)) r, Finset.sum_comm]

theorem tensSub_stable {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} (dual : Bool) (a b : Fin n) :
    ∀ f ∈ tensSub (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) := by
  intro f hf
  rw [tset_mem] at hf ⊢
  intro c
  have hE : ∀ x y v, v ∈ genSub E V → E x y v ∈ genSub E V := fun x y v hv => tset_genSub_E E V x y hv
  cases dual
  · show ((E a b).comp (coordV c) + (if c = a then coordV b else 0) : (Fin n → D) →ₗ[ℂ] D) f ∈ genSub E V
    split_ifs
    · rw [LinearMap.add_apply, LinearMap.comp_apply]
      exact Submodule.add_mem _ (hE a b _ (hf c)) (hf b)
    · rw [LinearMap.add_apply, LinearMap.zero_apply, add_zero, LinearMap.comp_apply]
      exact hE a b _ (hf c)
  · show ((E a b).comp (coordV c) - (if c = b then coordV a else 0) : (Fin n → D) →ₗ[ℂ] D) f ∈ genSub E V
    split_ifs
    · rw [LinearMap.sub_apply, LinearMap.comp_apply]
      exact Submodule.sub_mem _ (hE a b _ (hf c)) (hf a)
    · rw [LinearMap.sub_apply, LinearMap.zero_apply, sub_zero, LinearMap.comp_apply]
      exact hE a b _ (hf c)

theorem isGKEndo_eeF {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (V : Submodule ℂ D) (dual : Bool) : IsGKEndo dual ε σ E (genSub E V) (eeF dual E) := by
  have hg := hD.glRep
  have hc : ∀ (r c' a' b' : Fin n) (v : D), E r c' (E a' b' v) =
      E a' b' (E r c' v) + ((if c' = a' then E r b' v else 0) - (if b' = r then E a' c' v else 0)) := by
    intro r c' a' b' v
    have h : E r c' (E a' b' v) - E a' b' (E r c' v) =
        ((if c' = a' then E r b' else 0) - (if b' = r then E a' c' else 0) : Module.End ℂ D) v :=
      LinearMap.congr_fun (hg r c' a' b') v
    rw [← sub_eq_iff_eq_add', h]
    split_ifs <;> simp
  have hT : ∀ (a b : Fin n) (g : Fin n → D) (c : Fin n), tensV E a b g c = E a b (g c) + if c = a then g b else 0 := by
    intro a b g c; by_cases h : c = a <;> simp [tensV, coordV, h]
  have hTd : ∀ (a b : Fin n) (g : Fin n → D) (c : Fin n), tensVd E a b g c = E a b (g c) - if c = b then g a else 0 := by
    intro a b g c; by_cases h : c = b <;> simp [tensVd, coordV, h]
  have hEe : ∀ (g : Fin n → D) (s : Fin n), eeV E g s = ∑ r, E r s (g r) := by
    intro g s; simp [eeV, coordV]
  have hEd : ∀ (g : Fin n → D) (r : Fin n), eeVd E g r = -∑ s, E r s (g s) := by
    intro g r; simp [eeVd, coordV]
  have hirr : ∀ (P : Prop) [Decidable P] (g : Fin n → D), (∑ r, if P then g r else 0) = if P then ∑ r, g r else 0 := by
    intro P _ g; split_ifs <;> simp
  refine ⟨?_, ?_, fun k hk f _ f' _ h => tset_kV hσ hD dual hk f f' h⟩
  · intro f hf
    rw [tset_mem] at hf ⊢
    intro s
    cases dual
    · show eeV E f s ∈ genSub E V
      rw [hEe]
      exact Submodule.sum_mem _ fun r _ => tset_genSub_E E V r s (hf r)
    · show eeVd E f s ∈ genSub E V
      rw [hEd]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun r _ => tset_genSub_E E V s r (hf r))
  · intro a b f _
    funext c
    cases dual
    · show eeV E (tensV E a b f) c = tensV E a b (eeV E f) c
      simp only [hEe, hT]
      have e1 : ∀ r, E r c (E a b (f r) + if r = a then f b else 0) =
          E a b (E r c (f r)) + ((if c = a then E r b (f r) else 0) - (if b = r then E a c (f r) else 0))
            + (if r = a then E a c (f b) else 0) := by
        intro r
        rw [map_add, hc r c a b (f r)]
        by_cases h : r = a
        · rw [if_pos h, if_pos h, h]
        · rw [if_neg h, if_neg h, map_zero]
      simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, hirr, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, reduceIte, map_sum]
      abel
    · show eeVd E (tensVd E a b f) c = tensVd E a b (eeVd E f) c
      simp only [hEd, hTd]
      have e2 : ∀ s, E c s (E a b (f s) - if s = b then f a else 0) =
          E a b (E c s (f s)) + ((if s = a then E c b (f s) else 0) - (if b = c then E a s (f s) else 0))
            - (if s = b then E c b (f a) else 0) := by
        intro s
        rw [map_sub, hc c s a b (f s)]
        by_cases h : s = b
        · rw [if_pos h, if_pos h, h]
        · rw [if_neg h, if_neg h, map_zero]
      simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, hirr, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, reduceIte, map_sum, map_neg]
      by_cases hbc : b = c
      · rw [if_pos hbc, if_pos hbc.symm]; abel
      · rw [if_neg hbc, if_neg (Ne.symm hbc)]; abel

theorem isGKEndo_one (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S : Submodule ℂ D) : IsGKEndo dual ε σ E S 1 := by
  refine ⟨fun f hf => hf, fun a b f _ => rfl, fun k _ f _ f' _ h => h⟩

theorem isGKEmb_bot (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S : Submodule ℂ D) : IsGKEmb dual ε σ E S ⊥ 0 := by
  refine ⟨fun x _ => by simp, fun x hx _ => (Submodule.mem_bot ℂ).1 hx, fun a b x _ => by simp, ?_⟩
  intro k _ x _ x' _ _
  funext c
  simp [kDiag]

end Ambient

theorem casVal_shiftF (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    ((casVal lam + n : ℝ) : ℂ) + 2 * poleF dual lam s = ((casVal (shiftF dual lam s) : ℝ) : ℂ) := by
  cases dual
  · simp only [shiftF, poleF, cond_false, poleV, tset_casVal_add]; push_cast; ring
  · simp only [shiftF, poleF, cond_true, poleVd, tset_casVal_sub]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS
