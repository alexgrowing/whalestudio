import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlicesStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.UniqAlg

section Arrays
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem jm_arr_sum_apply {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Arr V n j) (α : Fin j → Fin n × Fin n) :
    (∑ i ∈ s, f i) α = ∑ i ∈ s, f i α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem jm_positionE_apply {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  by_cases h1 : (α i).1 = c <;> by_cases h2 : (α i).2 = d <;> simp [factorAction, arrTo, arrOf, h1, h2]

theorem jm_ptE_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : ptE E c d F α = E c d (F α) := by
  simp [ptE, arrTo, arrOf]

theorem jm_arrE_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : arrE E j c d F α = ∑ i, factorAction i c d F α + E c d (F α) := by
  simp only [arrE]
  rw [LinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply, LinearMap.sum_apply, jm_arr_sum_apply,
    jm_ptE_apply]

def jmW (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin j → Fin n × Fin n) : Module.End ℂ V :=
  ew E (List.ofFn α).reverse

theorem jm_ew_append (E : Fin n → Fin n → Module.End ℂ V) (l1 l2 : List (Fin n × Fin n)) :
    ew E (l1 ++ l2) = ew E l1 * ew E l2 := by
  induction l1 with
  | nil => simp [ew]
  | cons p l ih => simp [ew, ih, mul_assoc]

theorem jmW_zero (E : Fin n → Fin n → Module.End ℂ V) (α : Fin 0 → Fin n × Fin n) : jmW E α = 1 := by
  simp [jmW, ew]

theorem jmW_succ (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin (j + 1) → Fin n × Fin n) :
    jmW E α = E (α (Fin.last j)).1 (α (Fin.last j)).2 * jmW E (Fin.init α) := by
  simp only [jmW, List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
    List.singleton_append, ew, Fin.init]
  rfl

private lemma update_castSucc_apply_last {X : Type*} {j : ℕ} (α : Fin (j + 1) → X) (k : Fin j) (x : X) :
    Function.update α k.castSucc x (Fin.last j) = α (Fin.last j) :=
  Function.update_of_ne (Fin.castSucc_lt_last k).ne' x α

private lemma fin_castSucc_apply_eq_init {X : Type*} {j : ℕ} (α : Fin (j + 1) → X) (k : Fin j) :
    α k.castSucc = Fin.init α k := rfl

theorem jm_deriv (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    ∀ (j : ℕ) (α : Fin j → Fin n × Fin n), E c d * jmW E α - jmW E α * E c d =
      ∑ i, ((if d = (α i).1 then jmW E (Function.update α i (c, (α i).2)) else 0) -
        (if (α i).2 = c then jmW E (Function.update α i ((α i).1, d)) else 0)) := by
  intro j
  induction j with
  | zero => intro α; simp [jmW_zero]
  | succ j ih =>
    intro α
    rw [Fin.sum_univ_castSucc]
    simp only [jmW_succ E, Fin.init_update_last, Fin.init_update_castSucc, update_castSucc_apply_last, Function.update_self]
    have hrel := hE c d (α (Fin.last j)).1 (α (Fin.last j)).2
    have key : ∀ A B : Module.End ℂ V,
        E c d * (A * B) - A * B * E c d = (E c d * A - A * E c d) * B + A * (E c d * B - B * E c d) := by
      intro A B; noncomm_ring
    rw [key, hrel, ih (Fin.init α)]
    simp only [Finset.mul_sum, mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul, fin_castSucc_apply_eq_init]
    clear ih hrel key hE
    abel

theorem jm_thetaA_apply (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (F : Arr V n j) :
    thetaA E j F = ∑ α, jmW E α (F α) := by
  simp [thetaA, jmW, arrOf]

private lemma sum_eq_sum_update_involutive {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] {j : ℕ}
    (i : Fin j) (σ : X → X) (hσ : Function.Involutive σ) (g : (Fin j → X) → M) :
    ∑ α, g α = ∑ β, g (Function.update β i (σ (β i))) := by
  have hinv : Function.Involutive (fun β : Fin j → X => Function.update β i (σ (β i))) := by
    intro β
    simp [hσ (β i)]
  exact (Equiv.sum_comp (Function.Involutive.toPerm _ hinv) g).symm

private lemma sum_jmW_slotE_eq_sum_sub (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (c d : Fin n) (F : Arr V n j)
    (i : Fin j) :
    ∑ α, jmW E α (factorAction i c d F α) =
      ∑ α, ((if d = (α i).1 then jmW E (Function.update α i (c, (α i).2)) else 0) -
        (if (α i).2 = c then jmW E (Function.update α i ((α i).1, d)) else 0)) (F α) := by
  simp only [jm_positionE_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_eq_sum_update_involutive i (fun x : Fin n × Fin n => (Equiv.swap c d x.1, x.2)) (by intro x; simp)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rcases hb : β i with ⟨a, b⟩
    have hβ : Function.update β i (a, b) = β := by rw [← hb]; exact Function.update_eq_self i β
    by_cases h : a = d
    · subst h
      simp [hb, hβ]
    · have h' : d ≠ a := Ne.symm h
      simp [hb, h, h', Equiv.swap_apply_eq_iff]
  · rw [sum_eq_sum_update_involutive i (fun x : Fin n × Fin n => (x.1, Equiv.swap c d x.2)) (by intro x; simp)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rcases hb : β i with ⟨a, b⟩
    have hβ : Function.update β i (a, b) = β := by rw [← hb]; exact Function.update_eq_self i β
    by_cases h : b = c
    · subst h
      simp [hb, hβ]
    · simp [hb, h, Equiv.swap_apply_eq_iff]

theorem jm_theta_equiv (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {j : ℕ} (c d : Fin n)
    (F : Arr V n j) : thetaA E j (arrE E j c d F) = E c d (thetaA E j F) := by
  rw [jm_thetaA_apply, jm_thetaA_apply]
  simp only [jm_arrE_apply, map_add, map_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [sum_jmW_slotE_eq_sum_sub]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have h2 := congrArg (fun T : Module.End ℂ V => T (F α)) (jm_deriv E hE c d j α)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]
  simp only [LinearMap.sub_apply]

end Arrays

section Transfer
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

def mapArr (ι : V →ₗ[ℂ] V') (n j : ℕ) : Arr V n j →ₗ[ℂ] Arr V' n j :=
  arrTo V' n j ∘ₗ (LinearMap.pi fun α : Fin j → Fin n × Fin n =>
    ι ∘ₗ LinearMap.proj (R := ℂ) (φ := fun _ : Fin j → Fin n × Fin n => V) α) ∘ₗ arrOf V n j

theorem mapArr_apply (ι : V →ₗ[ℂ] V') {j : ℕ} (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    mapArr ι n j F α = ι (F α) := by
  simp [mapArr, arrTo, arrOf]

variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V')
  (ι : V →ₗ[ℂ] V') (u : V)

theorem kSpan_map (hι : ∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) :
    kSpan ε E' (ι u) = (kSpan ε E u).map ι := by
  apply le_antisymm
  · apply compactSpan_le_of_mem ε E' (Submodule.mem_map_of_mem (mem_compactSpan_self ε E u))
    intro c d hcd y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hι c d hcd x hx]
    exact Submodule.mem_map_of_mem (compactSpan_isCompactInvariant ε E u c d hcd x hx)
  · rw [Submodule.map_le_iff_le_comap]
    have hS : KStable ε E (kSpan ε E u ⊓ (kSpan ε E' (ι u)).comap ι) := by
      intro c d hcd x hx
      rw [Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
      refine ⟨compactSpan_isCompactInvariant ε E u c d hcd x hx.1, ?_⟩
      rw [hι c d hcd x hx.1]
      exact compactSpan_isCompactInvariant ε E' (ι u) c d hcd _ hx.2
    have hu : u ∈ kSpan ε E u ⊓ (kSpan ε E' (ι u)).comap ι :=
      Submodule.mem_inf.mpr ⟨mem_compactSpan_self ε E u, mem_compactSpan_self ε E' (ι u)⟩
    exact (compactSpan_le_of_mem ε E hu hS).trans inf_le_right

private lemma mem_arrV0_iff_forall_mem_kSpan {W : Type} [AddCommGroup W] [Module ℂ W] {j : ℕ} (e : Fin n → Bool)
    (D : Fin n → Fin n → Module.End ℂ W) (w : W) (F : Arr W n j) :
    F ∈ arrV0 e D w j ↔ ∀ α, F α ∈ (if ∀ i, e (α i).1 ≠ e (α i).2 then kSpan e D w else ⊥) := by
  simp only [arrV0, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

theorem val_mem {j : ℕ} (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) (α : Fin j → Fin n × Fin n) :
    F α ∈ kSpan ε E u := by
  have h := (mem_arrV0_iff_forall_mem_kSpan ε E u F).mp hF α
  by_cases hc : ∀ i, ε (α i).1 ≠ ε (α i).2
  · rwa [if_pos hc] at h
  · rw [if_neg hc, Submodule.mem_bot] at h
    rw [h]
    exact Submodule.zero_mem _

theorem mapArr_mem (hι : ∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x))
    {j : ℕ} (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) : mapArr ι n j F ∈ arrV0 ε E' (ι u) j := by
  rw [mem_arrV0_iff_forall_mem_kSpan] at hF ⊢
  intro α
  rw [mapArr_apply]
  have h := hF α
  by_cases hc : ∀ i, ε (α i).1 ≠ ε (α i).2
  · rw [if_pos hc] at h ⊢
    rw [kSpan_map ε E E' ι u hι]
    exact Submodule.mem_map_of_mem h
  · rw [if_neg hc, Submodule.mem_bot] at h ⊢
    rw [h, map_zero]

theorem mapArr_arrE (hι : ∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x))
    {j : ℕ} (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) (c d : Fin n) (hcd : ε c = ε d) :
    mapArr ι n j (arrE E j c d F) = arrE E' j c d (mapArr ι n j F) := by
  refine PiLp.ext (fun α => ?_)
  simp only [mapArr_apply, jm_arrE_apply, map_add, map_sum]
  rw [hι c d hcd _ (val_mem ε E u F hF α)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [jm_positionE_apply, jm_positionE_apply, map_sub]
  split_ifs <;> simp [mapArr_apply]

theorem mapArr_perm {j : ℕ} (F : Arr V n j) (s : Equiv.Perm (Fin j)) :
    mapArr ι n j (permArr V n s F) = permArr V' n s (mapArr ι n j F) := by
  refine PiLp.ext (fun α => ?_)
  simp [mapArr_apply, permArr, arrTo, arrOf]

theorem at1_sliceLin {j : ℕ} (F : Arr V n (j + 1)) (α' : Fin j → Fin n × Fin n) (a b : Fin n) :
    at1 (sliceLin V n α' F) a b = F (Fin.cons (a, b) α') := by
  simp [at1, sliceLin, arrTo, arrOf]

theorem theta_slices {j : ℕ} (F : Arr V n (j + 1)) :
    thetaA E' (j + 1) (mapArr ι n (j + 1) F) =
      ∑ α' : Fin j → Fin n × Fin n, ew E' (List.ofFn α').reverse
        (∑ a, ∑ b, E' a b (ι (at1 (sliceLin V n α' F) a b))) := by
  rw [jm_thetaA_apply]
  simp only [mapArr_apply]
  rw [← (Fin.consEquiv fun _ => Fin n × Fin n).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [at1_sliceLin]
  simp [jmW, List.ofFn_succ, jm_ew_append, ew, Fin.consEquiv]

theorem ew_mem_pfil (hE : GlRel E) (x : V) (hx : x ∈ kSpan ε E u) (w : List (Fin n × Fin n)) :
    ew E w x ∈ pfil ε E u w.length := by
  have hp := pfilFacts V n ε E u hE
  induction w with
  | nil =>
    simp only [ew, List.length_nil, Module.End.one_apply]
    rw [hp.1]
    exact hx
  | cons p w ih =>
    simp only [ew, List.length_cons, Module.End.mul_apply]
    exact hp.2.2.2.1 _ p.1 p.2 _ ih

end Transfer

theorem uniqAlg : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (E' : Fin n → Fin n → Module.End ℂ V') (ι : V →ₗ[ℂ] V') (ev : V' →ₗ[ℂ] V), GlRel E' → (∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) → (∀ y, ev y ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ y, ev (E' c d y) = E c d (ev y)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E' a b (ι (at1 G a b)) = 0) → (∀ x ∈ kSpan ε E u, ev (ι x) = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ kSpan ε E u, ev (ew E' w (ι x)) = 0 := by
  intro V _ _ n ε E lam g u hE hU hK hfd hgap hg V' _ _ E' ι ev hE' hι hev hevE hVm hevι
  have hPf : ∀ k : ℕ, (∀ m ≤ k, ∀ F ∈ arrV0 ε E u m, ev (thetaA E' m (mapArr ι n m F)) = 0) →
      ∀ y ∈ pfil ε E' (ι u) k, ev y = 0 := by
    intro k hD
    intro y hy
    have hle : pfil ε E' (ι u) k ≤ LinearMap.ker ev := by
      unfold pfil
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hnc, y, hy, rfl⟩
      rw [kSpan_map ε E E' ι u hι, Submodule.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      let α0 : Fin w.reverse.length → Fin n × Fin n := w.reverse.get
      have hw0 : ew E' w = jmW E' α0 := by
        show ew E' w = ew E' (List.ofFn w.reverse.get).reverse
        rw [List.ofFn_get, List.reverse_reverse]
      have hc0 : ∀ i, ε (α0 i).1 ≠ ε (α0 i).2 := fun i =>
        hnc _ (List.mem_reverse.mp (List.get_mem _ _))
      let F : Arr V n w.reverse.length := WithLp.toLp 2 (fun α => if α = α0 then z else 0)
      have hF : F ∈ arrV0 ε E u w.reverse.length := by
        rw [mem_arrV0_iff_forall_mem_kSpan]
        intro α
        by_cases h : α = α0
        · rw [h, if_pos hc0]
          simpa [F] using hz
        · simp [F, h]
      have hθ : thetaA E' _ (mapArr ι n _ F) = jmW E' α0 (ι z) := by
        rw [jm_thetaA_apply, Finset.sum_eq_single α0]
        · simp [mapArr_apply, F]
        · intro b _ hb
          simp [mapArr_apply, F, hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have h0 := hD _ (by simpa using hw) F hF
      rw [hθ, ← hw0] at h0
      exact h0
    exact hle hy
  have hD : ∀ m, ∀ F ∈ arrV0 ε E u m, ev (thetaA E' m (mapArr ι n m F)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero =>
        intro F hF
        rw [jm_thetaA_apply, Fintype.sum_unique, jmW_zero, Module.End.one_apply, mapArr_apply]
        exact hevι _ (val_mem ε E u F hF _)
      | succ j =>
        intro F hF
        have hC : ∀ y ∈ pfil ε E' (ι u) j, ev y = 0 :=
          hPf j (fun m hm => ih m (Nat.lt_succ_of_le hm))
        refine GlobalTheory.T.symmetric_kMap_eq_zero_of_vminus_slices V n ε E lam g u j hE hU hK hfd hgap hg
          (ev ∘ₗ thetaA E' (j + 1) ∘ₗ mapArr ι n (j + 1)) ?_ ?_ ?_ ?_ F hF
        · intro G _
          exact hev _
        · intro c d hcd G hG
          simp only [LinearMap.comp_apply]
          rw [mapArr_arrE ε E E' ι u hι G hG c d hcd, jm_theta_equiv E' hE', hevE c d hcd]
        · intro G hG s
          simp only [LinearMap.comp_apply]
          rw [mapArr_perm ι G s, ← sub_eq_zero, ← map_sub]
          exact hC _ ((thetaFil V' n ε E' (ι u) hE').2.2 j _ (mapArr_mem ε E E' ι u hι G hG) s)
        · intro G _ hsl
          simp only [LinearMap.comp_apply]
          rw [theta_slices E' ι G]
          simp [hVm _ (hsl _)]
  intro w x hx
  have hx' : ι x ∈ kSpan ε E' (ι u) := by
    rw [kSpan_map ε E E' ι u hι]
    exact Submodule.mem_map_of_mem hx
  exact hPf w.length (fun m _ => hD m) _
    (ew_mem_pfil ε E' (ι u) hE' (ι x) hx' w)

end GlobalTheory.Jet.UniqAlg
