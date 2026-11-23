import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

def wOp (E : Fin n → Fin n → Module.End ℂ M) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] Module.End ℂ M :=
  Finsupp.linearCombination ℂ (wordE E)

def lOp (E : Fin n → Fin n → Module.End ℂ M) : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] Module.End ℂ M :=
  Finsupp.linearCombination ℂ (fun q => E q.1 q.2)

theorem wordE_cons_mul (E : Fin n → Fin n → Module.End ℂ M) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    wordE E (p :: w) = E p.1 p.2 * wordE E w := by
  simp [wordE]

theorem wOp_mapDomain_cons (E : Fin n → Fin n → Module.End ℂ M) (p : Fin n × Fin n)
    (L : List (Fin n × Fin n) →₀ ℂ) :
    wOp E (Finsupp.mapDomain (p :: ·) L) = E p.1 p.2 * wOp E L := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy, mul_add]
  | single w r =>
    rw [Finsupp.mapDomain_single]
    simp [wOp, Finsupp.linearCombination_single, wordE_cons_mul]

theorem wOp_mapDomain_letter (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n))
    (l : Fin n × Fin n →₀ ℂ) :
    wOp E (Finsupp.mapDomain (· :: w) l) = lOp E l * wordE E w := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy, add_mul]
  | single q r =>
    rw [Finsupp.mapDomain_single]
    simp [wOp, lOp, Finsupp.linearCombination_single, wordE_cons_mul]

theorem lOp_adL (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) (p : Fin n × Fin n) :
    lOp E (adL a b p) = E a b * E p.1 p.2 - E p.1 p.2 * E a b := by
  rw [hE a b p.1 p.2]
  unfold adL
  split_ifs <;> simp [lOp, Finsupp.linearCombination_single]

theorem wOp_adLW (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    ∀ w, wOp E (adLW a b w) = E a b * wordE E w - wordE E w * E a b
  | [] => by simp [adLW, wordE]
  | p :: w => by
    rw [adLW, map_add, wOp_mapDomain_letter, wOp_mapDomain_cons, wOp_adLW E hE a b w, lOp_adL E hE,
      wordE_cons_mul]
    noncomm_ring

section Lift

variable (V : Submodule ℂ M)

def Bc (c : Fin n) (v : V) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] KS (n := n) V :=
  Finsupp.linearCombination ℂ (fun w' => Finsupp.single (w', c) v)

theorem Bc_single (c : Fin n) (v : V) (w : List (Fin n × Fin n)) (r : ℂ) :
    Bc V c v (Finsupp.single w r) = Finsupp.single (w, c) (r • v) := by
  simp [Bc, Finsupp.linearCombination_single, Finsupp.smul_single]

theorem sum_eq_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    (∑ w' ∈ L.support, L w' • Finsupp.lsingle (R := ℂ) (M := V) (w', c)) v = Bc V c v L := by
  simp [Bc, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]

variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (hV : IsKStableSub ε E V)

theorem sA_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    sA ε E V hV a b (Finsupp.single (w, c) v) =
      Bc V c v (adLW a b w) +
      (if h : ε a = ε b then Finsupp.single (w, c) ((E a b).restrict (fun v hv => hV a b h v hv) v) else 0) +
      (if c = b then Finsupp.single (w, a) v else 0) := by
  simp only [sA, Finsupp.lsum_single, LinearMap.add_apply, sum_eq_Bc]
  congr 1
  · congr 1
    split_ifs <;> simp
  · split_ifs <;> simp

theorem sT_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    sT E V (Bc V c v L) = Pi.single c (wOp E L v) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply, Pi.single_add]
  | single w r =>
    rw [Bc_single, sT_single]
    simp [wOp, Finsupp.linearCombination_single, Pi.single_smul]

theorem sθ_Bc (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) (c : Fin n) (v : V)
    (L : List (Fin n × Fin n) →₀ ℂ) :
    sθ V EM φ ℓ (Bc V c v L) = Pi.single c (ℓ v • wOp EM L φ) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply, smul_add, Pi.single_add]
  | single w r =>
    rw [Bc_single, sθ_single]
    simp [wOp, Finsupp.linearCombination_single, Pi.single_smul, smul_smul, mul_comm]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (d : Fin n) :
    tensV E a b f d = E a b (f d) + if d = a then f b else 0 := by
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval]
  split_ifs <;> simp

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sA_single, dif_pos hab, map_add, map_add, sT_Bc, wOp_adLW E hE, sT_single, sT_single]
    clear hE
    by_cases hcb : c = b
    on_goal 1 => subst hcb; rw [if_pos rfl, sT_single]
    on_goal 2 => rw [if_neg hcb, map_zero, add_zero]
    all_goals
      funext d
      simp only [Pi.add_apply, tensV_apply', LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.coe_restrict_apply, Pi.single_apply]
      split_ifs <;> subst_vars <;> simp_all

theorem sθ_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM)
    (ν Λ : Fin n → ℝ) (hφ : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ (a : Fin n) (v w : V), (w : M) = E a a v → ℓ w = ((Λ a : ℝ) : ℂ) * ℓ v) (a : Fin n)
    (x : KS (n := n) V) :
    sθ V EM φ ℓ (sA ε E V hV a a x) =
      tensV EM a a (sθ V EM φ ℓ x) + ((Λ a - ν a : ℝ) : ℂ) • sθ V EM φ ℓ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [sA_single, dif_pos rfl, map_add, map_add, sθ_Bc, wOp_adLW EM hEM, sθ_single, sθ_single]
    have hl : ℓ ((E a a).restrict (fun v hv => hV a a rfl v hv) v) = ((Λ a : ℝ) : ℂ) * ℓ v :=
      hℓ a v _ rfl
    rw [hl]
    clear hl hℓ hEM
    by_cases hca : c = a
    on_goal 1 => subst hca; rw [if_pos rfl, sθ_single]
    on_goal 2 => rw [if_neg hca, map_zero, add_zero]
    all_goals
      funext d
      simp only [Pi.add_apply, Pi.smul_apply, tensV_apply', LinearMap.sub_apply, Module.End.mul_apply, hφ,
        map_smul, Pi.single_apply]
      split_ifs <;> subst_vars <;> simp_all <;> module

theorem sES_single (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    sES V (Finsupp.single (w, c) v) = ∑ d : Fin n, Finsupp.single ((c, d) :: w, d) v := by
  simp [sES, Finsupp.lsum_single, LinearMap.sum_apply]

theorem sES_Bc (c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    sES V (Bc V c v L) = ∑ d : Fin n, Bc V d v (Finsupp.mapDomain ((c, d) :: ·) L) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.mapDomain_add, Finset.sum_add_distrib]
  | single w r => simp only [Bc_single, sES_single, Finsupp.mapDomain_single]

theorem adLW_cons (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) = Finsupp.mapDomain (· :: w) (adL a b p) + Finsupp.mapDomain (p :: ·) (adLW a b w) := by
  rw [adLW]

theorem mapDomain_neg' {α β : Type*} (f : α → β) (x : α →₀ ℂ) :
    Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x := by
  simpa [Finsupp.lmapDomain_apply] using (Finsupp.lmapDomain ℂ ℂ f).map_neg x

theorem Bc_adL (a b c d : Fin n) (v : V) (w : List (Fin n × Fin n)) :
    Bc V d v (Finsupp.mapDomain (· :: w) (adL a b (c, d))) =
      (if b = c then Finsupp.single ((a, d) :: w, d) v else 0) -
        (if d = a then Finsupp.single ((c, b) :: w, d) v else 0) := by
  simp only [adL]
  split_ifs <;> simp [Finsupp.mapDomain_sub, mapDomain_neg', Finsupp.mapDomain_single, Bc_single, map_neg]

theorem sA_comm_sES (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (hab : ε a = ε b) : Commute (sA ε E V hV a b) (sES V) := by
  show sA ε E V hV a b * sES V = sES V * sA ε E V hV a b
  apply Finsupp.lhom_ext
  rintro ⟨w, c⟩ v
  simp only [Module.End.mul_apply]
  rw [sES_single, map_sum, sA_single, dif_pos hab, map_add, map_add, sES_Bc, sES_single]
  simp only [sA_single, dif_pos hab, adLW_cons, map_add, Bc_adL, Finset.sum_add_distrib]
  by_cases hcb : c = b
  · subst hcb
    simp [sES_single, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    abel
  · simp [hcb, Ne.symm hcb, Finset.sum_ite_eq']
    abel

def tL (a b : Fin n) : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] (Fin n × Fin n →₀ ℂ) :=
  Finsupp.linearCombination ℂ (adL a b)

def TW (a b : Fin n) : (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (adLW a b)

def kap : (Fin n × Fin n →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) →ₗ[ℂ] (List (Fin n × Fin n) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun p => Finsupp.lmapDomain ℂ ℂ (p :: ·))

theorem tL_single (a b : Fin n) (p : Fin n × Fin n) (r : ℂ) :
    tL a b (Finsupp.single p r) = r • adL a b p := by
  simp [tL, Finsupp.linearCombination_single]

theorem TW_single (a b : Fin n) (w : List (Fin n × Fin n)) (r : ℂ) :
    TW a b (Finsupp.single w r) = r • adLW a b w := by
  simp [TW, Finsupp.linearCombination_single]

theorem kap_single_left (p : Fin n × Fin n) (r : ℂ) (L : List (Fin n × Fin n) →₀ ℂ) :
    kap (Finsupp.single p r) L = r • Finsupp.mapDomain (p :: ·) L := by
  simp [kap, Finsupp.linearCombination_single, Finsupp.lmapDomain_apply]

theorem kap_single_right (l : Fin n × Fin n →₀ ℂ) (w : List (Fin n × Fin n)) :
    kap l (Finsupp.single w 1) = Finsupp.mapDomain (· :: w) l := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, Finsupp.mapDomain_add]
  | single q r => simp [kap_single_left, Finsupp.mapDomain_single]

theorem kap_single_single (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (r s : ℂ) :
    kap (Finsupp.single p r) (Finsupp.single w s) = Finsupp.single (p :: w) (r * s) := by
  simp [kap_single_left, Finsupp.mapDomain_single, Finsupp.smul_single]

theorem adLW_cons' (a b : Fin n) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    adLW a b (p :: w) = kap (adL a b p) (Finsupp.single w 1) + kap (Finsupp.single p 1) (adLW a b w) := by
  rw [adLW_cons, kap_single_right, kap_single_left, one_smul]

theorem TW_kap (a b : Fin n) (l : Fin n × Fin n →₀ ℂ) (L : List (Fin n × Fin n) →₀ ℂ) :
    TW a b (kap l L) = kap (tL a b l) L + kap l (TW a b L) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]; abel
  | single p r =>
    induction L using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; abel
    | single w s =>
      rw [kap_single_single, TW_single, tL_single, TW_single, adLW_cons', map_smul, LinearMap.smul_apply,
        map_smul]
      rw [← Finsupp.smul_single_one p r, ← Finsupp.smul_single_one w s]
      simp only [map_smul, LinearMap.smul_apply, smul_add, smul_smul]
      rw [mul_comm s r]

theorem tL_rel_one (a b c d : Fin n) (p : Fin n × Fin n) :
    tL a b (adL c d p) - tL c d (adL a b p) =
      (if b = c then adL a d p else 0) - (if d = a then adL c b p else 0) := by
  obtain ⟨p1, p2⟩ := p
  simp only [adL, map_sub, apply_ite (tL a b), apply_ite (tL c d), map_zero, tL_single, one_smul]
  split_ifs <;> subst_vars <;> simp_all <;> abel

theorem tL_rel (a b c d : Fin n) (l : Fin n × Fin n →₀ ℂ) :
    tL a b (tL c d l) - tL c d (tL a b l) =
      (if b = c then tL a d l else 0) - (if d = a then tL c b l else 0) := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add]
    have e : ∀ x1 x2 y1 y2 : Fin n × Fin n →₀ ℂ, x1 + y1 - (x2 + y2) = (x1 - x2) + (y1 - y2) := by
      intros; abel
    rw [e, hx, hy]
    split_ifs <;> abel
  | single p r =>
    simp only [tL_single, map_smul]
    rw [← smul_sub, tL_rel_one]
    split_ifs <;> simp [smul_sub]

theorem TW_rel_word (a b c d : Fin n) : ∀ w : List (Fin n × Fin n),
    TW a b (TW c d (Finsupp.single w 1)) - TW c d (TW a b (Finsupp.single w 1)) =
      (if b = c then TW a d (Finsupp.single w 1) else 0) - (if d = a then TW c b (Finsupp.single w 1) else 0)
  | [] => by simp [TW_single, adLW]
  | p :: w => by
    have hw : Finsupp.single (p :: w) (1 : ℂ) = kap (Finsupp.single p 1) (Finsupp.single w 1) := by
      rw [kap_single_single, mul_one]
    have ih := TW_rel_word a b c d w
    have hl := tL_rel a b c d (Finsupp.single p 1)
    rw [hw]
    simp only [TW_kap, map_add]
    have e : ∀ (l : Fin n × Fin n →₀ ℂ) (L : List (Fin n × Fin n) →₀ ℂ),
        kap (tL a b (tL c d l)) L + kap (tL c d l) (TW a b L) +
            (kap (tL a b l) (TW c d L) + kap l (TW a b (TW c d L))) -
          (kap (tL c d (tL a b l)) L + kap (tL a b l) (TW c d L) +
            (kap (tL c d l) (TW a b L) + kap l (TW c d (TW a b L)))) =
        kap (tL a b (tL c d l) - tL c d (tL a b l)) L + kap l (TW a b (TW c d L) - TW c d (TW a b L)) := by
      intro l L
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [e, ih, hl]
    split_ifs <;> simp <;> abel

theorem TW_rel (a b c d : Fin n) (L : List (Fin n × Fin n) →₀ ℂ) :
    TW a b (TW c d L) - TW c d (TW a b L) =
      (if b = c then TW a d L else 0) - (if d = a then TW c b L else 0) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add]
    have e : ∀ x1 x2 y1 y2 : List (Fin n × Fin n) →₀ ℂ, x1 + y1 - (x2 + y2) = (x1 - x2) + (y1 - y2) := by
      intros; abel
    rw [e, hx, hy]
    split_ifs <;> abel
  | single w r =>
    rw [← Finsupp.smul_single_one w r]
    simp only [map_smul]
    rw [← smul_sub, TW_rel_word]
    split_ifs <;> simp [smul_sub]

def Dm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p =>
    ∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.lsingle (R := ℂ) (M := V) (w', p.2)

def eV (a b : Fin n) : Module.End ℂ V :=
  if h : ε a = ε b then (E a b).restrict (fun v hv => hV a b h v hv) else 0

def Fm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => Finsupp.lsingle p ∘ₗ eV V ε E hV a b

def Gm (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => if p.2 = b then Finsupp.lsingle (R := ℂ) (M := V) (p.1, a) else 0

theorem Dm_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    Dm V a b (Finsupp.single (w, c) v) = Bc V c v (TW a b (Finsupp.single w 1)) := by
  simp only [Dm, Finsupp.lsum_single, sum_eq_Bc, TW_single, one_smul]

theorem Fm_single (a b : Fin n) (p : List (Fin n × Fin n) × Fin n) (v : V) :
    Fm V ε E hV a b (Finsupp.single p v) = Finsupp.single p (eV V ε E hV a b v) := by
  simp [Fm, Finsupp.lsum_single]

theorem Gm_single (a b : Fin n) (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    Gm V a b (Finsupp.single (w, c) v) = if c = b then Finsupp.single (w, a) v else 0 := by
  simp only [Gm, Finsupp.lsum_single]
  split_ifs <;> simp

theorem Bc_smul_v (c : Fin n) (v : V) (r : ℂ) (L : List (Fin n × Fin n) →₀ ℂ) :
    Bc V c (r • v) L = r • Bc V c v L := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | single w s => simp [Bc_single, Finsupp.smul_single, smul_smul, mul_comm]

theorem Dm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Dm V a b (Bc V c v L) = Bc V c v (TW a b L) := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single w r =>
    rw [Bc_single, ← Finsupp.smul_single, map_smul, Dm_single, ← Finsupp.smul_single_one w r, map_smul,
      map_smul]

theorem Fm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Fm V ε E hV a b (Bc V c v L) = Bc V c (eV V ε E hV a b v) L := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single w r => simp [Bc_single, Fm_single, map_smul]

theorem Gm_Bc (a b c : Fin n) (v : V) (L : List (Fin n × Fin n) →₀ ℂ) :
    Gm V a b (Bc V c v L) = if c = b then Bc V a v L else 0 := by
  induction L using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]; split_ifs <;> simp
  | single w r => rw [Bc_single, Gm_single, Bc_single]

theorem sA_eq (a b : Fin n) : sA ε E V hV a b = Dm V a b + Fm V ε E hV a b + Gm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c⟩ v
  rw [sA_single, LinearMap.add_apply, LinearMap.add_apply, Dm_single, TW_single, one_smul, Fm_single,
    Gm_single]
  congr 2
  simp only [eV]
  split_ifs <;> simp

theorem eV_coe (a b : Fin n) (v : V) :
    (eV V ε E hV a b v : M) = if ε a = ε b then E a b v else 0 := by
  unfold eV
  split_ifs <;> simp [LinearMap.coe_restrict_apply]

theorem eV_rel (hE : IsGlRep E) (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    eV V ε E hV a b * eV V ε E hV c d - eV V ε E hV c d * eV V ε E hV a b =
      (if b = c then eV V ε E hV a d else 0) - (if d = a then eV V ε E hV c b else 0) := by
  have had : b = c → ε a = ε d := fun h => by rw [hab, h]; exact hcd
  have hcb : d = a → ε c = ε b := fun h => by rw [hcd, h]; exact hab
  refine LinearMap.ext fun v => Subtype.ext ?_
  have kv := LinearMap.congr_fun (hE a b c d) (v : M)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at kv
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, eV_coe, if_pos hab, if_pos hcd]
  rw [kv]
  rcases em (b = c) with h1 | h1 <;> rcases em (d = a) with h2 | h2
  · simp [h1, h2, eV_coe, had h1, hcb h2]
  · simp [h1, h2, eV_coe, had h1]
  · simp [h1, h2, eV_coe, hcb h2]
  · simp [h1, h2]

theorem Dm_rel (a b c d : Fin n) :
    Dm V a b * Dm V c d - Dm V c d * Dm V a b =
      (if b = c then Dm V a d else 0) - (if d = a then Dm V c b else 0) := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Dm_single, Dm_Bc, ← map_sub, TW_rel_word]
  split_ifs <;> simp [Dm_single]

theorem Fm_rel (hE : IsGlRep E) (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    Fm V ε E hV a b * Fm V ε E hV c d - Fm V ε E hV c d * Fm V ε E hV a b =
      (if b = c then Fm V ε E hV a d else 0) - (if d = a then Fm V ε E hV c b else 0) := by
  apply Finsupp.lhom_ext
  intro p v
  have key := LinearMap.congr_fun (eV_rel V ε E hV hE a b c d hab hcd) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Fm_single, ← Finsupp.single_sub, key]
  split_ifs <;> simp [Fm_single]

theorem Gm_rel (a b c d : Fin n) :
    Gm V a b * Gm V c d - Gm V c d * Gm V a b =
      (if b = c then Gm V a d else 0) - (if d = a then Gm V c b else 0) := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Gm_single]
  by_cases h1 : c0 = d <;> by_cases h2 : c0 = b <;>
    simp only [h1, h2, if_true, if_false, map_zero, Gm_single] <;> (try split_ifs) <;> subst_vars <;>
    (try simp only [Gm_single, map_zero, sub_zero, zero_sub]) <;> (try split_ifs) <;> subst_vars <;> simp_all

theorem Dm_Fm (a b c d : Fin n) : Dm V a b * Fm V ε E hV c d = Fm V ε E hV c d * Dm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Fm_single, Dm_single, Fm_Bc]

theorem Dm_Gm (a b c d : Fin n) : Dm V a b * Gm V c d = Gm V c d * Dm V a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Gm_single, Dm_single, Gm_Bc]
  split_ifs <;> simp [Dm_single]

theorem Fm_Gm (a b c d : Fin n) : Fm V ε E hV a b * Gm V c d = Gm V c d * Fm V ε E hV a b := by
  apply Finsupp.lhom_ext
  rintro ⟨w, c0⟩ v
  simp only [Module.End.mul_apply, Gm_single, Fm_single]
  split_ifs <;> simp [Fm_single]

theorem sA_isKRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (sA ε E V hV) := by
  intro a b c d hab hcd
  simp only [sA_eq]
  have e : ∀ D1 F1 G1 D2 F2 G2 : Module.End ℂ (KS (n := n) V),
      (D1 + F1 + G1) * (D2 + F2 + G2) - (D2 + F2 + G2) * (D1 + F1 + G1) =
        (D1 * D2 - D2 * D1) + (F1 * F2 - F2 * F1) + (G1 * G2 - G2 * G1) + (D1 * F2 - F2 * D1) +
          (D1 * G2 - G2 * D1) + (F1 * G2 - G2 * F1) - (D2 * F1 - F1 * D2) - (D2 * G1 - G1 * D2) -
            (F2 * G1 - G1 * F2) := by
    intros; noncomm_ring
  rw [e, Dm_rel, Fm_rel V ε E hV hE a b c d hab hcd, Gm_rel, Dm_Fm, Dm_Gm, Fm_Gm, Dm_Fm, Dm_Gm, Fm_Gm]
  split_ifs <;> abel

end Lift

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas
