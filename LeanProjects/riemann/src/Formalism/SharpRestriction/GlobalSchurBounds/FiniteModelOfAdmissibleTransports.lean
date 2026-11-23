import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.LocalRingCardinality.Lemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Pc

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField
open Formalism.LogVandermondeBounds.product_first_zeroth_parts (pair opU opD nmV nmP trV trP opGs opGsStar opFF diaP diaV)

variable (D : D7) (u : D.what₂.Word)

abbrev Val (i : ℕ) : Type := (D.mem u).C.Y i → ℂ

def fnl {k M : Type} [Field k] [AddCommGroup M] [Module k M] {r : ℕ} (e : M ≃ₗ[k] (Fin r → k)) :
    (Fin r → k) ≃ₗ[k] Module.Dual k M := (dotProductEquiv k (Fin r)).trans e.dualMap

lemma fnl_apply {k M : Type} [Field k] [AddCommGroup M] [Module k M] {r : ℕ} (e : M ≃ₗ[k] (Fin r → k))
    (f : Fin r → k) (y : M) : fnl e f y = pair f (e y) := rfl

structure Unf (i : ℕ) (v : (D.mem u).A.vT) where
  Lc : Type
  [LcFin : Fintype Lc]

  nL : Lc → ℕ
  nL_pos : ∀ Λ, 0 < nL Λ

  ipL : Lc → (Val D u i →ₗ⋆[ℂ] Val D u i →ₗ[ℂ] ℂ)

  cf : Lc → (Fin (D.R.N i) → (D.mem u).A.Fv v) → (D.mem u).C.cls i

  tf : Lc → (Fin (D.R.N i) → (D.mem u).A.Fv v) → (Val D u i ≃ₗ[ℂ] Val D u i)

  cx : Lc → (Fin (D.R.N i) → (D.mem u).A.Fv v) → (D.mem u).C.cls i

  tx : Lc → (Fin (D.R.N i) → (D.mem u).A.Fv v) → (Val D u i ≃ₗ[ℂ] Val D u i)
  cf_surj : ∀ c, ∃ Λ f, f ≠ 0 ∧ cf Λ f = c
  cx_surj : ∀ c, ∃ Λ x, x ≠ 0 ∧ cx Λ x = c

  up_tie : ∀ Λ f, f ≠ 0 →
    ∃ e : (D.fm u).lv i v (cf Λ f) ≃ₗ[(D.mem u).A.Fv v] (Fin (D.R.N i) → (D.mem u).A.Fv v),
      (D.fm u).fv i v (cf Λ f) = fnl e f ∧
      ∀ φ ∈ (D.fm u).Fi i, ∀ x, (D.fm u).fv i v (cf Λ f) x = 1 →
        tf Λ f ((D.fm u).upT i v (cf Λ f) x (φ ((D.fm u).up i v (cf Λ f) x))) = tx Λ (e x) (φ (cx Λ (e x)))

  dn_tie : ∀ Λ x, x ≠ 0 →
    ∃ e : (D.fm u).lk i v (cx Λ x) ≃ₗ[(D.mem u).A.Fv v] (Fin (D.R.N i) → (D.mem u).A.Fv v),
      e ((D.fm u).te i v (cx Λ x)) = x ∧
      ∀ φ ∈ (D.fm u).Fi i, ∀ f, f ≠ 0 →
        tx Λ x ((D.fm u).dnT i v (cx Λ x) (fnl e f) (φ ((D.fm u).dn i v (cx Λ x) (fnl e f)))) = tf Λ f (φ (cf Λ f))

  dil_f : ∀ Λ f, f ≠ 0 → ∀ a : ((D.mem u).A.Fv v)ˣ, ∀ φ ∈ (D.fm u).Fi i,
    tf Λ f ((D.fm u).dilT i v a (cf Λ f) (φ ((D.fm u).dil i v a (cf Λ f)))) =
      tf Λ ((a : (D.mem u).A.Fv v) • f) (φ (cf Λ ((a : (D.mem u).A.Fv v) • f)))

  unfoldDilationUnit : ∀ Λ x, x ≠ 0 → ∀ a : ((D.mem u).A.Fv v)ˣ, ∀ φ ∈ (D.fm u).Fi i,
    tx Λ x ((D.fm u).dilT i v a (cx Λ x) (φ ((D.fm u).dil i v a (cx Λ x)))) =
      tx Λ (((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x)
        (φ (cx Λ (((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x)))

  ip_f : ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i, (D.fm u).ipC i φ ψ =
    ∑ Λ, ((nL Λ : ℂ))⁻¹ * ∑ f ∈ Finset.univ.filter (fun f => f ≠ 0),
      ipL Λ (tf Λ f (φ (cf Λ f))) (tf Λ f (ψ (cf Λ f)))

  unfoldInnerProduct : ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i, (D.fm u).ipC i φ ψ =
    ∑ Λ, ((nL Λ : ℂ))⁻¹ * ∑ x ∈ Finset.univ.filter (fun x => x ≠ 0),
      ipL Λ (tx Λ x (φ (cx Λ x))) (tx Λ x (ψ (cx Λ x)))

attribute [instance] Unf.LcFin

variable {D u}

namespace Unf

variable {i : ℕ} {v : (D.mem u).A.vT} (H : Unf D u i v)

def P (Λ : H.Lc) (f : Fin (D.R.N i) → (D.mem u).A.Fv v) : Fn D u i →ₗ[ℂ] Val D u i :=
  (H.tf Λ f).toLinearMap ∘ₗ LinearMap.proj (H.cf Λ f)

def Q (Λ : H.Lc) (x : Fin (D.R.N i) → (D.mem u).A.Fv v) : Fn D u i →ₗ[ℂ] Val D u i :=
  (H.tx Λ x).toLinearMap ∘ₗ LinearMap.proj (H.cx Λ x)

lemma P_apply (Λ f) (φ : Fn D u i) : H.P Λ f φ = H.tf Λ f (φ (H.cf Λ f)) := rfl
lemma Q_apply (Λ x) (φ : Fn D u i) : H.Q Λ x φ = H.tx Λ x (φ (H.cx Λ x)) := rfl

lemma ext_Q {α β : Fn D u i} (h : ∀ Λ x, x ≠ 0 → H.Q Λ x α = H.Q Λ x β) : α = β := by
  funext c
  obtain ⟨Λ, x, hx, rfl⟩ := H.cx_surj c
  exact (H.tx Λ x).injective (h Λ x hx)

lemma ext_P {α β : Fn D u i} (h : ∀ Λ f, f ≠ 0 → H.P Λ f α = H.P Λ f β) : α = β := by
  funext c
  obtain ⟨Λ, f, hf, rfl⟩ := H.cf_surj c
  exact (H.tf Λ f).injective (h Λ f hf)

end Unf

lemma Uop_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) (c) : Uop D u i v φ c =
    ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv i v c => (D.fm u).fv i v c x = 1),
      (D.fm u).upT i v c x (φ ((D.fm u).up i v c x)) := by
  simp [LT.Uop]

lemma dn_sum_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) (c) : Dop D u i v φ c =
    ∑ g ∈ Finset.univ.filter (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
      (if g ((D.fm u).te i v c) = 1 then (1 : ℂ) else 0) • (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g)) := by
  simp only [Dop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearEquiv.coe_coe]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h : g ((D.fm u).te i v c) = 1
  · have : g ≠ 0 := by rintro rfl; simp at h
    simp [h, this]
  · simp [h]

lemma Eop_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) (c) : Eop D u i v φ c =
    ∑ g ∈ Finset.univ.filter (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
      (1 : ℂ) • (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g)) := by
  simp [Eop]

lemma FFop_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) (c) : FFop D u i v φ c =
    ∑ g ∈ Finset.univ.filter (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
      ((D.mem u).A.psiT v (g ((D.fm u).te i v c))) • (D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g)) := by
  simp [FFop]

lemma dia_apply (i : ℕ) (v : (D.mem u).A.vT) (a) (φ : Fn D u i) (c) :
    dia D u i v a φ c = (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) := rfl

namespace Unf

variable {i : ℕ} {v : (D.mem u).A.vT} (H : Unf D u i v)

lemma P_U {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {f} (hf : f ≠ 0) (y) :
    H.P Λ f (Uop D u i v φ) y = opU (fun x => H.Q Λ x φ y) f := by
  obtain ⟨e, he, ht⟩ := H.up_tie Λ f hf
  rw [P_apply, Uop_apply, map_sum, Finset.sum_apply]
  unfold opU
  refine Finset.sum_equiv e.toEquiv (fun x => ?_) (fun x hx => ?_)
  · simp [he, fnl_apply]
  · rw [ht φ hφ x (Finset.mem_filter.mp hx).2]; rfl

lemma Q_dn (s : (D.mem u).A.Fv v → ℂ) {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) :
    H.tx Λ x (∑ g ∈ Finset.univ.filter
        (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v (H.cx Λ x)) => g ≠ 0),
      s (g ((D.fm u).te i v (H.cx Λ x))) •
        (D.fm u).dnT i v (H.cx Λ x) g (φ ((D.fm u).dn i v (H.cx Λ x) g))) =
    ∑ f ∈ Finset.univ.filter (fun f => f ≠ 0), s (pair f x) • H.P Λ f φ := by
  obtain ⟨e, he, ht⟩ := H.dn_tie Λ x hx
  rw [map_sum]
  symm
  refine Finset.sum_equiv (fnl e).toEquiv (fun f => ?_) (fun f hf => ?_)
  · simp
  · have hf' : f ≠ 0 := (Finset.mem_filter.mp hf).2
    show _ = H.tx Λ x (s ((fnl e f) _) • _)
    rw [map_smul, fnl_apply, he]
    erw [ht φ hφ f hf']
    rfl

lemma Q_D {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (Dop D u i v φ) y = opD (fun f => H.P Λ f φ y) x := by
  rw [Q_apply, dn_sum_apply, H.Q_dn (fun t => if t = 1 then (1 : ℂ) else 0) hφ Λ hx, Finset.sum_apply]
  unfold opD
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h : pair f x = 1
  · have : f ≠ 0 := by rintro rfl; simp [pair] at h
    simp [h, this]
  · simp [h]

lemma Q_E {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (Eop D u i v φ) y = trP (fun f => H.P Λ f φ y) := by
  rw [Q_apply, Eop_apply, H.Q_dn (fun _ => (1 : ℂ)) hφ Λ hx, Finset.sum_apply]
  unfold trP
  simp

lemma Q_FF {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (FFop D u i v φ) y = opFF ((D.mem u).A.psiT v) (fun f => H.P Λ f φ y) x := by
  rw [Q_apply, FFop_apply, H.Q_dn (fun t => (D.mem u).A.psiT v t) hφ Λ hx, Finset.sum_apply]
  unfold opFF
  simp

lemma P_dia {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {f} (hf : f ≠ 0) (a) :
    H.P Λ f (dia D u i v a φ) = H.P Λ ((a : (D.mem u).A.Fv v) • f) φ := H.dil_f Λ f hf a φ hφ

lemma Q_dia {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (a) :
    H.Q Λ x (dia D u i v a φ) = H.Q Λ (((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • x) φ :=
  H.unfoldDilationUnit Λ x hx a φ hφ

lemma P_Nm {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {f} (hf : f ≠ 0) (y) :
    H.P Λ f (Nm D u i v φ) y = nmP (fun f => H.P Λ f φ y) f := by
  unfold Nm nmP diaP
  rw [LinearMap.sum_apply, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [H.P_dia hφ Λ hf a])

lemma Q_Nm {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (Nm D u i v φ) y = nmV (fun x => H.Q Λ x φ y) x := by
  unfold Nm nmV diaV
  rw [LinearMap.sum_apply, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [H.Q_dia hφ Λ hx a])

end Unf

lemma sum_upOperator_eq_card_pow_mul_sum {k : Type} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} (ψ : (Fin r → k) → ℂ) :
    trP (opU ψ) = (Fintype.card k : ℂ) ^ (r - 1) * trV ψ := by
  have h := Formalism.LogVandermondeBounds.product_first_zeroth_parts.up_down_operators_adjoint k r ℂ ψ (fun _ => 1)
  have h1 : ∑ f, opU ψ f * 1 = trP (opU ψ) := by
    unfold trP; rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases hf : f = 0
    · subst hf; simp [opU, pair]
    · simp [hf]
  have h2 : ∑ x, ψ x * opD (fun _ => (1 : ℂ)) x = (Fintype.card k : ℂ) ^ (r - 1) * trV ψ := by
    unfold trV; rw [Finset.mul_sum, Finset.sum_filter]; refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x = 0
    · subst hx; simp [opD, pair]
    · have := Formalism.LogVandermondeBounds.product_first_zeroth_parts.count1 hx (1 : k)
      simp [hx, opD, this]; ring
  rw [← h1, h, h2]

lemma gauss_units {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (F : kˣ → ℂ) :
    ∑ a : kˣ, ∑ b : kˣ, (ψ (a : k) * ψ (-(b : k))) * F (a * b⁻¹) = (Fintype.card k : ℂ) * F 1 - ∑ c, F c := by
  let Φ : (Fin 1 → k) → ℂ := fun f => if h : f 0 = 0 then 0 else F (Units.mk0 (f 0) h)
  have key : ∀ a : kˣ, Φ (fun _ => (a : k)) = F a := by intro a; simp [Φ]
  have h := Formalism.LogVandermondeBounds.product_first_zeroth_parts.gauss_operator_mul_adjoint_eq k 1 ψ hψ Φ (fun _ => ((1 : kˣ) : k))
  rw [key] at h
  rw [← (show nmP Φ (fun _ => ((1 : kˣ) : k)) = ∑ c, F c from by
    unfold nmP diaP
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← key c, show ((c : k) • fun _ : Fin 1 => ((1 : kˣ) : k)) = fun _ => (c : k) from by funext _; simp]), ← h]
  unfold opGs opGsStar
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← key (a * b⁻¹), AddChar.map_neg_eq_conj, mul_assoc,
    show (((b⁻¹ : kˣ) : k) • (a : k) • fun _ : Fin 1 => ((1 : kˣ) : k)) = fun _ => ((a * b⁻¹ : kˣ) : k) from by
      funext _; simp [mul_comm]]

lemma two_le_N (R : Ranks) (j : ℕ) : 2 ≤ R.N j := by
  have := R.m_add_three_le_k; unfold Ranks.N; omega

lemma T_ne (D : D7) (u : D.what₂.Word) : ((D.mem u).A.T : ℂ) ≠ 0 := by
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

namespace Unf

variable {i : ℕ} {v : (D.mem u).A.vT} (H : Unf D u i v)

omit H in
lemma cardC : (Fintype.card ((D.mem u).A.Fv v) : ℂ) = ((D.mem u).A.T : ℂ) := by
  rw [(D.mem u).A.card_Fv v]

include H

lemma Q_DU {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hU : Uop D u i v φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (Dop D u i v (Uop D u i v φ)) y = opD (opU (fun x => H.Q Λ x φ y)) x := by
  rw [H.Q_D hU Λ hx]; unfold opD; refine Finset.sum_congr rfl (fun f hf => ?_)
  have : f ≠ 0 := by rintro rfl; simpa [pair] using (Finset.mem_filter.mp hf).2
  exact H.P_U hφ Λ this y

lemma P_UD {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hD : Dop D u i v φ ∈ (D.fm u).Fi i) (Λ) {f} (hf : f ≠ 0) (y) :
    H.P Λ f (Uop D u i v (Dop D u i v φ)) y = opU (opD (fun f => H.P Λ f φ y)) f := by
  rw [H.P_U hD Λ hf]; unfold opU; refine Finset.sum_congr rfl (fun x hx => ?_)
  have : x ≠ 0 := by rintro rfl; simpa [pair] using (Finset.mem_filter.mp hx).2
  exact H.Q_D hφ Λ this y

lemma Q_trp {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hU : Uop D u i v φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) (y) :
    H.Q Λ x (trp D u i v φ) y = trV (fun x => H.Q Λ x φ y) := by
  unfold trp
  rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, LinearMap.comp_apply, H.Q_E hU Λ hx]
  have : trP (fun f => H.P Λ f (Uop D u i v φ) y) = trP (opU (fun x => H.Q Λ x φ y)) := by
    unfold trP; refine Finset.sum_congr rfl (fun f hf => ?_)
    exact H.P_U hφ Λ (Finset.mem_filter.mp hf).2 y
  rw [this, sum_upOperator_eq_card_pow_mul_sum, cardC, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ (T_ne D u))]

theorem DU {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hU : Uop D u i v φ ∈ (D.fm u).Fi i) :
    Dop D u i v (Uop D u i v φ) =
      ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • Nm D u i v φ
        + ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • trp D u i v φ := by
  apply H.ext_Q; intro Λ x hx; funext y
  rw [H.Q_DU hφ hU Λ hx, Formalism.LogVandermondeBounds.product_first_zeroth_parts.down_up_composition_formula _ _ ℂ (two_le_N D.R i) _ x hx, map_add, map_sub, map_smul,
    map_smul, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [H.Q_trp hφ hU Λ hx, H.Q_Nm hφ Λ hx, cardC]

section ram

variable {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hN : Nm D u i v φ = 0)
include hφ hN

lemma nmV_zero (Λ y) : ∀ x, x ≠ 0 → nmV (fun x => H.Q Λ x φ y) x = 0 := by
  intro x hx; rw [← H.Q_Nm hφ Λ hx, hN, map_zero]; rfl

lemma nmP_eq_zero_of_ne_zero (Λ y) : ∀ f, f ≠ 0 → nmP (fun f => H.P Λ f φ y) f = 0 := by
  intro f hf; rw [← H.P_Nm hφ Λ hf, hN, map_zero]; rfl

theorem trp_ram (hU : Uop D u i v φ ∈ (D.fm u).Fi i) : trp D u i v φ = 0 := by
  apply H.ext_Q; intro Λ x hx; funext y
  rw [H.Q_trp hφ hU Λ hx, ((Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramified_lattice_operator_identity _ _ ℂ).1 _ (H.nmV_zero hφ hN Λ y)).2.1, map_zero]; rfl

theorem DU_ram (hU : Uop D u i v φ ∈ (D.fm u).Fi i) :
    Dop D u i v (Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ := by
  rw [H.DU hφ hU, hN, H.trp_ram hφ hN hU]; simp

theorem UD_ram (hD : Dop D u i v φ ∈ (D.fm u).Fi i) :
    Uop D u i v (Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ := by
  apply H.ext_P; intro Λ f hf; funext y
  rw [H.P_UD hφ hD Λ hf,
    ((Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramified_lattice_operator_identity _ _ ℂ).2 _ (H.nmP_eq_zero_of_ne_zero hφ hN Λ y)).2.2 (two_le_N D.R i) f hf, map_smul, cardC]
  rfl

theorem Nm_U (hU : Uop D u i v φ ∈ (D.fm u).Fi i) : Nm D u i v (Uop D u i v φ) = 0 := by
  apply H.ext_P; intro Λ f hf; funext y
  rw [H.P_Nm hU Λ hf, map_zero]
  have : nmP (fun f => H.P Λ f (Uop D u i v φ) y) f = nmP (opU (fun x => H.Q Λ x φ y)) f := by
    unfold nmP diaP; refine Finset.sum_congr rfl (fun c _ => ?_)
    exact H.P_U hφ Λ (smul_ne_zero c.ne_zero hf) y
  rw [this, ((Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramified_lattice_operator_identity _ _ ℂ).1 _ (H.nmV_zero hφ hN Λ y)).1 f]; rfl

theorem Nm_D (hD : Dop D u i v φ ∈ (D.fm u).Fi i) : Nm D u i v (Dop D u i v φ) = 0 := by
  apply H.ext_Q; intro Λ x hx; funext y
  rw [H.Q_Nm hD Λ hx, map_zero]
  have : nmV (fun x => H.Q Λ x (Dop D u i v φ) y) x = nmV (opD (fun f => H.P Λ f φ y)) x := by
    unfold nmV diaV; refine Finset.sum_congr rfl (fun c _ => ?_)
    exact H.Q_D hφ Λ (smul_ne_zero (c⁻¹).ne_zero hx) y
  rw [this, ((Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramified_lattice_operator_identity _ _ ℂ).2 _ (H.nmP_eq_zero_of_ne_zero hφ hN Λ y)).1 x]; rfl

end ram

lemma P_U' {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {f} (hf : f ≠ 0) :
    H.P Λ f (Uop D u i v φ) = ∑ x ∈ Finset.univ.filter (fun x => pair f x = 1), H.Q Λ x φ := by
  funext y; rw [H.P_U hφ Λ hf, Finset.sum_apply]; rfl

lemma Q_D' {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (Λ) {x} (hx : x ≠ 0) :
    H.Q Λ x (Dop D u i v φ) = ∑ f ∈ Finset.univ.filter (fun f => pair f x = 1), H.P Λ f φ := by
  funext y; rw [H.Q_D hφ Λ hx, Finset.sum_apply]; rfl

theorem adjoint {φ ψ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hψ : ψ ∈ (D.fm u).Fi i)
    (hU : Uop D u i v φ ∈ (D.fm u).Fi i) (hD : Dop D u i v ψ ∈ (D.fm u).Fi i) :
    (D.fm u).ipC i (Uop D u i v φ) ψ = (D.fm u).ipC i φ (Dop D u i v ψ) := by
  rw [H.ip_f _ hU _ hψ, H.unfoldInnerProduct _ hφ _ hD]
  refine Finset.sum_congr rfl (fun Λ _ => ?_)
  congr 1
  have e1 : ∀ f ∈ Finset.univ.filter (fun f : Fin (D.R.N i) → (D.mem u).A.Fv v => f ≠ 0),
      H.ipL Λ (H.tf Λ f (Uop D u i v φ (H.cf Λ f))) (H.tf Λ f (ψ (H.cf Λ f))) =
        ∑ x ∈ Finset.univ.filter (fun x => pair f x = 1), H.ipL Λ (H.Q Λ x φ) (H.P Λ f ψ) := by
    intro f hf
    rw [← P_apply, H.P_U' hφ Λ (Finset.mem_filter.mp hf).2, map_sum, LinearMap.sum_apply]; rfl
  have e2 : ∀ x ∈ Finset.univ.filter (fun x : Fin (D.R.N i) → (D.mem u).A.Fv v => x ≠ 0),
      H.ipL Λ (H.tx Λ x (φ (H.cx Λ x))) (H.tx Λ x (Dop D u i v ψ (H.cx Λ x))) =
        ∑ f ∈ Finset.univ.filter (fun f => pair f x = 1), H.ipL Λ (H.Q Λ x φ) (H.P Λ f ψ) := by
    intro x hx
    rw [← Q_apply H Λ x (Dop D u i v ψ), H.Q_D' hψ Λ (Finset.mem_filter.mp hx).2, map_sum]; rfl
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  refine Finset.sum_comm' (fun f x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact ⟨h, by rintro rfl; simp [pair] at h⟩
  · rintro ⟨h, _⟩; exact ⟨by rintro rfl; simp [pair] at h, h⟩

theorem dia_adjoint {φ ψ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hψ : ψ ∈ (D.fm u).Fi i) (a)
    (h1 : dia D u i v a φ ∈ (D.fm u).Fi i) (h2 : dia D u i v a⁻¹ ψ ∈ (D.fm u).Fi i) :
    (D.fm u).ipC i (dia D u i v a φ) ψ = (D.fm u).ipC i φ (dia D u i v a⁻¹ ψ) := by
  rw [H.ip_f _ h1 _ hψ, H.ip_f _ hφ _ h2]
  refine Finset.sum_congr rfl (fun Λ _ => ?_)
  congr 1
  refine Finset.sum_nbij' (fun f => (a : (D.mem u).A.Fv v) • f)
    (fun f => ((a⁻¹ : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) • f) ?_ ?_ ?_ ?_ ?_
  · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact smul_ne_zero a.ne_zero hf
  · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact smul_ne_zero (a⁻¹).ne_zero hf
  · intro f _; simp [smul_smul]
  · intro f _; simp [smul_smul]
  · intro f hf
    have hf' : f ≠ 0 := (Finset.mem_filter.mp hf).2
    have e1 := H.P_dia hφ Λ hf' a
    have e2 := H.P_dia hψ Λ (smul_ne_zero a.ne_zero hf' : (a : (D.mem u).A.Fv v) • f ≠ 0) a⁻¹
    rw [smul_smul, Units.inv_mul, one_smul] at e2
    simp only [P_apply] at e1 e2
    rw [e1, e2]

theorem FF_eq {φ : Fn D u i} (hφ : φ ∈ (D.fm u).Fi i) (hN : Nm D u i v φ = 0)
    (hG : Gs D u i v φ ∈ (D.fm u).Fi i) : FFop D u i v φ = Dop D u i v (Gs D u i v φ) := by
  apply H.ext_Q; intro Λ x hx; funext y
  rw [H.Q_FF hφ Λ hx, H.Q_D hG Λ hx, Formalism.LogVandermondeBounds.product_first_zeroth_parts.fourier_eq_down_comp_gauss _ _ _ _ (H.nmP_eq_zero_of_ne_zero hφ hN Λ y) x]
  unfold opD; refine Finset.sum_congr rfl (fun f hf => ?_)
  have hf' : f ≠ 0 := by rintro rfl; simpa [pair] using (Finset.mem_filter.mp hf).2
  unfold opGs Gs
  beta_reduce
  rw [LinearMap.sum_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [LinearMap.smul_apply, map_smul, H.P_dia hφ Λ hf' c]; rfl

end Unf

variable (D u)

def FiSt : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v φ ∈ (D.fm u).Fi i ∧ Dop D u i v φ ∈ (D.fm u).Fi i ∧ ∀ a, dia D u i v a φ ∈ (D.fm u).Fi i

def CrossDia : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi i, ∀ a,
    dia D u i v' a (Uop D u i v φ) = Uop D u i v (dia D u i v' a φ) ∧
    dia D u i v' a (Dop D u i v φ) = Dop D u i v (dia D u i v' a φ) ∧
    ∀ b, dia D u i v' a (dia D u i v b φ) = dia D u i v b (dia D u i v' a φ)

def UnfAll : Prop := ∀ i, i ≤ D.R.m → ∀ v, Nonempty (Unf D u i v)

variable {D u}

lemma mem_MramI {i : ℕ} {φ : Fn D u i} :
    φ ∈ MramI D u i ↔ φ ∈ (D.fm u).Fi i ∧ ∀ v, Nm D u i v φ = 0 := by
  simp [MramI, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem ram_of (hF : FiSt D u) (hM : DiaMul D u) (hX : CrossDia D u) (hU : UnfAll D u) :
    ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i,
      Uop D u i v φ ∈ MramI D u i ∧ Dop D u i v φ ∈ MramI D u i ∧
      (∀ a, dia D u i v a φ ∈ MramI D u i) ∧ trp D u i v φ = 0 ∧
      Dop D u i v (Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
      Uop D u i v (Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ := by
  intro i hi v φ hφ
  obtain ⟨hφF, hφN⟩ := mem_MramI.mp hφ
  obtain ⟨H⟩ := hU i hi v
  obtain ⟨hUF, hDF, hdF⟩ := hF i hi v φ hφF
  refine ⟨mem_MramI.mpr ⟨hUF, fun v' => ?_⟩, mem_MramI.mpr ⟨hDF, fun v' => ?_⟩,
    fun a => mem_MramI.mpr ⟨hdF a, fun v' => ?_⟩, H.trp_ram hφF (hφN v) hUF, H.DU_ram hφF (hφN v) hUF,
    H.UD_ram hφF (hφN v) hDF⟩
  · by_cases h : v = v'
    · subst h; exact H.Nm_U hφF (hφN v) hUF
    · have : Nm D u i v' (Uop D u i v φ) = Uop D u i v (Nm D u i v' φ) := by
        unfold Nm; rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl (fun a _ => (hX i hi v v' h φ hφF a).1)
      rw [this, hφN v', map_zero]
  · by_cases h : v = v'
    · subst h; exact H.Nm_D hφF (hφN v) hDF
    · have : Nm D u i v' (Dop D u i v φ) = Dop D u i v (Nm D u i v' φ) := by
        unfold Nm; rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl (fun a _ => (hX i hi v v' h φ hφF a).2.1)
      rw [this, hφN v', map_zero]
  · by_cases h : v = v'
    · subst h
      have h0 := hφN v
      unfold Nm at h0 ⊢
      rw [LinearMap.sum_apply] at h0 ⊢
      calc ∑ b, dia D u i v b (dia D u i v a φ) = ∑ b, dia D u i v (b * a) φ :=
            Finset.sum_congr rfl (fun b _ => ((hM i hi v φ hφF).2 b a).symm)
        _ = ∑ b, dia D u i v b φ := Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun b => rfl)
        _ = 0 := h0
    · have : Nm D u i v' (dia D u i v a φ) = dia D u i v a (Nm D u i v' φ) := by
        unfold Nm; rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl (fun b _ => (hX i hi v v' h φ hφF b).2.2 a)
      rw [this, hφN v', map_zero]

lemma Gs_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    Gs D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • dia D u i v a φ := by
  simp [Gs]

lemma GsD_apply (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    GsD D u i v φ =
      ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (-(a : (D.mem u).A.Fv v)) • dia D u i v a⁻¹ φ := by
  simp [GsD]

lemma gauss_fn {i : ℕ} {v : (D.mem u).A.vT} {φ : Fn D u i} (h1 : dia D u i v 1 φ = φ) :
    ∑ a : ((D.mem u).A.Fv v)ˣ, ∑ b : ((D.mem u).A.Fv v)ˣ,
      ((D.mem u).A.psiT v (a : (D.mem u).A.Fv v) * (D.mem u).A.psiT v (-(b : (D.mem u).A.Fv v))) •
        dia D u i v (a * b⁻¹) φ = ((D.mem u).A.T : ℂ) • φ - Nm D u i v φ := by
  funext c y
  have h := gauss_units ((D.mem u).A.psiT v) ((D.mem u).A.psiT_ne v) (fun a => dia D u i v a φ c y)
  simp only [h1, Unf.cardC] at h
  simp only [Nm, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact h

theorem Gs_GsD (hM : DiaMul D u) : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Gs D u i v (GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Nm D u i v φ := by
  intro i hi v φ hφ
  obtain ⟨h1, hmul⟩ := hM i hi v φ hφ
  rw [← gauss_fn h1, GsD_apply, Gs_apply]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, hmul]

theorem GsD_Gs (hM : DiaMul D u) : ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    GsD D u i v (Gs D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Nm D u i v φ := by
  intro i hi v φ hφ
  obtain ⟨h1, hmul⟩ := hM i hi v φ hφ
  rw [← gauss_fn h1, Gs_apply, GsD_apply]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [mul_comm a b⁻¹, hmul, mul_comm]

lemma ipC_sum_left {i : ℕ} {ι : Type} [Fintype ι] (s : ι → ℂ) (F : ι → Fn D u i) (ψ : Fn D u i) :
    (D.fm u).ipC i (∑ a, s a • F a) ψ = ∑ a, (starRingEnd ℂ) (s a) * (D.fm u).ipC i (F a) ψ := by
  unfold MemberForms.ipC
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => by ring))

lemma ipC_sum_right {i : ℕ} {ι : Type} [Fintype ι] (s : ι → ℂ) (F : ι → Fn D u i) (φ : Fn D u i) :
    (D.fm u).ipC i φ (∑ a, s a • F a) = ∑ a, s a * (D.fm u).ipC i φ (F a) := by
  unfold MemberForms.ipC
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => by ring))

lemma ipC_smul_left {i : ℕ} (s : ℂ) (φ ψ : Fn D u i) :
    (D.fm u).ipC i (s • φ) ψ = (starRingEnd ℂ) s * (D.fm u).ipC i φ ψ := by
  unfold MemberForms.ipC
  simp only [Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => by ring)

lemma ipC_smul_right {i : ℕ} (s : ℂ) (φ ψ : Fn D u i) :
    (D.fm u).ipC i φ (s • ψ) = s * (D.fm u).ipC i φ ψ := by
  unfold MemberForms.ipC
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => by ring)

section T7

variable (hF : FiSt D u) (hM : DiaMul D u) (hX : CrossDia D u) (hU : UnfAll D u)
include hF hM hX hU

lemma Gs_ram {i : ℕ} (hi : i ≤ D.R.m) (v) {φ : Fn D u i} (hφ : φ ∈ MramI D u i) : Gs D u i v φ ∈ MramI D u i := by
  rw [Gs_apply]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ((ram_of hF hM hX hU i hi v φ hφ).2.2.1 a))

theorem FF_DGs {i : ℕ} (hi : i ≤ D.R.m) (v) {φ : Fn D u i} (hφ : φ ∈ MramI D u i) :
    FFop D u i v φ = Dop D u i v (Gs D u i v φ) := by
  obtain ⟨H⟩ := hU i hi v
  exact H.FF_eq (mem_MramI.mp hφ).1 ((mem_MramI.mp hφ).2 v) (mem_MramI.mp (Gs_ram hF hM hX hU hi v hφ)).1

theorem FF_ram {i : ℕ} (hi : i ≤ D.R.m) (v) {φ : Fn D u i} (hφ : φ ∈ MramI D u i) :
    FFop D u i v φ ∈ MramI D u i := by
  rw [FF_DGs hF hM hX hU hi v hφ]
  exact (ram_of hF hM hX hU i hi v _ (Gs_ram hF hM hX hU hi v hφ)).2.1

theorem Gs_iso {i : ℕ} (hi : i ≤ D.R.m) (v) {φ ψ : Fn D u i} (hφ : φ ∈ MramI D u i) (hψ : ψ ∈ MramI D u i) :
    (D.fm u).ipC i (Gs D u i v φ) (Gs D u i v ψ) = ((D.mem u).A.T : ℂ) * (D.fm u).ipC i φ ψ := by
  obtain ⟨H⟩ := hU i hi v
  have hβ := Gs_ram hF hM hX hU hi v hψ
  have hφF := (mem_MramI.mp hφ).1
  have hβF := (mem_MramI.mp hβ).1
  calc (D.fm u).ipC i (Gs D u i v φ) (Gs D u i v ψ)
      = ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (-(a : (D.mem u).A.Fv v)) *
          (D.fm u).ipC i φ (dia D u i v a⁻¹ (Gs D u i v ψ)) := by
        rw [Gs_apply i v φ, ipC_sum_left]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [AddChar.map_neg_eq_conj, H.dia_adjoint hφF hβF a ((hF i hi v φ hφF).2.2 a) ((hF i hi v _ hβF).2.2 a⁻¹)]
    _ = (D.fm u).ipC i φ (GsD D u i v (Gs D u i v ψ)) := by rw [GsD_apply, ipC_sum_right]
    _ = ((D.mem u).A.T : ℂ) * (D.fm u).ipC i φ ψ := by
        rw [GsD_Gs hM i hi v ψ (mem_MramI.mp hψ).1, (mem_MramI.mp hψ).2 v, sub_zero, ipC_smul_right]

theorem FF_iso {i : ℕ} (hi : i ≤ D.R.m) (v) {φ ψ : Fn D u i} (hφ : φ ∈ MramI D u i) (hψ : ψ ∈ MramI D u i) :
    (D.fm u).ipC i (FFop D u i v φ) (FFop D u i v ψ) = ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ := by
  obtain ⟨H⟩ := hU i hi v
  have hα := Gs_ram hF hM hX hU hi v hφ
  have hβ := Gs_ram hF hM hX hU hi v hψ
  have rα := ram_of hF hM hX hU i hi v _ hα
  have rβ := ram_of hF hM hX hU i hi v _ hβ
  have hDα := (mem_MramI.mp rα.2.1).1
  rw [FF_DGs hF hM hX hU hi v hφ, FF_DGs hF hM hX hU hi v hψ,
    ← H.adjoint hDα (mem_MramI.mp hβ).1 ((hF i hi v _ hDα).1) (mem_MramI.mp rβ.2.1).1,
    rα.2.2.2.2.2, ipC_smul_left, Gs_iso hF hM hX hU hi v hφ hψ, map_pow, Complex.conj_natCast, ← mul_assoc,
    ← pow_succ, Nat.sub_add_cancel (D.R.N_pos i)]

lemma FFlist {i : ℕ} (hi : i ≤ D.R.m) (l : List (D.mem u).A.vT) :
    ∀ φ ∈ MramI D u i, ∀ ψ ∈ MramI D u i,
      (l.foldr (fun v g => (FFop D u i v).comp g) LinearMap.id) φ ∈ MramI D u i ∧
      (D.fm u).ipC i ((l.foldr (fun v g => (FFop D u i v).comp g) LinearMap.id) φ)
          ((l.foldr (fun v g => (FFop D u i v).comp g) LinearMap.id) ψ) =
        (((D.mem u).A.T : ℂ) ^ D.R.N i) ^ l.length * (D.fm u).ipC i φ ψ := by
  induction l with
  | nil => intro φ hφ ψ _; simpa using hφ
  | cons v l ih =>
    intro φ hφ ψ hψ
    obtain ⟨h1, h2⟩ := ih φ hφ ψ hψ
    obtain ⟨h3, _⟩ := ih ψ hψ ψ hψ
    simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
    refine ⟨FF_ram hF hM hX hU hi v h1, ?_⟩
    rw [FF_iso hF hM hX hU hi v h1 h3, h2, pow_succ]; ring

theorem finiteModel_of_heckeEstimate (C : ℝ) (h4 : Conclusion4 D u C) : division_rows_rational_lattice D u := by
  refine ⟨fun i hi v φ hφ => FF_DGs hF hM hX hU hi v hφ, Gs_GsD hM,
    fun i hi v φ hφ => FF_ram hF hM hX hU hi v hφ,
    fun i hi v φ hφ ψ hψ => FF_iso hF hM hX hU hi v hφ hψ, fun i hi φ hφ ψ hψ => ?_, fun i hi v => ?_⟩
  · have h := (FFlist hF hM hX hU hi (Finset.univ : Finset (D.mem u).A.vT).toList φ hφ ψ hψ).2
    rw [Finset.length_toList, Finset.card_univ, (D.mem u).A.card_vT, ← pow_mul, mul_comm (D.R.N i)] at h
    exact h
  · obtain ⟨⟨c, hc, hn, _⟩, hdia, hram⟩ := h4 i hi v
    have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
    have hc0 : D.what₂.embLL c ≠ 0 := by
      intro h0
      have := hn D.what₂.embLL
      rw [h0, norm_zero] at this
      exact absurd this (Real.rpow_pos_of_pos hT _).ne
    have ha : ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) ≠ 0 := pow_ne_zero _ (T_ne D u)
    have ha' : ((D.mem u).A.T : ℂ) ^ (D.R.N (i + 1) - 1) ≠ 0 := pow_ne_zero _ (T_ne D u)
    refine ⟨(D.what₂.embLL c * ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1))⁻¹ * ((D.mem u).A.T : ℂ) ^ (D.R.N (i + 1) - 1),
      mul_ne_zero (inv_ne_zero (mul_ne_zero hc0 ha)) ha', fun φ hφ => ?_⟩
    have hi' : i ≤ D.R.m := hi.le
    have hφF := (mem_MramI.mp hφ).1
    have hG := Gs_ram hF hM hX hU hi' v hφ
    have rG := ram_of hF hM hX hU i hi' v _ hG
    have hKφ := hram φ hφ
    have hKG : KT D u i (Gs D u i v φ) = Gs D u (i + 1) v (KT D u i φ) := by
      rw [Gs_apply, Gs_apply, map_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [map_smul, hdia a φ hφF])
    have hχ := rG.2.1
    have e1 : Uop D u (i + 1) v (KT D u i (Dop D u i v (Gs D u i v φ))) =
        (D.what₂.embLL c * ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1)) • Gs D u (i + 1) v (KT D u i φ) := by
      rw [hc _ (mem_MramI.mp hχ).1, rG.2.2.2.2.2, map_smul, hKG, smul_smul]
    have e2 := (ram_of hF hM hX hU (i + 1) hi v _ (hram _ hχ)).2.2.2.2.1
    rw [e1, map_smul, ← FF_DGs hF hM hX hU hi v hKφ, ← FF_DGs hF hM hX hU hi' v hφ] at e2
    rw [mul_smul, ← e2, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc0 ha), one_smul]

end T7

variable (D u)

def UComm : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v (Uop D u i v' φ) = Uop D u i v' (Uop D u i v φ)

def IntAtT : Prop :=
  ∀ i, i ≤ D.R.m → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).Bw i w v) ((D.fm u).S i w) ∧
    Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).Bw i w v)

def IntOffT : Prop :=
  ∀ i, i ≤ D.R.m → ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).S i w) ((D.fm u).S i w) ∧ Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).S i w)

def Rat0 : Prop :=
  ∀ v, (∀ x, ∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    ∀ x, ∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x)

variable {D u}

lemma dia_rat (v) (a) (x : Vl D u 0) : ∃ y, (D.fm u).emb 0 y = dia D u 0 v a ((D.fm u).emb 0 x) := by
  rw [dia_zero]
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set (Vl D u 0)) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨y, _, hy⟩ := (D.fm u).rhoT_lat v a x h; exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, h1⟩ := hx; obtain ⟨a2, h2⟩ := hy
    exact ⟨a1 + a2, by rw [map_add, map_add, map_add, h1, h2]⟩
  | smul r x _ hx =>
    obtain ⟨a1, h1⟩ := hx
    exact ⟨r • a1, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul]⟩

lemma dia_S (w) (v) (a) : Into D u w (dia D u 0 v a) ((D.fm u).S 0 w) ((D.fm u).S 0 w) := by
  intro x hx
  rw [dia_zero]
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨y, hy1, hy⟩ := (D.fm u).rhoT_lat v a x h; exact ⟨y, Submodule.subset_span hy1, hy⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, m1, h1⟩ := hx; obtain ⟨a2, m2, h2⟩ := hy
    exact ⟨a1 + a2, Submodule.add_mem _ m1 m2, by rw [map_add, map_add, map_add, h1, h2]⟩
  | smul r x _ hx =>
    obtain ⟨a1, m1, h1⟩ := hx
    exact ⟨r • a1, Submodule.smul_mem _ r m1, by
      rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul]⟩

lemma mem_ramSub {x : Vl D u 0} : x ∈ (D.fm u).ramSub ↔ (D.fm u).emb 0 x ∈ MramI D u 0 := by
  rw [MramI_zero]; rfl

theorem baseChange_preserves_unitary_of (hF : FiSt D u) (hM : DiaMul D u) (hX : CrossDia D u) (hU : UnfAll D u) (hC : UComm D u)
    (h4 : IntAtT D u) (h5 : IntOffT D u) (hR : Rat0 D u) : Conclusion1 D u := by
  have ram := ram_of hF hM hX hU
  refine ⟨hF, hC, fun i hi v φ hφ ψ hψ => ?_, h4, h5, fun i hi v φ hφ => ?_, fun v x hx => ?_, fun w hw v => ?_, ram⟩
  · obtain ⟨H⟩ := hU i hi v
    exact H.adjoint hφ hψ (hF i hi v φ hφ).1 (hF i hi v ψ hψ).2.1
  · obtain ⟨H⟩ := hU i hi v
    exact H.DU hφ (hF i hi v φ hφ).1
  · have r := ram 0 (Nat.zero_le _) v _ (mem_ramSub.mp hx)
    refine ⟨?_, ?_, fun a => ?_⟩
    · obtain ⟨y, hy⟩ := (hR v).1 x
      exact ⟨y, mem_ramSub.mpr (hy ▸ r.1), hy⟩
    · obtain ⟨y, hy⟩ := (hR v).2 x
      exact ⟨y, mem_ramSub.mpr (hy ▸ r.2.1), hy⟩
    · obtain ⟨y, hy⟩ := dia_rat v a x
      exact ⟨y, mem_ramSub.mpr (hy ▸ r.2.2.1 a), hy⟩
  · refine ⟨fun x hx => ?_, fun x hx => ?_, fun a x hx => ?_⟩
    · have r := ram 0 (Nat.zero_le _) v _ (mem_ramSub.mp hx.2)
      obtain ⟨y, hyS, hy⟩ := (h5 0 (Nat.zero_le _) w hw v).1 x hx.1
      exact ⟨y, ⟨hyS, mem_ramSub.mpr (hy ▸ r.1)⟩, hy⟩
    · have r := ram 0 (Nat.zero_le _) v _ (mem_ramSub.mp hx.2)
      obtain ⟨y, hyS, hy⟩ := (h5 0 (Nat.zero_le _) w hw v).2 x hx.1
      exact ⟨y, ⟨hyS, mem_ramSub.mpr (hy ▸ r.2.1)⟩, hy⟩
    · have r := ram 0 (Nat.zero_le _) v _ (mem_ramSub.mp hx.2)
      obtain ⟨y, hyS, hy⟩ := dia_S w v a x hx.1
      exact ⟨y, ⟨hyS, mem_ramSub.mpr (hy ▸ r.2.2.1 a)⟩, hy⟩

theorem DiaMul_of (hF : FiSt D u) (hU : UnfAll D u) : DiaMul D u := by
  intro i hi v φ hφ
  obtain ⟨H⟩ := hU i hi v
  refine ⟨H.ext_P (fun Λ f hf => ?_), fun a b => H.ext_P (fun Λ f hf => ?_)⟩
  · rw [H.P_dia hφ Λ hf 1]; simp
  · rw [H.P_dia hφ Λ hf (a * b), H.P_dia ((hF i hi v φ hφ).2.2 b) Λ hf a,
      H.P_dia hφ Λ (smul_ne_zero a.ne_zero hf) b, smul_smul, Units.val_mul, mul_comm]

variable (D u)

def KDia : Prop :=
  ∀ i, i < D.R.m → ∀ v a, ∀ φ ∈ (D.fm u).Fi i, KT D u i (dia D u i v a φ) = dia D u (i + 1) v a (KT D u i φ)

def KFi : Prop := ∀ i, i < D.R.m → ∀ φ ∈ (D.fm u).Fi i, KT D u i φ ∈ (D.fm u).Fi (i + 1)

variable {D u}

theorem K_ram (hK : KDia D u) (hKF : KFi D u) : ∀ i, i < D.R.m → ∀ φ ∈ MramI D u i, KT D u i φ ∈ MramI D u (i + 1) := by
  intro i hi φ hφ
  obtain ⟨hφF, hφN⟩ := mem_MramI.mp hφ
  refine mem_MramI.mpr ⟨hKF i hi φ hφF, fun v => ?_⟩
  have : Nm D u (i + 1) v (KT D u i φ) = KT D u i (Nm D u i v φ) := by
    unfold Nm; rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl (fun a _ => (hK i hi v a φ hφF).symm)
  rw [this, hφN v, map_zero]

theorem heckeValue_estimate_of_record_value (C : ℝ) (hC : 0 ≤ C) (h : LevelChainUOperatorCommutation D u) (hK : KDia D u) (hKF : KFi D u) : Conclusion4 D u C := by
  intro i hi v
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hpow : (((D.mem u).A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ) = ((D.mem u).A.T : ℝ) ^ (s + 1) := by
    rw [← Real.rpow_natCast]; congr 1; rw [hs]; push_cast; ring
  refine ⟨⟨(((D.mem u).A.T : ℕ) : D.what₂.LL) ^ (s + 1), fun φ hφ => ?_, fun σ => ?_, fun w hw => ?_⟩,
    hK i hi v, K_ram hK hKF i hi⟩
  · rw [h i hi v φ hφ, hpow, map_pow, map_natCast]; push_cast; rfl
  · rw [hpow, map_pow, map_natCast, norm_pow, Complex.norm_natCast]
  · refine ⟨((s + 1 : ℕ) : ℤ) * (D.what₂.places.ramIdx w : ℤ), ?_, ?_⟩
    · rw [AddValuation.map_pow, ← (show D.what₂.places.resChar w = (D.mem u).A.T from hw),
        D.what₂.places.val_resChar w]
      rw [← (nsmul_eq_mul (s + 1) (D.what₂.places.ramIdx w : ℤ)), WithTop.coe_nsmul]
    · have he : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
      have hW : (0 : ℝ) ≤ (Wt D u ((D.fm u).tauOf w v) : ℝ) := Nat.cast_nonneg _
      have hN : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
      have ht : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
      push_cast
      rw [abs_of_nonneg (by positivity), mul_comm]
      apply mul_le_mul_of_nonneg_left _ he
      have := mul_nonneg hC hN
      rw [ht]; linarith

variable (D u)

structure FreeT where
  X : Type
  [XFin : Fintype X]
  [act : MulAction (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) X]
  free : ∀ (g : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) (x : X), g • x = x → g = 1
  Θ : (D.mem u).A.Mu0 ≃ₗ[ℂ] (X → ℂ)
  equiv : ∀ v a (φ : (D.mem u).A.Mu0) (h : (D.mem u).A.rhoT v a φ ∈ (D.mem u).A.Mu0) x,
    Θ ⟨(D.mem u).A.rhoT v a φ, h⟩ x = Θ φ ((Pi.mulSingle v a : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) • x)

attribute [instance] FreeT.XFin FreeT.act

variable {D u}

lemma rho_mem (v a) (φ : (D.mem u).A.Mu0) : (D.mem u).A.rhoT v a φ ∈ (D.mem u).A.Mu0 :=
  (D.mem u).A.Mu0_stable v a (Submodule.mem_map_of_mem φ.2)

lemma NmA_mem (v) (φ : (D.mem u).A.Mu0) : (D.mem u).A.Nm v φ ∈ (D.mem u).A.Mu0 := by
  unfold ColumnsAtT.Nm; rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ (fun a _ => rho_mem v a φ)

lemma FreeT.key (W : FreeT D u) (v) (φ : (D.mem u).A.Mu0) (x : W.X) :
    ∑ a, W.Θ φ ((Pi.mulSingle v a : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) • x) =
      W.Θ ⟨(D.mem u).A.Nm v φ, NmA_mem v φ⟩ x := by
  have : (⟨(D.mem u).A.Nm v φ, NmA_mem v φ⟩ : (D.mem u).A.Mu0) =
      ∑ a, ⟨(D.mem u).A.rhoT v a φ, rho_mem v a φ⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp [ColumnsAtT.Nm, LinearMap.sum_apply]
  rw [this, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => (W.equiv v a φ _ x).symm)

theorem rank_nat (W : FreeT D u) :
    (D.mem u).A.du * ((D.mem u).A.T - 1) ^ D.R.f = D.duS u * ((D.mem u).A.T - 1 - 1) ^ D.R.f := by
  have : Fact ((D.mem u).A.T).Prime := ⟨(D.mem u).A.T_prime⟩
  let jU : ∀ v : (D.mem u).A.vT, (ZMod (D.mem u).A.T)ˣ ≃* ((D.mem u).A.Fv v)ˣ := fun v =>
    Units.mapEquiv (ZMod.ringEquivOfPrime ((D.mem u).A.Fv v) (D.mem u).A.T_prime ((D.mem u).A.card_Fv v)).toMulEquiv
  let J : ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) ≃* (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) :=
    MulEquiv.piCongrRight jU
  let _ : MulAction ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) W.X := MulAction.compHom W.X J.toMonoidHom
  have hsm : ∀ (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) (x : W.X), g • x = J g • x := fun _ _ => rfl
  have hJ : ∀ v c, J (Pi.mulSingle v c) = Pi.mulSingle v (jU v c) := by
    intro v c; funext w
    exact Pi.apply_mulSingle (fun w => (jU w : _ → _)) (fun w => map_one (jU w)) v c w
  have hfree : ∀ (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) (x : W.X), g • x = x → g = 1 := by
    intro g x h
    have := W.free (J g) x h
    exact J.injective (by rw [this, map_one])
  have T2 := Formalism.LogVandermondeBounds.product_first_zeroth_parts.finrankFiberSumZero (D.mem u).A.vT (ZMod (D.mem u).A.T)ˣ W.X ℂ hfree
  have hsum : ∀ (ξ : W.X → ℂ) v x, ∑ c : (ZMod (D.mem u).A.T)ˣ,
      ξ ((Pi.mulSingle v c : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) • x) =
      ∑ a, ξ ((Pi.mulSingle v a : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) • x) := by
    intro ξ v x
    refine Fintype.sum_equiv (jU v).toEquiv _ _ (fun c => ?_)
    rw [hsm, hJ]; rfl
  let R' : Submodule ℂ (D.mem u).A.Mu0 := Submodule.comap (D.mem u).A.Mu0.subtype (D.mem u).A.Mram
  have hmap : R'.map (W.Θ : (D.mem u).A.Mu0 →ₗ[ℂ] (W.X → ℂ)) =
      Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramSub (D.mem u).A.vT (ZMod (D.mem u).A.T)ˣ W.X ℂ := by
    ext ξ
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      intro v x
      have hφ' : (φ : Fn D u 0) ∈ (D.mem u).A.Mram := hφ
      have h0 : (D.mem u).A.Nm v φ = 0 := (Submodule.mem_iInf _).mp hφ'.2 v
      have e := W.key v φ x
      rw [hsum]
      show ∑ a, W.Θ φ _ = 0
      rw [e]
      have : (⟨(D.mem u).A.Nm v φ, NmA_mem v φ⟩ : (D.mem u).A.Mu0) = 0 := Subtype.ext h0
      rw [this, map_zero]; rfl
    · intro hξ
      refine ⟨W.Θ.symm ξ, ?_, by simp⟩
      show ((W.Θ.symm ξ : (D.mem u).A.Mu0) : Fn D u 0) ∈ (D.mem u).A.Mram
      refine ⟨(W.Θ.symm ξ).2, (Submodule.mem_iInf _).mpr (fun v => ?_)⟩
      have : (⟨(D.mem u).A.Nm v (W.Θ.symm ξ), NmA_mem v _⟩ : (D.mem u).A.Mu0) = 0 := by
        apply W.Θ.injective
        funext x
        rw [← W.key v _ x, map_zero, LinearEquiv.apply_symm_apply, ← hsum]
        exact hξ v x
      exact congrArg Subtype.val this
  have hdu : (D.mem u).A.du =
      Module.finrank ℂ (Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramSub (D.mem u).A.vT (ZMod (D.mem u).A.T)ˣ W.X ℂ) := by
    rw [← hmap]
    unfold ColumnsAtT.du
    rw [← (Submodule.comapSubtypeEquivOfLe (show (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 from inf_le_left)).finrank_eq]
    exact (W.Θ.submoduleMap R').finrank_eq
  have hd : D.duS u = Fintype.card W.X := by
    unfold D7.duS
    rw [W.Θ.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [hdu, hd, ← (D.mem u).A.card_vT, ← ZMod.card_units (D.mem u).A.T]
  exact T2

theorem rank_line (W : FreeT D u) :
    ((D.mem u).A.du : ℚ) = (D.duS u : ℚ) * (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) ^ D.R.f := by
  have h := rank_nat W
  have h2 : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hq : ((D.mem u).A.du : ℚ) * (((D.mem u).A.T : ℚ) - 1) ^ D.R.f =
      (D.duS u : ℚ) * (((D.mem u).A.T : ℚ) - 1 - 1) ^ D.R.f := by
    have := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast [Nat.cast_sub (show 1 ≤ (D.mem u).A.T by omega), Nat.cast_sub (show 1 ≤ (D.mem u).A.T - 1 by omega)] at this
    exact this
  have h1 : (((D.mem u).A.T : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ ((D.mem u).A.T : ℚ) := by exact_mod_cast h2
    intro h0; linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) = (((D.mem u).A.T : ℚ) - 1 - 1) / (((D.mem u).A.T : ℚ) - 1) := by
    field_simp
  rw [e, div_pow, ← mul_div_assoc, ← hq, mul_div_assoc, div_self (pow_ne_zero _ h1), mul_one]

theorem muMax_line (h0 : (D.fm u).ramL ≠ ⊥) : (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  have hg := (D.fm u).lat_good 0
  have hle : (D.fm u).ramL ≤ ((D.fm u).lat 0).L := inf_le_left
  have : IsNoetherian (𝓞 D.what₂.LL) ((D.fm u).lat 0).L := isNoetherian_of_fg_of_noetherian _ hg.2.1
  have hfg : (D.fm u).ramL.FG := isNoetherian_submodule.mp this _ hle
  have := Formalism.BranchingDeterminantCap.OrthogonalSumAlt.muMax_mono ((D.fm u).lat 0).b ((D.fm u).lat 0).X hg.1 hfg hg.2.1 hle h0
  show Formalism.HN.muMaxDef _ _ _ ≤ Formalism.HN.muMaxDef _ _ _
  unfold Formalism.HN.muMaxDef
  show 2 * Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (D.fm u).ramL - _ + _ ≤ _
  linarith

lemma emb_mem (i : ℕ) (x : Vl D u i) : (D.fm u).emb i x ∈ (D.fm u).Fi i := by
  rw [← ((D.fm u).emb_basis i).2, ← ((D.fm u).lat i).b.sum_repr x, map_sum]
  exact Submodule.sum_mem _ (fun a _ => by
    rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

def sT (R : Ranks) : ℕ := (R.t + 1) / 2

lemma sT_cast (R : Ranks) : ((sT R : ℕ) : ℝ) = ((R.t : ℝ) + 1) / 2 := by
  obtain ⟨s, hs⟩ := R.t_odd
  have : sT R = s + 1 := by unfold sT; omega
  rw [this, hs]; push_cast; ring

lemma X4 (h : LevelChainUOperatorCommutation D u) : ∀ i, i < D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u (i + 1) v (KT D u i φ) = ((D.mem u).A.T : ℂ) ^ sT D.R • KT D u i (Uop D u i v φ) := by
  intro i hi v φ hφ
  rw [h i hi v φ hφ, ← sT_cast, Real.rpow_natCast]; push_cast; rfl

def Ul (D : D7) (u : D.what₂.Word) (i : ℕ) (l : List (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  l.foldr (fun v g => (Uop D u i v).comp g) LinearMap.id

lemma Ul_fi (hF : FiSt D u) {i : ℕ} (hi : i ≤ D.R.m) (l : List (D.mem u).A.vT) :
    ∀ φ ∈ (D.fm u).Fi i, Ul D u i l φ ∈ (D.fm u).Fi i := by
  induction l with
  | nil => intro φ hφ; simpa [Ul] using hφ
  | cons v l ih => intro φ hφ; exact (hF i hi v _ (ih φ hφ)).1

lemma Ul_pow_fi (hF : FiSt D u) {i : ℕ} (hi : i ≤ D.R.m) (l : List (D.mem u).A.vT) (n : ℕ) :
    ∀ φ ∈ (D.fm u).Fi i, (Ul D u i l ^ n) φ ∈ (D.fm u).Fi i := by
  induction n with
  | zero => intro φ hφ; simpa using hφ
  | succ n ih => intro φ hφ; rw [pow_succ]; exact ih _ (Ul_fi hF hi l φ hφ)

lemma Ul_K (hF : FiSt D u) (h : LevelChainUOperatorCommutation D u) {i : ℕ} (hi : i < D.R.m) (l : List (D.mem u).A.vT) :
    ∀ φ ∈ (D.fm u).Fi i, Ul D u (i + 1) l (KT D u i φ) =
      (((D.mem u).A.T : ℂ) ^ sT D.R) ^ l.length • KT D u i (Ul D u i l φ) := by
  induction l with
  | nil => intro φ _; simp [Ul]
  | cons v l ih =>
    intro φ hφ
    show Uop D u (i + 1) v (Ul D u (i + 1) l (KT D u i φ)) = _ • KT D u i (Uop D u i v (Ul D u i l φ))
    rw [ih φ hφ, map_smul, X4 h i hi v _ (Ul_fi hF hi.le l φ hφ), smul_smul, List.length_cons, pow_succ]

lemma Ul_pow_K (hF : FiSt D u) (h : LevelChainUOperatorCommutation D u) {i : ℕ} (hi : i < D.R.m) (l : List (D.mem u).A.vT) (n : ℕ) :
    ∀ φ ∈ (D.fm u).Fi i, (Ul D u (i + 1) l ^ n) (KT D u i φ) =
      ((((D.mem u).A.T : ℂ) ^ sT D.R) ^ l.length) ^ n • KT D u i ((Ul D u i l ^ n) φ) := by
  induction n with
  | zero => intro φ _; simp
  | succ n ih =>
    intro φ hφ
    rw [pow_succ, pow_succ (Ul D u i l), Module.End.mul_apply, Module.End.mul_apply, Ul_K hF h hi l φ hφ, map_smul,
      ih _ (Ul_fi hF hi.le l φ hφ), smul_smul, pow_succ, mul_comm]

def chL (D : D7) (u : D.what₂.Word) : (j : ℕ) → (Fn D u 0 →ₗ[ℂ] Fn D u j)
  | 0 => LinearMap.id
  | j + 1 => (KT D u j).comp (chL D u j)

lemma colT_eq (φ : Fn D u 0) : colT D u φ = chL D u D.R.m φ := by
  have : ∀ j, Formalism.ThetaLiftIndependence.chainOpM (D.mem u).C.wt (D.mem u).C.Kmap j φ = chL D u j φ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show (D.mem u).C.K j (Formalism.ThetaLiftIndependence.chainOpM (D.mem u).C.wt (D.mem u).C.Kmap j φ) = KT D u j (chL D u j φ)
      rw [ih]; rfl
  exact this _

def chUK (D : D7) (u : D.what₂.Word) (l : List (D.mem u).A.vT) : (j : ℕ) → (Fn D u 0 →ₗ[ℂ] Fn D u j)
  | 0 => LinearMap.id
  | j + 1 => ((Ul D u (j + 1) l).comp (KT D u j)).comp (chUK D u l j)

def Ex : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, n => Ex j (n + 1) + (n + 1)

lemma Ex_eq (j : ℕ) : ∀ n, 2 * Ex j n = 2 * j * n + j * (j + 1) := by
  induction j with
  | zero => intro n; simp [Ex]
  | succ j ih => intro n; have := ih (n + 1); simp only [Ex]; nlinarith

lemma chUK_fi (hF : FiSt D u) (hKF : KFi D u) (l : List (D.mem u).A.vT) :
    ∀ j, j ≤ D.R.m → ∀ φ ∈ (D.fm u).Fi 0, chUK D u l j φ ∈ (D.fm u).Fi j := by
  intro j
  induction j with
  | zero => intro _ φ hφ; exact hφ
  | succ j ih =>
    intro hj φ hφ
    exact Ul_fi hF hj l _ (hKF j hj _ (ih (Nat.le_of_succ_le hj) φ hφ))

lemma chain_comm (hF : FiSt D u) (hKF : KFi D u) (h : LevelChainUOperatorCommutation D u) (l : List (D.mem u).A.vT) :
    ∀ j, j ≤ D.R.m → ∀ n, ∀ φ ∈ (D.fm u).Fi 0,
      ((((D.mem u).A.T : ℂ) ^ sT D.R) ^ l.length) ^ Ex j n • chL D u j ((Ul D u 0 l ^ (n + j)) φ) =
        (Ul D u j l ^ n) (chUK D u l j φ) := by
  intro j
  induction j with
  | zero => intro _ n φ _; simp [Ex, chL, chUK]
  | succ j ih =>
    intro hj n φ hφ
    have hj' : j ≤ D.R.m := Nat.le_of_succ_le hj
    have e := ih hj' (n + 1) φ hφ
    have hA := chUK_fi hF hKF l j hj' φ hφ
    show _ • KT D u j (chL D u j ((Ul D u 0 l ^ (n + (j + 1))) φ)) =
      (Ul D u (j + 1) l ^ n) (Ul D u (j + 1) l (KT D u j (chUK D u l j φ)))
    rw [← Module.End.mul_apply, ← pow_succ, Ul_pow_K hF h hj l (n + 1) _ hA, ← e, map_smul, smul_smul,
      show n + (j + 1) = n + 1 + j by ring]
    simp only [Ex]
    rw [pow_add, mul_comm]

theorem column_exponent_lattice_bound (C : ℝ) (hC : 0 ≤ C) (hS : HidaSetting D u) (hF : FiSt D u) (hKF : KFi D u) (h3 : PointsLemma D u C)
    (h4 : LevelChainUOperatorCommutation D u) : ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      Into D u w (fun φ => tpow D u e • colT D u φ) (Nlam D u w) ((D.fm u).S D.R.m w) := by
  intro w hw
  set l := (VV D u w).toList with hl
  have hUl : ∀ i, Uprod D u i w = Ul D u i l := fun i => rfl

  have hint : ∀ j, j ≤ D.R.m → ∃ E1 : ℕ, (E1 : ℝ) ≤ j * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) ∧
      ∀ x ∈ (D.fm u).S 0 w, ∃ y ∈ (D.fm u).S j w,
        (D.fm u).emb j y = ((D.mem u).A.T : ℂ) ^ E1 • chUK D u l j ((D.fm u).emb 0 x) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp, fun x hx => ⟨x, hx, by simp [chUK]⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨E1, hE1, hI⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨e1, he1, hI1⟩ := ((h3 w hw).1 j hj).2.2
      refine ⟨E1 + e1, by push_cast; linarith, fun x hx => ?_⟩
      obtain ⟨y, hy, hy'⟩ := hI x hx
      obtain ⟨z, hz, hz'⟩ := hI1 y hy
      refine ⟨z, hz, ?_⟩
      rw [hz', hy', hUl]
      show tpow D u e1 • Ul D u (j + 1) l (KT D u j (_ • chUK D u l j _)) =
        _ • Ul D u (j + 1) l (KT D u j (chUK D u l j _))
      rw [map_smul, map_smul, smul_smul, pow_add, mul_comm]; rfl
  obtain ⟨E1, hE1, hI⟩ := hint D.R.m le_rfl
  have hexp : 0 ≤ LT.expT D u w := by
    unfold LT.expT
    refine mul_nonneg (Int.natCast_nonneg _) (Finset.sum_nonneg (fun v hv => hS.2.2 _ ?_))
    unfold LT.VVT at hv
    split_ifs at hv with hs
    · exact (Finset.mem_filter.mp hv).2
    · simp at hv
  obtain ⟨n0, hn0⟩ := Int.eq_ofNat_of_zero_le hexp
  refine ⟨E1 + sT D.R * l.length * Ex D.R.m 0, ?_, fun z hz => ?_⟩
  · have h1 : ((Ex D.R.m 0 : ℕ) : ℝ) = (D.R.m : ℝ) * (D.R.m + 1) / 2 := by
      have := Ex_eq D.R.m 0
      have h' : (2 : ℝ) * (Ex D.R.m 0 : ℝ) = 2 * D.R.m * 0 + D.R.m * (D.R.m + 1) := by exact_mod_cast this
      linarith
    have h2 : ((sT D.R * l.length * Ex D.R.m 0 : ℕ) : ℝ) =
        ∑ v ∈ VV D u w, (((D.R.t : ℝ) + 1) / 2) * ((D.R.m : ℝ) * (D.R.m + 1) / 2) := by
      rw [Finset.sum_const, hl, Finset.length_toList]; push_cast; rw [sT_cast, h1, nsmul_eq_mul]; ring
    push_cast at h2 ⊢
    rw [h2]
    refine add_le_add hE1 (Finset.sum_le_sum (fun v _ => ?_))
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hW : (0 : ℝ) ≤ (Wt D u ((D.fm u).tauOf w v) : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ C * (D.R.N D.R.m : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · obtain ⟨x, hx, hzx⟩ := hz
    obtain ⟨y, hy, hy'⟩ := hI x hx.1
    have hc := chain_comm hF hKF h4 l D.R.m le_rfl 0 _ (emb_mem 0 x)
    rw [pow_zero, Module.End.one_apply, zero_add] at hc
    have hTm : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ∈ Ow D w := Subring.pow_mem _ (natCast_mem _ _) _
    refine ⟨(⟨_, hTm⟩ : Ow D w) • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [Subring.smul_def, LinearMap.map_smulₛₗ, hy', ← hc]
    show _ = tpow D u _ • colT D u _
    rw [colT_eq, hzx, hn0, show LT.Uprod D u 0 w = Ul D u 0 l from rfl]
    simp only [LinearMap.smul_apply, map_smul, smul_smul, tpow, map_pow, map_natCast, zpow_natCast]
    congr 1
    rw [pow_add, ← pow_mul, ← pow_mul]; ring

lemma rat_of_into {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn D u i →ₗ[ℂ] Fn D u j)
    (A : Submodule (Ow D w) (Vl D u i)) (B : Submodule (Ow D w) (Vl D u j)) (h : Into D u w f A B)
    (hA : Submodule.span D.what₂.LL (A : Set (Vl D u i)) = ⊤) (x : Vl D u i) :
    ∃ y, (D.fm u).emb j y = f ((D.fm u).emb i x) := by
  have hx : x ∈ Submodule.span D.what₂.LL (A : Set (Vl D u i)) := by rw [hA]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨y, _, hy⟩ := h x hx; exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, h1⟩ := hx; obtain ⟨a2, h2⟩ := hy
    exact ⟨a1 + a2, by rw [map_add, map_add, map_add, h1, h2]⟩
  | smul r x _ hx =>
    obtain ⟨a1, h1⟩ := hx
    exact ⟨r • a1, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul]⟩

lemma S_span (i : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span D.what₂.LL ((D.fm u).S i w : Set (Vl D u i)) = ⊤ := by
  rw [eq_top_iff, ← ((D.fm u).lat_good i).2.2]
  exact Submodule.span_mono (fun x hx => Submodule.subset_span hx)

theorem Rat0_of_IntOffT (w : D.what₂.places.Pl) (hw : ¬ OverT D u w) (h5 : IntOffT D u) : Rat0 D u := fun v =>
  ⟨rat_of_into w _ _ _ (h5 0 (Nat.zero_le _) w hw v).1 (S_span 0 w),
    rat_of_into w _ _ _ (h5 0 (Nat.zero_le _) w hw v).2 (S_span 0 w)⟩

theorem Rat0_of_IntAtT (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (h4 : IntAtT D u) :
    Rat0 D u := fun v =>
  ⟨rat_of_into w _ _ _ (h4 0 (Nat.zero_le _) w hw hs v).1 ((D.fm u).Bw_span 0 w v),
    rat_of_into w _ _ _ (h4 0 (Nat.zero_le _) w hw hs v).2 (S_span 0 w)⟩

lemma Ul_into {j : ℕ} {w : D.what₂.places.Pl} {BV : Finset (D.mem u).A.vT → Submodule (Ow D w) (Vl D u j)}
    (hB : IsBfam D u j w BV) : ∀ l : List (D.mem u).A.vT, l.Nodup → ∀ V : Finset (D.mem u).A.vT, (∀ v ∈ l, v ∈ V) →
      Into D u w (Ul D u j l) (BV V) (BV (V \ l.toFinset)) := by
  intro l
  induction l with
  | nil => intro _ V _ x hx; exact ⟨x, by simpa using hx, by simp [Ul]⟩
  | cons v l ih =>
    intro hnd V hV x hx
    obtain ⟨hv, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨y, hy, e⟩ := ih hnd' V (fun a ha => hV a (List.mem_cons_of_mem _ ha)) x hx
    have hvm : v ∈ V \ l.toFinset := Finset.mem_sdiff.mpr ⟨hV v List.mem_cons_self, by simpa using hv⟩
    obtain ⟨z, hz, e'⟩ := (hB.2.2.1 _ v hvm).1 y hy
    refine ⟨z, ?_, ?_⟩
    · rw [List.toFinset_cons, Finset.sdiff_insert]; exact hz
    · rw [e', e]; rfl

lemma T_into {j : ℕ} {w : D.what₂.places.Pl} {BV : Finset (D.mem u).A.vT → Submodule (Ow D w) (Vl D u j)}
    (hB : IsBfam D u j w BV) : ∀ l : List (D.mem u).A.vT, l.Nodup → ∀ V : Finset (D.mem u).A.vT,
      (∀ v ∈ l, v ∈ V ∧ (D.fm u).tauOf w v ∉ tops D) →
      Into D u w (fun φ => tpow D u ((l.map (fun v => 2 * Wt D u ((D.fm u).tauOf w v) + D.R.t)).sum) • φ)
        (BV V) (BV (V \ l.toFinset)) := by
  intro l
  induction l with
  | nil => intro _ V _ x hx; exact ⟨x, by simpa using hx, by simp [tpow]⟩
  | cons v l ih =>
    intro hnd V hV x hx
    obtain ⟨hv, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨y, hy, e⟩ := ih hnd' V (fun a ha => hV a (List.mem_cons_of_mem _ ha)) x hx
    have hvm : v ∈ V \ l.toFinset :=
      Finset.mem_sdiff.mpr ⟨(hV v List.mem_cons_self).1, by simpa using hv⟩
    obtain ⟨z, hz, e'⟩ := hB.2.2.2 _ v hvm (hV v List.mem_cons_self).2 y hy
    refine ⟨z, ?_, ?_⟩
    · rw [List.toFinset_cons, Finset.sdiff_insert]; exact hz
    · rw [e', e]
      beta_reduce
      rw [smul_smul, List.map_cons, List.sum_cons]
      simp only [tpow, pow_add]

lemma t_le_N (R : Ranks) : R.t ≤ R.N R.m := by
  have := R.two_le_m; unfold Ranks.N; nlinarith

lemma card_Tau (u : D.what₂.Word) (w : D.what₂.places.Pl) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Fintype.card_congr ((D.fm u).tauOf w), (D.mem u).A.card_vT]

lemma exponent_e1_count_bound (C : ℝ) (w : D.what₂.places.Pl) :
    ∑ τ, (2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m + if τ ∉ tops D then 2 * (Wt D u τ : ℝ) + D.R.t else 0) ≤
      4 * ∑ τ, (Wt D u τ : ℝ) + (C + 1) * D.R.f * D.R.N D.R.m := by
  have core := Formalism.HermitianLattices.LocalLatticeBases.exponent_loss_per_embedding D.what₂.Tau Finset.univ (fun τ => τ ∉ tops D) (fun τ => (Wt D u τ : ℝ))
    (fun τ => 2 * (Wt D u τ : ℝ) + D.R.t) C (D.R.N D.R.m) D.R.t (fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast t_le_N D.R) (fun τ _ _ => le_rfl)
  rw [Finset.card_univ, card_Tau u w] at core
  exact core

theorem exists_exponent_e1_latticeInto (C : ℝ) (hC : 0 ≤ C) (w : D.what₂.places.Pl) (i : ℕ)
    (h1 : (D.fm u).seenP w = false →
      Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) ((D.fm u).S (i + 1) w))
    (h2 : (D.fm u).seenP w = true → ∃ BV, IsBfam D u (i + 1) w BV ∧
      Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) (BV Finset.univ)) :
    ∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt D u τ : ℝ) + (C + 1) * D.R.f * D.R.N D.R.m ∧
      Into D u w (fun φ => tpow D u e1 • Uprod D u (i + 1) w (KT D u i φ)) ((D.fm u).S i w) ((D.fm u).S (i + 1) w) := by
  have hnn : ∀ τ : D.what₂.Tau, 0 ≤ 2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m := fun τ =>
    add_nonneg (by positivity) (mul_nonneg hC (Nat.cast_nonneg _))
  have hloss : (lossK D u C : ℝ) ≤ ∑ τ, (2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m) :=
    Nat.floor_le (Finset.sum_nonneg (fun τ _ => hnn τ))
  by_cases hs : (D.fm u).seenP w = true
  · obtain ⟨BV, hB, hK⟩ := h2 hs
    have hVV : VV D u w = Finset.univ.filter (fun v => (D.fm u).tauOf w v ∈ tops D) := by
      simp [LT.VVT, hs]
    set l' := (Finset.univ \ VV D u w).toList with hl'
    refine ⟨lossK D u C + (l'.map (fun v => 2 * Wt D u ((D.fm u).tauOf w v) + D.R.t)).sum, ?_, fun x hx => ?_⟩
    · refine le_trans ?_ (exponent_e1_count_bound C w)
      rw [hl', Finset.sum_map_toList,
        show (∑ τ, (2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m + if τ ∉ tops D then 2 * (Wt D u τ : ℝ) + D.R.t else 0)) =
          ∑ τ, (2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m) +
            ∑ τ, (if τ ∉ tops D then 2 * (Wt D u τ : ℝ) + D.R.t else 0) from Finset.sum_add_distrib]
      push_cast
      refine add_le_add hloss (le_of_eq ?_)
      rw [hVV, ← Finset.filter_not, Finset.sum_filter,
        ← Equiv.sum_comp ((D.fm u).tauOf w) (fun τ => if τ ∉ tops D then 2 * (Wt D u τ : ℝ) + D.R.t else 0)]
    · obtain ⟨y1, hy1, e1⟩ := hK x hx
      obtain ⟨y2, hy2, e2⟩ := Ul_into hB (VV D u w).toList (Finset.nodup_toList _) Finset.univ
        (fun v _ => Finset.mem_univ v) y1 hy1
      rw [Finset.toList_toFinset] at hy2
      obtain ⟨y3, hy3, e3⟩ := T_into hB l' (Finset.nodup_toList _) (Finset.univ \ VV D u w) (fun v hv => by
        have hv' : v ∈ Finset.univ \ VV D u w := Finset.mem_toList.mp hv
        refine ⟨hv', fun ht => ?_⟩
        rw [hVV] at hv'
        exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ht⟩)) y2 hy2
      rw [hl', Finset.toList_toFinset, sdiff_self, Finset.bot_eq_empty] at hy3
      refine ⟨y3, by rw [← hB.1]; exact hy3, ?_⟩
      rw [e3, e2, e1]
      beta_reduce
      rw [map_smul, smul_smul]
      show _ = tpow D u _ • Ul D u (i + 1) (VV D u w).toList (KT D u i _)
      simp only [tpow, pow_add, mul_comm]
  · have hs' : (D.fm u).seenP w = false := by simpa using hs
    have hU : Uprod D u (i + 1) w = LinearMap.id := by
      simp [LT.Uprod, LT.VVT, hs']
    refine ⟨lossK D u C, ?_, ?_⟩
    · refine le_trans (le_trans hloss (Finset.sum_le_sum (fun τ _ => ?_))) (exponent_e1_count_bound C w)
      have : (0 : ℝ) ≤ if τ ∉ tops D then 2 * (Wt D u τ : ℝ) + D.R.t else 0 := by
        split_ifs <;> positivity
      linarith
    · rw [hU]; exact h1 hs'

lemma Into_mono {i j : ℕ} {w : D.what₂.places.Pl} {f : Fn D u i → Fn D u j} {A : Submodule (Ow D w) (Vl D u i)}
    {B : Submodule (Ow D w) (Vl D u j)} {n n' : ℕ} (hn : n ≤ n')
    (h : Into D u w (fun φ => tpow D u n • f φ) A B) : Into D u w (fun φ => tpow D u n' • f φ) A B := by
  intro x hx
  obtain ⟨y, hy, e⟩ := h x hx
  have hTm : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ (n' - n) ∈ Ow D w := Subring.pow_mem _ (natCast_mem _ _) _
  refine ⟨(⟨_, hTm⟩ : Ow D w) • y, Submodule.smul_mem _ _ hy, ?_⟩
  rw [Subring.smul_def, LinearMap.map_smulₛₗ, e]
  beta_reduce
  rw [smul_smul, map_pow, map_natCast]
  simp only [tpow]
  rw [← pow_add, Nat.sub_add_cancel hn]

lemma lossK_mono {C C' : ℝ} (h : C ≤ C') : lossK D u C ≤ lossK D u C' := by
  unfold lossK
  refine Nat.floor_le_floor (Finset.sum_le_sum (fun τ _ => ?_))
  have : C * (D.R.N D.R.m : ℝ) ≤ C' * (D.R.N D.R.m : ℝ) := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
  linarith

variable (D u) in

def LatticeChainWithoutLast (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    (∀ i, i < D.R.m →
      ((D.fm u).seenP w = false →
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) ((D.fm u).S (i + 1) w)) ∧
      ((D.fm u).seenP w = true → ∃ BV, IsBfam D u (i + 1) w BV ∧
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) (BV Finset.univ))) ∧
    (∀ i, i ≤ D.R.m → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
      Into D u w (fun φ => tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • φ) ((D.fm u).Bw i w v) ((D.fm u).S i w))

theorem latticeChain_succ_of_partial (C : ℝ) (hC : 0 ≤ C) (h : LatticeChainWithoutLast D u C) : PointsLemma D u (C + 1) := by
  intro w hw
  obtain ⟨hA, hB⟩ := h w hw
  refine ⟨fun i hi => ⟨fun hs => Into_mono (lossK_mono (by linarith)) ((hA i hi).1 hs), fun hs => ?_,
    exists_exponent_e1_latticeInto C hC w i (hA i hi).1 (hA i hi).2⟩, hB⟩
  obtain ⟨BV, h1, h2⟩ := (hA i hi).2 hs
  exact ⟨BV, h1, Into_mono (lossK_mono (by linarith)) h2⟩

lemma natCast_not_isUnit (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ)
  rw [show ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) from by simp,
    Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis K)] at h1
  have hne : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ≠ 0 := by
    have := (RingOfIntegers.basis K).index_nonempty
    exact Fintype.card_ne_zero
  have h2 : IsUnit ((p : ℕ) : ℤ) := (isUnit_pow_iff hne).mp h1
  have h3 := Int.isUnit_iff_natAbs_eq.mp h2
  rw [Int.natAbs_natCast] at h3
  exact hp.one_lt.ne' h3

theorem exists_offT (D : D7) (u : D.what₂.Word) : ∃ w, ¬ OverT D u w := by
  obtain ⟨p, hp, hne⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ (D.mem u).A.T := by
    by_cases h : (D.mem u).A.T = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h' => h h'.symm⟩
  have htop : Ideal.span {((p : ℕ) : 𝓞 D.what₂.LL)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit D.what₂.LL hp
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ htop
  have hpP : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ P := hPle (Ideal.mem_span_singleton_self _)
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨P, hPmax.isPrime, hP0⟩
  refine ⟨D.plEq.symm Q, fun hw => ?_⟩
  have hw' : D.what₂.places.resChar (D.plEq.symm Q) = (D.mem u).A.T := hw
  have h1 := D.val_resChar' (D.plEq.symm Q)
  rw [Equiv.apply_symm_apply, hw'] at h1
  have hTP : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ P := by
    have : Q.valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL)) < 1 := by
      rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      have := D.what₂.places.ramIdx_pos (D.plEq.symm Q)
      omega
    exact (Q.valuation_lt_one_iff_mem _).mp this
  have hcop : IsCoprime ((p : ℕ) : ℤ) (((D.mem u).A.T : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp (D.mem u).A.T_prime).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have h2 : (a : 𝓞 D.what₂.LL) * ((p : ℕ) : 𝓞 D.what₂.LL) + (b : 𝓞 D.what₂.LL) * (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab
  exact hPmax.ne_top ((Ideal.eq_top_iff_one P).mpr (h2 ▸ P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hTP)))

theorem Rat0_of_Int (h5 : IntOffT D u) : Rat0 D u := by
  obtain ⟨w, hw⟩ := exists_offT D u
  exact Rat0_of_IntOffT w hw h5

lemma val_unit (w : D.what₂.places.Pl) (ε : (Ow D w)ˣ) : D.what₂.places.val w ((ε : Ow D w) : D.what₂.LL) = 0 := by
  have h1 : (0 : WithTop ℤ) ≤ D.what₂.places.val w ((ε : Ow D w) : D.what₂.LL) := (ε : Ow D w).2
  have h2 : (0 : WithTop ℤ) ≤ D.what₂.places.val w (((ε⁻¹ : (Ow D w)ˣ) : Ow D w) : D.what₂.LL) :=
    ((ε⁻¹ : (Ow D w)ˣ) : Ow D w).2
  have h3 : D.what₂.places.val w ((ε : Ow D w) : D.what₂.LL) +
      D.what₂.places.val w (((ε⁻¹ : (Ow D w)ˣ) : Ow D w) : D.what₂.LL) = 0 := by
    rw [← AddValuation.map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg h1 h2).mp h3).1

lemma val_decomp (w : D.what₂.places.Pl) (ϖ : Ow D w) (ε : (Ow D w)ˣ) (n : ℕ) (x : Ow D w) (h : x = ε * ϖ ^ n) :
    D.what₂.places.val w (x : D.what₂.LL) = n • D.what₂.places.val w (ϖ : D.what₂.LL) := by
  rw [h, Subring.coe_mul, Subring.coe_pow, AddValuation.map_mul, AddValuation.map_pow, val_unit, zero_add]

lemma exists_unif (w : D.what₂.places.Pl) (hw : OverT D u w) :
    ∃ ϖ : Ow D w, Irreducible ϖ ∧ ∃ ε : (Ow D w)ˣ,
      (((D.mem u).A.T : ℕ) : Ow D w) = ε * ϖ ^ D.what₂.places.ramIdx w := by
  have := D.intW_dvr w
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow D w)
  obtain ⟨x, hx⟩ := D.what₂.places.val_surj w 1
  have hxm : x ∈ Ow D w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w x
    rw [hx]; exact_mod_cast (zero_le_one : (0 : ℤ) ≤ 1)
  have hx0 : (⟨x, hxm⟩ : Ow D w) ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, AddValuation.map_zero] at hx
    exact WithTop.top_ne_coe hx
  obtain ⟨n, ε, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hv := val_decomp w ϖ ε n _ hn
  have hϖ0 : D.what₂.places.val w (ϖ : D.what₂.LL) ≠ ⊤ := by
    intro h
    exact hϖ.ne_zero (Subtype.ext ((AddValuation.top_iff _).mp h))
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hϖ0
  have ha0 : 0 ≤ a := by
    have : (0 : WithTop ℤ) ≤ D.what₂.places.val w (ϖ : D.what₂.LL) := ϖ.2
    rw [← ha] at this; exact_mod_cast this
  have ha1 : a = 1 := by
    have h1 : ((1 : ℤ) : WithTop ℤ) = ((n • a : ℤ) : WithTop ℤ) := by
      rw [WithTop.coe_nsmul, ha, ← hv]; exact hx.symm
    have h2 : (1 : ℤ) = n • a := WithTop.coe_injective h1
    rw [nsmul_eq_mul, mul_comm] at h2
    exact Int.eq_one_of_mul_eq_one_right ha0 h2.symm
  have hT0 : (((D.mem u).A.T : ℕ) : Ow D w) ≠ 0 := by
    intro h
    have h0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) = 0 := by
      have := congrArg (Subtype.val) h; simpa using this
    have h1 := D.what₂.places.val_resChar w
    rw [show D.what₂.places.resChar w = (D.mem u).A.T from hw, h0, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨n', ε', hn'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 hϖ
  refine ⟨ϖ, hϖ, ε', ?_⟩
  have hv' := val_decomp w ϖ ε' n' _ hn'
  have h1 := D.what₂.places.val_resChar w
  rw [show D.what₂.places.resChar w = (D.mem u).A.T from hw] at h1
  have h2 : (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) = ((n' • (1 : ℤ) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_nsmul, ← ha1, ha, ← hv', ← h1]; simp
  have h3 : ((D.what₂.places.ramIdx w : ℕ) : ℤ) = n' • (1 : ℤ) := WithTop.coe_injective h2
  have h4 : D.what₂.places.ramIdx w = n' := by simpa using h3
  rw [h4]; exact hn'

lemma finrank_Vl : Module.finrank D.what₂.LL (Vl D u 0) = D.duS u := by
  rw [Module.finrank_eq_card_basis ((D.fm u).lat 0).b]
  unfold D7.duS
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2, finrank_span_eq_card ((D.fm u).emb_basis 0).1]

lemma int_mem (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ Ow D w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

lemma S_fg (i : ℕ) (w : D.what₂.places.Pl) : ((D.fm u).S i w).FG := by
  obtain ⟨t, ht⟩ := ((D.fm u).lat_good i).2.1
  refine ⟨t, le_antisymm (Submodule.span_mono (by rw [← ht]; exact Submodule.subset_span)) ?_⟩
  unfold MemberForms.S locW
  rw [Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe, ← ht] at hx
  rw [SetLike.mem_coe]
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul r y _ h =>
    have : r • y = (⟨(r : D.what₂.LL), int_mem w r⟩ : Ow D w) • y := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL r y]
    rw [this]; exact Submodule.smul_mem _ _ h

lemma map_unit_smul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (c : Rˣ) (f : M →ₗ[R] M)
    (A : Submodule R M) : A.map ((c : R) • f) = A.map f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(c : R) • x, A.smul_mem _ hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨((c⁻¹ : Rˣ) : R) • x, A.smul_mem _ hx, by simp [smul_smul]⟩

lemma imgL_eq_map (w : D.what₂.places.Pl) (f : Fn D u 0 →ₗ[ℂ] Fn D u 0) (g : Vl D u 0 →ₗ[Ow D w] Vl D u 0)
    (h : ∀ x, (D.fm u).emb 0 (g x) = f ((D.fm u).emb 0 x)) (A : Submodule (Ow D w) (Vl D u 0)) :
    imgL D u w f A = A.map g := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx, (D.fm u).emb_inj 0 (by rw [h, hy])⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, h x⟩

def UR (hR : Rat0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : Vl D u 0 →ₗ[Ow D w] Vl D u 0 :=
  (descend ((D.fm u).emb 0) ((D.fm u).emb 0) ((D.fm u).emb_inj 0) (Uop D u 0 v) (hR v).1).restrictScalars (Ow D w)

def DR (hR : Rat0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : Vl D u 0 →ₗ[Ow D w] Vl D u 0 :=
  (descend ((D.fm u).emb 0) ((D.fm u).emb 0) ((D.fm u).emb_inj 0) (Dop D u 0 v) (hR v).2).restrictScalars (Ow D w)

lemma UR_spec (hR : Rat0 D u) (w v) (x : Vl D u 0) :
    (D.fm u).emb 0 (UR hR w v x) = Uop D u 0 v ((D.fm u).emb 0 x) :=
  descend_spec ((D.fm u).emb 0) ((D.fm u).emb 0) ((D.fm u).emb_inj 0) (Uop D u 0 v) (hR v).1 x

lemma DR_spec (hR : Rat0 D u) (w v) (x : Vl D u 0) :
    (D.fm u).emb 0 (DR hR w v x) = Dop D u 0 v ((D.fm u).emb 0 x) :=
  descend_spec ((D.fm u).emb 0) ((D.fm u).emb 0) ((D.fm u).emb_inj 0) (Dop D u 0 v) (hR v).2 x

lemma emb_smulR (w : D.what₂.places.Pl) (r : Ow D w) (x : Vl D u 0) :
    (D.fm u).emb 0 (r • x) = D.what₂.embLL (r : D.what₂.LL) • (D.fm u).emb 0 x := by
  rw [Subring.smul_def, LinearMap.map_smulₛₗ]

lemma finrank_S_le (w : D.what₂.places.Pl) [Module.Free (Ow D w) ((D.fm u).S 0 w)]
    [Module.Finite (Ow D w) ((D.fm u).S 0 w)] :
    Module.finrank (Ow D w) ((D.fm u).S 0 w) ≤ D.duS u := by
  have := D.intW_dvr w
  have := D.intW_frac w
  have : Module.Finite D.what₂.LL (Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
  rw [← finrank_Vl, Module.finrank_eq_card_chooseBasisIndex]
  have li : LinearIndependent (Ow D w)
      (fun i => ((Module.Free.chooseBasis (Ow D w) ((D.fm u).S 0 w) i : (D.fm u).S 0 w) : Vl D u 0)) :=
    (Module.Free.chooseBasis (Ow D w) ((D.fm u).S 0 w)).linearIndependent.map' ((D.fm u).S 0 w).subtype
      (Submodule.ker_subtype _)
  exact ((LinearIndependent.iff_fractionRing (Ow D w) D.what₂.LL).mp li).fintype_card_le_finrank

theorem LemmaC_core (hR : Rat0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v) (n0 : ℕ)
    (hSB : ∀ x ∈ (D.fm u).S 0 w, (((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • x ∈ (D.fm u).Bw 0 w v)
    (hUB : Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w))
    (hDS : Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v))
    (ram : ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
      Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ) :
    Module.length (Ow D w) (Sram D u w ⧸
        ((Sram D u w).map ((((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • UR hR w v)).comap (Sram D u w).subtype) ≤
      Module.length (Ow D w) ((D.fm u).Bw 0 w v ⧸
        (((D.fm u).S 0 w).map ((((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • (LinearMap.id : Vl D u 0 →ₗ[Ow D w] Vl D u 0))).comap
          ((D.fm u).Bw 0 w v).subtype) + ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) := by
  have hdvr := D.intW_dvr w
  obtain ⟨ϖ, hϖ, ε, hT⟩ := exists_unif (u := u) w hw
  have hTn : ∀ n : ℕ, (((D.mem u).A.T : ℕ) : Ow D w) ^ n =
      ((ε ^ n : (Ow D w)ˣ) : Ow D w) * ϖ ^ (D.what₂.places.ramIdx w * n) := by
    intro n; rw [hT, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]
  have hfin : Module.Finite (Ow D w) ((D.fm u).S 0 w) := Module.Finite.iff_fg.2 (S_fg 0 w)
  have htf : Module.IsTorsionFree (Ow D w) (Vl D u 0) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r x h => by
      rw [Subring.smul_def] at h
      rcases smul_eq_zero.mp h with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr h)
  have hfree : Module.Free (Ow D w) ((D.fm u).S 0 w) := inferInstance
  let c : (Ow D w)ˣ := (ε ^ (D.R.k - 1))⁻¹
  have core := Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_twist_ramified (Ow D w) ϖ hϖ (Vl D u 0)
    ((D.fm u).ramSub.restrictScalars (Ow D w)) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v) (UR hR w v)
    ((c : Ow D w) • DR hR w v) (D.what₂.places.ramIdx w * (D.R.k - 1)) (D.what₂.places.ramIdx w * n0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfree hfin
  · rw [hTn n0, mul_smul, mul_smul, map_unit_smul, map_unit_smul]
    refine le_trans core (add_le_add_right ?_ _)
    have := finrank_S_le (u := u) w
    have h2 : D.what₂.places.ramIdx w * (D.R.k - 1) * Module.finrank (Ow D w) ((D.fm u).S 0 w) ≤
        D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    exact_mod_cast h2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := hSB x hx
    rw [hTn n0, mul_smul] at h1
    have h2 := ((D.fm u).Bw 0 w v).smul_mem (((ε ^ n0)⁻¹ : (Ow D w)ˣ) : Ow D w) h1
    rwa [smul_smul, Units.inv_mul, one_smul] at h2
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hUB x hx
    rwa [← (D.fm u).emb_inj 0 (hy'.trans (UR_spec hR w v x).symm)]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hDS x hx
    rw [LinearMap.smul_apply, ← (D.fm u).emb_inj 0 (hy'.trans (DR_spec hR w v x).symm)]
    exact Submodule.smul_mem _ _ hy
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_ramSub.mpr (by rw [UR_spec]; exact (ram _ (mem_ramSub.mp hx)).1)
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    exact mem_ramSub.mpr (by rw [DR_spec]; exact (ram _ (mem_ramSub.mp hx)).2.1)
  · intro x hx
    have hne : ((ϖ : Ow D w) : D.what₂.LL) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hx' : ((ϖ : Ow D w) : D.what₂.LL) • x ∈ (D.fm u).ramSub := hx
    exact ((D.fm u).ramSub.smul_mem_iff hne).1 hx'
  · intro s hs
    have h1 : UR hR w v (DR hR w v s) = (((D.mem u).A.T : ℕ) : Ow D w) ^ (D.R.k - 1) • s := by
      apply (D.fm u).emb_inj 0
      rw [UR_spec, DR_spec, (ram _ (mem_ramSub.mp hs.2)).2.2, emb_smulR, D.R.N_zero]
      simp
    rw [LinearMap.smul_apply, map_smul, h1, hTn, smul_smul, ← mul_assoc]
    show ((((ε ^ (D.R.k - 1))⁻¹ : (Ow D w)ˣ) : Ow D w) * _ * _) • s = _
    rw [Units.inv_mul, one_mul]

theorem LemmaC_one (hR : Rat0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v)
    (hSB : (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v)
    (hUB : Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w))
    (hDS : Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v))
    (ram : ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
      Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ) :
    len D u w (Sram D u w) (imgL D u w (Uop D u 0 v) (Sram D u w)) ≤
      len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) +
        ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
        len D u w (imgL D u w (Uop D u 0 v) (Sram D u w)) (Sram D u w) := by
  have h := LemmaC_core hR w hw v 0 (fun x hx => by simpa using hSB hx) hUB hDS ram
  rw [show (((D.mem u).A.T : ℕ) : Ow D w) ^ 0 • UR hR w v = UR hR w v from by simp,
    show ((D.fm u).S 0 w).map ((((D.mem u).A.T : ℕ) : Ow D w) ^ 0 • (LinearMap.id : Vl D u 0 →ₗ[Ow D w] Vl D u 0)) =
      (D.fm u).S 0 w from by simp] at h
  unfold len
  rw [imgL_eq_map w (Uop D u 0 v) (UR hR w v) (UR_spec hR w v)]
  exact le_trans h le_self_add

theorem LemmaC_two (hR : Rat0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v) (b : ℤ) (hb : 0 ≤ b)
    (hSB : tL D u w b ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v)
    (hUB : Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w))
    (hDS : Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v))
    (ram : ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
      Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ) :
    len D u w (Sram D u w) (imgL D u w ((((D.mem u).A.T : ℂ) ^ b) • Uop D u 0 v) (Sram D u w)) ≤
      len D u w ((D.fm u).Bw 0 w v) (tL D u w b ((D.fm u).S 0 w)) +
        ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
        len D u w (imgL D u w ((((D.mem u).A.T : ℂ) ^ b) • Uop D u 0 v) (Sram D u w)) (Sram D u w) := by
  obtain ⟨n0, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  have e1 : tL D u w (n0 : ℤ) ((D.fm u).S 0 w) = ((D.fm u).S 0 w).map
      ((((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • (LinearMap.id : Vl D u 0 →ₗ[Ow D w] Vl D u 0)) :=
    imgL_eq_map w _ _ (fun x => by simp [emb_smulR]) _
  have e2 : imgL D u w ((((D.mem u).A.T : ℂ) ^ (n0 : ℤ)) • Uop D u 0 v) (Sram D u w) =
      (Sram D u w).map ((((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • UR hR w v) :=
    imgL_eq_map w _ _ (fun x => by simp [emb_smulR, UR_spec]) _
  have h := LemmaC_core hR w hw v n0
    (fun x hx => hSB (by rw [e1]; exact ⟨x, hx, rfl⟩)) hUB hDS ram
  unfold len
  rw [e1, e2]
  exact le_trans h le_self_add

lemma exists_int_smul_mem (i : ℕ) (x : Vl D u i) :
    ∃ r : 𝓞 D.what₂.LL, r ≠ 0 ∧ r • x ∈ ((D.fm u).lat i).L := by
  first | exact UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem .. | (apply UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem D u i x | exact @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem D u i | exact @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem D u | exact @UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem D

lemma finrank_ramSub : Module.finrank D.what₂.LL (D.fm u).ramSub = (D.mem u).A.du := by
  rw [← D.nuIn_range u, LinearMap.finrank_range_of_inj (D.nuIn_inj u), D.NuV_finrank u]

lemma ramL_ne_bot (h : 0 < (D.mem u).A.du) : (D.fm u).ramL ≠ ⊥ := by
  have h1 : (D.fm u).ramSub ≠ ⊥ := by
    intro h0
    have := finrank_ramSub (u := u)
    rw [h0, finrank_bot] at this
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
  obtain ⟨r, hr, hrx⟩ := exists_int_smul_mem 0 x
  intro hbot
  have hmem : r • x ∈ (D.fm u).ramL := by
    refine ⟨hrx, ?_⟩
    show r • x ∈ (D.fm u).ramSub
    rw [← algebraMap_smul D.what₂.LL r x]
    exact Submodule.smul_mem _ _ hx
  rw [hbot, Submodule.mem_bot, ← algebraMap_smul D.what₂.LL r x] at hmem
  rcases smul_eq_zero.mp hmem with h0 | h0
  · exact hr ((FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL) (h0.trans (map_zero _).symm))
  · exact hx0 h0

theorem muMax_line' (hS : HidaSetting D u) (W : FreeT D u) : (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  by_cases hd : D.duS u = 0
  · have : Module.Finite D.what₂.LL (Vl D u 0) := Module.Finite.of_basis ((D.fm u).lat 0).b
    have hsub : Subsingleton (Vl D u 0) := Module.finrank_zero_iff.mp (by rw [finrank_Vl, hd])
    have e : (D.fm u).ramL = ((D.fm u).lat 0).L :=
      le_antisymm inf_le_left (fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _)
    show Formalism.HN.muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (D.fm u).ramL ≤ _
    rw [e]; exact le_rfl
  · refine muMax_line (ramL_ne_bot ?_)
    have h := rank_nat W
    have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    have hN := D.R.N_pos D.R.m
    have h2 : 0 < 2 * D.R.f * D.R.N D.R.m := Nat.mul_pos (Nat.mul_pos two_pos hf) hN
    have hT : 0 < (D.mem u).A.T - 1 - 1 := by have := hS.1; omega
    by_contra h0
    have h0' : (D.mem u).A.du = 0 := by omega
    rw [h0', zero_mul] at h
    exact absurd h.symm (Nat.mul_pos (Nat.pos_of_ne_zero hd) (pow_pos hT _)).ne'

variable (D u)

def SlopeLine : Prop :=
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

def LemB : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ)))) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))))

variable {D u}

theorem slopeEstimate_of_lemmaB_slopeLine (hS : HidaSetting D u) (W : FreeT D u) (hμ : SlopeLine D u) (hB : LemB D u) (h1 : Conclusion1 D u) :
    Conclusion2 D u := by
  obtain ⟨_, _, _, h4, _, _, _, _, h9⟩ := h1
  refine ⟨rank_line W, hμ, muMax_line' hS W, fun w hw hs v => ?_⟩
  have hR : Rat0 D u := Rat0_of_IntAtT w hw hs h4
  have ram : ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
      Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ := fun φ hφ =>
    ⟨(h9 0 (Nat.zero_le _) v φ hφ).1, (h9 0 (Nat.zero_le _) v φ hφ).2.1, (h9 0 (Nat.zero_le _) v φ hφ).2.2.2.2.2⟩
  obtain ⟨hUB, hDS⟩ := h4 0 (Nat.zero_le _) w hw hs v
  refine ⟨fun hd => ?_, fun hb => ?_⟩
  · obtain ⟨a1, a2⟩ := (hB w hw hs v).1 hd
    exact ⟨a1, a2, LemmaC_one hR w hw v a1 hUB hDS ram⟩
  · obtain ⟨a1, a2⟩ := (hB w hw hs v).2 hb
    exact ⟨a1, a2, LemmaC_two hR w hw v _ hb a1 hUB hDS ram⟩

theorem len_comp_le {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A : Submodule R M) (g h : M →ₗ[R] M)
    (hg : A.map g ≤ A) (_hh : A.map h ≤ A) :
    Module.length R (A ⧸ (A.map (g ∘ₗ h)).comap A.subtype) ≤
      Module.length R (A ⧸ (A.map g).comap A.subtype) + Module.length R (A ⧸ (A.map h).comap A.subtype) := by
  have hg' : ∀ x ∈ A, g x ∈ A := fun x hx => hg ⟨x, hx, rfl⟩
  let γ : A →ₗ[R] A := g.restrict hg'
  have hHQ : (A.map h).comap A.subtype ≤ ((A.map (g ∘ₗ h)).comap A.subtype).comap γ := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, ha, by
      show g (h a) = g (x : M)
      rw [hax]; rfl⟩
  let γb : (A ⧸ (A.map h).comap A.subtype) →ₗ[R] (A ⧸ (A.map (g ∘ₗ h)).comap A.subtype) :=
    Submodule.mapQ _ _ γ hHQ
  have e := Module.length_eq_add_of_exact (LinearMap.range γb).subtype (LinearMap.range γb).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h1 : Module.length R (LinearMap.range γb) ≤ Module.length R (A ⧸ (A.map h).comap A.subtype) :=
    Module.length_le_of_surjective γb.rangeRestrict γb.surjective_rangeRestrict
  have hP : (A.map g).comap A.subtype ≤
      LinearMap.ker ((LinearMap.range γb).mkQ ∘ₗ ((A.map (g ∘ₗ h)).comap A.subtype).mkQ) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
    show Submodule.Quotient.mk (γ ⟨a, ha⟩) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hax
  have hs : Function.Surjective (Submodule.liftQ _ _ hP) := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
    exact (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have h2 := Module.length_le_of_surjective _ hs
  rw [e, add_comm]
  exact add_le_add h2 h1

lemma len_id {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A : Submodule R M) :
    Module.length R (A ⧸ (A.map (LinearMap.id : M →ₗ[R] M)).comap A.subtype) = 0 := by
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
  simp

theorem len_list_le {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] (A : Submodule R M)
    (g : ι → (M →ₗ[R] M)) (l : List ι) (hg : ∀ v ∈ l, A.map (g v) ≤ A) :
    A.map (l.foldr (fun v G => (g v).comp G) LinearMap.id) ≤ A ∧
    Module.length R (A ⧸ (A.map (l.foldr (fun v G => (g v).comp G) LinearMap.id)).comap A.subtype) ≤
      (l.map (fun v => Module.length R (A ⧸ (A.map (g v)).comap A.subtype))).sum := by
  induction l with
  | nil => exact ⟨by simp, by rw [List.foldr_nil, len_id]; simp⟩
  | cons v l ih =>
    obtain ⟨i1, i2⟩ := ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    have hv := hg v List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [List.foldr_cons, Submodule.map_comp]
      exact le_trans (Submodule.map_mono i1) hv
    · rw [List.foldr_cons, List.map_cons, List.sum_cons]
      exact le_trans (len_comp_le A _ _ hv i1) (add_le_add_right i2 _)

theorem len_pow_le {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A : Submodule R M) (G : M →ₗ[R] M)
    (hG : A.map G ≤ A) (m : ℕ) :
    A.map (G ^ m) ≤ A ∧
    Module.length R (A ⧸ (A.map (G ^ m)).comap A.subtype) ≤ m • Module.length R (A ⧸ (A.map G).comap A.subtype) := by
  induction m with
  | zero =>
    refine ⟨by simp [Module.End.one_eq_id], ?_⟩
    rw [pow_zero, Module.End.one_eq_id, len_id]; simp
  | succ m ih =>
    obtain ⟨i1, i2⟩ := ih
    rw [pow_succ, Module.End.mul_eq_comp]
    refine ⟨?_, ?_⟩
    · rw [Submodule.map_comp]; exact le_trans (Submodule.map_mono hG) i1
    · rw [succ_nsmul]
      exact le_trans (len_comp_le A _ _ i1 hG) (add_le_add_left i2 _)

lemma entry_le (τ : D.what₂.Tau) (a : Fin (D.R.N 0)) (ha : a.1 ≠ 0) :
    (((D.fm u).lam 0 τ).w a).natAbs ≤ Wt D u τ := by
  have h1 := Finset.le_sup (s := Finset.range (D.R.m + 1))
    (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
      if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
      else (((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.mpr (Nat.succ_pos D.R.m))
  have h2 := Finset.le_sup (s := (Finset.univ : Finset (Fin (D.R.N 0))))
    (f := fun a : Fin (D.R.N 0) =>
      if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
      else (((D.fm u).lam 0 τ).w a - ((0 * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_univ a)
  have h3 := le_trans h2 h1
  rw [if_neg (fun h => ha h.1)] at h3
  have e0 : ((0 * (D.R.t + 1) / 2 : ℕ) : ℤ) = 0 := by simp
  rw [e0, sub_zero] at h3
  exact h3

lemma aTop_le_amax {τ : D.what₂.Tau} (hτ : τ ∈ tops D) : (D.fm u).aTop τ ≤ amax D u :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨τ, hτ, le_rfl⟩)

lemma bTop_le (τ : D.what₂.Tau) : (D.fm u).bTop τ ≤ (Wt D u τ : ℤ) := by
  have hk : 2 ≤ D.R.N 0 := two_le_N D.R 0
  have h := entry_le (u := u) τ ⟨D.R.N 0 - 1, by omega⟩ (by show D.R.N 0 - 1 ≠ 0; omega)
  unfold MemberForms.bTop DomWeight.detShift
  rw [dif_pos (D.R.N_pos 0)]
  have h2 : -(((D.fm u).lam 0 τ).w ⟨D.R.N 0 - 1, by omega⟩) ≤
      ((((D.fm u).lam 0 τ).w ⟨D.R.N 0 - 1, by omega⟩).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]; exact neg_le_abs _
  exact le_trans h2 (by exact_mod_cast h)

lemma wsum_le {τ : D.what₂.Tau} (hτ : τ ∈ tops D) :
    wsum ((D.fm u).lam 0 τ) ≤ amax D u + ((D.R.N 0 - 1 : ℕ) : ℤ) * (Wt D u τ : ℤ) := by
  unfold wsum
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨0, D.R.N_pos 0⟩ : Fin (D.R.N 0)))]
  refine add_le_add (aTop_le_amax hτ) ?_
  have h := Finset.sum_le_card_nsmul (Finset.univ.erase (⟨0, D.R.N_pos 0⟩ : Fin (D.R.N 0)))
    (fun i => ((D.fm u).lam 0 τ).w i) (Wt D u τ : ℤ) (fun i hi => by
      have hne : i.1 ≠ 0 := fun h0 => (Finset.mem_erase.mp hi).1 (Fin.ext h0)
      have h1 := entry_le (u := u) τ i hne
      have h2 : ((D.fm u).lam 0 τ).w i ≤ ((((D.fm u).lam 0 τ).w i).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact le_abs_self _
      exact le_trans h2 (by exact_mod_cast h1))
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

theorem twist_le {τ : D.what₂.Tau} (hτ : τ ∈ tops D) :
    ((wsum ((D.fm u).lam 0 τ) : ℝ) + (D.R.k : ℝ) * ((D.fm u).bTop τ : ℝ)) / (D.R.k : ℝ) ≤
      (amax D u : ℝ) / D.R.k + 2 * (Wt D u τ : ℝ) := by
  have hk2 : 2 ≤ D.R.k := by have := two_le_N D.R 0; rwa [D.R.N_zero] at this
  have hk : (0 : ℝ) < (D.R.k : ℝ) := by exact_mod_cast (by omega : 0 < D.R.k)
  have h1 : (wsum ((D.fm u).lam 0 τ) : ℝ) ≤ (amax D u : ℝ) + ((D.R.k : ℝ) - 1) * (Wt D u τ : ℝ) := by
    have := wsum_le (u := u) hτ
    rw [show ((D.R.N 0 - 1 : ℕ) : ℤ) = ((D.R.k - 1 : ℕ) : ℤ) from by rw [D.R.N_zero]] at this
    have h' : ((wsum ((D.fm u).lam 0 τ) : ℤ) : ℝ) ≤
        ((amax D u + ((D.R.k - 1 : ℕ) : ℤ) * (Wt D u τ : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : 1 ≤ D.R.k)] at h'
    exact h'
  have h2 : ((D.fm u).bTop τ : ℝ) ≤ (Wt D u τ : ℝ) := by exact_mod_cast bTop_le (u := u) τ
  have hW : (0 : ℝ) ≤ (Wt D u τ : ℝ) := Nat.cast_nonneg _
  rw [div_add' _ _ _ hk.ne', div_le_div_iff_of_pos_right hk]
  nlinarith [mul_le_mul_of_nonneg_left h2 hk.le]

lemma tL_eq_map (w : D.what₂.places.Pl) (n0 : ℕ) (A : Submodule (Ow D w) (Vl D u 0)) :
    tL D u w (n0 : ℤ) A =
      A.map ((((D.mem u).A.T : ℕ) : Ow D w) ^ n0 • (LinearMap.id : Vl D u 0 →ₗ[Ow D w] Vl D u 0)) :=
  imgL_eq_map w _ _ (fun x => by simp [emb_smulR]) _

def nb (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : ℕ :=
  ((D.fm u).bTop ((D.fm u).tauOf w v)).toNat

def gR (hR : Rat0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) : Vl D u 0 →ₗ[Ow D w] Vl D u 0 :=
  (((D.mem u).A.T : ℕ) : Ow D w) ^ nb D u w v • UR hR w v

def GR (hR : Rat0 D u) (w : D.what₂.places.Pl) (l : List (D.mem u).A.vT) : Vl D u 0 →ₗ[Ow D w] Vl D u 0 :=
  l.foldr (fun v G => (gR hR w v).comp G) LinearMap.id

lemma gR_spec (hR : Rat0 D u) (w v) (x : Vl D u 0) :
    (D.fm u).emb 0 (gR hR w v x) = ((D.mem u).A.T : ℂ) ^ nb D u w v • Uop D u 0 v ((D.fm u).emb 0 x) := by
  simp [gR, emb_smulR, UR_spec]

lemma GR_spec (hR : Rat0 D u) (w) (l : List (D.mem u).A.vT) (x : Vl D u 0) :
    (D.fm u).emb 0 (GR hR w l x) =
      ((D.mem u).A.T : ℂ) ^ (l.map (nb D u w)).sum • Ul D u 0 l ((D.fm u).emb 0 x) := by
  induction l with
  | nil => simp [GR, Ul]
  | cons v l ih =>
    show (D.fm u).emb 0 (gR hR w v (GR hR w l x)) = _ • Uop D u 0 v (Ul D u 0 l _)
    rw [gR_spec, ih, map_smul, smul_smul, List.map_cons, List.sum_cons, pow_add]

lemma GR_pow_spec (hR : Rat0 D u) (w) (l : List (D.mem u).A.vT) (n : ℕ) : ∀ x : Vl D u 0,
    (D.fm u).emb 0 ((GR hR w l ^ n) x) =
      (((D.mem u).A.T : ℂ) ^ (l.map (nb D u w)).sum) ^ n • (Ul D u 0 l ^ n) ((D.fm u).emb 0 x) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [pow_succ, Module.End.mul_apply, ih, GR_spec, map_smul, smul_smul, pow_succ (Ul D u 0 l),
      Module.End.mul_apply, pow_succ]

lemma mem_VV {w : D.what₂.places.Pl} {v : (D.mem u).A.vT} (hv : v ∈ VV D u w) :
    (D.fm u).seenP w = true ∧ (D.fm u).tauOf w v ∈ tops D := by
  have hv' : v ∈ LT.VVT D u w := hv
  unfold LT.VVT at hv'
  split_ifs at hv' with hs
  · exact ⟨hs, (Finset.mem_filter.mp hv').2⟩
  · simp at hv'

lemma Nlam_eq (hS : HidaSetting D u) (hR : Rat0 D u) (w : D.what₂.places.Pl) :
    Nlam D u w = (Sram D u w).map (GR hR w (VV D u w).toList ^ D.R.m) := by
  refine imgL_eq_map w _ _ (fun x => ?_) _
  rw [GR_pow_spec, LinearMap.smul_apply]
  congr 1
  rw [← pow_mul, ← zpow_natCast]
  congr 1
  unfold LT.expT
  rw [Finset.sum_map_toList]
  push_cast
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl (fun v hv => ?_)
  exact Int.toNat_of_nonneg (hS.2.2 _ (mem_VV hv).2)

lemma gR_Sram (hS : HidaSetting D u) (hR : Rat0 D u) (hB : LemB D u) (h1 : Conclusion1 D u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) {v : (D.mem u).A.vT} (hv : v ∈ VV D u w) :
    (Sram D u w).map (gR hR w v) ≤ Sram D u w ∧
    ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)) ∧
      Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v)).comap (Sram D u w).subtype) ≤
        ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) := by
  obtain ⟨_, _, _, h4, _, _, _, _, h9⟩ := h1
  obtain ⟨hs, ht⟩ := mem_VV hv
  have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) := hS.2.2 _ ht
  have hnb : ((nb D u w v : ℕ) : ℤ) = (D.fm u).bTop ((D.fm u).tauOf w v) := Int.toNat_of_nonneg hb
  obtain ⟨hUB, hDS⟩ := h4 0 (Nat.zero_le _) w hw hs v
  obtain ⟨a1, n, a2, a3⟩ := (hB w hw hs v).2 hb
  rw [← hnb, tL_eq_map] at a1 a2
  have ram : ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
      Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ := fun φ hφ =>
    ⟨(h9 0 (Nat.zero_le _) v φ hφ).1, (h9 0 (Nat.zero_le _) v φ hφ).2.1, (h9 0 (Nat.zero_le _) v φ hφ).2.2.2.2.2⟩
  refine ⟨?_, n, a3, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxB : (((D.mem u).A.T : ℕ) : Ow D w) ^ nb D u w v • x ∈ (D.fm u).Bw 0 w v := a1 ⟨x, hx.1, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hUB _ hxB
    have e : gR hR w v x = y := by
      apply (D.fm u).emb_inj 0
      rw [hy', gR_spec, emb_smulR, map_smul]; simp
    rw [e]
    refine ⟨hy, mem_ramSub.mpr ?_⟩
    rw [← e, gR_spec]
    exact Submodule.smul_mem _ _ (ram _ (mem_ramSub.mp hx.2)).1
  · have h := LemmaC_core hR w hw v (nb D u w v) (fun x hx => a1 ⟨x, hx, rfl⟩) hUB hDS ram
    unfold len at a2
    rw [a2] at h
    exact_mod_cast h

theorem ramified_length_bound (hS : HidaSetting D u) (hB : LemB D u) (h1 : Conclusion1 D u) : ∀ w, OverT D u w →
    Nlam D u w ≤ Sram D u w ∧
    (∃ n : ℕ, len D u w (Sram D u w) (Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ VV D u w,
        ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v)))) := by
  intro w hw
  by_cases hs : (D.fm u).seenP w = true
  · have hR : Rat0 D u := Rat0_of_IntAtT w hw hs h1.2.2.2.1
    have hg : ∀ v ∈ (VV D u w).toList, (Sram D u w).map (gR hR w v) ≤ Sram D u w :=
      fun v hv => (gR_Sram hS hR hB h1 w hw (Finset.mem_toList.mp hv)).1
    obtain ⟨hG, hGl⟩ := len_list_le (Sram D u w) (gR hR w) (VV D u w).toList hg
    obtain ⟨hP, hPl⟩ := len_pow_le (Sram D u w) (GR hR w (VV D u w).toList) hG D.R.m
    rw [Nlam_eq hS hR w]
    refine ⟨hP, ?_⟩
    have H : ∀ v : {v // v ∈ VV D u w}, ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℚ) +
            (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℚ)) / (D.R.k : ℚ)) ∧
        Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v.1)).comap (Sram D u w).subtype) ≤
          ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) :=
      fun v => (gR_Sram hS hR hB h1 w hw v.2).2
    choose nn hnq hnl using H
    have hsum : Module.length (Ow D w) (Sram D u w ⧸
        ((Sram D u w).map (GR hR w (VV D u w).toList ^ D.R.m)).comap (Sram D u w).subtype) ≤
        ((D.R.m * ∑ v ∈ (VV D u w).attach, (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℕ∞) := by
      refine le_trans hPl ?_
      push_cast
      rw [nsmul_eq_mul]
      refine mul_le_mul_right (le_trans hGl ?_) _
      rw [Finset.sum_map_toList, ← Finset.sum_attach]
      exact Finset.sum_le_sum (fun v _ => by exact_mod_cast hnl v)
    obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hsum
    refine ⟨n, hn, ?_⟩
    have hk : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
    have he : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
    have hterm : ∀ v : {v // v ∈ VV D u w},
        ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (D.duS u * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
            (D.fm u).bTop ((D.fm u).tauOf w v.1))) := by
      intro v
      have ht := (mem_VV v.2).2
      have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v.1) := hS.2.2 _ ht
      have hbR : (0 : ℝ) ≤ ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := by exact_mod_cast hb
      have hN1 := twist_le (u := u) ht
      have hq : ((nn v : ℕ) : ℝ) = (D.what₂.places.ramIdx w : ℝ) * ((D.duS u : ℝ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hnq v)
        push_cast at this; exact this
      have hk1 : ((D.R.k - 1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Nat.sub_le _ _
      push_cast
      rw [hq, mul_div_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ he
      have e1 : (D.duS u : ℝ) * (((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) ≤
          (D.duS u : ℝ) * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1)) :=
        mul_le_mul_of_nonneg_left hN1 hd
      have e2 : ((D.R.k - 1 : ℕ) : ℝ) * (D.duS u : ℝ) ≤ (D.duS u : ℝ) * (D.R.k : ℝ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk1 hd
      have e3 : 0 ≤ (D.duS u : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := mul_nonneg hd hbR
      nlinarith
    calc (n : ℝ) ≤ ((D.R.m * ∑ v ∈ (VV D u w).attach,
            (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach,
            ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach, ((D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v.1)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hterm v)) (Nat.cast_nonneg _)
      _ = _ := by
          rw [Finset.sum_attach (VV D u w) (fun v => (D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v)))), ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  · have hs' : (D.fm u).seenP w = false := by simpa using hs
    have hVV : VV D u w = ∅ := by simp [LT.VVT, hs']
    have hN : Nlam D u w = Sram D u w := by
      have := imgL_eq_map (u := u) w ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (Uprod D u 0 w) ^ D.R.m) LinearMap.id
        (fun x => by simp [LT.expT, LT.Uprod, LT.VVT, hs']) (Sram D u w)
      rw [Submodule.map_id] at this
      exact this
    rw [hN, hVV]
    refine ⟨le_rfl, 0, ?_, by simp⟩
    unfold len
    rw [Submodule.comap_subtype_self]
    simp

theorem exists_overT (D : D7) (u : D.what₂.Word) : ∃ w, OverT D u w := by
  have hp := (D.mem u).A.T_prime
  have htop : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit D.what₂.LL hp
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ htop
  have hpP : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ P := hPle (Ideal.mem_span_singleton_self _)
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let Q : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨P, hPmax.isPrime, hP0⟩
  refine ⟨D.plEq.symm Q, ?_⟩
  by_contra hne
  have hne' : D.what₂.places.resChar (D.plEq.symm Q) ≠ (D.mem u).A.T := hne
  have h1 := D.val_resChar' (D.plEq.symm Q)
  rw [Equiv.apply_symm_apply] at h1
  have hqP : ((D.what₂.places.resChar (D.plEq.symm Q) : ℕ) : 𝓞 D.what₂.LL) ∈ P := by
    have : Q.valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL
        ((D.what₂.places.resChar (D.plEq.symm Q) : ℕ) : 𝓞 D.what₂.LL)) < 1 := by
      rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      have := D.what₂.places.ramIdx_pos (D.plEq.symm Q)
      omega
    exact (Q.valuation_lt_one_iff_mem _).mp this
  have hcop : IsCoprime ((D.what₂.places.resChar (D.plEq.symm Q) : ℕ) : ℤ) (((D.mem u).A.T : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes (D.what₂.places.resChar_prime _) hp).mpr hne')
  obtain ⟨a, b, hab⟩ := hcop
  have h2 : (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar (D.plEq.symm Q) : ℕ) : 𝓞 D.what₂.LL) +
      (b : 𝓞 D.what₂.LL) * (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab
  exact hPmax.ne_top ((Ideal.eq_top_iff_one P).mpr (h2 ▸ P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hpP)))

lemma fi_of_rat {i j : ℕ} (f : Fn D u i →ₗ[ℂ] Fn D u j) (h : ∀ x, ∃ y, (D.fm u).emb j y = f ((D.fm u).emb i x)) :
    ∀ φ ∈ (D.fm u).Fi i, f φ ∈ (D.fm u).Fi j := by
  intro φ hφ
  rw [← ((D.fm u).emb_basis i).2] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨y, hy⟩ := h (((D.fm u).lat i).b a)
    rw [← hy]; exact emb_mem j y
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem KFi_of (C : ℝ) (h : LatticeChainWithoutLast D u C) : KFi D u := by
  obtain ⟨w, hw⟩ := exists_overT D u
  intro i hi
  have hT : tpow D u (lossK D u C) ≠ 0 := pow_ne_zero _ (T_ne D u)
  have key : ∀ φ ∈ (D.fm u).Fi i, (tpow D u (lossK D u C) • KT D u i) φ ∈ (D.fm u).Fi (i + 1) := by
    by_cases hs : (D.fm u).seenP w = true
    · obtain ⟨BV, _, hI⟩ := (((h w hw).1 i hi).2 hs)
      exact fi_of_rat _ (rat_of_into w (tpow D u (lossK D u C) • KT D u i) _ _ hI (S_span i w))
    · have hs' : (D.fm u).seenP w = false := by simpa using hs
      exact fi_of_rat _ (rat_of_into w (tpow D u (lossK D u C) • KT D u i) _ _ (((h w hw).1 i hi).1 hs') (S_span i w))
  intro φ hφ
  have := Submodule.smul_mem _ (tpow D u (lossK D u C))⁻¹ (key φ hφ)
  rwa [LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hT, one_smul] at this

variable (D u) in

def DiaFi : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, ∀ a, dia D u i v a φ ∈ (D.fm u).Fi i

theorem FiSt_of (h5 : IntOffT D u) (hd : DiaFi D u) : FiSt D u := by
  obtain ⟨w, hw⟩ := exists_offT D u
  intro i hi v φ hφ
  exact ⟨fi_of_rat _ (rat_of_into w _ _ _ (h5 i hi w hw v).1 (S_span i w)) φ hφ,
    fi_of_rat _ (rat_of_into w _ _ _ (h5 i hi w hw v).2 (S_span i w)) φ hφ, hd i hi v φ hφ⟩

lemma dense_embLL (D : D7) : DenseRange D.what₂.embLL := by
  have hv : (InfinitePlace.mk D.what₂.embLL).IsComplex := IsTotallyComplex.isComplex _
  have hd := denseRange_embedding_of_isComplex _ hv
  rcases InfinitePlace.embedding_mk_eq D.what₂.embLL with h | h
  · rw [h] at hd; exact hd
  · rw [h] at hd
    have h2 : DenseRange ((starRingEnd ℂ) ∘ (ComplexEmbedding.conjugate D.what₂.embLL)) :=
      DenseRange.comp (Function.Surjective.denseRange (fun z => ⟨(starRingEnd ℂ) z, Complex.conj_conj z⟩)) hd
        Complex.continuous_conj
    have e : ((starRingEnd ℂ) ∘ (ComplexEmbedding.conjugate D.what₂.embLL)) = D.what₂.embLL := by
      funext x; simp [ComplexEmbedding.conjugate_coe_eq]
    rwa [e] at h2

lemma cplx_rat (h : (D.fm u).PRat)
    (hb : ∀ x : Vl D u D.R.m,
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk D.what₂.embLL) ((D.fm u).PtL h x)
        ((D.fm u).PtL h x)).re ≤
      ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X (InfinitePlace.mk D.what₂.embLL) x x).re)
    (x : Vl D u D.R.m) :
    ((D.fm u).ipP (Pt D u ((D.fm u).emb D.R.m x)) (Pt D u ((D.fm u).emb D.R.m x))).re ≤
      ptB D u * ((D.fm u).ipC D.R.m ((D.fm u).emb D.R.m x) ((D.fm u).emb D.R.m x)).re := by
  have := hb x
  rw [(D.fm u).ptEmb_norm, (D.fm u).PtL_spec h x, (D.fm u).emb_norm] at this
  exact this

theorem cplx_of_place (h : (D.fm u).PRat)
    (hb : ∀ x : Vl D u D.R.m,
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk D.what₂.embLL) ((D.fm u).PtL h x)
        ((D.fm u).PtL h x)).re ≤
      ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X (InfinitePlace.mk D.what₂.embLL) x x).re) :
    ∀ φ ∈ (D.fm u).Fi D.R.m,
      ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≤ ptB D u * ((D.fm u).ipC D.R.m φ φ).re := by
  intro φ hφ
  rw [← ((D.fm u).emb_basis D.R.m).2] at hφ
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hφ
  set e : ((D.fm u).lat D.R.m).ι → Fn D u D.R.m := fun a => (D.fm u).emb D.R.m (((D.fm u).lat D.R.m).b a) with he
  have e1 : ∀ z : ((D.fm u).lat D.R.m).ι → ℂ, (D.fm u).ipC D.R.m (∑ a, z a • e a) (∑ a, z a • e a) =
      ∑ a, (starRingEnd ℂ) (z a) * ∑ b, z b * (D.fm u).ipC D.R.m (e a) (e b) := by
    intro z
    rw [ipC_sum_left]
    exact Finset.sum_congr rfl (fun a _ => by rw [ipC_sum_right])
  have e2 : ∀ z : ((D.fm u).lat D.R.m).ι → ℂ,
      (D.fm u).ipP (Pt D u (∑ a, z a • e a)) (Pt D u (∑ a, z a • e a)) =
      ∑ a, (starRingEnd ℂ) (z a) * ∑ b, z b * (D.fm u).ipP (Pt D u (e a)) (Pt D u (e b)) := by
    intro z
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  have cont : ∀ c : ((D.fm u).lat D.R.m).ι → ((D.fm u).lat D.R.m).ι → ℂ,
      Continuous (fun z : ((D.fm u).lat D.R.m).ι → ℂ => ∑ a, (starRingEnd ℂ) (z a) * ∑ b, z b * c a b) := fun c =>
    continuous_finsetSum _ (fun a _ => (Complex.continuous_conj.comp (continuous_apply a)).mul
      (continuous_finsetSum _ (fun b _ => (continuous_apply b).mul continuous_const)))
  have hclosed : IsClosed {z : ((D.fm u).lat D.R.m).ι → ℂ |
      ((D.fm u).ipP (Pt D u (∑ a, z a • e a)) (Pt D u (∑ a, z a • e a))).re ≤
        ptB D u * ((D.fm u).ipC D.R.m (∑ a, z a • e a) (∑ a, z a • e a)).re} := by
    simp only [e1, e2]
    exact isClosed_le (Complex.continuous_re.comp (cont _))
      (continuous_const.mul (Complex.continuous_re.comp (cont _)))
  have hdense : DenseRange (Pi.map (fun _ : ((D.fm u).lat D.R.m).ι => (D.what₂.embLL : D.what₂.LL → ℂ))) :=
    DenseRange.piMap (fun _ => dense_embLL D)
  refine hdense.induction_on (p := fun z => ((D.fm u).ipP (Pt D u (∑ a, z a • e a)) (Pt D u (∑ a, z a • e a))).re ≤
        ptB D u * ((D.fm u).ipC D.R.m (∑ a, z a • e a) (∑ a, z a • e a)).re) z hclosed (fun r => ?_)
  have hr : ∑ a, (Pi.map (fun _ : ((D.fm u).lat D.R.m).ι => (D.what₂.embLL : D.what₂.LL → ℂ)) r) a • e a =
      (D.fm u).emb D.R.m (∑ a, r a • ((D.fm u).lat D.R.m).b a) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [LinearMap.map_smulₛₗ]; rfl)
  rw [hr]
  exact cplx_rat h hb _

theorem deg_eq_degZ (τ : D.what₂.Tau) :
    (D.fm u).deg τ = Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr D u τ) (sgTr D u τ) := by
  have hN : ((D.R.N D.R.m : ℕ) : ℤ) = ((D.R.N D.R.m - 1 : ℕ) : ℤ) + 1 := by
    have := D.R.N_pos D.R.m
    omega
  unfold MemberForms.deg Formalism.MainNotions.PrimeDegreeVariant.degZ Formalism.MainNotions.PrimeDegreeVariant.wsum lamTr sgTr wSh cTw
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hN]
  ring

section Shift

open Formalism.MainNotions.PrimeDegreeVariant

theorem sqAct_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) (g : GL (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    sqAct ℂ n (wSh l c) g f = detPow ℂ n g (-c) • sqAct ℂ n l g f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      simp [Matrix.det_isEmpty]
    unfold sqAct detPow
    simp [DomWeight.detShift, hd]
  · unfold sqAct
    rw [detShift_wSh l c hn, smul_smul]
    congr 1
    unfold detPow
    rw [sub_eq_add_neg, zpow_add, Units.val_mul, mul_comm]

theorem det_embGL {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.det (embGL ℂ n N h g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  have e : ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix
        (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, e, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_lastGL {N : ℕ} (hN : 0 < N) (a : ℂˣ) :
    Matrix.GeneralLinearGroup.det (lastGL ℂ N a) = a := by
  apply Units.ext
  simp only [lastGL, diagGL, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (⟨N - 1, by omega⟩ : Fin N)]
  · rw [if_pos (by show N - 1 + 1 = N; omega)]
  · intro b _ hb
    rw [if_neg]
    · rfl
    · intro h
      apply hb
      apply Fin.ext
      show b.1 = N - 1
      omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem degZ_wSh {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (c : ℤ) :
    degZ (wSh lam c) (wSh sg c) = degZ lam sg - c := by
  subst h
  unfold degZ Formalism.MainNotions.PrimeDegreeVariant.wsum wSh
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem normFock_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) (f g : MvPolynomial (Fin n × Fin n) ℂ) :
    normFock (wSh l c) f g = normFock l f g := by
  unfold normFock; rw [extremal_wSh]

theorem brBd_wSh {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (c : ℤ) :
    brBd h (wSh lam c) (wSh sg c) = brBd h lam sg := by
  have hs : (wSh lam c).spread = lam.spread := by
    unfold DomWeight.spread wSh
    split_ifs <;> simp
  have h0 : D0 h (wSh lam c) (wSh sg c) = D0 h lam sg := by
    unfold D0 wSh
    exact Finset.sum_congr rfl fun i _ => by simp
  have h1 : D1 h (wSh lam c) (wSh sg c) = D1 h lam sg := by
    unfold D1
    rw [h0]
    exact Finset.sum_congr rfl fun i _ => by simp [wSh]
  unfold brBd cBd
  rw [hs, h1, delSq_wSh]

theorem isBr_wSh {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (c : ℤ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (H : IsBr h lam sg br) :
    IsBr h (wSh lam c) (wSh sg c) br := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  have hN : 0 < N := by omega
  refine ⟨by simpa only [delSq_wSh] using h1, by simpa only [delSq_wSh] using h2, by simpa only [delSq_wSh] using h3,
    fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [delSq_wSh] at hf
    rw [sqAct_wSh, sqAct_wSh, map_smul, h4 g f hf]
    unfold detPow
    rw [det_embGL]
  · rw [delSq_wSh] at hf
    rw [sqAct_wSh, map_smul, h5 a f hf, degZ_wSh h, smul_smul]
    unfold detPow
    rw [det_lastGL hN, ← Units.val_mul, ← zpow_add]
    congr 3
    ring
  · rw [delSq_wSh] at hf
    rw [normFock_wSh, normFock_wSh, brBd_wSh]
    exact h6 f hf

theorem wSh_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) : wSh (wSh l c) (-c) = l := by
  cases l; simp [wSh]

theorem admissibleBranching_iff_isBranching {D : D7} {u : D.what₂.Word} (P : Pend D u) :
    ArchimedeanSignatureMatching P ↔ ∀ τ, IsBr (Nm_succ D.R) ((D.fm u).lam D.R.m τ) ((D.fm u).sg τ) (P.br τ) := by
  refine ⟨fun H τ => ?_, fun H τ => isBr_wSh _ _ _ _ _ (H τ)⟩
  have := isBr_wSh _ _ _ (-(cTw D.R)) _ (H τ)
  unfold lamTr sgTr at this
  rwa [wSh_wSh, wSh_wSh] at this

end Shift

theorem br_frames (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (τ : D.what₂.Tau) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hf : f ∈ delSq ℂ _ (lamTr D u τ)) :
    P.br τ (sqAct ℂ _ (lamTr D u τ) (gFull D u g) f) =
      (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) • sqAct ℂ _ (sgTr D u τ) g (P.br τ f) := by
  obtain ⟨-, -, -, h4a, h5, -⟩ := h4 τ
  unfold gFull
  rw [(factSqActMul ℂ _ _ _ _ f).1, h4a g _ ((factSqStable ℂ _ _ _).2 f hf), h5 _ f hf, deg_eq_degZ]
  unfold sqAct
  rw [map_smul, smul_comm]

lemma blk_IntSpan (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (w : D.what₂.places.Pl)
    (p : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hp : p ∈ IntSpan D w ((D.fm u).lam D.R.m)) : blk (fun τ => P.br τ) p ∈ IntSpan D w (D.fm u).sg := by
  unfold IntSpan at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hx
    have hg : ∀ τ, ∃ g ∈ delSq ℤ _ ((D.fm u).sg τ),
        P.br τ (MvPolynomial.map (Int.castRingHom ℂ) (f τ)) = MvPolynomial.map (Int.castRingHom ℂ) g :=
      fun τ => by
        have h := (h4 τ).1 (f τ) (by unfold lamTr; rw [delSq_wSh]; exact hf τ)
        unfold sgTr at h
        rwa [delSq_wSh] at h
    choose g hg1 hg2 using hg
    refine AddSubgroup.subset_closure ⟨r, g, hr, hg1, ?_⟩
    rw [map_smul, blk_ten]
    congr 2
    funext τ
    exact hg2 τ
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem Pt_loc (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (hPF : ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC)
    (w : D.what₂.places.Pl) : ∀ x ∈ (D.fm u).S D.R.m w,
      ∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = Pt D u ((D.fm u).emb D.R.m x) := by
  intro x hx
  refine (P.pt_co w _ (hPF _ (emb_mem _ x))).mpr (fun c => ?_)
  rw [P.Pt_eq w _ (emb_mem _ x) c]
  exact blk_IntSpan P h4 w _ (P.lat_co w x hx c)

theorem PRat_of (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (hPF : ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC) :
    (D.fm u).PRat := by
  obtain ⟨w, _⟩ := exists_offT D u
  intro x
  show ∃ y, (D.fm u).ptEmb y = Pt D u ((D.fm u).emb D.R.m x)
  have hx : x ∈ Submodule.span D.what₂.LL ((D.fm u).S D.R.m w : Set (Vl D u D.R.m)) := by
    rw [S_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨y, _, hy⟩ := Pt_loc P h4 hPF w x hx; exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, h1⟩ := hx; obtain ⟨a2, h2⟩ := hy
    exact ⟨a1 + a2, by rw [map_add, map_add, map_add, h1, h2]⟩
  | smul r x _ hx =>
    obtain ⟨a1, h1⟩ := hx
    exact ⟨r • a1, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul]⟩

lemma mem_of_forall_inLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (A : Submodule (𝓞 K) V) (y : V) (h : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), InLoc w A y) : y ∈ A := by
  let I : Ideal (𝓞 K) :=
    { carrier := {s | s • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • y ∈ A
        rw [add_smul]; exact A.add_mem ha hb
      zero_mem' := by show (0 : 𝓞 K) • y ∈ A; rw [zero_smul]; exact A.zero_mem
      smul_mem' := fun c a ha => by
        show (c • a) • y ∈ A
        rw [smul_eq_mul, mul_smul]; exact A.smul_mem c ha }
  by_contra hy
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 K) ∈ I := by rw [h1]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := by
    intro h0
    exact NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.mpr (h0 ▸ hM))
  obtain ⟨s, hs, hsy⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact hs (hIM hsy)

theorem Pt_integral (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (hPF : ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC)
    (h : (D.fm u).PRat) : (D.fm u).PtilIntegral h := by
  intro x hx
  refine mem_of_forall_inLoc _ _ (fun p => ?_)
  obtain ⟨y, hy, hy'⟩ := Pt_loc P h4 hPF (D.plEq.symm p) x (Submodule.subset_span hx)
  have e : y = (D.fm u).PtL h x := (D.fm u).ptEmb_inj (by rw [hy', (D.fm u).PtL_spec h x]; rfl)
  have := D.inLoc_of_mem_locW (D.plEq.symm p) (D.fm u).ptLat.L y hy
  rwa [Equiv.apply_symm_apply, e] at this

variable (D u) in

def ClassMapInjectiveBijectiveNorms : Prop :=
  Function.Injective (D.fm u).til ∧
  (∀ c, Function.Bijective ((D.fm u).stabMap c)) ∧
  (∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC) ∧
  (∀ (h : (D.fm u).PRat) (v : InfinitePlace D.what₂.LL) (x : Vl D u D.R.m),
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
        ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re)

theorem classMap_estimate_of_partial (P : Pend D u) (h4 : ArchimedeanSignatureMatching P) (h : ClassMapInjectiveBijectiveNorms D u) : Conclusion6 D u :=
  ⟨h.1, h.2.1, h.2.2.1,
    ⟨PRat_of P h4 h.2.2.1, Pt_integral P h4 h.2.2.1 _, h.2.2.2 _⟩,
    cplx_of_place (PRat_of P h4 h.2.2.1) (fun x => h.2.2.2 _ (InfinitePlace.mk D.what₂.embLL) x)⟩

theorem ramifiedLattice_of_chain_estimates (C : ℝ) (hC : 0 ≤ C) (hS : HidaSetting D u) (hKF : KFi D u) (hB : LemB D u) (h1 : Conclusion1 D u)
    (h3 : PointsLemma D u C) (h4 : LevelChainUOperatorCommutation D u) : Conclusion5 D u C := fun w hw =>
  ⟨(ramified_length_bound hS hB h1 w hw).1, column_exponent_lattice_bound C hC hS h1.1 hKF h3 h4 w hw, (ramified_length_bound hS hB h1 w hw).2⟩

theorem transportEstimate_of_admissible (hT : admT D u) (hd : DiaFi D u) (hX : CrossDia D u) (hU : UnfAll D u) (hC : UComm D u)
    (h4 : IntAtT D u) (h5 : IntOffT D u) : Conclusion1 D u :=
  baseChange_preserves_unitary_of (FiSt_of h5 hd) hT.2.2.2 hX hU hC h4 h5 (Rat0_of_Int h5)

theorem finiteModel_of_admissible_transports (hT : admT D u) (hF : FiSt D u) (hX : CrossDia D u) (hU : UnfAll D u) (C : ℝ)
    (h4 : Conclusion4 D u C) : division_rows_rational_lattice D u :=
  finiteModel_of_heckeEstimate hF hT.2.2.2 hX hU C h4

theorem classMap_estimate_of_admissible (hA : AdmE D u) (h : ClassMapInjectiveBijectiveNorms D u) : Conclusion6 D u := by
  obtain ⟨P, G, hA⟩ := hA
  exact classMap_estimate_of_partial P hA.2.2.2.2.2.1 h

variable (D u) in

def Rest (C : ℝ) : Prop :=
  DiaFi D u ∧ CrossDia D u ∧ UnfAll D u ∧ UComm D u ∧ IntAtT D u ∧ IntOffT D u ∧
  Nonempty (FreeT D u) ∧ SlopeLine D u ∧ LemB D u ∧
  LatticeChainWithoutLast D u C ∧ LevelChainUOperatorCommutation D u ∧ KDia D u ∧ ClassMapInjectiveBijectiveNorms D u ∧ Conclusion5Sharp D u

theorem conclusion_of_rest (C : ℝ) (hC : 0 ≤ C) (hS : HidaSetting D u) (hA : AdmE D u) (h : Rest D u C) : Conclusion₂ D u (C + 1) := by
  obtain ⟨hd, hX, hU, hUC, hI4, hI5, ⟨W⟩, hμ, hB, h3a, h4X, hKD, h6, h5S⟩ := h
  have hC1 : 0 ≤ C + 1 := by linarith
  have hF := FiSt_of hI5 hd
  have hKF := KFi_of C h3a
  have hM := DiaMul_of hF hU
  have h1 := baseChange_preserves_unitary_of hF hM hX hU hUC hI4 hI5 (Rat0_of_Int hI5)
  have h3 := latticeChain_succ_of_partial C hC h3a
  have h4 := heckeValue_estimate_of_record_value (C + 1) hC1 h4X hKD hKF
  exact ⟨h1, slopeEstimate_of_lemmaB_slopeLine hS W hμ hB h1, h3, h4, ramifiedLattice_of_chain_estimates (C + 1) hC1 hS hKF hB h1 h3 h4X, classMap_estimate_of_admissible hA h6,
    finiteModel_of_heckeEstimate hF hM hX hU (C + 1) h4, h4X, h5S⟩

theorem packetEstimate_of_remainder (C : ℝ) (hC : 0 ≤ C) (h : HidaSetting D u → AdmE D u → Rest D u C) : Stmt D u (C + 1) :=
  fun hS hA => conclusion_of_rest C hC hS hA (h hS hA)

def RestF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    HidaSetting (Fm.D x i) u → Rest (Fm.D x i) u C

theorem familyEstimate_of_remainder {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) (hC : 0 ≤ C) (h : RestF Fm C) : KudlaFamilyStatement Fm (C + 1) := by
  obtain ⟨x0, h⟩ := h
  rintro ⟨x1, hA⟩
  exact ⟨max x0 x1, fun x hx i u hS => conclusion_of_rest C hC hS (hA x (le_trans (le_max_right _ _) hx) i u)
    (h x (le_trans (le_max_left _ _) hx) i u hS)⟩

end Formalism.MainNotions.product_first_zeroth_parts
