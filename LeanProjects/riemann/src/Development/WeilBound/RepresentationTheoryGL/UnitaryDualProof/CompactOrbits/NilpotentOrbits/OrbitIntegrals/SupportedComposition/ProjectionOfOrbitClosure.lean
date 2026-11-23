import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil Set Polynomial

namespace PositivityTheory.RgUd.T.Nil.Orb.Oasm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

section Alg

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_add (x x' : Matrix (Fin n) (Fin n) k) : qZ Z (x + x') = qZ Z x + qZ Z x' := by
  funext i; simp [qZ, mul_add, trace_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_smul (a : k) (x : Matrix (Fin n) (Fin n) k) : qZ Z (a • x) = a • qZ Z x := by
  funext i; simp [qZ, trace_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_sub (x x' : Matrix (Fin n) (Fin n) k) : qZ Z (x - x') = qZ Z x - qZ Z x' := by
  funext i; simp [qZ, mul_sub, trace_sub]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_mem_Z {g : GL (Fin n) k} (hg : g ∈ Gz Z) {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Z) :
    g.val * a * g⁻¹.val = a := by
  rw [← hg a ha, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_conj {g : GL (Fin n) k} (hg : g ∈ Gz Z) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (g.val * x * g⁻¹.val) = qZ Z x := by
  funext i
  simp only [qZ]
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k)
  have hb : b * g.val = g.val * b := hg b (Module.finBasis k Z i).2
  have e : b * (g.val * x * g⁻¹.val) = g.val * (b * x) * g⁻¹.val := by
    rw [← mul_assoc, ← mul_assoc, hb, mul_assoc g.val b x]
  rw [e, trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_Bz_of_mem (hZ : CR Z) {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Z) : a ∈ Bz Z :=
  fun b hb => hZ.1 b hb a ha

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_zero_of_nilp (hZ : CR Z) {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Z) (h : IsNilpotent a) : a = 0 := by
  haveI := hZ.2
  obtain ⟨m, hm⟩ := h
  have h' : IsNilpotent (⟨a, ha⟩ : Z) := ⟨m, Subtype.ext (by simpa using hm)⟩
  exact congrArg Subtype.val (IsNilpotent.eq_zero h')

variable {Z}

theorem qZ_Z_exists (h2 : FibZN (k := k)) (hZ : CR Z) (y : Fin (Module.finrank k Z) → k) : ∃ c ∈ Z, qZ Z c = y := by
  obtain ⟨c, hc, hcy, -⟩ := h2 n Z hZ y
  exact ⟨c, hc, hcy⟩

theorem qZ_Z_inj (h2 : FibZN (k := k)) (hZ : CR Z) {c c' : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (hc' : c' ∈ Z)
    (h : qZ Z c = qZ Z c') : c = c' := by
  obtain ⟨d, hd, -, hiff⟩ := h2 n Z hZ (qZ Z c)
  have n1 : IsNilpotent (c - d) := (hiff c (mem_Bz_of_mem Z hZ hc)).1 ⟨rfl, c, hc, by simp⟩
  have n2 : IsNilpotent (c' - d) := (hiff c' (mem_Bz_of_mem Z hZ hc')).1 ⟨h.symm, c', hc', by simp⟩
  have z1 := eq_zero_of_nilp Z hZ (Z.sub_mem hc hd) n1
  have z2 := eq_zero_of_nilp Z hZ (Z.sub_mem hc' hd) n2
  rw [sub_eq_zero] at z1 z2
  rw [z1, z2]

theorem piZ_spec (h2 : FibZN (k := k)) (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k) :
    piZ Z x ∈ Z ∧ qZ Z (piZ Z x) = qZ Z x := by
  have h : ∃ c ∈ Z, qZ Z c = qZ Z x := qZ_Z_exists h2 hZ (qZ Z x)
  unfold piZ
  rw [dif_pos h]
  exact h.choose_spec

theorem piZ_eq_of (h2 : FibZN (k := k)) (hZ : CR Z) {x c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    (h : qZ Z c = qZ Z x) : piZ Z x = c :=
  qZ_Z_inj h2 hZ (piZ_spec h2 hZ x).1 hc ((piZ_spec h2 hZ x).2.trans h.symm)

theorem piZ_qZ (h2 : FibZN (k := k)) (hZ : CR Z) {x x' : Matrix (Fin n) (Fin n) k} (h : qZ Z x = qZ Z x') :
    piZ Z x = piZ Z x' :=
  piZ_eq_of h2 hZ (piZ_spec h2 hZ x').1 (by rw [(piZ_spec h2 hZ x').2, h])

theorem qZ_sig (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (piZ Z x + (t : k) • (x - piZ Z x)) = qZ Z x := by
  rw [qZ_add, qZ_smul, qZ_sub, (piZ_spec h2 hZ x).2, sub_self, smul_zero, add_zero]

theorem sig_sig (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) (p : Sp k n) : sig Z t⁻¹ (sig Z t p) = p := by
  have e := piZ_qZ h2 hZ (qZ_sig h2 hZ t p.1)
  simp only [sig, e]
  refine Prod.ext ?_ rfl
  simp only [Units.val_inv_eq_inv_val]
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ t.ne_zero, one_smul, add_sub_cancel]

theorem sig_act (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) {g : GL (Fin n) k} (hg : g ∈ Gz Z) (p : Sp k n) :
    sig Z t (act g p) = act g (sig Z t p) := by
  have e : piZ Z (g.val * p.1 * g⁻¹.val) = piZ Z p.1 := piZ_qZ h2 hZ (qZ_conj Z hg p.1)
  have e2 : g.val * piZ Z p.1 * g⁻¹.val = piZ Z p.1 := conj_mem_Z Z hg (piZ_spec h2 hZ p.1).1
  simp only [sig, act, e]
  refine Prod.ext ?_ rfl
  simp only
  rw [mul_add, add_mul, e2, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, e2]

end Alg

section Top

local instance t2SpaceLocalField : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_qZ [IsTopologicalRing k] : Continuous (qZ Z) :=
  continuous_pi fun _ => (continuous_const.matrix_mul continuous_id).matrix_trace

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def qLin (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Z →ₗ[k] (Fin (Module.finrank k Z) → k) where
  toFun c := qZ Z c
  map_add' a b := by simp [qZ_add]
  map_smul' a b := by simp [qZ_smul]

theorem qLin_bij (h2 : FibZN (k := k)) (hZ : CR Z) : Function.Bijective (qLin Z) :=
  ⟨fun a b h => Subtype.ext (qZ_Z_inj h2 hZ a.2 b.2 h), fun y => by
      obtain ⟨c, hc, hcy⟩ := qZ_Z_exists h2 hZ y
      exact ⟨⟨c, hc⟩, hcy⟩⟩

def eZ (h2 : FibZN (k := k)) (hZ : CR Z) : (Fin (Module.finrank k Z) → k) →ₗ[k] Matrix (Fin n) (Fin n) k :=
  Z.val.toLinearMap ∘ₗ (LinearEquiv.ofBijective (qLin Z) (qLin_bij h2 hZ)).symm.toLinearMap

theorem eZ_mem (h2 : FibZN (k := k)) (hZ : CR Z) (y) : eZ h2 hZ y ∈ Z := by
  simp [eZ]

theorem qZ_eZ (h2 : FibZN (k := k)) (hZ : CR Z) (y) : qZ Z (eZ h2 hZ y) = y := by
  have := (LinearEquiv.ofBijective (qLin Z) (qLin_bij h2 hZ)).apply_symm_apply y
  rw [LinearEquiv.ofBijective_apply] at this
  exact this

theorem piZ_eq_eZ (h2 : FibZN (k := k)) (hZ : CR Z) (x) : piZ Z x = eZ h2 hZ (qZ Z x) :=
  piZ_eq_of h2 hZ (eZ_mem h2 hZ _) (qZ_eZ h2 hZ _)

theorem continuous_piZ (h2 : FibZN (k := k)) (hZ : CR Z) : Continuous (piZ Z) := by
  have e : piZ Z = fun x => eZ h2 hZ (qZ Z x) := funext (piZ_eq_eZ h2 hZ)
  rw [e]
  have hs : ∀ y, eZ h2 hZ y = ∑ i, y i • eZ h2 hZ (fun j => if i = j then 1 else 0) :=
    fun y => LinearMap.pi_apply_eq_sum_univ (eZ h2 hZ) y
  have hc : Continuous (eZ h2 hZ) := by
    rw [show (eZ h2 hZ : _ → _) = fun y => ∑ i, y i • eZ h2 hZ (fun j => if i = j then 1 else 0) from funext hs]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  exact hc.comp continuous_qZ

theorem continuous_sig (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) : Continuous (sig Z t) := by
  have hp := continuous_piZ h2 hZ
  have hf : Continuous (fun p : Sp k n => p.1) := continuous_fst
  have hs : Continuous (fun p : Sp k n => p.2) := continuous_snd
  unfold sig
  exact ((hp.comp hf).add ((continuous_const : Continuous (fun _ : Sp k n => (t : k))).smul
    (hf.sub (hp.comp hf)))).prodMk hs

def sigH (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := sig Z t
  invFun := sig Z t⁻¹
  left_inv p := sig_sig h2 hZ t p
  right_inv p := by simpa using sig_sig h2 hZ t⁻¹ p
  continuous_toFun := continuous_sig h2 hZ t
  continuous_invFun := continuous_sig h2 hZ t⁻¹

theorem comp_mem_supportedIn (h : Sp k n ≃ₜ Sp k n) {U : Set (Sp k n)} {f : Sp k n → ℂ} (hf : f ∈ supportedIn U) :
    (fun p => f (h p)) ∈ supportedIn (h ⁻¹' U) :=
  ⟨⟨hf.1.1.comp_continuous h.continuous, hf.1.2.comp_homeomorph h⟩, fun _ hx => hf.2 hx⟩

theorem pull_apply (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (f : Sp k n → ℂ) :
    pull Z t ξ f = ξ (fun p => f (sig Z t p)) := rfl

theorem inv_pull (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Inv Z ξ) :
    Inv Z (pull Z t ξ) := by
  intro g hg f hf
  rw [pull_apply, pull_apply]
  have e : (fun p => f (act g (sig Z t p))) = fun p => (fun q => f (sig Z t q)) (act g p) := by
    funext p; show f (act g (sig Z t p)) = f (sig Z t (act g p)); rw [sig_act h2 hZ t hg]
  rw [e]
  exact hξ g hg _ (by simpa using comp_mem_supportedIn (sigH h2 hZ t) hf)

theorem kills_pull (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU) :
    Kills (pull Z t ξ) UU := by
  intro f hf
  rw [pull_apply]
  refine hξ _ ⟨(comp_mem_supportedIn (sigH h2 hZ t) hf).1, fun p hp => ?_⟩
  have := (comp_mem_supportedIn (sigH h2 hZ t) hf).2 hp
  simpa [sigH, sig, UU] using this

theorem kills_aeval (h2 : FibZN (k := k)) (hZ : CR Z) (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU)
    (Q : ℂ[X]) : Kills (aeval (pull Z t) Q ξ) UU := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => intro f hf; simp [hp f hf, hq f hf]
  | monomial m a =>
    intro f hf
    have key : ∀ m : ℕ, Kills (((pull Z t) ^ m : Module.End ℂ _) ξ) UU := by
      intro m
      induction m with
      | zero => simpa using hξ
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact kills_pull h2 hZ t ih
    simp [aeval_monomial, key m f hf]

end Top

section Sets

local instance instT2k' : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isNilpotent_iff_pow (M : Matrix (Fin n) (Fin n) k) : IsNilpotent M ↔ M ^ n = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨n, h⟩⟩
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : M.charpoly = X ^ n := by
    have := h1.eq_zero
    simpa [sub_eq_zero] using this
  have h3 := Matrix.aeval_self_charpoly M
  rw [h2, map_pow, aeval_X] at h3
  exact h3

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_pow (g : GL (Fin n) k) (N : Matrix (Fin n) (Fin n) k) (m : ℕ) :
    (g.val * N * g⁻¹.val) ^ m = g.val * N ^ m * g⁻¹.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    congr 2
    rw [← mul_assoc (g⁻¹.val), ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isClosed_Bz [IsTopologicalRing k] [T2Space k] : IsClosed (Bz Z) := by
  have : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a} := by
    ext x; simp [Bz]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul continuous_id)
    (continuous_id.matrix_mul continuous_const)

def C0 (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (c : Matrix (Fin n) (Fin n) k) : Set (Sp k n) :=
  {q | q.1 ∈ Bz Z ∧ IsNilpotent (q.1 - c)}

theorem isClosed_C0 (c : Matrix (Fin n) (Fin n) k) : IsClosed (C0 Z c) := by
  have : C0 Z c = (Prod.fst) ⁻¹' (Bz Z ∩ {x | (x - c) ^ n = 0}) := by
    ext q; simp [C0, isNilpotent_iff_pow]
  rw [this]
  refine IsClosed.preimage continuous_fst (isClosed_Bz.inter (isClosed_eq ?_ continuous_const))
  exact (continuous_id.sub continuous_const).pow n

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isOpen_UU [T2Space k] : IsOpen (UU : Set (Sp k n)) :=
  isOpen_ne_fun continuous_snd continuous_const

theorem isClosed_Fib (y : Fin (Module.finrank k Z) → k) : IsClosed (Fib Z y) :=
  (isClosed_Bz.inter (isClosed_singleton.preimage continuous_qZ)).prod isClosed_univ

theorem projection_of_orbit_closure (h2 : FibZN (k := k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hn : IsNilpotent (x - c)) : piZ Z x = c ∧ qZ Z x = qZ Z c := by
  obtain ⟨c', hc', hc'y, hiff⟩ := h2 n Z hZ (qZ Z c)
  have e : c' = c := qZ_Z_inj h2 hZ hc' hc hc'y
  subst e
  have hq := ((hiff x hx).2 hn).1
  exact ⟨piZ_eq_of h2 hZ hc' hq.symm, hq⟩

theorem scaling_on_orbit_closure (h2 : FibZN (k := k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (t : kˣ) {q : Sp k n}
    (hq : q ∈ C0 Z c) : sig Z t q = (c + (t : k) • (q.1 - c), q.2) := by
  simp [sig, (projection_of_orbit_closure h2 hZ hc hq.1 hq.2).1]

theorem scaling_mem_orbit_closure (h2 : FibZN (k := k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (t : kˣ)
    {q : Sp k n} (hq : q ∈ C0 Z c) : sig Z t q ∈ C0 Z c := by
  rw [scaling_on_orbit_closure h2 hZ hc t hq]
  refine ⟨fun a ha => ?_, ?_⟩
  · have h1 := hq.1 a ha
    have h2' := hZ.1 a ha c hc
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, h1, h2']
  · simpa using hq.2.smul (t : k)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem action_mem_orbit_closure (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {q : Sp k n} (hq : q ∈ C0 Z c) : act g q ∈ C0 Z c := by
  refine ⟨fun a ha => ?_, ?_⟩
  · show a * (g.val * q.1 * g⁻¹.val) = g.val * q.1 * g⁻¹.val * a
    calc a * (g.val * q.1 * g⁻¹.val) = (g.val * a * g⁻¹.val) * (g.val * q.1 * g⁻¹.val) := by
          rw [conj_mem_Z Z hg ha]
      _ = g.val * (a * q.1) * g⁻¹.val := by simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = g.val * (q.1 * a) * g⁻¹.val := by rw [hq.1 a ha]
      _ = (g.val * q.1 * g⁻¹.val) * (g.val * a * g⁻¹.val) := by simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = g.val * q.1 * g⁻¹.val * a := by rw [conj_mem_Z Z hg ha]
  · have e : g.val * q.1 * g⁻¹.val - c = g.val * (q.1 - c) * g⁻¹.val := by
      rw [mul_sub, sub_mul, conj_mem_Z Z hg hc]
    show IsNilpotent (g.val * q.1 * g⁻¹.val - c)
    rw [e]
    obtain ⟨m, hm⟩ := hq.2
    exact ⟨m, by rw [conj_pow, hm, mul_zero, zero_mul]⟩

end Sets

section Supp

local instance instT2k'' : T2Space k := GlobalTheory.SplitWeil.t2Space k
local instance instTDk : TotallyDisconnectedSpace k := GroundTheory.Automorphic.Whittaker.totallyDisconnectedSpace_localField
local instance instSCk : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
local instance instTDM : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
  inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
local instance instSCM : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

example : LocallyCompactSpace (Sp k n) := inferInstance
example : TotallyDisconnectedSpace (Sp k n) := inferInstance
example : LocallyCompactSpace (GL (Fin n) k) := inferInstance
example : SecondCountableTopology (Matrix (Fin n) (Fin n) k) := inferInstance

theorem support_in_orbit_closure (h1 : ZNClosed (k := k)) (h2 : FibZN (k := k)) (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hs : Supp ξ (Fib Z (qZ Z c))) (hk : Kills ξ (UU ∩ {p | p.1 ∉ ZN Z})) :
    SuppU ξ (C0 Z c) := by
  intro f hf h0
  set A : Set (Sp k n) := ZN Z ×ˢ Set.univ
  have hA : IsClosed A := (h1 n Z hZ).prod isClosed_univ
  set K := Function.support f ∩ A
  have hK : IsCompact K := (isCompact_support hf.1).inter_right hA
  have hKF : K ⊆ (Fib Z (qZ Z c))ᶜ := by
    rintro q ⟨hq, hqA⟩ hqF
    obtain ⟨c', hc', hc'y, hiff⟩ := h2 n Z hZ (qZ Z c)
    have e : c' = c := qZ_Z_inj h2 hZ hc' hc hc'y
    subst e
    exact hq (h0 q ⟨hqF.1.1, (hiff q.1 hqF.1.1).1 ⟨hqF.1.2, hqA.1⟩⟩)
  obtain ⟨W, hWc, hWo, hKW, hWF⟩ := exists_isCompact_isOpen_between hK (isClosed_Fib _).isOpen_compl hKF
  have hWcl : IsClopen W := ⟨hWc.isClosed, hWo⟩
  have hf1 := indicator_mul_mem (U := Set.univ) hWcl ⟨hf.1, Set.subset_univ _⟩
  have hf2 := indicator_mul_mem (U := UU) hWcl.compl hf
  have e : f = (fun q => W.indicator 1 q * f q) + (fun q => Wᶜ.indicator 1 q * f q) := by
    funext q
    by_cases hq : q ∈ W <;> simp [hq]
  rw [e, map_add]
  have z1 : ξ (fun q => W.indicator 1 q * f q) = 0 := by
    refine hs _ hf1 fun q hq => ?_
    have : q ∉ W := fun hqW => hWF hqW hq
    simp [this]
  have z2 : ξ (fun q => Wᶜ.indicator 1 q * f q) = 0 := by
    refine hk _ ⟨hf2.1, fun q hq => ⟨hf2.2 hq, fun hqZN => ?_⟩⟩
    have hqW : q ∉ W := by
      intro hqW
      simp [hqW] at hq
    have hfq : f q ≠ 0 := by
      intro h
      simp [h] at hq
    exact hqW (hKW ⟨hfq, hqZN, Set.mem_univ _⟩)
  rw [z1, z2, add_zero]

end Supp

section Baire

local instance instT2k3 : T2Space k := GlobalTheory.SplitWeil.t2Space k
local instance instSCk3 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
local instance instSCM3 : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_snd_ne {g : GL (Fin n) k} {q : Sp k n} (hq : q.2 ≠ 0) : (act g q).2 ≠ 0 := by
  intro h
  apply hq
  have := congrArg (fun w => g⁻¹.val *ᵥ w) h
  simpa [act, Matrix.mulVec_mulVec, ← Units.val_mul] using this

def actU (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : MulAction (GzS Z) (UU : Set (Sp k n)) where
  smul g q := ⟨act g.1 q.1, act_snd_ne (q := q.1) q.2⟩
  one_smul q := Subtype.ext (act_one q.1)
  mul_smul g h q := Subtype.ext (act_mul g.1 h.1 q.1)

theorem continuous_act [IsTopologicalRing k] : Continuous (fun x : GL (Fin n) k × Sp k n => act x.1 x.2) := by
  have h1 : Continuous (fun x : GL (Fin n) k × Sp k n => (x.1 : Matrix (Fin n) (Fin n) k)) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun x : GL (Fin n) k × Sp k n => ((x.1⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :=
    Units.continuous_coe_inv.comp continuous_fst
  have h3 : Continuous (fun x : GL (Fin n) k × Sp k n => x.2.1) := continuous_fst.comp continuous_snd
  have h4 : Continuous (fun x : GL (Fin n) k × Sp k n => x.2.2) := continuous_snd.comp continuous_snd
  exact ((h1.matrix_mul h3).matrix_mul h2).prodMk (h1.matrix_mulVec h4)

theorem isClosed_GzS : IsClosed ((GzS Z : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
  have : ((GzS Z : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) =
      ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g; simp [GzS, Gz]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

theorem isClosed_diff_of {D O : Set (Sp k n)} (hD : IsClosed D) (hO : O ⊆ UU)
    (h : IsClosed {u : (UU : Set (Sp k n)) | u.1 ∈ D \ O}) : IsClosed (D \ O) := by
  obtain ⟨F, hF, hFeq⟩ := isClosed_induced_iff.1 h
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxD : x ∈ D := closure_minimal Set.sdiff_subset hD hx
  by_contra hxn
  have hxO : x ∈ O := by
    by_contra h'
    exact hxn ⟨hxD, h'⟩
  have hxU : x ∈ UU := hO hxO
  have hsub : D \ O ⊆ F ∪ UUᶜ := by
    intro q hq
    by_cases hqU : q ∈ UU
    · left
      have : (⟨q, hqU⟩ : (UU : Set (Sp k n))) ∈ {u : (UU : Set (Sp k n)) | u.1 ∈ D \ O} := hq
      rw [← hFeq] at this
      exact this
    · right
      exact hqU
  rcases closure_minimal hsub (hF.union isOpen_UU.isClosed_compl) hx with hxF | hxU'
  · have : (⟨x, hxU⟩ : (UU : Set (Sp k n))) ∈ Subtype.val ⁻¹' F := hxF
    rw [hFeq] at this
    exact hxn this
  · exact hxU' hxU

theorem orb_subset_UU {p : Sp k n} (hp : p.2 ≠ 0) : orb Z p ⊆ UU := by
  rintro q ⟨g, -, rfl⟩
  exact act_snd_ne hp

theorem exists_open_orbit (T : Finset (Sp k n)) (hT : ∀ p ∈ T, p.2 ≠ 0) (D : Set (Sp k n)) (hD : IsClosed D)
    (hDinv : ∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) (hcov : D ∩ UU ⊆ ⋃ p ∈ T, orb Z p) (hne : (D ∩ UU).Nonempty) :
    ∃ p₀ ∈ T, orb Z p₀ ⊆ D ∧ IsClosed (D \ orb Z p₀) := by
  letI := actU Z
  haveI : ContinuousSMul (GzS Z) (UU : Set (Sp k n)) :=
    ⟨Continuous.subtype_mk (continuous_act.comp (Continuous.prodMap
      (continuous_subtype_val : Continuous (fun g : GzS Z => (g : GL (Fin n) k))) continuous_subtype_val)) _⟩
  haveI : SecondCountableTopology (GL (Fin n) k) := inferInstance
  haveI : SigmaCompactSpace (GL (Fin n) k) := inferInstance
  haveI : SigmaCompactSpace (GzS Z) := isClosed_GzS.sigmaCompactSpace
  haveI : LocallyCompactSpace (UU : Set (Sp k n)) := isOpen_UU.locallyCompactSpace
  set Z' : Set (UU : Set (Sp k n)) := {u | u.1 ∈ D}
  have hZ' : IsClosed Z' := hD.preimage continuous_subtype_val
  obtain ⟨q₀, hq₀D, hq₀U⟩ := hne
  have hZne : Z'.Nonempty := ⟨⟨q₀, hq₀U⟩, hq₀D⟩
  have hinv : ∀ h : GzS Z, ∀ x ∈ Z', h • x ∈ Z' := fun h x hx => hDinv h.1 h.2 x.1 hx
  set s' : Set (UU : Set (Sp k n)) := {u | u.1 ∈ (T : Set (Sp k n))}
  have hs' : s'.Countable := (T.finite_toSet.preimage Subtype.val_injective.injOn).countable
  have orbit_eq : ∀ (u : (UU : Set (Sp k n))) (p : Sp k n) (hp : p.2 ≠ 0), u.1 ∈ orb Z p →
      MulAction.orbit (GzS Z) u = {v : (UU : Set (Sp k n)) | v.1 ∈ orb Z p} := by
    rintro u p hp ⟨g, hg, hgu⟩
    ext v
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h.1 * g, (GzS Z).mul_mem h.2 hg, by rw [act_mul, hgu]; rfl⟩
    · rintro ⟨g', hg', hg'v⟩
      refine ⟨⟨g' * g⁻¹, (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg)⟩, Subtype.ext ?_⟩
      show act (g' * g⁻¹) u.1 = v.1
      rw [← hgu, ← act_mul, mul_assoc, inv_mul_cancel, mul_one, hg'v]
  have hcov' : Z' ⊆ ⋃ x ∈ s', MulAction.orbit (GzS Z) x := by
    intro u hu
    obtain ⟨p, hpT, hup⟩ := Set.mem_iUnion₂.1 (hcov ⟨hu, u.2⟩)
    have hpU : p ∈ (UU : Set (Sp k n)) := hT p hpT
    refine Set.mem_iUnion₂.2 ⟨⟨p, hpU⟩, hpT, ?_⟩
    rw [orbit_eq ⟨p, hpU⟩ p (hT p hpT) ⟨1, (GzS Z).one_mem, act_one p⟩]
    exact hup
  obtain ⟨x₀, hx₀, hcl⟩ := GroundTheory.Automorphic.ContragredientTranspose.exists_isClosed_diff_orbit hZ' hZne hinv hs' hcov'
  obtain ⟨p₀, hp₀T, hx₀p⟩ := Set.mem_iUnion₂.1 (hcov ⟨hx₀, x₀.2⟩)
  have hO : orb Z p₀ ⊆ D := by
    rintro q ⟨g, hg, rfl⟩
    obtain ⟨g₀, hg₀, hg₀x⟩ := hx₀p
    have : act (g * g₀⁻¹) x₀.1 = act g p₀ := by
      rw [← hg₀x, ← act_mul, mul_assoc, inv_mul_cancel, mul_one]
    rw [← this]
    exact hDinv _ ((GzS Z).mul_mem hg ((GzS Z).inv_mem hg₀)) _ hx₀
  refine ⟨p₀, hp₀T, hO, isClosed_diff_of hD (orb_subset_UU (hT p₀ hp₀T)) ?_⟩
  rw [orbit_eq x₀ p₀ (hT p₀ hp₀T) hx₀p] at hcl
  exact hcl

end Baire

section Main

local instance instT2k5 : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem kills_of_suppU {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} {D : Set (Sp k n)} (hD : D ∩ UU = ∅) (h : SuppU ξ D) :
    Kills ξ UU := by
  intro f hf
  refine h f hf fun q hq => ?_
  by_contra hfq
  have : q ∈ D ∩ UU := ⟨hq, hf.2 hfq⟩
  rw [hD] at this
  exact this

theorem inv_sub_smul {ξ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h1 : Inv Z ξ) (h2 : Inv Z η) (a : ℂ) : Inv Z (ξ - a • η) := by
  intro g hg f hf
  simp [h1 g hg f hf, h2 g hg f hf]

theorem aeval_X_sub (t : kˣ) (a : ℂ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) :
    aeval (pull Z t) (X - Polynomial.C a) ξ = pull Z t ξ - a • ξ := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem main_ind (h2 : FibZN (k := k)) (h4 : StepMod (k := k)) (hZ : CR Z) (t : kˣ) (mm : Sp k n → ℂ)
    (s : Finset (Sp k n))
    (hs : ∀ p ∈ s, p.2 ≠ 0 ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k), g ∈ Gz Z ∧ act g p = sig Z t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      ((modul (stab Z p) K L g : ℝ) : ℂ) = mm p) :
    ∀ (N : ℕ) (T : Finset (Sp k n)), T.card ≤ N → T ⊆ s → ∀ D : Set (Sp k n), IsClosed D →
      (∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) → (∀ q ∈ D, sig Z t q ∈ D) → D ∩ UU ⊆ ⋃ p ∈ T, orb Z p →
      ∀ ξ, Inv Z ξ → SuppU ξ D → ∀ Q : ℂ[X], (∏ p ∈ T, (X - Polynomial.C (mm p))) ∣ Q →
        Kills (aeval (pull Z t) Q ξ) UU := by
  classical
  intro N
  induction N with
  | zero =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hT)
    subst hT0
    have hD0 : D ∩ UU = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => ?_
      simpa using hcov hq
    exact kills_aeval h2 hZ t (kills_of_suppU hD0 hS) Q
  | succ N ih =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    by_cases hne : (D ∩ UU).Nonempty
    swap
    · exact kills_aeval h2 hZ t (kills_of_suppU (Set.not_nonempty_iff_eq_empty.1 hne) hS) Q
    obtain ⟨p₀, hp₀T, hO, hcl⟩ := exists_open_orbit T (fun p hp => (hs p (hTs hp)).1) D hD hinv hcov hne
    obtain ⟨hp₀2, K, L, g, hg, hgp, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hm⟩ := hs p₀ (hTs hp₀T)
    set O := orb Z p₀ with hOdef
    set U := (UU : Set (Sp k n)) ∩ (D \ O)ᶜ with hUdef
    have hU : IsOpen U := isOpen_UU.inter hcl.isOpen_compl
    have hUD : U ∩ D = O := by
      ext q
      constructor
      · rintro ⟨⟨_, hqn⟩, hqD⟩
        by_contra hqO
        exact hqn ⟨hqD, hqO⟩
      · intro hqO
        exact ⟨⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩, hO hqO⟩
    have hstep := h4 n Z hZ t p₀ g hg hgp hp₀2 K hK hKo hKc L hLo hLKK hLn1 hLn2 D U hD hU hUD hinv hsig ξ hξ hS
    have hDU : D \ U = D \ O := by
      ext q
      constructor
      · rintro ⟨hqD, hqU⟩
        refine ⟨hqD, fun hqO => hqU ⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩⟩
      · rintro ⟨hqD, hqO⟩
        exact ⟨hqD, fun h => h.2 ⟨hqD, hqO⟩⟩
    rw [hDU, hm] at hstep
    have hOinv : ∀ h ∈ Gz Z, ∀ q, act h q ∈ O → q ∈ O := by
      rintro h hh q ⟨g', hg', hg'q⟩
      refine ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', ?_⟩
      rw [act_mul, hg'q, ← act_mul, inv_mul_cancel, act_one]
    have hsig0 : sig Z t⁻¹ p₀ = act g⁻¹ p₀ := by
      have e1 : sig Z t⁻¹ (act g p₀) = p₀ := by rw [hgp, sig_sig h2 hZ]
      rw [sig_act h2 hZ t⁻¹ hg] at e1
      calc sig Z t⁻¹ p₀ = act g⁻¹ (act g (sig Z t⁻¹ p₀)) := by rw [← act_mul, inv_mul_cancel, act_one]
        _ = act g⁻¹ p₀ := by rw [e1]
    have hsigO : ∀ q, sig Z t q ∈ O → q ∈ O := by
      rintro q ⟨g', hg', hg'q⟩
      refine ⟨g' * g⁻¹, (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg), ?_⟩
      rw [act_mul, ← hsig0, ← sig_act h2 hZ t⁻¹ hg', hg'q, sig_sig h2 hZ]
    set T' := T.filter (fun p => orb Z p ≠ O) with hT'def
    have hT'sub : T' ⊆ T.erase p₀ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_erase.2 ⟨fun h => hp.2 (by rw [h]), hp.1⟩
    have hT'card : T'.card ≤ N := by
      have := Finset.card_le_card hT'sub
      rw [Finset.card_erase_of_mem hp₀T] at this
      omega
    obtain ⟨Q0, hQ0⟩ := hQ
    set R := (∏ p ∈ T.erase p₀, (X - Polynomial.C (mm p))) * Q0 with hRdef
    have hQR : Q = R * (X - Polynomial.C (mm p₀)) := by
      rw [hQ0, ← Finset.mul_prod_erase T _ hp₀T, hRdef]
      ring
    have hT'R : (∏ p ∈ T', (X - Polynomial.C (mm p))) ∣ R :=
      dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ hT'sub) Q0
    have key : aeval (pull Z t) Q ξ = aeval (pull Z t) R (pull Z t ξ - mm p₀ • ξ) := by
      rw [hQR, map_mul, Module.End.mul_apply, aeval_X_sub]
    rw [key]
    refine ih T' hT'card (fun p hp => hTs (Finset.mem_of_mem_filter p hp)) (D \ O) hcl ?_ ?_ ?_ _
      (inv_sub_smul (inv_pull h2 hZ t hξ) hξ _) hstep R hT'R
    · rintro h hh q ⟨hqD, hqO⟩
      exact ⟨hinv h hh q hqD, fun h' => hqO (hOinv h hh q h')⟩
    · rintro q ⟨hqD, hqO⟩
      exact ⟨hsig q hqD, fun h' => hqO (hsigO q h')⟩
    · rintro q ⟨⟨hqD, hqO⟩, hqU⟩
      obtain ⟨p, hpT, hqp⟩ := Set.mem_iUnion₂.1 (hcov ⟨hqD, hqU⟩)
      refine Set.mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨hpT, fun h => hqO (h ▸ hqp)⟩, hqp⟩

end Main

section Final

local instance instT2k6 : T2Space k := GlobalTheory.SplitWeil.t2Space k

variable (k) in

theorem orbP_of [CharZero k] (h1 : ZNClosed (k := k)) (h2 : FibZN (k := k)) (h3 : Reps (k := k))
    (h4 : StepMod (k := k)) (h5 : ModBound (k := k)) : OrbP (k := k) := by
  classical
  intro n Z hZ hd t ht y
  obtain ⟨c, hc, hcy, -⟩ := h2 n Z hZ y
  obtain ⟨s, hs, hcov⟩ := h3 n Z hZ c hc
  have H : ∀ p ∈ s, ∃ a : ℝ, 2 * a < dB0 Z ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      g ∈ Gz Z ∧ act g p = sig Z t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := by
    intro p hp
    obtain ⟨hp1, hpn, hp2, P, w, hgr, hpos⟩ := hs p hp
    obtain ⟨a, ha, hat⟩ := h5 n Z hZ hd c hc p P w hp1 hpn hp2 hgr hpos
    obtain ⟨K, L, g, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hgval, hmod⟩ := hat t ht
    have hgr' := hgr t
    simp only [← hgval] at hgr'
    obtain ⟨hgZ, hE, hv⟩ := hgr'
    have hgG : g ∈ Gz Z := fun b hb => hgZ b hb
    have e1 : g.val * (p.1 - c) * g⁻¹.val = (t : k) • (p.1 - c) := by
      rw [hE, smul_mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have e2 : g.val * p.1 * g⁻¹.val = c + (t : k) • (p.1 - c) := by
      calc g.val * p.1 * g⁻¹.val = g.val * (c + (p.1 - c)) * g⁻¹.val := by rw [add_sub_cancel]
        _ = g.val * c * g⁻¹.val + g.val * (p.1 - c) * g⁻¹.val := by rw [mul_add, add_mul]
        _ = c + (t : k) • (p.1 - c) := by rw [conj_mem_Z Z hgG hc, e1]
    have hact : act g p = sig Z t p := by
      rw [scaling_on_orbit_closure h2 hZ hc t ⟨hp1, hpn⟩]
      exact Prod.ext e2 hv
    exact ⟨a, ha, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩
  choose! a ha hKLg using H
  refine ⟨s.toList.map a, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ha p (Finset.mem_toList.1 hp)
  · intro ξ hsupp hinv hkill
    set mm : Sp k n → ℂ := fun p => (((nabs k t)⁻¹ ^ a p : ℝ) : ℂ) with hmm
    have hprod : (((s.toList.map a).map fun x => pull Z t - ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) • LinearMap.id).prod :
        Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) = aeval (pull Z t) (∏ p ∈ s, (X - Polynomial.C (mm p))) := by
      rw [← Finset.prod_map_toList s (fun p => X - Polynomial.C (mm p)), map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp only [mm, Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hprod]
    refine main_ind h2 h4 hZ t mm s ?_ s.card s le_rfl subset_rfl (C0 Z c) (isClosed_C0 c)
      (fun h hh q hq => action_mem_orbit_closure hZ hc hh hq) (fun q hq => scaling_mem_orbit_closure h2 hZ hc t hq) ?_ ξ hinv
      (support_in_orbit_closure h1 h2 hZ hc (hcy ▸ hsupp) hkill) _ dvd_rfl
    · intro p hp
      obtain ⟨K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩ := hKLg p hp
      exact ⟨(hs p hp).2.2.1, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, by rw [hmod]⟩
    · rintro q ⟨⟨hq1, hqn⟩, hqU⟩
      obtain ⟨p, hp, hqp⟩ := hcov q.1 hq1 hqn q.2 hqU
      exact Set.mem_iUnion₂.2 ⟨p, hp, hqp⟩

end Final

end PositivityTheory.RgUd.T.Nil.Orb.Oasm
