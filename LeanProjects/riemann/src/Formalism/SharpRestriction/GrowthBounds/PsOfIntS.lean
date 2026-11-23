import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjGauge

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def IsPt (V : VF C) {τ : Type} (a : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (a i) = 0 ∧ IntS V (a i)

def BiInt (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ (τ : Type) [Finite τ] (n : ℕ) (a : ℕ → κ → MvPowerSeries τ C) (s c : κ → MvPowerSeries τ C),
    (∀ k, IsPt V (a k)) → IsPt V s → IsPt V c →
    (∀ i, MvPowerSeries.subst s (X.lg i) = ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (X.lg i)) →
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X (a k) c - hAt X s c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range n, hAt X c (a k) - hAt X c s))

def NormRel (X : RawChart C d I κ) (l n : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) =
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i))

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

section Lem

variable {V : VF C}

theorem intS_of_ps {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) : IntS V f := fun μ => by
  have hμ : μ = Finsupp.single () (μ ()) := Finsupp.ext fun u => by cases u; simp
  rw [hμ]; exact hf (μ ())

theorem ps_of_intS {f : PowerSeries C} (hf : IntS V f) : ∀ n, V.Ge 0 (PowerSeries.coeff n f) :=
  fun n => hf (Finsupp.single () n)

theorem subst_ps {τ : Type} {a : MvPowerSeries τ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hai : IntS V a) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 ∧ IntS V (PowerSeries.subst a f) := by
  refine ⟨constantCoeff_subst_zero (σ := Unit) (fun _ => ha) hf0, ?_⟩
  exact PartialDerivEval.intS_subst (fun _ => ha) (fun _ => hai) (intS_of_ps hf)

theorem inV_pt (j : Fin 2) {f : PowerSeries C} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) :
    MvPowerSeries.constantCoeff (inV j f) = 0 ∧ IntS V (inV j f) :=
  subst_ps (MvPowerSeries.constantCoeff_X j) (PartialDerivEval.intS_X j) hf0 hf

theorem rc_cv {c : C} (hc : V.Ge 0 c) {γ : κ → PowerSeries C} (hγ : IsCv V γ) : IsCv V (rc c γ) := by
  intro i
  refine ⟨?_, fun n => ?_⟩
  · show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (hγ i).1]
  · show V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale c (γ i)))
    rw [PowerSeries.coeff_rescale]
    exact (hc.pow n).mul_int ((hγ i).2 n)

theorem pw_cv {n : ℕ} (hn : 0 < n) {δ : κ → PowerSeries C} (hδ : IsCv V δ) : IsCv V (pw n δ) := by
  intro i
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hXi : IntS V ((PowerSeries.X : PowerSeries C) ^ n) :=
    PartialDerivEval.intS_pow (intS_of_ps fun m => by
      rw [PowerSeries.coeff_X]; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0]) n
  obtain ⟨h0, hI⟩ := subst_ps (τ := Unit) hX hXi (hδ i).1 (hδ i).2
  exact ⟨h0, ps_of_intS hI⟩

theorem subst_inV (j : Fin 2) {x : κ → PowerSeries C} (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun i => inV j (x i)) F = inV j (alongCv x F) := by
  unfold inV alongCv
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => MvPowerSeries.constantCoeff_X j))]

theorem inV_sum (j : Fin 2) {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) :
    inV j (∑ k ∈ s, f k) = ∑ k ∈ s, inV j (f k) := by
  unfold inV
  have hS : PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X j)
  rw [← PowerSeries.coe_substAlgHom hS, map_sum]

theorem log_rel (X : RawChart C d I κ) (j : Fin 2) {l n : ℕ} (hn : 0 < n) {ζ : C} {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0)
    (hN : NormRel X l n ζ γ δ) (i : κ) :
    MvPowerSeries.subst (fun i => inV j (pw n δ i)) (X.lg i) =
      ∑ k ∈ Finset.range l, MvPowerSeries.subst (fun i => inV j (rc (ζ ^ k) γ i)) (X.lg i) := by
  have hX : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ n) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  have hpw0 : ∀ i, PowerSeries.constantCoeff (pw n δ i) = 0 := fun i =>
    constantCoeff_subst_zero (σ := Unit) (fun _ => hX) (hδ i)
  have hrc0 : ∀ (c : C) i, PowerSeries.constantCoeff (rc c γ i) = 0 := fun c i => by
    show PowerSeries.constantCoeff (PowerSeries.rescale c (γ i)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ i]
  rw [subst_inV j hpw0]
  simp only [subst_inV j (hrc0 _)]
  rw [← inV_sum]
  congr 1
  rw [show alongCv (pw n δ) (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) from
    alongCv_repar hδ hX (X.lg i), hN i]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : PowerSeries.constantCoeff ((ζ ^ k) • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  show PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i)) = alongCv (fun i => PowerSeries.rescale (ζ ^ k) (γ i)) (X.lg i)
  rw [PowerSeries.rescale_eq_subst]
  simp only [PowerSeries.rescale_eq_subst]
  rw [alongCv_repar hγ hc]

end Lem

theorem hInt_core [CharZero C] (V : VF C) (X : RawChart C d I κ) (hBi : BiInt X V) (ζ : C) (hζ : ζ ^ V.l = 1)
    (n : ℕ) (hn : 0 < n) (γ δ c : κ → PowerSeries C) (hγ : IsCv V γ) (hδ : IsCv V δ) (hc : IsCv V c)
    (hN : NormRel X V.l n ζ γ δ) :
    IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (Formalism.IncomingBounds.mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ))) := by
  have hζint : V.Ge 0 ζ := V.ge_of_pow_eq_one V.l_prime.ne_zero hζ
  have hrc : ∀ k, IsCv V (rc (ζ ^ k) γ) := fun k => rc_cv (hζint.pow k) hγ
  have hpw : IsCv V (pw n δ) := pw_cv hn hδ
  have pt : ∀ (j : Fin 2) (x : κ → PowerSeries C), IsCv V x → IsPt V (fun i => inV j (x i)) :=
    fun j x hx i => inV_pt j (hx i).1 (hx i).2
  refine ⟨?_, ?_⟩
  · exact (hBi (Fin 2) V.l (fun k i => inV 0 (rc (ζ ^ k) γ i)) (fun i => inV 0 (pw n δ i))
      (fun i => inV 1 (c i)) (fun k => pt 0 _ (hrc k)) (pt 0 _ hpw) (pt 1 _ hc)
      (log_rel X 0 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).1
  · exact (hBi (Fin 2) V.l (fun k i => inV 1 (rc (ζ ^ k) γ i)) (fun i => inV 1 (pw n δ i))
      (fun i => inV 0 (c i)) (fun k => pt 1 _ (hrc k)) (pt 1 _ hpw) (pt 0 _ hc)
      (log_rel X 1 hn (fun i => (hγ i).1) (fun i => (hδ i).1) hN)).2

end SelfConjGauge

end Formalism.L2.FormalSeriesBounds
