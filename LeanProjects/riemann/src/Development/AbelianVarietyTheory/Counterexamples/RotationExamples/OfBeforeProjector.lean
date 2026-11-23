import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

noncomputable section
open NumberField
open scoped TensorProduct
namespace GlobalTheory.PhaseRationalDegenerate
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def IsRat (F : GA D (Wc D i) → ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
    F h = ∑ k, D.what₂.embLL (a k) *
      ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)

theorem IsRat.zero : IsRat O κ cc 0 := ⟨0, Fin.elim0, Fin.elim0, fun _ => by simp⟩

theorem IsRat.add {F F' : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) (h' : IsRat O κ cc F') : IsRat O κ cc (F + F') := by
  obtain ⟨n, a, f, hf⟩ := h
  obtain ⟨n', a', f', hf'⟩ := h'
  refine ⟨n + n', Fin.append a a', Fin.append f f', fun x => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply, hf x, hf' x]

theorem IsRat.mul (b : D.what₂.LL) {F : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) : IsRat O κ cc (D.what₂.embLL b • F) := by
  obtain ⟨n, a, f, hf⟩ := h
  refine ⟨n, fun k => b * a k, f, fun x => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hf x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]; ring

theorem levChi_flag (k : GA D (Wc D i)) :
    Formalism.IndefR.Lev.levChi (Wc D i) (R.βW i) (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)) k = 1 := by
  unfold Formalism.IndefR.Lev.levChi levFn
  have h1 : ∀ x, ext1 (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)).P.H (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs <;> rfl
  rw [h1, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul, Units.val_one]
  · intro PP hP; exact absurd hP (Finset.notMem_empty _)
  · intro PP _; exact Finset.prod_eq_one fun c hc => absurd hc (Finset.notMem_empty _)

theorem IsRat.act (hE : O.EquivAt κ cc) (hχ : R.grp_chiW) (g : G) {F : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) :
    IsRat O κ cc (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F) := by
  show IsRat O κ cc (Formalism.IndefR.Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F)
  unfold Formalism.IndefR.Lev.actG0
  split_ifs with hk
  · obtain ⟨n, a, f, hf⟩ := h
    have e := hE g _ hk.choose_spec
    refine ⟨n, fun k => a k * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL),
      fun k => ⟨_, (e _ (f k).2).1⟩, fun x => ?_⟩
    rw [levChi_flag, inv_one]
    beta_reduce
    rw [one_mul, hf]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e2 := (e _ (f k).2).2 x
    rw [← hχ i g] at e2
    have e3 : D.what₂.embLL ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) *
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show _ = _ * (_ * O.phi cc (actLev C.Q.c O.lev2 g (f k : C.R ((i : ℕ) + 1))) x)
    rw [e2, map_mul]
    linear_combination (-(D.what₂.embLL (a k) * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi cc (f k : C.R ((i : ℕ) + 1)) (x * hk.choose))) * e3
  · exact IsRat.zero O κ cc

set_option maxHeartbeats 1000000 in

theorem of_before_projector (hE : O.EquivAt κ cc) (hχ : R.grp_chiW) (hG : R.thP_thG) (ph : ℂ)
    (h : ∀ x : A.fam.amb.FL i A.μ0, IsRat O κ cc (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) : O.PhRat κ v₀ cc ph := by
  intro x
  have key : IsRat O κ cc (R.eWf i (sg0 D A) (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply]
    refine Finset.sum_induction _ (IsRat O κ cc) (fun _ _ => IsRat.add O κ cc) (IsRat.zero O κ cc) fun g _ => ?_
    have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
    have : RealDat.eC (A := A) (sg0 D A) g = D.what₂.embLL ((idemOf A.X).coeff g) :=
      RingHom.congr_fun hs ((idemOf A.X).coeff g)
    have h2 := IsRat.mul O κ cc ((idemOf A.X).coeff g) (IsRat.act O κ cc hE hχ g (h x))
    rw [← this] at h2
    exact h2
  obtain ⟨n, a, f, hf⟩ := key
  refine ⟨n, a, f, fun y => ?_⟩
  rw [← hf y, hG i A.μ0, map_smul]
  rfl

end GlobalTheory.PhaseRationalDegenerate
