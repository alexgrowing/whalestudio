import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt
  Formalism.L2.Pj.CompSplitPfB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_frMap_test {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {p : TRing c.F} {S : Type}
    [CommRing S] [Algebra c.F S] {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) :
    evR Xo c f z = φ (f p y) := by
  have ht : Tested z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dif_pos ht]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem idem_notMem_iff (Z : Comp Xo c) {p : TRing c.F} (y : FrPt Xo c p.R) (q : PrimeSpectrum p.R) :
    idem Z p y ∉ q.asIdeal ↔ ptF y q ∈ (Z : Set (Xo.XF c)) :=
  cspB_idem_spec _ (cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q

theorem liesOff_of_map_idem {Z : Comp Xo c} {p : TRing c.F} {S : Type} [CommRing S] [Algebra c.F S]
    {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R} {z : FrPt Xo c S} (h : FrMap φ y z) (h0 : φ (idem Z p y) = 0) :
    LiesOff Z z := fun q hq => by
  have hC := cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z
  have h1 : cspB_idem _ hC z.x z.x_over = 0 := (cspB_idem_map _ hC φ y.x_over z.x_over h.1).symm.trans h0
  exact (cspB_idem_spec _ hC z.x z.x_over q).2 hq (h1 ▸ q.asIdeal.zero_mem)

theorem mem_suppOn_iff_idem_mul_of_natural {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := by
  refine ⟨fun h => funext fun p => funext fun y => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _
      (Ideal.Quotient.mkₐ c.F (Ideal.span {idem Z p y})) y
    have h0 := h _ z (liesOff_of_map_idem hz (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)))
    rw [evR_of_frMap_test hf hz] at h0
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : idem Z p y * idem Z p y = idem Z p y := congrFun (congrFun (idem_mul_idem Z) p) y
    show idem Z p y * f p y = f p y
    rw [← ha, mul_left_comm, h1]
  · rw [← h, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem mem_suppOn_iff_idem_mul {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (Z : Comp Xo c) :
    f ∈ suppOn Z ↔ idem Z * f = f := mem_suppOn_iff_idem_mul_of_natural hf.1 Z

theorem idem_mul_eq {e : Ix Dw → ℤ} {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ secZ Xo c e ⊓ suppOn Z) :
    idem Z * f = f := (mem_suppOn_iff_idem_mul hf.1 Z).1 hf.2

theorem idem_mul_mem {e : Ix Dw → ℤ} (Z : Comp Xo c) {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    idem Z * f ∈ secZ Xo c e ⊓ suppOn Z :=
  ⟨zero_add e ▸ mul_mem_secZ (idem_mem_secZ Z) hf, mul_comm f (idem Z) ▸ mul_mem_suppOn f (idem_mem_suppOn Z)⟩

theorem eq_zero_of_forall_prime {K : Type} [Field K] {p : TRing K} {a : p.R}
    (h : ∀ q : PrimeSpectrum p.R, a ∈ q.asIdeal) : a = 0 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  exact (nilpotent_iff_mem_prime.2 fun J hJ => h ⟨J, hJ⟩).eq_zero

theorem idem_mul_idem_of_ne {Z Z' : Comp Xo c} (h : Z ≠ Z') : idem Z * idem Z' = 0 :=
  funext fun p => funext fun y => eq_zero_of_forall_prime fun q => by
    show idem Z p y * idem Z' p y ∈ q.asIdeal
    by_contra hn
    have h1 := not_or.1 (mt q.isPrime.mul_mem_iff_mem_or_mem.2 hn)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) ((idem_notMem_iff Z y q).1 h1.1)
      ((idem_notMem_iff Z' y q).1 h1.2)

variable (Xo c) in

theorem sum_idem [Fintype (Comp Xo c)] : ∑ Z : Comp Xo c, idem Z = 1 := by
  classical
  refine funext fun p => funext fun y => ?_
  rw [Finset.sum_apply, Finset.sum_apply]
  show _ = (1 : p.R)
  refine sub_eq_zero.1 (eq_zero_of_forall_prime fun q => ?_)
  have hall : ptF y q ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨W, hW, hq⟩ := Set.mem_sUnion.1 hall
  let Z₀ : Comp Xo c := ⟨W, hW⟩
  have h1 : idem Z₀ p y ∉ q.asIdeal := (idem_notMem_iff Z₀ y q).2 hq
  refine (q.isPrime.mem_or_mem (x := idem Z₀ p y) ?_).resolve_left h1
  have h2 : idem Z₀ p y * ∑ Z : Comp Xo c, idem Z p y = idem Z₀ p y := by
    rw [Finset.mul_sum]
    exact (Finset.sum_eq_single Z₀ (fun Z _ h => congrFun (congrFun (idem_mul_idem_of_ne h.symm) p) y)
      (fun h => absurd (Finset.mem_univ _) h)).trans (congrFun (congrFun (idem_mul_idem Z₀) p) y)
  rw [mul_sub, h2, mul_one, sub_self]
  exact q.asIdeal.zero_mem

variable (Xo c) in

theorem finsum_idem : ∑ᶠ Z : Comp Xo c, idem Z = 1 := by
  have := CompFin.finite_comp Xo c
  have := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem]

theorem sum_idem_mul [Fintype (Comp Xo c)] (f : Rul Xo c) : ∑ Z : Comp Xo c, idem Z * f = f := by
  rw [← Finset.sum_mul, sum_idem, one_mul]

namespace ConstSec

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {la : Weight Dw}
  {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U x Z la δ)

theorem mul_sig_mul_inv {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e ⊓ suppOn Z) :
    f * s.sig * s.inv = f := by
  rw [mul_assoc, s.mul_inv, mul_comm, idem_mul_eq hf]

theorem mul_inv_mul_sig {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e ⊓ suppOn Z) :
    f * s.inv * s.sig = f := by
  rw [mul_right_comm, s.mul_sig_mul_inv hf]

theorem mul_sig_mem {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    f * s.sig ∈ secZ Xo c (e + exOf Dw la 0) ⊓ suppOn Z :=
  ⟨mul_mem_secZ hf s.sig_mem, mul_mem_suppOn f s.sig_mem_suppOn⟩

theorem mul_inv_mem {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c (e + exOf Dw la 0)) :
    f * s.inv ∈ secZ Xo c e ⊓ suppOn Z :=
  ⟨add_neg_cancel_right e (exOf Dw la 0) ▸ mul_mem_secZ hf s.inv_mem, mul_mem_suppOn f s.inv_mem_suppOn⟩

def mulEquiv (e : Ix Dw → ℤ) :
    (secZ Xo c e ⊓ suppOn Z : Submodule c.F (Rul Xo c)) ≃ₗ[c.F]
      (secZ Xo c (e + exOf Dw la 0) ⊓ suppOn Z : Submodule c.F (Rul Xo c)) where
  toFun f := ⟨f.1 * s.sig, s.mul_sig_mem f.2.1⟩
  invFun f := ⟨f.1 * s.inv, s.mul_inv_mem f.2.1⟩
  map_add' f g := Subtype.ext (add_mul f.1 g.1 s.sig)
  map_smul' a f := Subtype.ext (smul_mul_assoc a f.1 s.sig)
  left_inv f := Subtype.ext (s.mul_sig_mul_inv f.2)
  right_inv f := Subtype.ext (s.mul_inv_mul_sig f.2)

@[simp] theorem coe_mulEquiv (e : Ix Dw → ℤ) (f : (secZ Xo c e ⊓ suppOn Z : Submodule c.F (Rul Xo c))) :
    (s.mulEquiv e f : Rul Xo c) = f.1 * s.sig := rfl

@[simp] theorem coe_mulEquiv_symm (e : Ix Dw → ℤ)
    (f : (secZ Xo c (e + exOf Dw la 0) ⊓ suppOn Z : Submodule c.F (Rul Xo c))) :
    ((s.mulEquiv e).symm f : Rul Xo c) = f.1 * s.inv := rfl

end ConstSec

theorem suppOn_idem_laws (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) :
    (∀ (e : Ix Dw → ℤ) (f : Rul Xo c), f ∈ secZ Xo c e → ∀ Z : Comp Xo c, f ∈ suppOn Z ↔ idem Z * f = f) ∧
    (∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (la : Weight Dw)
      (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z la δ) (e : Ix Dw → ℤ),
      (∀ f ∈ secZ Xo c e ⊓ suppOn Z, f * s.sig * s.inv = f) ∧
      ∃ m : (secZ Xo c e ⊓ suppOn Z : Submodule c.F (Rul Xo c)) ≃ₗ[c.F]
          (secZ Xo c (e + exOf Dw la 0) ⊓ suppOn Z : Submodule c.F (Rul Xo c)),
        (∀ f, (m f : Rul Xo c) = f.1 * s.sig) ∧ ∀ g, (m.symm g : Rul Xo c) = g.1 * s.inv) ∧
    (Finite (Comp Xo c) ∧ ∀ [Fintype (Comp Xo c)], ∑ Z : Comp Xo c, idem Z = 1) :=
  ⟨fun _ _ hf Z => mem_suppOn_iff_idem_mul hf Z,
    fun _ _ _ _ _ _ s e => ⟨fun _ hf => s.mul_sig_mul_inv hf, s.mulEquiv e, fun _ => rfl, fun _ => rfl⟩,
    CompFin.finite_comp Xo c, sum_idem Xo c⟩

end GlobalTheory.FlatLine
