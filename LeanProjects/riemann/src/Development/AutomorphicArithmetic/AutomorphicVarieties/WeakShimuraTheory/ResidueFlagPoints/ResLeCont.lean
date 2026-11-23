import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeMemDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws.Pt

theorem adicPt {l : ℕ} [Fact l.Prime] (c : Coef l) {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (y : R →ₐ[c.O] PadicAlgCl l) {Γ : Type} [TopologicalSpace Γ] (f : Γ → R) (hf : AdicCont (maximalIdeal R) f) :
    Continuous fun g => y (f g) := by
  obtain ⟨a, ha1, ha0, hbd⟩ := ((coPt c R).1 y).2
  rw [continuous_iff_continuousAt]
  intro g0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ N) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  have hmem : f g - f g0 ∈ maximalIdeal R ^ N := Ideal.Quotient.eq.mp hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hbd N _ hmem) hN

theorem trCont {Γ k ι : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] [Fintype ι] [DecidableEq ι] (r : Γ →* Matrix ι ι k) (hr : Irr r)
    (ht : Continuous fun g => (r g).trace) : Continuous r := by
  have hr' : Submodule.span k (Set.range r) = ⊤ := hr
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hE : Matrix.single j i (1 : k) ∈ Submodule.span k (Set.range r) := by
    rw [hr']
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hE
  have key : ∀ g, r g i j = c.sum fun h a => a * (r (g * h)).trace := by
    intro g
    have h1 : r g i j = (r g * Matrix.single j i 1).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single i (by intro b _ hb; simp [Ne.symm hb]) (by simp),
        Finset.sum_eq_single j (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
      simp
    rw [h1, ← hc, Finsupp.sum, Matrix.mul_sum, Matrix.trace_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, map_mul]
  have hfun : (fun g => r g i j) = fun g => c.sum fun h a => a * (r (g * h)).trace :=
    funext key
  rw [hfun]
  exact continuous_finset_sum _ fun h _ =>
    continuous_const.mul (ht.comp (continuous_id.mul continuous_const))

theorem resLe_cont {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} [NumberField F]
    [NumberField L] (hFL : F ≤ L) : Continuous (resLe hFL) := by
  letI : Algebra F L := (IntermediateField.inclusion hFL).toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

private theorem continuous_monoidHom_units_of_continuous_coe {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
    [Monoid M] [TopologicalSpace M] (φ : Γ →* Mˣ) (h : Continuous fun g => (φ g : M)) :
    Continuous φ := by
  rw [Units.continuous_iff]
  refine ⟨h, (h.comp continuous_inv).congr fun g => ?_⟩
  simp only [Function.comp, map_inv]

theorem psi_cont {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    (x : B.Pt) (v : W.Vl l L) (i : Fin n) : Continuous (x.psi v i) := by
  letI := V.frame.tv v
  have h1 := adicPt c x _ (W.Resid.IsPsi.cont (B.u.psi v i))
  exact continuous_monoidHom_units_of_continuous_coe _ (h1.congr fun g => rfl)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h)

theorem twc_cont (n : ℕ) : Continuous (K.twc n) := by
  refine continuous_monoidHom_units_of_continuous_coe _ ?_
  have hA : AdicCont (maximalIdeal c'.O)
      fun g => ((K.κ g : c'.O) : c'.O) * ((K.β g : c'.O)) ^ n := by
    intro N
    have := (K.κ_cont N).comp₂ (K.β_cont N) (fun a b => a * b ^ n)
    convert this using 1
    funext g
    simp [map_mul, map_pow]
  have h1 := adicPt c' (Algebra.ofId c'.O (PadicAlgCl l)) _ hA
  refine h1.congr fun g => ?_
  rw [Link.twc_val]
  rfl

theorem rho_cont (n : ℕ) {r : G T.F Ω →* M4 (PadicAlgCl l)} (hr : Continuous r) : Continuous (K.rhoQ n r) := by
  refine continuous_monoidHom_units_of_continuous_coe _ ?_
  have h1 : Continuous fun g => ((K.twc n g : (PadicAlgCl l)ˣ) : PadicAlgCl l) :=
    Units.continuous_val.comp (twc_cont K n)
  have h2 := h1.smul (hr.comp (resLe_cont T.F_le))
  refine h2.congr fun g => ?_
  rw [Link.rho_val]
  rfl

variable {K}

theorem pt_cont (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
    (hy : Irr (X.P.map (y : X.A →+* PadicAlgCl l)).r) : Continuous (X.P.map (y : X.A →+* PadicAlgCl l)).r := by
  apply trCont _ hy
  have hcoef := adicPt c' (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) _ (X.cp_cont 3)
  refine hcoef.neg.congr fun g => ?_
  show -(y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) ((X.cp g).coeff 3) =
    ((X.P.r g).map (y : X.A →+* PadicAlgCl l)).trace
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.charpoly_map, ← X.cp_map g, Polynomial.map_map,
    Polynomial.coeff_map]
  simp

end UpperTheory.V.Ws.Pt
