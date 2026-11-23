import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniqueness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsRest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDerivation

open Polynomial

theorem lift_with_value {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (φ : A →+* R) (α : A →+* V) (hα : IsLocalHom α) (θ : R) (ζ : V) (q : Polynomial A)
    (hq : q.Monic) (hqθ : (q.map φ).eval θ = 0) (hqζ : (q.map α).eval ζ = 0)
    (happ : ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n)
    (hinj : ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree →
      (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n) :
    ∃ ψ : R →+* V, ψ.comp φ = α ∧ ψ θ = ζ := by
  classical
  have hq1 : q ≠ 1 := by
    rintro rfl
    simp at hqθ
  have key : ∀ (n : ℕ) (P P' : Polynomial A),
      (P.map φ).eval θ - (P'.map φ).eval θ ∈ maximalIdeal R ^ n →
      (P.map α).eval ζ - (P'.map α).eval ζ ∈ maximalIdeal V ^ n := by
    intro n P P' h
    have hD := Polynomial.modByMonic_add_div (P - P') q
    have e1 : (P.map φ).eval θ - (P'.map φ).eval θ = (((P - P') %ₘ q).map φ).eval θ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqθ, zero_mul, add_zero]
    have e2 : (P.map α).eval ζ - (P'.map α).eval ζ = (((P - P') %ₘ q).map α).eval ζ := by
      rw [← Polynomial.eval_sub, ← Polynomial.map_sub]
      conv_lhs => rw [← hD]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hqζ, zero_mul, add_zero]
    rw [e2]
    rw [e1] at h
    exact GlobalTheory.eval_map_mem_maximalIdeal_pow_of_coeff_mem α n _
      (hinj n _ (Polynomial.natDegree_modByMonic_lt _ hq hq1) h) ζ
  have hmem : ∀ (n : ℕ) (x : V),
      x ∈ (maximalIdeal V ^ n) • (⊤ : Submodule V V) ↔ x ∈ maximalIdeal V ^ n :=
    fun n x => GlobalTheory.mem_ideal_smul_top_iff_mem _ x
  have ex : ∀ r : R, ∃ L : V, ∀ (n : ℕ) (P : Polynomial A),
      r - (P.map φ).eval θ ∈ maximalIdeal R ^ n → L - (P.map α).eval ζ ∈ maximalIdeal V ^ n := by
    intro r
    choose Pn hPn using fun n => happ n r
    have hc : ∀ {m n : ℕ}, m ≤ n → ((Pn m).map α).eval ζ ≡ ((Pn n).map α).eval ζ
        [SMOD (maximalIdeal V ^ m • (⊤ : Submodule V V))] := by
      intro m n hmn
      rw [SModEq.sub_mem, hmem]
      apply key
      have h1 : r - ((Pn n).map φ).eval θ ∈ maximalIdeal R ^ m :=
        Ideal.pow_le_pow_right hmn (hPn n)
      have := Ideal.sub_mem _ h1 (hPn m)
      convert this using 1
      ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun k => ((Pn k).map α).eval ζ) inferInstance hc
    refine ⟨L, fun n P hP => ?_⟩
    have h1 := (hmem n _).1 ((SModEq.sub_mem).1 (hL n))
    have h2 : ((Pn n).map α).eval ζ - (P.map α).eval ζ ∈ maximalIdeal V ^ n := by
      apply key
      have := Ideal.sub_mem _ hP (hPn n)
      convert this using 1
      ring
    have := Ideal.sub_mem _ h2 h1
    convert this using 1
    ring
  have haus : ∀ x : V, (∀ n, x ∈ maximalIdeal V ^ n) → x = 0 := by
    intro x hx
    exact IsHausdorff.haus inferInstance x fun n =>
      SModEq.sub_mem.2 (by rw [sub_zero, hmem]; exact hx n)
  choose ψ0 hψ0 using ex
  have char : ∀ (x : R) (b : V), (∀ n, ∃ P : Polynomial A,
      x - (P.map φ).eval θ ∈ maximalIdeal R ^ n ∧ b - (P.map α).eval ζ ∈ maximalIdeal V ^ n) →
      ψ0 x = b := by
    intro x b h
    rw [← sub_eq_zero]
    apply haus
    intro n
    obtain ⟨P, h1, h2⟩ := h n
    have := Ideal.sub_mem _ (hψ0 x n P h1) h2
    convert this using 1
    ring
  let ψ : R →+* V :=
    { toFun := ψ0
      map_one' := char 1 1 fun n => ⟨1, by simp, by simp⟩
      map_zero' := char 0 0 fun n => ⟨0, by simp, by simp⟩
      map_add' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px + Py, ?_, ?_⟩
        · have := Ideal.add_mem _ hx hy
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
        · have := Ideal.add_mem _ (hψ0 x n Px hx) (hψ0 y n Py hy)
          convert this using 1
          simp only [Polynomial.map_add, Polynomial.eval_add]
          ring
      map_mul' := fun x y => char _ _ fun n => by
        obtain ⟨Px, hx⟩ := happ n x
        obtain ⟨Py, hy⟩ := happ n y
        refine ⟨Px * Py, ?_, ?_⟩
        · have := Ideal.add_mem _ (Ideal.mul_mem_right y _ hx)
            (Ideal.mul_mem_left _ ((Px.map φ).eval θ) hy)
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring
        · have := Ideal.add_mem _ (Ideal.mul_mem_right (ψ0 y) _ (hψ0 x n Px hx))
            (Ideal.mul_mem_left _ ((Px.map α).eval ζ) (hψ0 y n Py hy))
          convert this using 1
          simp only [Polynomial.map_mul, Polynomial.eval_mul]
          ring }
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    show ψ0 (φ a) = α a
    exact char _ _ fun n => ⟨Polynomial.C a, by simp, by simp⟩
  · show ψ0 θ = ζ
    exact char _ _ fun n => ⟨Polynomial.X, by simp, by simp⟩

theorem ringHom_ext_of_approx {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsHausdorff (maximalIdeal V) V]
    (φ : A →+* R) (hm : (maximalIdeal A).map φ = maximalIdeal R) (θ : R)
    (happ : ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n)
    (g₁ g₂ : R →+* V) (hloc : ∀ a ∈ maximalIdeal A, g₁ (φ a) ∈ maximalIdeal V)
    (h : g₁.comp φ = g₂.comp φ) (hθ : g₁ θ = g₂ θ) : g₁ = g₂ := by
  have hpow : ∀ (g : R →+* V), g.comp φ = g₁.comp φ →
      ∀ n, ∀ x ∈ maximalIdeal R ^ n, g x ∈ maximalIdeal V ^ n := by
    intro g hg n x hx
    rw [← hm, ← Ideal.map_pow] at hx
    have hle : Ideal.map g ((maximalIdeal A ^ n).map φ) ≤ maximalIdeal V ^ n := by
      rw [Ideal.map_map, hg, Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact hloc a ha
    exact hle (Ideal.mem_map_of_mem g hx)
  have hev : ∀ (g : R →+* V) (P : Polynomial A), g ((P.map φ).eval θ) = P.eval₂ (g.comp φ) (g θ) := by
    intro g P
    rw [Polynomial.eval_map, Polynomial.hom_eval₂]
  ext r
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal V) V) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, GlobalTheory.mem_ideal_smul_top_iff_mem]
  obtain ⟨P, hP⟩ := happ n r
  have h1 := hpow g₁ rfl n _ hP
  have h2 := hpow g₂ h.symm n _ hP
  have h3 : g₁ ((P.map φ).eval θ) = g₂ ((P.map φ).eval θ) := by
    rw [hev, hev, h, hθ]
  have := Ideal.sub_mem _ h1 h2
  rw [map_sub, map_sub, h3] at this
  convert this using 1
  ring

end GlobalTheory.ChartDerivation

namespace GlobalTheory.ChartDerivation

open Polynomial

theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (k : Type) [Field k] [CharZero k] (m d : ℕ) (ψ : A →+* ChartRing k m d), IsEtaleCompletion ψ → ∀ δ : Derivation ℤ A A, ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), ∀ a, D' (ψ a) = ψ (δ a) := by
  intro A _ _ k _ _ m d ψ hψ δ
  obtain ⟨hflat, hmax, hfin⟩ := hψ
  have hloc : ∀ a ∈ maximalIdeal A, ψ a ∈ maximalIdeal (ChartRing k m d) := fun a ha =>
    hmax ▸ Ideal.mem_map_of_mem ψ ha
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    exact (mem_maximalIdeal _).1 (hloc a ((mem_maximalIdeal a).2 hna)) ha⟩
  haveI : CharZero (ChartRing k m d) :=
    (RingHom.charZero_iff (algebraMap k (ChartRing k m d)).injective).1 inferInstance
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI hRA : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hur := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m d ψ ⟨hflat, hmax, hfin⟩
  obtain ⟨θ, q, hqm, hqθ, hqu, happ1, hind⟩ :=
    GlobalTheory.exists_hensel_generator_of_residue_finite_unramified ψ hfin hur
  have happ := GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow ψ hmax θ happ1
  have hinj := GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max ψ hflat hmax θ q hqm hqθ happ hind
  obtain ⟨hVloc, -, hVcomp, -, -, -⟩ := GlobalTheory.DualNumberLocal.main (ChartRing k m d)
  let α : A →+* DualNumber (ChartRing k m d) :=
    { toFun := fun a => TrivSqZeroExt.inl (ψ a) + TrivSqZeroExt.inr (ψ (δ a))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring
      map_mul' := fun a b => by
        ext
        · simp
        · simp [TrivSqZeroExt.snd_mul, Derivation.leibniz]
          ring_nf }
  have hαfst : ∀ a, (α a).fst = ψ a := fun a => by simp [α]
  have hαsnd : ∀ a, (α a).snd = ψ (δ a) := fun a => by simp [α]
  have hαloc : IsLocalHom α := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hαfst] at ha
    exact IsUnit.of_map ψ a ha⟩
  let fstR : DualNumber (ChartRing k m d) →+* ChartRing k m d :=
    (TrivSqZeroExt.fstHom (ChartRing k m d) (ChartRing k m d) (ChartRing k m d)).toRingHom
  have hfstR : ∀ x, fstR x = x.fst := fun x => rfl
  have hfα : fstR.comp α = ψ := by ext a; simp [hfstR, hαfst]
  have hfev : ∀ (P : Polynomial A) (x : DualNumber (ChartRing k m d)),
      ((P.map α).eval x).fst = (P.map ψ).eval x.fst := by
    intro P x
    rw [← hfstR, Polynomial.eval_map, Polynomial.hom_eval₂, hfα, hfstR, Polynomial.eval_map]
  set w := (q.map α).eval (TrivSqZeroExt.inl θ) with hw
  set t := (q.derivative.map ψ).eval θ with ht
  have hw0 : w.fst = 0 := by rw [hw, hfev, TrivSqZeroExt.fst_inl, hqθ]
  set u : ChartRing k m d := -((hqu.unit⁻¹ : (ChartRing k m d)ˣ) : ChartRing k m d) * w.snd with hu
  set ζ : DualNumber (ChartRing k m d) := TrivSqZeroExt.inl θ + TrivSqZeroExt.inr u with hζ
  have hsq : (TrivSqZeroExt.inr u : DualNumber (ChartRing k m d)) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have hqζ : (q.map α).eval ζ = 0 := by
    rw [hζ, Polynomial.eval_add_of_sq_eq_zero _ _ _ hsq, ← hw]
    have hD : ((q.map α).derivative.eval (TrivSqZeroExt.inl θ)).fst = t := by
      rw [Polynomial.derivative_map, hfev, TrivSqZeroExt.fst_inl]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hw0]
    · have h1 : t * ((hqu.unit⁻¹ : (ChartRing k m d)ˣ) : ChartRing k m d) = 1 := hqu.mul_val_inv
      show (w + _).snd = (0 : DualNumber (ChartRing k m d)).snd
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, hD,
        TrivSqZeroExt.snd_zero, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul, hu]
      rw [← _root_.mul_assoc, mul_neg, h1, neg_mul, _root_.one_mul, add_neg_cancel]
  obtain ⟨Ψ, hΨ, hΨθ⟩ := lift_with_value ψ α hαloc θ ζ q hqm hqθ hqζ happ hinj
  have hid : RingHom.id (ChartRing k m d) = fstR.comp Ψ := by
    refine ringHom_ext_of_approx ψ hmax θ happ _ _ (fun a ha => hloc a ha) ?_ ?_
    · rw [RingHom.comp_assoc, hΨ, hfα]; rfl
    · simp [hfstR, hΨθ, hζ]
  have hfst : ∀ r, (Ψ r).fst = r := fun r => (RingHom.congr_fun hid r).symm
  let L : ChartRing k m d →ₗ[ℤ] ChartRing k m d :=
    (AddMonoidHom.mk' (fun r => (Ψ r).snd) (fun x y => by simp)).toIntLinearMap
  have hL : ∀ r, L r = (Ψ r).snd := fun r => rfl
  refine ⟨{ toLinearMap := L
            map_one_eq_zero' := by
              show (Ψ 1).snd = 0
              rw [map_one]; rfl
            leibniz' := fun x y => by
              show (Ψ (x * y)).snd = x • (Ψ y).snd + y • (Ψ x).snd
              rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, smul_eq_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
              ring }, fun a => ?_⟩
  show (Ψ (ψ a)).snd = ψ (δ a)
  rw [← RingHom.comp_apply, hΨ, hαsnd]

end GlobalTheory.ChartDerivation
