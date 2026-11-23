import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedLatticeTowerExistsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupFromTowerStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerDualStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerFreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TateMapDualHomBidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisRest
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.HT.TowerPoint

section Lin

open Module

variable {C O : Type} [Field C] [CommRing O] [IsDomain O] [Algebra O C] [IsFractionRing O C]

theorem exists_smul_eq {La M : Type} [AddCommGroup La] [AddCommGroup M] [Module O M]
    (inc : M →ₗ[O] C ⊗[ℤ] La) (h : ∀ a : La, ∃ m, inc m = 1 ⊗ₜ a) (x : C ⊗[ℤ] La) :
    ∃ d : O, d ≠ 0 ∧ ∃ m, inc m = d • x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul c a =>
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    obtain ⟨m, hm⟩ := h a
    have hd0 : algebraMap O C d ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero (map_mem_nonZeroDivisors _ (IsFractionRing.injective O C) hd)
    refine ⟨d, nonZeroDivisors.ne_zero hd, n • m, ?_⟩
    rw [map_smul, hm, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    field_simp
  | add x y hx hy =>
    obtain ⟨d, hd, m, hm⟩ := hx
    obtain ⟨d', hd', m', hm'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • m + d • m', ?_⟩
    rw [map_add, map_smul, map_smul, hm, hm', smul_add, smul_smul, smul_smul, mul_comm d' d]

theorem tmul_one_injective {W : Type} [AddCommGroup W] [Module O W] [Module.Free O W] {w : W}
    (h : (1 : C) ⊗ₜ[O] w = 0) : w = 0 := by
  have hi : Function.Injective ((Algebra.linearMap O C).rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O C)
  have h1 : (Algebra.linearMap O C).rTensor W ((1 : O) ⊗ₜ[O] w) = 0 := by
    simpa using h
  have h2 := hi (h1.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid O W) h2

variable {E : Type} [Field E] [NumberField E]

def omAct (C : Type) [Field C] [Algebra O C] (c : E ≃+* E) {L : Type} [AddCommGroup L] [Module O L]
    (ρL : 𝓞 E →+* Module.End O L) : 𝓞 E →+* Module.End C (C ⊗[O] Module.Dual O L) where
  toFun a := LinearMap.baseChange C (ρL (RingOfIntegers.mapRingEquiv c a)).dualMap
  map_one' := by
    ext w
    simp [LinearMap.baseChange_tmul]
    rfl
  map_mul' a b := by
    ext w
    simp [LinearMap.baseChange_tmul, mul_comm a b]
    rfl
  map_zero' := by
    ext w
    simp [LinearMap.baseChange_tmul]
    exact (congrArg _ (by ext x; simp [LinearMap.dualMap_apply])).trans (TensorProduct.tmul_zero _ _)
  map_add' a b := by
    ext w
    simp [LinearMap.baseChange_tmul, TensorProduct.tmul_add]
    exact (congrArg _ (by ext x; simp [LinearMap.dualMap_apply])).trans (TensorProduct.tmul_add _ _ _)

theorem omAct_tmul (c : E ≃+* E) {L : Type} [AddCommGroup L] [Module O L]
    (ρL : 𝓞 E →+* Module.End O L) (a : 𝓞 E) (t : C) (w : Module.Dual O L) :
    omAct C c ρL a (t ⊗ₜ w) = t ⊗ₜ (w ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a)) := rfl

theorem exists_point {c : E ≃+* E} {κ : O} {N : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    {EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ} {u : Fin N → La} {L : Type} [AddCommGroup L] [Module O L]
    [Module.Free O L] [Module.Finite O L] (ρL : 𝓞 E →+* Module.End O L)
    (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La))
    (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C)
    (hρ : ∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x))
    (hT : T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x))
    (hfree : IsFreeOn ρ T (fun i => 1 ⊗ₜ u i))
    (he : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C))
    (halt : ∀ x, e x x = 0) (hnd : ∀ y, (∀ x, e x y = 0) → y = 0) (hperf : dualLat e T = T)
    (hadj : ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y))
    {M : Type} [AddCommGroup M] [Module O M] (inc : M →ₗ[O] C ⊗[ℤ] La) (gen : La →+ M)
    (hinc : ∀ a, inc (gen a) = 1 ⊗ₜ a) (hgen : Submodule.span O (Set.range gen) = ⊤)
    (D : M →ₗ[O] Module.Dual O L) (B : M →ₗ[O] M →ₗ[O] O)
    (hB : ∀ a b, B (gen a) (gen b) = (EF a b : O))
    (hlin : ∀ (a : 𝓞 E) x, D (gen (a • x)) = D (gen x) ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a))
    (hκ : ∀ w, ∃ m, D m = κ • w) (hκ0 : algebraMap O C κ ≠ 0)
    (hlag : ∀ x, D x = 0 ↔ ∀ y, D y = 0 → B x y = 0) :
    ∃ P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L),
      P.ρ = ρ ∧ P.e = e ∧ (∀ i, P.t i = 1 ⊗ₜ u i) ∧
      P.om = LinearMap.range (TensorProduct.mk O C (Module.Dual O L) 1) ∧
      P.ρΩ = omAct C c ρL ∧ ∀ x, P.ht (1 ⊗ₜ x) = 1 ⊗ₜ D (gen x) := by
  let mk1 : Module.Dual O L →ₗ[O] C ⊗[O] Module.Dual O L := TensorProduct.mk O C (Module.Dual O L) 1
  let h0 : La →ₗ[ℤ] C ⊗[O] Module.Dual O L :=
    (mk1.restrictScalars ℤ) ∘ₗ (D.restrictScalars ℤ) ∘ₗ gen.toIntLinearMap
  let ht : C ⊗[ℤ] La →ₗ[C] C ⊗[O] Module.Dual O L := LinearMap.liftBaseChange C h0
  have ht1 : ∀ x, ht (1 ⊗ₜ x) = 1 ⊗ₜ D (gen x) := fun x => by
    simp [ht, h0, mk1, LinearMap.liftBaseChange_tmul]
  have htinc : ∀ m, ht (inc m) = 1 ⊗ₜ D m := fun m => by
    have : (ht.restrictScalars O) ∘ₗ inc = mk1 ∘ₗ D := by
      refine LinearMap.ext_on hgen ?_
      rintro _ ⟨a, rfl⟩
      simp [hinc, ht1, mk1]
    exact LinearMap.congr_fun this m
  have hincT : ∀ m, inc m ∈ T := fun m => by
    have : (⊤ : Submodule O M) ≤ T.comap inc := by
      rw [← hgen, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      change inc (gen a) ∈ T
      rw [hinc, hT]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact this (Submodule.mem_top (x := m))
  have hBe : ∀ m m', e (inc m) (inc m') = algebraMap O C (B m m') := by
    have h1 : ∀ a m', e (inc (gen a)) (inc m') = algebraMap O C (B (gen a) m') := fun a m' => by
      have : ((e (inc (gen a))).restrictScalars O) ∘ₗ inc = Algebra.linearMap O C ∘ₗ B (gen a) := by
        refine LinearMap.ext_on hgen ?_
        rintro _ ⟨b, rfl⟩
        simp [hinc, he, hB]
      exact LinearMap.congr_fun this m'
    intro m m'
    have : ((e.flip (inc m')).restrictScalars O) ∘ₗ inc = Algebra.linearMap O C ∘ₗ B.flip m' := by
      refine LinearMap.ext_on hgen ?_
      rintro _ ⟨a, rfl⟩
      simpa using h1 a m'
    exact LinearMap.congr_fun this m
  have hd0 : ∀ {d : O}, d ≠ 0 → algebraMap O C d ≠ 0 := fun hd h =>
    hd (IsFractionRing.injective O C (h.trans (map_zero _).symm))
  have hsurj : ∀ a : La, ∃ m, inc m = 1 ⊗ₜ a := fun a => ⟨gen a, hinc a⟩
  have hzero : ∀ (x : C ⊗[ℤ] La) (d : O) (m : M), d ≠ 0 → inc m = d • x → (ht x = 0 ↔ D m = 0) := by
    intro x d m hd hm
    have h1 : algebraMap O C d • ht x = 1 ⊗ₜ D m := by
      rw [← map_smul, algebraMap_smul, ← hm, htinc]
    constructor
    · intro h
      rw [h, smul_zero] at h1
      exact tmul_one_injective (C := C) h1.symm
    · intro h
      rw [h, TensorProduct.tmul_zero] at h1
      exact (smul_eq_zero.1 h1).resolve_left (hd0 hd)
  refine ⟨{ T := T, ρ := ρ, t := fun i => 1 ⊗ₜ u i, free := hfree, e := e, alt := halt, nondeg := hnd,
            perfect := hperf, adj := hadj, om := LinearMap.range mk1, om_lat := ?_,
            ρΩ := omAct C c ρL, om_stable := ?_, ht := ht, ht_lin := ?_, ht_mem := ?_, κ_ne := hκ0,
            κ_mem := ?_, lagr := ?_ }, rfl, rfl, fun _ => rfl, rfl, rfl, ht1⟩
  · refine ⟨?_, ?_⟩
    · rw [LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map _
    · rw [eq_top_iff]
      intro t _
      induction t using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | tmul s w =>
        have : s ⊗ₜ[O] w = s • ((1 : C) ⊗ₜ[O] w) := by simp [TensorProduct.smul_tmul']
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
      | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  · rintro a _ ⟨w, rfl⟩
    exact ⟨w ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a), rfl⟩
  · intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      have hs : ∀ z : La, s ⊗ₜ[ℤ] z = s • ((1 : C) ⊗ₜ[ℤ] z) := fun z => by simp [TensorProduct.smul_tmul']
      rw [hs, map_smul, map_smul, map_smul, map_smul, hρ, ht1, ht1, omAct_tmul, hlin]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x hx
    rw [hT] at hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact ⟨D (gen a), (ht1 a).symm⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul C r x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx
  · rintro _ ⟨w, rfl⟩
    obtain ⟨m, hm⟩ := hκ w
    refine ⟨inc m, hincT m, ?_⟩
    rw [htinc, hm]
    exact TensorProduct.tmul_smul _ _ _
  · intro x
    obtain ⟨d, hd, m, hm⟩ := exists_smul_eq inc hsurj x
    rw [hzero x d m hd hm]
    constructor
    · intro hDm y hy
      obtain ⟨d', hd', m', hm'⟩ := exists_smul_eq inc hsurj y
      have h1 := (hlag m).1 hDm m' ((hzero y d' m' hd' hm').1 hy)
      have h2 := hBe m m'
      rw [h1, map_zero, hm, hm', ← algebraMap_smul C d x, ← algebraMap_smul C d' y, map_smul,
        map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (hd0 hd'))).resolve_left (hd0 hd)
    · intro h
      refine (hlag m).2 fun y hy => ?_
      have h1 := h (inc y) (by rw [htinc, hy, TensorProduct.tmul_zero])
      have h2 := hBe m y
      rw [hm, ← algebraMap_smul C d x, map_smul, LinearMap.smul_apply, h1, smul_zero] at h2
      exact IsFractionRing.injective O C (h2.symm.trans (map_zero _).symm)

end Lin

section Forms

theorem baseChange_alt {R A W : Type} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup W] [Module R W]
    (B : LinearMap.BilinForm R W) (h : ∀ x, B x x = 0) (z : A ⊗[R] W) :
    LinearMap.BilinForm.baseChange A B z z = 0 := by
  have hs : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  have skew : ∀ z z' : A ⊗[R] W, LinearMap.BilinForm.baseChange A B z z' +
      LinearMap.BilinForm.baseChange A B z' z = 0 := by
    intro z z'
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      linear_combination hx + hy
    | tmul a m =>
      induction z' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        linear_combination hx + hy
      | tmul a' m' =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs m m', neg_smul,
          _root_.mul_comm a a', neg_add_cancel]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    linear_combination hx + hy + skew x y
  | tmul a m => rw [LinearMap.BilinForm.baseChange_tmul, h, zero_smul]

theorem baseChange_perfect {R W : Type} [CommRing R] [AddCommGroup W] [Module.Free ℤ W]
    [Module.Finite ℤ W] (B : LinearMap.BilinForm ℤ W) (h : ∀ x, B x x = 0) (hb : Function.Bijective B) :
    Function.Bijective (LinearMap.BilinForm.baseChange R B) := by
  classical
  have hs : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  let b := Module.finBasis ℤ W
  let bR := Algebra.TensorProduct.basis R b
  have hbR : ∀ i, bR i = 1 ⊗ₜ b i := fun i => by simp [bR]
  choose d hd using fun i => hb.2 (b.coord i)
  have hdb : ∀ i k, B (d i) (b k) = if k = i then 1 else 0 := fun i k => by
    rw [hd]; simp [Module.Basis.coord_apply, Finsupp.single_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine bR.ext_elem fun k => ?_
    have h1 := LinearMap.congr_fun hx (1 ⊗ₜ d k)
    rw [← bR.sum_repr x] at h1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hbR,
      LinearMap.BilinForm.baseChange_tmul, hs (b _), hdb] at h1
    simpa [Finset.sum_ite_eq] using h1
  · intro f
    refine ⟨∑ i, f (1 ⊗ₜ b i) • ((1 : R) ⊗ₜ[ℤ] d i), bR.ext fun k => ?_⟩
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hbR,
      LinearMap.BilinForm.baseChange_tmul, hdb]
    simp [Finset.sum_ite_eq]

theorem span_gen {R W T : Type} [CommRing R] [AddCommGroup W] [AddCommGroup T] [Module R T]
    (j : R ⊗[ℤ] W ≃ₗ[R] T) : Submodule.span R (Set.range fun a : W => j (1 ⊗ₜ a)) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.DYlb6.main j

theorem span_gen_baseChange {R O W T : Type} [CommRing R] [CommRing O] [Algebra R O] [AddCommGroup W]
    [AddCommGroup T] [Module R T] (j : R ⊗[ℤ] W ≃ₗ[R] T) :
    Submodule.span O (Set.range fun a : W => (1 : O) ⊗ₜ[R] j (1 ⊗ₜ a)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul o t =>
    have ht : t ∈ Submodule.span R (Set.range fun a : W => j (1 ⊗ₜ a)) := by
      rw [span_gen]; trivial
    induction ht using Submodule.span_induction generalizing o with
    | mem t h =>
      obtain ⟨a, rfl⟩ := h
      have : o ⊗ₜ[R] j (1 ⊗ₜ a) = o • ((1 : O) ⊗ₜ[R] j (1 ⊗ₜ a)) := by simp [TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ (hx o) (hy o)
    | smul s t _ ht =>
      rw [← TensorProduct.smul_tmul]
      exact ht _

theorem exists_inc {R O C W T : Type} [CommRing R] [CommRing O] [Field C] [Algebra R O] [Algebra O C]
    [AddCommGroup W] [AddCommGroup T] [Module R T] (j : R ⊗[ℤ] W ≃ₗ[R] T) :
    ∃ inc : O ⊗[R] T →ₗ[O] C ⊗[ℤ] W, ∀ a, inc (1 ⊗ₜ j (1 ⊗ₜ a)) = 1 ⊗ₜ a := by
  refine ⟨(AlgebraTensorModule.map (Algebra.linearMap O C) (LinearMap.id : W →ₗ[ℤ] W)) ∘ₗ
    (AlgebraTensorModule.cancelBaseChange ℤ R O O W).toLinearMap ∘ₗ
    (LinearEquiv.baseChange R O _ _ j.symm).toLinearMap, fun a => ?_⟩
  simp [LinearEquiv.baseChange]

end Forms

section Tower

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

theorem tate_dual_ext {G : PDivGroup p O} {χ ψ : G.dual.Tate} (h : ∀ n, charElem χ n = charElem ψ n) : χ = ψ :=
  TateOver.ext (funext fun n => AlgHom.ext fun φ => by
    rw [← apply_charElem, ← apply_charElem, h])

omit [Fact p.Prime] in

theorem lev_surjective {La : Type} [AddCommGroup La] (n : ℕ) : Function.Surjective (lev (La := La) p n) :=
  fun t => by
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
    exact ⟨a, ha⟩

theorem muRoot_intCast_smul (ζ : ℕ → Oˣ) (h0 : (fun n => ((ζ n : Oˣ) : O)) 0 = 1)
    (h : ∀ n, (fun n => ((ζ n : Oˣ) : O)) (n + 1) ^ p = (fun n => ((ζ n : Oˣ) : O)) n) (z : ℤ) (n : ℕ) :
    muRoot ((z : ℤ_[p]) • muTate O (fun n => ((ζ n : Oˣ) : O)) h0 h) n = ((ζ n ^ z : Oˣ) : O) := by
  set t := muTate O (fun n => ((ζ n : Oˣ) : O)) h0 h
  rw [Int.cast_smul_eq_zsmul]
  have key : ∀ z : ℤ, muRoot ((z + 1) • t) n = muRoot (z • t) n * (ζ n : O) := fun z => by
    rw [add_smul, one_smul, muRoot_add, muRoot_muTate]
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [key, ih, zpow_add_one, Units.val_mul]
  | pred i ih =>
    have h1 := key (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h1
    rw [zpow_sub_one]
    have h2 := congrArg (· * ((ζ n)⁻¹ : Oˣ).1) h1
    simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one] at h2
    rw [Units.val_mul, h2]

variable {La L : Type} [AddCommGroup La] [AddCommGroup L] [Module O L] {X : OrdTower p O La L}
  {G : PDivGroup p O} {e : ∀ n, G.A n ≃ₐ[O] X.A n} {τ : La →+ G.Tate}

theorem lam_tau_act {B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ} {ζ : ℕ → Oˣ} {lam : G ⟶ G.dual}
    (hlam : ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) =
      ((ζ n ^ B a b : Oˣ) : O))
    {φ ψ : La → La} {f : G ⟶ G}
    (hf : ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a)))
    (hadj : ∀ x y, B (ψ x) y = B x (φ y)) (x : La) :
    tateMap G G.dual O lam (τ (ψ x)) =
      tateMap _ _ O (dualHom G G f) (tateMap G G.dual O lam (τ x)) := by
  refine tate_dual_ext fun n => ?_
  rw [charElem_tateMap]
  refine (e n).injective (Subtype.ext (funext fun t => ?_))
  obtain ⟨b, rfl⟩ := lev_surjective n t
  rw [hlam, hf, hlam, hadj]

theorem pairing_tau (hre : X.Realises G e τ) {B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ} {ζ : ℕ → Oˣ} {lam : G ⟶ G.dual}
    (hlam : ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) =
      ((ζ n ^ B a b : Oˣ) : O))
    (h0 : (fun n => ((ζ n : Oˣ) : O)) 0 = 1)
    (h : ∀ n, (fun n => ((ζ n : Oˣ) : O)) (n + 1) ^ p = (fun n => ((ζ n : Oˣ) : O)) n) (a b : La) :
    pairing G O (τ b) (tateMap G G.dual O lam (τ a)) =
      ((B a b : ℤ) : ℤ_[p]) • muTate O (fun n => ((ζ n : Oˣ) : O)) h0 h :=
  muRoot_ext fun n => by
    rw [muRoot_intCast_smul, muRoot_pairing, hre.pt, hlam]

end Tower

section Bij

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

theorem tateMap_bijective {G : PDivGroup p O} (lam : G ⟶ G.dual) (ε : (mu p O).Tate)
    (hε : Function.Bijective fun a : ℤ_[p] => (a • ε : (mu p O).Tate))
    (hp2 : Function.Bijective (pairing G O).flip)
    (Bp : G.Tate →ₗ[ℤ_[p]] G.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : Function.Bijective Bp)
    (h : ∀ x y, pairing G O y (tateMap G G.dual O lam x) = Bp x y • ε) :
    Function.Bijective (tateMap G G.dual O lam) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine hB.1 ((LinearMap.ext fun y => ?_).trans (map_zero Bp).symm)
    refine hε.1 ?_
    change Bp x y • ε = (0 : ℤ_[p]) • ε
    rw [← h, hx, map_zero, zero_smul]
  · intro χ
    let u : ℤ_[p] ≃ₗ[ℤ_[p]] (mu p O).Tate :=
      LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ε) hε
    obtain ⟨x, hx⟩ := hB.2 (u.symm.toLinearMap ∘ₗ (pairing G O).flip χ)
    refine ⟨x, hp2.1 (LinearMap.ext fun y => ?_)⟩
    change pairing G O y (tateMap G G.dual O lam x) = pairing G O y χ
    rw [h, hx]
    exact u.apply_symm_apply (pairing G O y χ)

end Bij

theorem exists_HTPoint : FarguesHodgeTate → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La) (hu : IsPolLattice c p EF u) (L : Type) [AddCommGroup L] [Module O L] [Module.Free O L] [Module.Finite O L] (X : OrdTower p O La L) (ρL : 𝓞 E →+* Module.End O L) (ζ : ℕ → Oˣ) (κ : O), (∀ a : 𝓞 E, X.Acts (DistribMulAction.toAddMonoidHom La a) (ρL a)) → 2 * Module.finrank O L = Module.finrank ℤ La → (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends EF ζ → IsHTConst v p κ → ∃ P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L), IsPointOf p X.der EF ζ ρL u P := by
  intro hF p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c hc La _ _ EF N u hu L _ _ _ _ X ρL ζ κ hact hrank hprim hcomp
    hpair hκ
  classical
  haveI := hu.free
  haveI := hu.finite
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : IsIntegrallyClosed O := hv.isIntegrallyClosed
  obtain ⟨alg⟩ := (GlobalTheory.T.complete_integers_properties p C v O hv hp hO).1
  letI := alg
  obtain ⟨ρ, T, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ := GlobalTheory.T.polarised_lattice_tower_exists p C v O hv hp hO E c La EF N u hu
  obtain ⟨G, ee, τ, hre, hheight, j, hj⟩ := GlobalTheory.T.divisible_group_from_tower p C v O hv hp hO La L X
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.divisible_group_tower_dual p C v O hv hp hO La L X G ee τ hre EF ζ hprim hcomp hpair
  obtain ⟨jj, hder, hjj⟩ := GlobalTheory.T.divisible_group_tower_free p C v O hv hp hO La L X G ee τ hre
  have hend := (GlobalTheory.T.divisible_group_tower_compatibility p C v O hv hp hO La L X G ee τ hre).1
  haveI : Module.Free O G.omega := Module.Free.of_equiv jj.symm
  haveI : Module.Finite O G.omega := Module.Finite.equiv jj.symm

  let ζ' : ℕ → O := fun n => ((ζ n : Oˣ) : O)
  have hprim' : ∀ n, IsPrimitiveRoot (ζ' n) (p ^ n) := fun n => (IsPrimitiveRoot.coe_units_iff).2 (hprim n)
  have h0 : ζ' 0 = 1 := by simpa using (hprim' 0).pow_eq_one
  have hs : ∀ n, ζ' (n + 1) ^ p = ζ' n := fun n => by
    change ((ζ (n + 1) : Oˣ) : O) ^ p = (ζ n : O)
    rw [← Units.val_pow_eq_pow_val, hcomp]
  have hζ1 : ζ' 1 ≠ 1 := by
    have := (hprim' 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt)
    exact this

  let b0 : LinearMap.BilinForm ℤ_[p] (ℤ_[p] ⊗[ℤ] La) := LinearMap.BilinForm.baseChange ℤ_[p] EF
  let Bp : LinearMap.BilinForm ℤ_[p] G.Tate :=
    b0.compl₁₂ j.symm.toLinearMap j.symm.toLinearMap
  have hjs : ∀ a, j.symm (τ a) = 1 ⊗ₜ a := fun a => by rw [← hj, LinearEquiv.symm_apply_apply]
  have hBp : ∀ a b, Bp (τ a) (τ b) = ((EF a b : ℤ) : ℤ_[p]) := fun a b => by
    simp [Bp, b0, hjs, LinearMap.BilinForm.baseChange_tmul]
  have hBpalt : ∀ x, Bp x x = 0 := fun x => baseChange_alt EF hu.alt _
  have hBpbij : Function.Bijective Bp := by
    have hb := baseChange_perfect (R := ℤ_[p]) EF hu.alt hu.unimod
    constructor
    · intro x y hxy
      refine j.symm.injective (hb.1 (LinearMap.ext fun w => ?_))
      have := LinearMap.congr_fun hxy (j w)
      simpa [Bp] using this
    · intro f
      obtain ⟨w, hw⟩ := hb.2 (f ∘ₗ j.toLinearMap)
      refine ⟨j w, LinearMap.ext fun y => ?_⟩
      have := LinearMap.congr_fun hw (j.symm y)
      simpa [Bp, b0] using this
  have hpairing : ∀ x y, pairing G O y (tateMap G G.dual O lam x) = Bp x y • muTate O ζ' h0 hs := by
    have hst : Submodule.span ℤ_[p] (Set.range τ) = ⊤ := by
      have := span_gen j
      simpa only [hj] using this
    have hbil : (pairing G O).flip ∘ₗ tateMap G G.dual O lam =
        Bp.compr₂ (LinearMap.toSpanSingleton ℤ_[p] _ (muTate O ζ' h0 hs)) := by
      refine LinearMap.ext_on hst ?_
      rintro _ ⟨a, rfl⟩
      refine LinearMap.ext_on hst ?_
      rintro _ ⟨b, rfl⟩
      change pairing G O (τ b) (tateMap G G.dual O lam (τ a)) = Bp (τ a) (τ b) • muTate O ζ' h0 hs
      rw [hBp]
      exact pairing_tau hre hlam h0 hs a b
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun hbil x) y
  have hperf := PDivGroup.tate_free_perfect p O C G
  have hbij : Function.Bijective (tateMap G G.dual O lam) :=
    tateMap_bijective lam (muTate O ζ' h0 hs) (hperf.2.2.2.2.2.1 ζ' h0 hs hprim') hperf.2.2.2.2.2.2.2 Bp hBpbij
      hpairing
  have hrk : 2 * Module.finrank O G.omega = G.height := by
    rw [jj.finrank_eq, ← (Module.Free.chooseBasis O L).toDualEquiv.finrank_eq, hrank, hheight]

  let B : LinearMap.BilinForm O (O ⊗[ℤ_[p]] G.Tate) := LinearMap.BilinForm.baseChange O Bp
  have hBB : ∀ x y, B (1 ⊗ₜ x) (1 ⊗ₜ y) = algebraMap ℤ_[p] O (Bp x y) := fun x y => by
    simp [B, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨hcok, hlag⟩ := GlobalTheory.CompanionTheory.Ar.HT.dlog_lagrangian hF p C v O hv hp hO G lam ζ' h0 hs B κ hζ1 hκ hbij hrk
    (fun x y => ⟨Bp x y, hpairing x y, hBB x y⟩) (baseChange_alt Bp hBpalt)
  let D : O ⊗[ℤ_[p]] G.Tate →ₗ[O] Module.Dual O L :=
    jj.toLinearMap ∘ₗ dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O
  let gen : La →+ O ⊗[ℤ_[p]] G.Tate := ((TensorProduct.mk ℤ_[p] O G.Tate 1).toAddMonoidHom).comp τ
  have hDgen : ∀ x, D (gen x) = jj (dlog G (tateMap G G.dual O lam (τ x))) := fun x => by
    simp [D, gen]
  obtain ⟨inc, hinc⟩ := exists_inc (C := C) (O := O) j
  have hinc' : ∀ a, inc (gen a) = 1 ⊗ₜ a := fun a => by
    have := hinc a
    rwa [hj] at this
  have hgen : Submodule.span O (Set.range gen) = ⊤ := by
    have h' := span_gen_baseChange (O := O) j
    simp only [hj] at h'
    exact h'
  have hlin : ∀ (a : 𝓞 E) x, D (gen (a • x)) = D (gen x) ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a) := by
    intro a x
    obtain ⟨f, -, hf⟩ := hend _ _ (hact (RingOfIntegers.mapRingEquiv c a))
    have h := lam_tau_act (ψ := fun y => a • y) hlam hf (fun y z => hu.adj a y z) x
    rw [hDgen, hDgen, h, dlog_tateMap, hjj _ _ f (hact _) hf]
  obtain ⟨P, hPρ, hPe, hPt, hPom, hPΩ, hPht⟩ := exists_point (κ := κ) (u := u) ρL ρ T e h1 h2 h3 h4 h5 h6 h7 h8 inc gen
    hinc' hgen D B (fun a b => by
      change B (1 ⊗ₜ τ a) (1 ⊗ₜ τ b) = _
      rw [hBB, hBp, map_intCast]) hlin
    (fun w => by
      obtain ⟨m, hm⟩ := hcok (jj.symm w)
      refine ⟨m, ?_⟩
      change jj (_) = _
      rw [hm, map_smul, LinearEquiv.apply_symm_apply]) hκ.1
    (fun x => by
      have hz : ∀ y, D y = 0 ↔ (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O) y = 0 := fun y =>
        jj.map_eq_zero_iff
      simp only [hz]
      exact hlag x)
  refine ⟨P, hPt, fun a x => by rw [hPρ]; exact h1 a x, fun x y => by rw [hPe]; exact h4 x y, hPom,
    fun a w => by rw [hPΩ]; rfl, ?_⟩
  intro n x f w hf hd
  have hfe : f = (ee n (charElem (tateMap G G.dual O lam (τ x)) n)).1 := funext fun t => by
    obtain ⟨b, rfl⟩ := lev_surjective n t
    rw [hf, hlam]
  have h9 := hder (tateMap G G.dual O lam (τ x)) n
  rw [← hfe] at h9
  obtain ⟨y, hy⟩ := (X.der_unique n f w _ hd).1 h9
  refine ⟨1 ⊗ₜ y, by rw [hPom]; exact ⟨y, rfl⟩, ?_⟩
  rw [hPht, hDgen, hy, TensorProduct.tmul_add, TensorProduct.tmul_smul]

end GlobalTheory.CompanionTheory.Ar.HT.TowerPoint
