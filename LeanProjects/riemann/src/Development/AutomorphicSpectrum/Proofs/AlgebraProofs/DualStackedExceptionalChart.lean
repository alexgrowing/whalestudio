import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChartParts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix
open GroundTheory.Heights₂.Heights.StackedExceptionalChart GroundTheory.Heights₂.Heights.StackedExceptionalFirstGeometric

noncomputable section

theorem exists_forms_of_linear {k R A : Type*} [Field k] [CommRing R] [AddCommGroup A] (σ₀ : k →+* R) {n : ℕ}
    (E : A →+ (Fin n → k)) (Λ : A →+ R)
    (hact : ∀ (c : k) (φ : A), ∃ φ' : A, E φ' = c • E φ ∧ Λ φ' = σ₀ c * Λ φ)
    (hker : ∀ φ, E φ = 0 → Λ φ = 0) :
    ∃ W : Fin n → R, ∀ φ, ∑ j, σ₀ (E φ j) * W j = Λ φ := by
  classical
  letI : Module k R := Module.compHom R σ₀
  have hsm : ∀ (c : k) (r : R), c • r = σ₀ c * r := fun _ _ => rfl
  have hwd : ∀ φ φ', E φ = E φ' → Λ φ = Λ φ' := fun φ φ' h => by
    have := hker (φ - φ') (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let V : Submodule k (Fin n → k) :=
    { carrier := Set.range E
      add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add E x y⟩
      zero_mem' := ⟨0, map_zero E⟩
      smul_mem' := by rintro c _ ⟨x, rfl⟩; obtain ⟨x', h, -⟩ := hact c x; exact ⟨x', h⟩ }
  let pre : V → A := fun w => Classical.choose w.2
  have hpre : ∀ w : V, E (pre w) = w := fun w => Classical.choose_spec w.2
  let L : V →ₗ[k] R :=
    { toFun := fun w => Λ (pre w)
      map_add' := fun w w' => by
        rw [← map_add]
        exact hwd _ _ (by rw [map_add, hpre, hpre, hpre]; rfl)
      map_smul' := fun c w => by
        obtain ⟨x', h, h'⟩ := hact c (pre w)
        rw [RingHom.id_apply, hsm, ← h']
        exact hwd _ _ (by rw [h, hpre, hpre]; rfl) }
  obtain ⟨G, hG⟩ := LinearMap.exists_extend L
  refine ⟨fun j => G (Pi.single j 1), fun φ => ?_⟩
  have h1 : E φ = ∑ j, E φ j • (Pi.single j 1 : Fin n → k) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : G (E φ) = Λ φ := by
    have h3 : G (E φ) = L ⟨E φ, φ, rfl⟩ := by
      rw [← hG]; rfl
    rw [h3]
    exact hwd _ _ (hpre _)
  rw [← h2]
  conv_rhs => rw [h1, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hsm]

section Quad

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem formCoord_mul_of_quadIdentity {φ₁ φ₂ φ₃ φ₄ : Fin i → K} (h : QuadIdentity φ₁ φ₂ φ₃ φ₄) :
    (formCoord φ₁ : ProjField K i) * formCoord φ₂ = formCoord φ₃ * formCoord φ₄ := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hp : (∑ j, C (φ₁ j) * X j : MvPolynomial (Fin i) K) * (∑ j, C (φ₂ j) * X j) =
      (∑ j, C (φ₃ j) * X j) * (∑ j, C (φ₄ j) * X j) := by
    refine MvPolynomial.funext fun x => ?_
    have := h x
    simpa [dotProduct, map_sum] using this
  simp only [formCoord, AddMonoidHom.mk'_apply, ← map_mul, hp]

theorem graphMap_secondForm {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (d : T → ℤ) :
    graphMap (dualIdeal b') (linForm (stackedDiag a)) (graphSecondForm d) =
      C (Ideal.Quotient.mk (dualIdeal b') (linD fun t => d t * a t)) * X () := by
  have h : ∀ t, linForm (stackedDiag a) ⟨(), t⟩ = (C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) := by
    intro t
    simp [linForm, stackedDiag]
  have h2 : ∀ t, graphMap (dualIdeal b') (linForm (stackedDiag a)) (graphSecond t) =
      C (Ideal.Quotient.mk (dualIdeal b') (C (a t) * X ⟨(), t⟩)) * X () := by
    intro t
    simp only [graphMap, graphSecond, coe_eval₂Hom, eval₂_X, h]
  simp only [graphSecondForm, linD, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h3 : Ideal.Quotient.mk (dualIdeal b') (C (d t * a t) * X ⟨(), t⟩) =
      ((d t : ℤ) : MRing (dualBlocks T) ⧸ dualIdeal b') * Ideal.Quotient.mk (dualIdeal b') (C (a t) * X ⟨(), t⟩) := by
    rw [C_mul, mul_assoc, map_mul, show (C (d t) : MRing (dualBlocks T)) = ((d t : ℤ) : MRing (dualBlocks T)) from
      eq_intCast _ _, map_intCast]
  rw [map_mul, h2, show (C (d t) : MRing (stackedBlocks T)) = ((d t : ℤ) : MRing (stackedBlocks T)) from
    eq_intCast _ _, map_intCast, h3]
  generalize Ideal.Quotient.mk (dualIdeal b') (C (a t) * X ⟨(), t⟩) = q
  rw [map_mul, map_intCast, mul_assoc]

theorem quadRel : DualStackedGraphQuadRel.Statement := by
  intro K _ _ i F' T _ _ b' a
  refine ⟨fun c₁ c₂ c₃ c₄ h => ?_, fun c₁ d₂ c₃ d₄ h => ?_⟩
  · have hm := mem_dualIdeal_of_isLinAt_quad (isLinAt_linD b' c₁) (isLinAt_linD b' c₂) (isLinAt_linD b' c₃)
      (isLinAt_linD b' c₄) (formCoord_mul_of_quadIdentity h)
    have := fstEmb_mem a hm
    simpa [graphFirstForm, fstEmb_linD] using this
  · have hm := mem_dualIdeal_of_isLinAt_quad (isLinAt_linD b' c₁) (isLinAt_linD b' fun t => d₂ t * a t)
      (isLinAt_linD b' c₃) (isLinAt_linD b' fun t => d₄ t * a t) (formCoord_mul_of_quadIdentity h)
    show _ ∈ RingHom.ker _
    have e : ∀ c : T → ℤ, graphFirstForm c = fstEmb (linD c) := fun c => by rw [fstEmb_linD]; rfl
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_secondForm, graphMap_secondForm, e, e,
      graphMap_fstEmb, graphMap_fstEmb]
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, h0, sub_self]

end Quad

section Chart

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
  {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T)

omit [DecidableEq T] in
theorem latCombo_injective : Function.Injective (latCombo b') := by
  intro c c' h
  rw [latCombo_eq, latCombo_eq] at h
  exact b'.equivFun.symm.injective (Subtype.ext h)

omit [DecidableEq T] in
theorem latCombo_add (c c' : T → ℤ) : latCombo b' (c + c') = latCombo b' c + latCombo b' c' := by
  simp only [latCombo, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem latCombo_single (t : T) : latCombo b' (Pi.single t 1) = (b' t : Fin i → K) := by
  rw [latCombo, Finset.sum_eq_single t (fun s _ hs => by rw [Pi.single_eq_of_ne hs, zero_smul])
    (fun h => absurd (Finset.mem_univ t) h), Pi.single_eq_same, one_smul]

omit [DecidableEq T] in
theorem graphFirstForm_add (c c' : T → ℤ) :
    graphFirstForm (c + c') = graphFirstForm c + graphFirstForm c' := by
  simp only [graphFirstForm, Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib]

theorem graphFirstForm_single (t : T) : graphFirstForm (Pi.single t 1) = graphFirst t := by
  rw [graphFirstForm, Finset.sum_eq_single t (fun s _ hs => by rw [Pi.single_eq_of_ne hs, C_0, zero_mul])
    (fun h => absurd (Finset.mem_univ t) h), Pi.single_eq_same, C_1, one_mul]

def scaleCoord (ω : 𝓞 K) : T → ℤ :=
  b'.equivFun ⟨algebraMap (𝓞 K) K ω • (b' v : Fin i → K), smul_mem_dual F' ω (b' v).2⟩

theorem latCombo_scaleCoord (ω : 𝓞 K) :
    latCombo b' (scaleCoord b' v ω) = algebraMap (𝓞 K) K ω • (b' v : Fin i → K) := by
  rw [latCombo_eq, scaleCoord, LinearEquiv.symm_apply_apply]

def chartInv : excChartRing b' a v u :=
  ((isUnit_first b' a v u).unit⁻¹ : (excChartRing b' a v u)ˣ)

theorem first_mul_chartInv : excChartMap b' a v u (graphFirst v) * chartInv b' a v u = 1 :=
  (isUnit_first b' a v u).mul_val_inv

theorem chartMap_eq_zero {e : MRing (stackedBlocks T)} (he : e ∈ stackedGraph b' a) :
    excChartMap b' a v u e = 0 := by
  have hJ : e ∈ excChartIdeal b' a u := Ideal.mem_sup_left he
  rw [excChartMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hJ, map_zero]

def chartScale : 𝓞 K →+* excChartRing b' a v u where
  toFun ω := excChartMap b' a v u (graphFirstForm (scaleCoord b' v ω)) * chartInv b' a v u
  map_one' := by
    have h : scaleCoord b' v 1 = Pi.single v 1 := latCombo_injective b' (by
      rw [latCombo_scaleCoord, latCombo_single, map_one, one_smul])
    rw [h, graphFirstForm_single, first_mul_chartInv]
  map_mul' ω₁ ω₂ := by
    have h := (quadRel K i F' T b' a).1 (scaleCoord b' v ω₁) (scaleCoord b' v ω₂) (scaleCoord b' v (ω₁ * ω₂))
      (Pi.single v 1) (by
        intro x
        simp only [latCombo_scaleCoord, latCombo_single, smul_dotProduct, smul_eq_mul, map_mul]
        ring)
    have h0 := chartMap_eq_zero b' a v u h
    rw [map_sub, map_mul (excChartMap b' a v u), map_mul (excChartMap b' a v u), graphFirstForm_single,
      sub_eq_zero] at h0
    have hi := first_mul_chartInv b' a v u
    set x := excChartMap b' a v u (graphFirst v)
    set z := chartInv b' a v u
    calc _ = excChartMap b' a v u (graphFirstForm (scaleCoord b' v (ω₁ * ω₂))) * x * z * z := by
            rw [mul_assoc _ x z, hi, mul_one]
      _ = _ := by rw [← h0]; ring

  map_zero' := by
    have h : scaleCoord b' v 0 = 0 := by
      simp [scaleCoord]
    rw [h]
    simp [graphFirstForm]
  map_add' ω₁ ω₂ := by
    have h : scaleCoord b' v (ω₁ + ω₂) = scaleCoord b' v ω₁ + scaleCoord b' v ω₂ := latCombo_injective b' (by
      rw [latCombo_add, latCombo_scaleCoord, latCombo_scaleCoord, latCombo_scaleCoord, map_add, add_smul])
    rw [h, graphFirstForm_add, map_add, add_mul]

theorem chartScale_mul_first (ω : 𝓞 K) {c : T → ℤ}
    (hc : latCombo b' c = algebraMap (𝓞 K) K ω • (b' v : Fin i → K)) :
    chartScale b' a v u ω * excChartMap b' a v u (graphFirst v) = excChartMap b' a v u (graphFirstForm c) := by
  have h : scaleCoord b' v ω = c := latCombo_injective b' (by rw [latCombo_scaleCoord, hc])
  show excChartMap b' a v u (graphFirstForm (scaleCoord b' v ω)) * chartInv b' a v u * _ = _
  rw [h, mul_assoc, mul_comm (chartInv b' a v u), first_mul_chartInv, mul_one]

theorem chartMap_firstForm_mul (e : T → ℤ) :
    excChartMap b' a v u (graphFirstForm fun s => e s * a s) = 0 := by
  rw [graphFirstForm, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [C_mul, mul_assoc, map_mul (excChartMap b' a v u), first_eq_zero, mul_zero]

end Chart

section Forms

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
  {F F' : HermLattice K i}

def evalInt {y : Fin i → K} (hy : y ∈ F.lattice) (φ : dualLattice F) : 𝓞 K :=
  Classical.choose (RingHom.mem_range.mp (φ.2 y hy))

theorem algebraMap_evalInt {y : Fin i → K} (hy : y ∈ F.lattice) (φ : dualLattice F) :
    algebraMap (𝓞 K) K (evalInt hy φ) = (φ : Fin i → K) ⬝ᵥ y :=
  Classical.choose_spec (RingHom.mem_range.mp (φ.2 y hy))

theorem eq_evalInt {y : Fin i → K} (hy : y ∈ F.lattice) (φ : dualLattice F) {c : 𝓞 K}
    (h : algebraMap (𝓞 K) K c = (φ : Fin i → K) ⬝ᵥ y) : c = evalInt hy φ :=
  FaithfulSMul.algebraMap_injective (𝓞 K) K (h.trans (algebraMap_evalInt hy φ).symm)

def evalVec {k : Type} [Field k] (ρ : 𝓞 K →+* k) {n : ℕ} (Y : Fin n → Fin i → K) (hY : ∀ j, Y j ∈ F.lattice) :
    dualLattice F →+ (Fin n → k) :=
  AddMonoidHom.mk' (fun φ j => ρ (evalInt (hY j) φ)) (by
    intro φ ψ
    funext j
    rw [Pi.add_apply, ← map_add]
    congr 1
    refine (eq_evalInt (hY j) _ ?_).symm
    rw [map_add, algebraMap_evalInt, algebraMap_evalInt, Submodule.coe_add, add_dotProduct])

omit [DecidableEq T] in
theorem graphSecondForm_add (d d' : T → ℤ) :
    graphSecondForm (d + d') = graphSecondForm d + graphSecondForm d' := by
  simp only [graphSecondForm, Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib]

theorem graphSecondForm_single (t : T) : graphSecondForm (Pi.single t 1) = graphSecond t := by
  rw [graphSecondForm, Finset.sum_eq_single t (fun s _ hs => by rw [Pi.single_eq_of_ne hs, C_0, zero_mul])
    (fun h => absurd (Finset.mem_univ t) h), Pi.single_eq_same, C_1, one_mul]

def chartSecond (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ)
    (v u : T) : dualLattice F →+ excChartRing b' a v u :=
  AddMonoidHom.mk' (fun φ => excChartMap b' a v u (graphSecondForm (b.equivFun φ))) (by
    intro φ ψ
    rw [map_add, graphSecondForm_add, map_add])

omit [DecidableEq T] in

theorem latCombo_equivFun (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (φ : dualLattice F) :
    latCombo b' (fun s => b.equivFun φ s * a s) = (φ : Fin i → K) := by
  have h := congrArg Subtype.val (b.sum_equivFun φ)
  rw [Submodule.coe_sum] at h
  refine Eq.trans ?_ h
  rw [latCombo]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Submodule.coe_smul, hab, mul_smul]

theorem chartScale_mul_second (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (v u : T) (ω : 𝓞 K)
    {φ φ' : dualLattice F} (h : (φ' : Fin i → K) = algebraMap (𝓞 K) K ω • (φ : Fin i → K)) :
    chartScale b' a v u ω * chartSecond b b' a v u φ = chartSecond b b' a v u φ' := by
  have q := (quadRel K i F' T b' a).2 (scaleCoord b' v ω) (b.equivFun φ) (Pi.single v 1) (b.equivFun φ') (by
    intro x
    rw [latCombo_equivFun b b' hab, latCombo_equivFun b b' hab, latCombo_scaleCoord, latCombo_single, h]
    simp only [smul_dotProduct, smul_eq_mul]
    ring)
  have h0 := chartMap_eq_zero b' a v u q
  rw [map_sub, map_mul (excChartMap b' a v u), map_mul (excChartMap b' a v u), graphFirstForm_single, sub_eq_zero,
    ← chartScale_mul_first b' a v u ω (latCombo_scaleCoord b' v ω)] at h0
  refine (isUnit_first b' a v u).mul_left_cancel ?_
  show _ * (_ * excChartMap b' a v u (graphSecondForm (b.equivFun φ))) =
    _ * excChartMap b' a v u (graphSecondForm (b.equivFun φ'))
  rw [← h0]
  ring

theorem chartScale_eq_zero (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (v u : T) {ω : 𝓞 K}
    (hω : algebraMap (𝓞 K) K ω • (b' v : Fin i → K) ∈ dualLattice F) : chartScale b' a v u ω = 0 := by
  obtain ⟨e, he⟩ := exists_latCombo b b' hab hω
  have h := chartScale_mul_first b' a v u ω he.symm
  rw [chartMap_firstForm_mul] at h
  exact (isUnit_first b' a v u).mul_left_eq_zero.mp h

theorem chartSecond_eq_zero (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (v u : T) {P : 𝓞 K → Prop}
    (hP : ∀ ω, P ω → chartScale b' a v u ω = 0) {φ : dualLattice F}
    (hφ : (φ : Fin i → K) ∈ Submodule.span ℤ
      {ψ | ∃ c : 𝓞 K, P c ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ}) :
    chartSecond b b' a v u φ = 0 := by
  have hle : Submodule.span ℤ {ψ : Fin i → K | ∃ c : 𝓞 K, P c ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ} ≤
      Submodule.map (dualLattice F).subtype (LinearMap.ker (chartSecond b b' a v u).toIntLinearMap) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, hc, χ, hχ, rfl⟩
    refine ⟨⟨_, smul_mem_dual F c hχ⟩, ?_, rfl⟩
    have h := chartScale_mul_second b b' hab v u c (φ := ⟨χ, hχ⟩) (φ' := ⟨_, smul_mem_dual F c hχ⟩) rfl
    rw [hP c hc, zero_mul] at h
    exact h.symm
  obtain ⟨x, hx, hxe⟩ := hle hφ
  have : x = φ := Subtype.ext hxe
  rw [← this]
  exact hx

theorem exists_lift {R k : Type*} [CommRing R] [Field k] (ρ : 𝓞 K →+* k) (hρ : Function.Surjective ρ)
    (τ : 𝓞 K →+* R) (hτ : ∀ ω, ρ ω = 0 → τ ω = 0) : ∃ σ₀ : k →+* R, ∀ ω, σ₀ (ρ ω) = τ ω :=
  ⟨ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨τ, fun ω hω => hτ ω (RingHom.mem_ker.mp hω)⟩,
    fun ω => RingHom.liftOfRightInverse_comp_apply _ _ _ _ ω⟩

end Forms

theorem chartForms : DualStackedExcChartForms.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ ρ π y₀ m g α M hX v u
  obtain ⟨hρ, -, hy₀, hg, -, hM0, hMs, -, -, h10, -, h12⟩ := hX
  have hk : ∀ ω, ρ ω = 0 → chartScale b' a v u ω = 0 := fun ω hω =>
    chartScale_eq_zero b b' hab v u (h10 ω hω _ (b' v).2)
  obtain ⟨σ₀, hσ⟩ := exists_lift ρ hρ (chartScale b' a v u) hk
  refine ⟨σ₀, fun ω c hc => by rw [hσ]; exact chartScale_mul_first b' a v u ω hc, ?_⟩
  let Y : Fin (m + 1) → Fin i → K := Fin.cons y₀ g
  have hY : ∀ j, Y j ∈ F.lattice := by
    refine Fin.cases ?_ fun j => ?_
    · exact hy₀
    · exact hlt.le (hg j)
  have hEval : ∀ (φ : dualLattice F) (j), evalVec ρ Y hY φ j = ρ (evalInt (hY j) φ) := fun _ _ => rfl
  obtain ⟨W, hW⟩ := exists_forms_of_linear σ₀ (evalVec ρ Y hY) (chartSecond b b' a v u)
    (fun c φ => by
      obtain ⟨ω, rfl⟩ := hρ c
      refine ⟨⟨_, smul_mem_dual F ω φ.2⟩, ?_, ?_⟩
      · funext j
        rw [Pi.smul_apply, hEval, hEval, smul_eq_mul, ← map_mul]
        congr 1
        refine (eq_evalInt (hY j) _ ?_).symm
        rw [map_mul, algebraMap_evalInt, smul_dotProduct, smul_eq_mul]
      · rw [hσ]
        exact (chartScale_mul_second b b' hab v u ω rfl).symm)
    (fun φ hφ => by
      have h0 : ∀ j, ρ (evalInt (hY j) φ) = 0 := fun j => congrFun hφ j
      refine chartSecond_eq_zero b b' hab v u (P := fun c => ρ c = 0) hk
        (h12 φ φ.2 (fun c hc => ?_) (fun j c hc => ?_))
      · rw [eq_evalInt (hY 0) φ hc]
        exact h0 0
      · rw [eq_evalInt (hY j.succ) φ hc]
        exact h0 j.succ)
  refine ⟨W, fun t => ?_⟩
  have hE : ∀ j, evalVec ρ Y hY (b t) j = M t j := by
    refine Fin.cases ?_ fun j => ?_
    · obtain ⟨c, hc, hcM⟩ := hM0 t
      rw [hEval, ← eq_evalInt (hY 0) (b t) hc, hcM]
    · obtain ⟨c, hc, hcM⟩ := hMs t j
      rw [hEval, ← eq_evalInt (hY j.succ) (b t) hc, hcM]
  have h1 := hW (b t)
  simp only [hE] at h1
  rw [h1]
  show excChartMap b' a v u (graphSecondForm (b.equivFun (b t))) = _
  have h2 : b.equivFun (b t) = Pi.single t 1 := by
    funext s
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    simp [eq_comm]
  rw [h2, graphSecondForm_single]

theorem dualStackedExcChart : GroundTheory.Heights₂.Heights.DualStackedExcChart.Statement :=
  DualStackedExcChart.proof chartForms

end

end GlobalTheory.CompanionTheory.Ar.Giv
