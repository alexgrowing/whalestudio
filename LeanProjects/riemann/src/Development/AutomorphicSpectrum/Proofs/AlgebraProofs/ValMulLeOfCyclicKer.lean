import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBaseStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinColengthOfHasLen
import ReciprocityTheory.DualLattices.HasLenCokerDet
import ReciprocityTheory.DualLattices.MemAugIdeal
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Num.PtInj

open Matrix in

theorem val_mul_le_of_cyclic_ker {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {B D : Type} [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (π : B →ₗ[R] D) (a : B) (hs : Function.Surjective π)
    (hk : ∀ b, π b = 0 → ∃ r : R, b = r • a) {x y : NNReal} (hB : HasLen v R B x)
    (hD : HasLen v R D y) (k : R) (hka : k • a = 0) : v (algebraMap R C k) * y ≤ x := by
  obtain ⟨m, d, ⟨e⟩, rfl⟩ := hD
  let ε : Fin m → D := fun j => e.symm (Pi.single j 1)
  choose b hb using fun j => hs (ε j)
  have hε : ∀ j, d j • ε j = 0 := by
    intro j
    have : d j • (Pi.single j 1 : (i : Fin m) → R ⧸ Ideal.span {d i}) = 0 := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      · simp [Pi.single_eq_of_ne hij]
    simp only [ε, ← map_smul, this, map_zero]
  have ht : ∀ j, ∃ t : R, d j • b j = t • a := fun j => hk _ (by rw [map_smul, hb, hε])
  choose t ht using ht
  let q : (Unit ⊕ Fin m → R) →ₗ[R] B := Fintype.linearCombination R (Sum.elim (fun _ => a) b)
  have hq : ∀ u, q u = u (Sum.inl ()) • a + ∑ j, u (Sum.inr j) • b j := by
    intro u
    simp [q, Fintype.linearCombination_apply, Fintype.sum_sum_type]
  have hqs : Function.Surjective q := by
    intro z
    have hz : ∃ r : Fin m → R, π z = ∑ j, r j • ε j := by
      refine ⟨fun j => Quotient.out (e (π z) j), e.injective ?_⟩
      funext i
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
      · simp only [ε, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same,
          Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out _).symm
      · intro l _ hl
        simp [ε, Pi.single_eq_of_ne (Ne.symm hl)]
      · intro h; exact absurd (Finset.mem_univ i) h
    obtain ⟨r, hr⟩ := hz
    obtain ⟨r0, h0⟩ := hk (z - ∑ j, r j • b j) (by simp [map_sub, map_sum, hb, hr])
    refine ⟨Sum.elim (fun _ => r0) r, ?_⟩
    rw [hq]
    simp only [Sum.elim_inl, Sum.elim_inr, ← h0]
    abel
  let X : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) R :=
    Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => k) (Matrix.of fun (_ : Unit) j => - t j) 0
      (Matrix.diagonal d)
  have hdet : X.det = k * ∏ j, d j := by
    simp [X, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  have hqX : ∀ u, q (X *ᵥ u) = 0 := by
    intro u
    rw [hq]
    have h1 : (X *ᵥ u) (Sum.inl ()) = k * u (Sum.inl ()) + ∑ j, - t j * u (Sum.inr j) := by
      simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have h2 : ∀ j, (X *ᵥ u) (Sum.inr j) = d j * u (Sum.inr j) := by
      intro j
      simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply]
    simp only [h1, h2, add_smul, Finset.sum_smul, mul_comm k, mul_smul, hka, smul_zero, zero_add]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_comm (d j), ht, smul_comm (u (Sum.inr j)) (t j), neg_smul]
    exact neg_add_cancel _
  have hle : LinearMap.range X.mulVecLin ≤ LinearMap.ker q := by
    rintro _ ⟨u, rfl⟩
    exact hqX u
  have hlen := hasLen_coker_det' v R hv (Unit ⊕ Fin m) X
  have := GlobalTheory.AvChartCompare.hasLen_le_of_surjective hv
    ((LinearMap.range X.mulVecLin).liftQ q hle)
    (by
      intro z
      obtain ⟨u, rfl⟩ := hqs z
      exact ⟨Submodule.Quotient.mk u, by simp⟩) hlen hB
  rw [hdet, map_mul, map_mul, map_prod, map_prod] at this
  exact this

section Proj

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
  [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem proj_eq_sum (χ : MulChar F R) {u : R} (hu : algebraMap R C u = (Fintype.card Fˣ : C)⁻¹)
    (g : N → C) :
    proj χ g = ∑ a : Fˣ, fun x => algebraMap R C (u * χ⁻¹ (a : F)) * g ((a : F) • x) := by
  funext x
  simp only [proj, Finset.sum_apply, Finset.mul_sum, map_mul, hu, mul_assoc]

theorem proj_mem (T : AddSubgroup (N → C)) (χ : MulChar F R) {u : R}
    (hu : algebraMap R C u = (Fintype.card Fˣ : C)⁻¹)
    (hR : ∀ r : R, ∀ g ∈ T, (fun x => algebraMap R C r * g x) ∈ T)
    (hF : ∀ a : F, ∀ g ∈ T, (fun x => g (a • x)) ∈ T) {g : N → C} (hg : g ∈ T) : proj χ g ∈ T := by
  rw [proj_eq_sum χ hu]
  exact T.sum_mem fun a _ => hR _ _ (hF _ _ hg)

theorem proj_sub (χ : MulChar F R) (g h : N → C) (x : N) :
    proj χ (g - h) x = proj χ g x - proj χ h x := by
  simp only [proj, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inv_mul_self (χ : MulChar F R) (a : Fˣ) : χ⁻¹ (a : F) * χ (a : F) = 1 := by
  rw [MulChar.inv_apply', ← map_mul, inv_mul_cancel₀ a.ne_zero, map_one]

theorem proj_eig (χ : MulChar F R) {g : N → C} (h0 : g 0 = 0) (a : F) (x : N) :
    proj χ g (a • x) = algebraMap R C (χ a) * proj χ g x := by
  by_cases ha : a = 0
  · subst ha
    have : χ 0 = 0 := χ.map_nonunit not_isUnit_zero
    simp [proj, this, h0]
  · let a' : Fˣ := Units.mk0 a ha
    have e : ∑ b : Fˣ, algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • a • x) =
        algebraMap R C (χ a) * ∑ b : Fˣ, algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight a')
        (fun b : Fˣ => algebraMap R C (χ a) * (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      have h1 : χ⁻¹ (b : F) = χ a * χ⁻¹ ((b * a' : Fˣ) : F) := by
        have h2 := inv_mul_self χ a'
        simp only [a', Units.val_mk0] at h2
        simp only [Units.val_mul, a', Units.val_mk0, map_mul]
        calc χ⁻¹ (b : F) = χ⁻¹ (b : F) * (χ⁻¹ a * χ a) := by rw [h2, mul_one]
          _ = _ := by ring
      simp only [Equiv.coe_mulRight, Units.val_mul, a', Units.val_mk0, mul_smul]
      rw [h1, map_mul, mul_assoc]
      simp only [Units.val_mul, a', Units.val_mk0]
    simp only [proj, e]
    ring

theorem proj_on (χ : MulChar F R) (hc : (Fintype.card Fˣ : C) ≠ 0) (S : Set N) {g : N → C}
    (hg : ∀ (a : Fˣ), ∀ x ∈ S, g ((a : F) • x) = algebraMap R C (χ a) * g x) {x : N} (hx : x ∈ S) :
    proj χ g x = g x := by
  have : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) = g x := by
    intro a
    rw [hg a x hx, ← mul_assoc, ← map_mul, inv_mul_self, map_one, one_mul]
  simp only [proj, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Proj

section Sq

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem sq_lift {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (ψ : Y → X) (h0 : ψ 0 = 0)
    (M : Submodule R (X → C)) {f : Y → C}
    (hf : f ∈ sqIdeal (augIdeal (M.map (LinearMap.funLeft R C ψ)))) :
    ∃ g ∈ sqIdeal (augIdeal M), LinearMap.funLeft R C ψ g = f := by
  have hlift : ∀ f ∈ augIdeal (M.map (LinearMap.funLeft R C ψ)),
      ∃ g ∈ augIdeal M, LinearMap.funLeft R C ψ g = f := by
    rintro f ⟨⟨g, hg, rfl⟩, hf0⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    have : g (ψ 0) = 0 := hf0
    rw [h0] at this
    exact this
  induction hf using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨f, hf, f', hf', rfl⟩ := hh
    obtain ⟨g, hg, rfl⟩ := hlift f hf
    obtain ⟨g', hg', rfl⟩ := hlift f' hf'
    exact ⟨g * g', Submodule.subset_span ⟨g, hg, g', hg', rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨g', hg', rfl⟩ := hb
    exact ⟨g + g', Submodule.add_mem _ hg hg', map_add _ _ _⟩
  | smul r a _ ha =>
    obtain ⟨g, hg, rfl⟩ := ha
    exact ⟨r • g, Submodule.smul_mem _ r hg, map_smul _ _ _⟩

theorem sq_res {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (ψ : Y → X) (h0 : ψ 0 = 0)
    (M : Submodule R (X → C)) {g : X → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    LinearMap.funLeft R C ψ g ∈ sqIdeal (augIdeal (M.map (LinearMap.funLeft R C ψ))) := by
  refine PullbackHopfOrder.sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) ?_ hg
  rintro f ⟨hf, hf0⟩
  refine ⟨⟨f, hf, rfl⟩, ?_⟩
  show f (ψ 0) = 0
  rw [h0]
  exact hf0

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

theorem sq_stable {M : Submodule R (N → C)} (hF : FStable F M) (a : F) {g : N → C}
    (hg : g ∈ sqIdeal (augIdeal M)) : (fun x => g (a • x)) ∈ sqIdeal (augIdeal M) := by
  refine PullbackHopfOrder.sqIdeal_le (LinearMap.funLeft R C fun x : N => a • x) (fun _ _ => rfl) ?_ hg
  rintro f ⟨hf, hf0⟩
  refine ⟨hF a f hf, ?_⟩
  show f (a • 0) = 0
  rw [smul_zero]
  exact hf0

end Sq

section Step

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem smul_fun (r : R) (g : N → C) : (fun x => algebraMap R C r * g x) = r • g := by
  funext x
  simp [Algebra.smul_def]

theorem sq_le_aug {M : Submodule R (N → C)} (hmul : ∀ f g, f ∈ M → g ∈ M → f * g ∈ M) :
    sqIdeal (augIdeal M) ≤ augIdeal M := by
  refine Submodule.span_le.2 ?_
  rintro h ⟨f, hf, f', hf', rfl⟩
  obtain ⟨h1, h2⟩ := PullbackHopfOrder.mem_augIdeal.1 hf
  obtain ⟨h3, _⟩ := PullbackHopfOrder.mem_augIdeal.1 hf'
  exact PullbackHopfOrder.mem_augIdeal.2 ⟨hmul _ _ h1 h3, by simp [h2]⟩

theorem eig_zero {M : Submodule R (N → C)} {χ : MulChar F R} {h : N → C} (hh : h ∈ eig M χ) :
    h 0 = 0 := by
  have := hh.2 0 0
  have h0 : χ 0 = 0 := χ.map_nonunit not_isUnit_zero
  simpa [h0] using this

theorem step_bound (hv : v.Integers R) {M : Submodule R (N → C)} (hF : FStable F M)
    (hmul : ∀ f g, f ∈ M → g ∈ M → f * g ∈ M) (χ : MulChar F R) {u : R}
    (hu : algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (hc : (Fintype.card Fˣ : C) ≠ 0)
    {K₀ K₁ : Submodule F N} (h01 : K₀ ≤ K₁) (a₁ : K₁ → C)
    (ha₁ : a₁ ∈ eig (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))) χ)
    (hker : ∀ g ∈ augIdeal M, (∀ x ∈ K₀, g x = 0) →
      ∃ r : R, ∃ g' ∈ sqIdeal (augIdeal M), ∀ x : K₁,
        proj χ g (x : N) = algebraMap R C r * a₁ x + g' (x : N))
    {x y : NNReal}
    (hB : HasLen v R (OmType (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))) χ) x)
    (hD : HasLen v R (OmType (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))) χ) y)
    (k : R)
    (hk : k • a₁ ∈ sqIdeal (augIdeal (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))))) :
    v (algebraMap R C k) * y ≤ x := by
  have hMR : ∀ r : R, ∀ g ∈ M.toAddSubgroup, (fun x => algebraMap R C r * g x) ∈ M.toAddSubgroup := by
    intro r g hg
    rw [smul_fun]
    exact M.smul_mem r hg
  have hSR : ∀ r : R, ∀ g ∈ (sqIdeal (augIdeal M)).toAddSubgroup,
      (fun x => algebraMap R C r * g x) ∈ (sqIdeal (augIdeal M)).toAddSubgroup := by
    intro r g hg
    rw [smul_fun]
    exact Submodule.smul_mem _ r hg
  let ι : K₀ → K₁ := Submodule.inclusion h01
  let ρ : (K₁ → C) →ₗ[R] (K₀ → C) := LinearMap.funLeft R C ι
  have hρ : ∀ h ∈ eig (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))) χ,
      ρ h ∈ eig (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))) χ := by
    rintro h ⟨⟨g, hg, rfl⟩, he⟩
    exact ⟨⟨g, hg, rfl⟩, fun a x => he a (ι x)⟩
  let E := ρ.restrict hρ
  have hS : ((sqIdeal (augIdeal (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))))).comap
        (eig (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))) χ).subtype) ≤
      ((sqIdeal (augIdeal (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))))).comap
        (eig (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))) χ).subtype).comap E := by
    intro z hz
    refine PullbackHopfOrder.sqIdeal_le ρ (fun _ _ => rfl) ?_ hz
    rintro f hf
    obtain ⟨⟨g, hg, rfl⟩, hf0⟩ := PullbackHopfOrder.mem_augIdeal.1 hf
    exact PullbackHopfOrder.mem_augIdeal.2 ⟨⟨g, hg, rfl⟩, hf0⟩
  let π := Submodule.mapQ _ _ E hS
  refine val_mul_le_of_cyclic_ker hv π (Submodule.Quotient.mk ⟨a₁, ha₁⟩) ?_ ?_ hB hD k ?_
  · intro z
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have h0 := eig_zero hh
    obtain ⟨⟨g, hg, rfl⟩, he⟩ := hh
    have g0 : g 0 = 0 := h0
    have hg' : proj χ g ∈ M := proj_mem M.toAddSubgroup χ hu hMR hF hg
    have hmem : LinearMap.funLeft R C (Subtype.val : K₁ → N) (proj χ g) ∈
        eig (M.map (LinearMap.funLeft R C (Subtype.val : K₁ → N))) χ :=
      ⟨⟨_, hg', rfl⟩, fun a x => proj_eig χ g0 a x⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
    refine congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext ?_)
    funext x
    exact proj_on χ hc (K₀ : Set N) (fun a x hx => he a ⟨x, hx⟩) x.2
  · intro b hb
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have hb2 : E ⟨h, hh⟩ ∈ (sqIdeal (augIdeal
        (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))))).comap
        (eig (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N))) χ).subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 hb
    have hb' : ρ h ∈ sqIdeal (augIdeal (M.map (LinearMap.funLeft R C (Subtype.val : K₀ → N)))) :=
      hb2
    obtain ⟨g2, hg2, e2⟩ := sq_lift (Subtype.val : K₀ → N) rfl M hb'
    have h0 := eig_zero hh
    obtain ⟨⟨g, hg, rfl⟩, he⟩ := hh
    have g0 : g 0 = 0 := h0
    obtain ⟨hg2M, hg20⟩ := PullbackHopfOrder.mem_augIdeal.1 (sq_le_aug hmul hg2)
    obtain ⟨r, g', hg', hr⟩ := hker (g - g2)
      (PullbackHopfOrder.mem_augIdeal.2 ⟨M.sub_mem hg hg2M, by simp [g0, hg20]⟩) (fun x hx => by
        have := congrFun e2 ⟨x, hx⟩
        have h3 : g2 x = g x := this
        simp [h3])
    refine ⟨r, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    have hp2 : proj χ g2 ∈ sqIdeal (augIdeal M) :=
      proj_mem (sqIdeal (augIdeal M)).toAddSubgroup χ hu hSR (fun a g hg => sq_stable hF a hg) hg2
    have e3 : LinearMap.funLeft R C (Subtype.val : K₁ → N) g - r • a₁ =
        LinearMap.funLeft R C (Subtype.val : K₁ → N) (g' + proj χ g2) := by
      funext x
      have h4 := hr x
      rw [proj_sub, proj_on χ hc (K₁ : Set N) (fun a x hx => he a ⟨x, hx⟩) x.2] at h4
      have h7 : (r • a₁) x = algebraMap R C r * a₁ x := by
        rw [Pi.smul_apply, Algebra.smul_def]
      show g x - (r • a₁) x = g' x + proj χ g2 x
      rw [h7]
      linear_combination h4
    refine Submodule.mem_comap.2 ?_
    show LinearMap.funLeft R C (Subtype.val : K₁ → N) g - r • a₁ ∈ sqIdeal _
    rw [e3]
    exact sq_res _ rfl M (Submodule.add_mem _ hg' hp2)
  · rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hk

end Step

section Flag

variable {F : Type} [Field F] {n : ℕ}

theorem mem_flagSub {j : ℕ} {x : Fin n → F} :
    x ∈ flagSub (Pi.basisFun F (Fin n)) j ↔ ∀ k : Fin n, j ≤ (k : ℕ) → x k = 0 := by
  rw [flagSub, Module.Basis.mem_span_image]
  constructor
  · intro h k hk
    by_contra hx
    have hm : k ∈ ((Pi.basisFun F (Fin n)).repr x).support := by
      simpa using hx
    have := h hm
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro h k hk
    have hk' : x k ≠ 0 := by simpa using hk
    by_contra hlt
    exact hk' (h k (not_lt.1 hlt))

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem mem_xIdeal_res (M : Submodule R ((Fin n → F) → C)) (i : Fin n) (σ₁ : MulChar F R) (t : R) :
    t ∈ xIdeal (stepOrderRes M (flagSub (Pi.basisFun F (Fin n)) i) (Pi.basisFun F (Fin n) i)) σ₁ ↔
      ∃ g ∈ M, ∀ x ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1),
        g x = algebraMap R C t * algebraMap R C (σ₁ (x i)) := by
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun x hx => ?_⟩
    have hk : x - x i • Pi.basisFun F (Fin n) i ∈ flagSub (Pi.basisFun F (Fin n)) i := by
      refine mem_flagSub.2 fun k hk => ?_
      by_cases hki : k = i
      · subst hki
        simp
      · have h1 : (i : ℕ) + 1 ≤ k := by
          have : (i : ℕ) ≠ k := fun h => hki (Fin.ext h.symm)
          omega
        simp [mem_flagSub.1 hx k h1, Pi.single_eq_of_ne hki]
    have := h (x i) _ hk
    rw [add_sub_cancel] at this
    simpa [Algebra.smul_def] using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun a k hk => ?_⟩
    have hx : a • Pi.basisFun F (Fin n) i + k ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) := by
      refine mem_flagSub.2 fun l hl => ?_
      have h1 : l ≠ i := fun h => by subst h; omega
      have h2 := mem_flagSub.1 hk l (by omega)
      simp [h2, Pi.single_eq_of_ne h1]
    have hki := mem_flagSub.1 hk i le_rfl
    rw [h _ hx]
    simp [hki, Algebra.smul_def]

theorem mem_vanSub {j : ℕ} {h : (Fin n → F) → C} :
    h ∈ vanSub C F n j ↔ ∀ x ∈ flagSub (Pi.basisFun F (Fin n)) j, h x = 0 := by
  simp only [vanSub, Submodule.mem_pi, Submodule.mem_bot, mem_flagSub, Set.mem_setOf_eq]

variable {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s)

theorem mem_xId (χ₁ : F → C) (i : Fin n) (t : C) :
    t ∈ D.xId χ₁ i ↔ ∃ g ∈ D.M, ∀ x ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1),
      g x = t * χ₁ (x i) := by
  simp only [LieLatticeData.xId, AddSubgroup.mem_comap]
  constructor
  · intro h
    obtain ⟨g, hg, h', hh, e⟩ := AddSubgroup.mem_sup.1 h
    refine ⟨g, hg, fun x hx => ?_⟩
    have h1 := congrFun e x
    have h2 := mem_vanSub.1 hh x hx
    simpa [h2, LinearMap.toSpanSingleton_apply] using h1
  · rintro ⟨g, hg, h⟩
    refine AddSubgroup.mem_sup.2 ⟨g, hg, (t • fun x => χ₁ (x i)) - g, ?_, by simp⟩
    refine mem_vanSub.2 fun x hx => ?_
    simp [h x hx]

theorem mem_stepGraph (τ : Sg) (χ₁ : F → C) (i : Fin n) (t : C) (m : Fin (r τ) → C) :
    (t, m) ∈ D.stepGraph τ χ₁ i ↔ ∃ g, (g, m) ∈ D.Th τ ∧
      ∀ x ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1), g x = t * χ₁ (x i) := by
  simp only [LieLatticeData.stepGraph, AddSubgroup.mem_comap]
  constructor
  · intro h
    obtain ⟨⟨g, m'⟩, hg, ⟨h', m''⟩, hh, e⟩ := AddSubgroup.mem_sup.1 h
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_prod.1 hh
    have h2' : m'' = 0 := h2
    subst h2'
    have e1 : g + h' = t • fun x => χ₁ (x i) := congrArg Prod.fst e
    have e2 : m' + 0 = m := congrArg Prod.snd e
    rw [add_zero] at e2
    subst e2
    refine ⟨g, hg, fun x hx => ?_⟩
    have h3 := congrFun e1 x
    have h4 : h' x = 0 := mem_vanSub.1 h1 x hx
    simpa [h4] using h3
  · rintro ⟨g, hg, h⟩
    refine AddSubgroup.mem_sup.2 ⟨(g, m), hg, ((t • fun x => χ₁ (x i)) - g, 0), ?_, ?_⟩
    · refine AddSubgroup.mem_prod.2 ⟨mem_vanSub.2 fun x hx => ?_, AddSubgroup.zero_mem _⟩
      simp [h x hx]
    · ext <;> simp [LinearMap.toSpanSingleton_apply]

end Flag

section Main

theorem exists_unit {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    (v : Valuation C NNReal) (hRC : ∀ c, c ∈ RC ↔ v c ≤ 1) (p : ℕ) (hp1 : v (p : C) < 1)
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] :
    ∃ u : RC, algebraMap RC C u = (Fintype.card Fˣ : C)⁻¹ ∧ (Fintype.card Fˣ : C) ≠ 0 := by
  have hnat : ∀ m : ℕ, v (m : C) ≤ 1 := fun m => (hRC _).1 (natCast_mem RC m)
  have hc : Fintype.card Fˣ + 1 = Fintype.card F := by
    rw [Fintype.card_units]
    exact Nat.sub_add_cancel Fintype.card_pos
  have hcC : (Fintype.card Fˣ : C) + 1 = (Fintype.card F : C) := by exact_mod_cast congrArg (Nat.cast : ℕ → C) hc
  obtain ⟨m, hm⟩ : p ∣ Fintype.card F := (CharP.cast_eq_zero_iff F p _).1 (Nat.cast_card_eq_zero F)
  have hq : v (Fintype.card F : C) < 1 := by
    rw [hm, Nat.cast_mul, map_mul]
    calc v (p : C) * v (m : C) ≤ v (p : C) * 1 := by gcongr; exact hnat m
      _ < 1 := by rwa [mul_one]
  have h1 : v (Fintype.card Fˣ : C) = 1 := by
    refine le_antisymm (hnat _) (not_lt.1 fun hlt => ?_)
    have e : (1 : C) = (Fintype.card F : C) - (Fintype.card Fˣ : C) := by rw [← hcC]; ring
    have h2 := v.map_sub (Fintype.card F : C) (Fintype.card Fˣ : C)
    rw [← e, map_one] at h2
    exact absurd (lt_of_le_of_lt h2 (max_lt hq hlt)) (lt_irrefl _)
  have hne : (Fintype.card Fˣ : C) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  exact ⟨⟨(Fintype.card Fˣ : C)⁻¹, (hRC _).2 (by rw [map_inv₀, h1, inv_one])⟩, rfl, hne⟩

theorem xId_iff {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C)
    {F : Type} [Field F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s)
    (hle : ∀ g ∈ D.M, ∀ x, g x ∈ RC) (M : Submodule RC ((Fin n → F) → C))
    (hMD : ∀ g, g ∈ D.M ↔ g ∈ M) (i : Fin n) (σ₁ : MulChar F RC) (χ₁ : F → C)
    (hχ₁ : ∀ a, χ₁ a = (σ₁ a : RC)) (c₁ : RC)
    (hX : xIdeal (stepOrderRes M (flagSub (Pi.basisFun F (Fin n)) i)
      (Pi.basisFun F (Fin n) i)) σ₁ = Ideal.span {c₁}) (t : C) :
    t ∈ D.xId χ₁ i ↔ ∃ r : RC, t = r * c₁ := by
  rw [mem_xId]
  constructor
  · rintro ⟨g, hg, h⟩
    have hi : Pi.basisFun F (Fin n) i ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) := by
      refine mem_flagSub.2 fun k hk => ?_
      have : k ≠ i := fun e => by subst e; omega
      simp [Pi.single_eq_of_ne this]
    have h1 := h _ hi
    have h2 : χ₁ 1 = 1 := by rw [hχ₁]; simp
    simp only [Pi.basisFun_apply, Pi.single_eq_same, h2, mul_one] at h1
    have ht : t ∈ RC := by
      rw [← h1]
      exact hle g hg _
    have h3 : (⟨t, ht⟩ : RC) ∈ Ideal.span {c₁} := by
      rw [← hX, mem_xIdeal_res]
      refine ⟨g, (hMD g).1 hg, fun x hx => ?_⟩
      rw [h x hx, hχ₁]
      rfl
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h3
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · rintro ⟨a, rfl⟩
    have h3 : c₁ ∈ xIdeal (stepOrderRes M (flagSub (Pi.basisFun F (Fin n)) i)
        (Pi.basisFun F (Fin n) i)) σ₁ := by
      rw [hX]
      exact Ideal.mem_span_singleton_self _
    obtain ⟨g, hg, h⟩ := (mem_xIdeal_res M i σ₁ c₁).1 h3
    refine ⟨a • g, (hMD _).2 (M.smul_mem a hg), fun x hx => ?_⟩
    have h4 : (a • g) x = (a : C) * g x := rfl
    rw [h4, h x hx, hχ₁]
    simp only [mul_assoc]
    rfl

theorem kernel_stepGraph : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan RC p (D.xId (χ τ) i) := by
  intro o C _ _ _ _ _ RC v hRC p _ hp1 F _ _ _ _ n Sg r s D w χ φ hB AA hM hFs σ hσ hfl e hχ hφ hTh τ i
  have hpt := GlobalTheory.T.hopf_order_lattice_base RC v hRC p hp1 D w χ φ hB AA hM hFs σ hσ hfl e hχ hφ hTh (φ τ) i
  obtain ⟨c, δ, hc, -, hlen⟩ := hfl
  have hv : v.Integers RC :=
    ⟨Subtype.val_injective, fun x => (hRC _).1 x.2, fun {c} hc => ⟨⟨c, (hRC c).2 hc⟩, rfl⟩⟩
  obtain ⟨u, hu, hcard⟩ := exists_unit RC v hRC p hp1 F
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hMD : ∀ g, g ∈ D.M ↔ g ∈ AA.carrier := by
    intro g
    rw [← hM]
    rfl
  have hle : ∀ g ∈ D.M, ∀ x, g x ∈ RC := fun g hg x =>
    (AddSubgroup.mem_pi _).1 (hB.M_le hg) x trivial
  set s₀ := e τ with hs₀
  set σ' := σ ^ p ^ (s₀ + 1) with hσ'
  have hχ' : ∀ a, χ (φ τ) a = ((σ' a : RC) : C) := fun a => by rw [hχ (φ τ) a, hφ τ]
  have hχ0 : ∀ a, χ τ a = (((σ ^ p ^ s₀) a : RC) : C) := hχ τ
  have hpow : ∀ a, χ τ a ^ p = χ (φ τ) a := by
    intro a
    rw [hχ0, hχ', hσ', pow_succ, pow_mul, MulChar.pow_apply' _ hp0]
    rfl
  obtain ⟨hH1, hH2, hH3⟩ := hTh (φ τ)
  rw [hφ τ] at hH3
  obtain ⟨hth1, -, -⟩ := hB.th (φ τ)
  have hTproj : ∀ g, (g, (0 : Fin (r (φ τ)) → C)) ∈ D.Th (φ τ) →
      (proj σ' g, (0 : Fin (r (φ τ)) → C)) ∈ D.Th (φ τ) := by
    intro g hg
    refine proj_mem ((D.Th (φ τ)).comap (AddMonoidHom.inl _ _)) σ' hu ?_ ?_ hg
    · intro a g hg
      have := ((hB.stable (φ τ) a a.2).2.2) (g, 0) hg
      have e1 : (a : C) • (g, (0 : Fin (r (φ τ)) → C)) =
          ((fun x => algebraMap RC C a * g x), 0) := by
        ext <;> simp [Algebra.smul_def]
      rw [e1] at this
      exact this
    · intro a g hg
      have := hH2 a g 0 hg
      rw [smul_zero] at this
      exact this
  have hMproj : ∀ g ∈ AA.carrier, proj σ' g ∈ AA.carrier := fun g hg =>
    proj_mem AA.carrier.toAddSubgroup σ' hu (fun a g hg => by
      rw [smul_fun]; exact AA.carrier.smul_mem a hg) hFs hg
  have hxid := fun (s' : ℕ) (σ₁ : MulChar F RC) (χ₁ : F → C) (h₁ : ∀ a, χ₁ a = (σ₁ a : RC))
    (h₂ : σ₁ = σ ^ p ^ s') (t : C) =>
    xId_iff RC D hle AA.carrier hMD i σ₁ χ₁ h₁ (c i s') (by rw [h₂]; exact (hc i s').2.2.1) t
  have hxid' := hxid (s₀ + 1) σ' (χ (φ τ)) hχ' rfl
  have hxid₀ := hxid s₀ (σ ^ p ^ s₀) (χ τ) hχ0 rfl
  apply le_antisymm
  · intro t ht
    have ht' : (t, (0 : Fin (r (φ τ)) → C)) ∈ D.stepGraph (φ τ) (χ (φ τ)) i := ht
    obtain ⟨g, hgTh, hgx⟩ := (mem_stepGraph D _ _ _ _ _).1 ht'
    obtain ⟨hgM, hg0⟩ := (hth1 g).1 ⟨0, hgTh⟩
    obtain ⟨k, rfl⟩ := (hxid' t).1 ((mem_xId D _ _ _).2 ⟨g, hgM, hgx⟩)
    set c' := c i (s₀ + 1) with hc'
    let a₁ : flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) → C :=
      fun x => (c' : C) * ((σ' ((x : Fin n → F) i) : RC) : C)
    have hx1 : c' ∈ xIdeal (stepOrderRes AA.carrier (flagSub (Pi.basisFun F (Fin n)) i)
        (Pi.basisFun F (Fin n) i)) σ' := by
      rw [(hc i (s₀ + 1)).2.2.1]
      exact Ideal.mem_span_singleton_self _
    have ha₁ : a₁ ∈ eig (AA.carrier.map (LinearMap.funLeft RC C (Subtype.val :
        flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) → (Fin n → F)))) σ' := by
      obtain ⟨g', hg', h'⟩ := (mem_xIdeal_res AA.carrier i σ' c').1 hx1
      refine ⟨⟨g', hg', funext fun x => h' x.1 x.2⟩, fun a x => ?_⟩
      show (c' : C) * ((σ' (a * (x : Fin n → F) i) : RC) : C) = _
      rw [map_mul]
      show _ = ((σ' a : RC) : C) * ((c' : C) * ((σ' ((x : Fin n → F) i) : RC) : C))
      push_cast
      ring
    have h01 : flagSub (Pi.basisFun F (Fin n)) i ≤ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) := by
      intro x hx
      exact mem_flagSub.2 fun l hl => mem_flagSub.1 hx l (by omega)
    have hprojS : ∀ g, (g, (0 : Fin (r (φ τ)) → C)) ∈ D.Th (φ τ) →
        proj σ' g ∈ sqIdeal (augIdeal AA.carrier) := by
      intro g hg
      obtain ⟨hgM, hg0⟩ := (hth1 g).1 ⟨0, hg⟩
      exact hH3 _ ⟨hMproj g ((hMD g).1 hgM), proj_eig σ' hg0⟩ (hTproj g hg)
    have hker : ∀ g ∈ augIdeal AA.carrier, (∀ x ∈ flagSub (Pi.basisFun F (Fin n)) i, g x = 0) →
        ∃ r : RC, ∃ g' ∈ sqIdeal (augIdeal AA.carrier),
          ∀ x : flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1),
            proj σ' g (x : Fin n → F) = algebraMap RC C r * a₁ x + g' (x : Fin n → F) := by
      intro g hg hgv
      obtain ⟨hgA, hgA0⟩ := PullbackHopfOrder.mem_augIdeal.1 hg
      obtain ⟨m, hm⟩ := (hth1 g).2 ⟨(hMD g).2 hgA, hgA0⟩
      have hmk : m ∈ D.kk (φ τ) i := ⟨(g, m), ⟨hm, mem_vanSub.2 hgv, trivial⟩, rfl⟩
      rw [← hpt] at hmk
      obtain ⟨⟨t, m'⟩, hst, rfl⟩ := hmk
      obtain ⟨g3, hg3, hg3x⟩ := (mem_stepGraph D _ _ _ _ _).1 hst
      obtain ⟨hg3M, hg30⟩ := (hth1 g3).1 ⟨_, hg3⟩
      obtain ⟨r₁, rfl⟩ := (hxid' t).1 ((mem_xId D _ _ _).2 ⟨g3, hg3M, hg3x⟩)
      have hd : (g - g3, (0 : Fin (r (φ τ)) → C)) ∈ D.Th (φ τ) := by
        have := (D.Th (φ τ)).sub_mem hm hg3
        simpa using this
      refine ⟨r₁, proj σ' (g - g3), hprojS _ hd, fun x => ?_⟩
      have e1 : proj σ' g3 (x : Fin n → F) = g3 x := by
        refine proj_on σ' hcard
          (flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) : Set (Fin n → F)) (fun a y hy => ?_) x.2
        have hy' : (a : F) • y ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) :=
          Submodule.smul_mem _ _ hy
        rw [hg3x _ hy', hg3x y hy, hχ', hχ']
        show _ * ((σ' ((a : F) * y i) : RC) : C) = _
        rw [map_mul]
        show _ = ((σ' (a : F) : RC) : C) * _
        push_cast
        ring
      rw [proj_sub, e1, hg3x x.1 x.2, hχ']
      show _ = ((r₁ : C) * ((c' : C) * ((σ' ((x : Fin n → F) i) : RC) : C))) + _
      push_cast
      ring
    have hS₁ : proj σ' g ∈ sqIdeal (augIdeal AA.carrier) := hprojS g hgTh
    have hres : k • a₁ = LinearMap.funLeft RC C (Subtype.val :
        flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) → (Fin n → F)) (proj σ' g) := by
      funext x
      have e1 : proj σ' g (x : Fin n → F) = g x := by
        refine proj_on σ' hcard
          (flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) : Set (Fin n → F)) (fun a y hy => ?_) x.2
        have hy' : (a : F) • y ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) :=
          Submodule.smul_mem _ _ hy
        rw [hgx _ hy', hgx y hy, hχ', hχ']
        show _ * ((σ' ((a : F) * y i) : RC) : C) = _
        rw [map_mul]
        show _ = ((σ' (a : F) : RC) : C) * _
        push_cast
        ring
      show (k : C) * ((c' : C) * ((σ' ((x : Fin n → F) i) : RC) : C)) = proj σ' g (x : Fin n → F)
      rw [e1, hgx x.1 x.2, hχ']
      ring
    have hbound := step_bound hv hFs AA.mul_mem σ' hu hcard h01 a₁ ha₁ hker
      (hlen ((i : ℕ) + 1) s₀) (hlen i s₀) k (by rw [hres]; exact sq_res _ rfl _ hS₁)
    have hδ : ∀ (l : Fin n), δ l s₀ ≠ 0 := by
      intro l h0
      have h1 := (hc l s₀).2.2.2.2.1
      rw [h0, zero_mul] at h1
      exact (hc l s₀).1 (pow_eq_zero_iff hp0 |>.1 h1)
    have hvδ : ∀ l, v (algebraMap RC C (δ l s₀)) ≠ 0 := fun l =>
      (Valuation.ne_zero_iff v).2 (fun h => hδ l (Subtype.ext h))
    have hfilter : Finset.univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1) =
        insert i (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ))) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hfilter, Finset.prod_insert (by simp)] at hbound
    have hY : (∏ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ)),
        v (algebraMap RC C (δ l s₀))) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hvδ l
    have hkle : v (algebraMap RC C k) ≤ v (algebraMap RC C (δ i s₀)) :=
      le_of_mul_le_mul_right hbound (pos_iff_ne_zero.2 hY)
    have hδC : ((δ i s₀ : RC) : C) ≠ 0 := fun h => hδ i (Subtype.ext h)
    have hu' : (k : C) / (δ i s₀ : RC) ∈ RC := by
      refine (hRC _).2 ?_
      rw [map_div₀]
      exact div_le_one_of_le₀ hkle zero_le
    have hcs : ((c i s₀ : RC) : C) ∈ D.xId (χ τ) i := (hxid₀ _).2 ⟨1, by simp⟩
    have hcp : ((c i s₀ : RC) : C) ^ p = (δ i s₀ : RC) * (c' : C) := by
      have := congrArg (Subtype.val) (hc i s₀).2.2.2.2.1
      simpa using this
    refine AddSubgroup.subset_closure ⟨(k : C) / (δ i s₀ : RC), hu', _, ⟨_, hcs, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    rw [hcp]
    field_simp
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨g, hgM, hg⟩ := (mem_xId D _ _ _).1 hy
    have hz : (0 : Fin n → F) ∈ flagSub (Pi.basisFun F (Fin n)) ((i : ℕ) + 1) := Submodule.zero_mem _
    have hχz : χ τ 0 = 0 := by
      rw [hχ0, MulChar.map_nonunit _ not_isUnit_zero]
      rfl
    have hg0 : g 0 = 0 := by
      have := hg 0 hz
      simpa [hχz] using this
    have hgA : g ∈ augIdeal AA.carrier := PullbackHopfOrder.mem_augIdeal.2 ⟨(hMD g).1 hgM, hg0⟩
    have hgpow : ∀ m : ℕ, g ^ (m + 1) ∈ augIdeal AA.carrier := by
      intro m
      induction m with
      | zero => simpa using hgA
      | succ m ih =>
        obtain ⟨h1, h2⟩ := PullbackHopfOrder.mem_augIdeal.1 ih
        rw [pow_succ]
        exact PullbackHopfOrder.mem_augIdeal.2 ⟨AA.mul_mem _ _ h1 ((hMD g).1 hgM), by simp [hg0]⟩
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
    have hS : g ^ (m + 2) ∈ sqIdeal (augIdeal AA.carrier) :=
      Submodule.subset_span ⟨g, hgA, g ^ (m + 1), hgpow m, by rw [pow_succ' g (m + 1)]⟩
    have hS' : (⟨a, ha⟩ : RC) • g ^ (m + 2) ∈ sqIdeal (augIdeal AA.carrier) :=
      Submodule.smul_mem _ _ hS
    refine (mem_stepGraph D _ _ _ _ _).2 ⟨_, hH1 _ hS', fun x hx => ?_⟩
    have e1 : ((⟨a, ha⟩ : RC) • g ^ (m + 2)) x = a * g x ^ (m + 2) := rfl
    rw [e1, hg x hx, ← hpow, mul_pow, smul_eq_mul]
    ring

end Main

end GlobalTheory.CompanionTheory.Ar.Num.PtInj
