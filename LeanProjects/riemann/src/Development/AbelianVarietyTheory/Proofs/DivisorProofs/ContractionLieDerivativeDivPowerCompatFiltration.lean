import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDividedPowerFiltrationSuccLeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem ctr_algebraMap' (v : Derivation R B B) (b : B) : ctr v (algebraMap B (DR R B) b) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ b

theorem ctr_ι' (v : Derivation R B B) (ω : Ω[B⁄R]) :
    ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) :=
  CliffordAlgebra.contractLeft_ι _ _ ω

theorem ctr_mul' (v : Derivation R B B) (x y : DR R B) :
    ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indDR generalizing y with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap', zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | hd b =>
    rw [ctr_ι', sgn_ι]
    rw [show ctr v (ι1 (D R B b) * y) = _ from CliffordAlgebra.contractLeft_ι_mul _ _ _]
    rw [Algebra.smul_def, neg_mul, sub_eq_add_neg]
    rfl
  | hm x z hx hz =>
    rw [mul_assoc, hx, hz, hx, map_mul]
    simp only [mul_add, add_mul, mul_assoc]
    abel
  | ha x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, map_add, add_mul, add_mul]
    abel

theorem ctr_mem_of_span (v : Derivation R B B) {S : Set (DR R B)} {T : Ideal (DR R B)}
    (hST : Ideal.span S ≤ T) (hS : ∀ s ∈ S, ctr v s ∈ T) : ∀ x ∈ Ideal.span S, ctr v x ∈ T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, ctr_mul']
    exact add_mem (Ideal.mul_mem_left _ _ (hST hx))
      (Ideal.mul_mem_left _ _ ih)

end GlobalTheory.CtrFil

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)
  (v : Derivation R B B)

theorem lie_apply' (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem ctr_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : ctr v x ∈ rel R δ := by
  refine ctr_mem_of_span v le_rfl ?_ x hx
  rintro _ ⟨n, a, ha, rfl⟩
  rw [ctr_ι', map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, hv n a ha, sub_self, map_zero]
  exact zero_mem _

theorem lie_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : lie v x ∈ rel R δ := by
  rw [lie_apply']
  exact add_mem (dDR_mem_rel R δ (ctr_mem_rel δ v hv hx)) (ctr_mem_rel δ v hv (dDR_mem_rel R δ hx))

theorem fil_succ_le' (n : ℕ) : fil δ (n + 1) ≤ fil δ n :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem filDR_succ_le' (n : ℕ) : filDR R δ (n + 1) ≤ filDR R δ n :=
  sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_succ_le' δ n))) _

theorem rel_le_filDR' (n : ℕ) : rel R δ ≤ filDR R δ n := le_sup_right

theorem span_le_filDR' (n : ℕ) : Ideal.span (algebraMap B (DR R B) '' fil δ n) ≤ filDR R δ n := le_sup_left

theorem ctr_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ n) : ctr v x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine add_mem (ctr_mem_of_span v (span_le_filDR' δ n) ?_ y hy) (rel_le_filDR' δ n (ctr_mem_rel δ v hv hz))
  rintro _ ⟨b, _, rfl⟩
  rw [ctr_algebraMap']
  exact zero_mem _

theorem ι_mem_filDR (n : ℕ) {ω : Ω[B⁄R]} (hω : ω ∈ fil δ n • (⊤ : Submodule B Ω[B⁄R]) ⊔ N1 R δ) :
    ι1 ω ∈ filDR R δ n := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hω
  rw [map_add]
  refine add_mem ?_ (rel_le_filDR' δ n hw)
  refine span_le_filDR' δ n ?_
  refine Submodule.smul_induction_on hu (fun c hc ω _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul, Algebra.smul_def, Algebra.commutes]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c, hc, rfl⟩)
  · rw [map_add]; exact add_mem hx hy

theorem dDR_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : dDR R B x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine add_mem ?_ (rel_le_filDR' δ n (dDR_mem_rel R δ hz))
  clear hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    rw [dDR_algebraMap]
    refine ι_mem_filDR δ n (GlobalTheory.T.derivation_dividedPowerFiltration_succ_le R B Ω[B⁄R] J δ (D R B) (N1 R δ) ?_ n b hb)
    intro m a ha
    exact Ideal.subset_span ⟨m, a, ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, dDR_mul]
    refine add_mem (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_left _ _ ?_)
    exact filDR_succ_le' δ n (span_le_filDR' δ (n + 1) hx)

theorem lie_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : lie v x ∈ filDR R δ n := by
  rw [lie_apply']
  exact add_mem (dDR_mem_filDR δ v hv n (ctr_mem_filDR δ v hv (n + 1) hx))
    (ctr_mem_filDR δ v hv n (dDR_mem_filDR δ v hv n hx))

end GlobalTheory.CtrFil

open GlobalTheory.CtrFil in

theorem GlobalTheory.PDForm.ctr_lie_rel_filDR : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) →
    ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B]
    [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B),
    (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧
    (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n :=
  ⟨fun _ _ _ _ _ _ δ v hv _ hx ↦ ⟨ctr_mem_rel δ v hv hx, lie_mem_rel δ v hv hx⟩,
    fun _ _ _ _ _ _ δ v hv n ↦ ⟨fun _ hx ↦ ctr_mem_filDR δ v hv n hx, fun _ hx ↦ dDR_mem_filDR δ v hv n hx,
      fun _ hx ↦ lie_mem_filDR δ v hv n hx⟩⟩
