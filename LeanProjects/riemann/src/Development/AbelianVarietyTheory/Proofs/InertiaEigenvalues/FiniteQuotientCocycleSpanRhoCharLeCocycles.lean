import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.Cut.Coc

theorem KOG_torsion {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (t : KOG O k) :
    ∃ d : O, d ≠ 0 ∧ d • t = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  choose u hu using hb
  exact ⟨u, funext fun j => hu j⟩

theorem smul_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k : ℕ} (t : KOG O k) :
    Continuous fun a : O => a • t := by
  obtain ⟨d, hd, hdt⟩ := KOG_torsion t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.mp hO).1 n
  have hk : ∀ a ∈ (IsLocalRing.maximalIdeal O ^ n : Ideal O), a • t = 0 := by
    intro a ha
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : c * ϖ ^ n = (c * ((u⁻¹ : Oˣ) : O)) * (u * ϖ ^ n) := by
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, mul_smul, hdt, smul_zero]
  refine continuous_of_continuousAt_zero (LinearMap.toSpanSingleton O (KOG O k) t) ?_
  refine (continuousAt_const (y := (0 : KOG O k))).congr ?_
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
  exact (hk a ha).symm

theorem lin_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k n : ℕ} {X : Type} [Fintype X]
    [DecidableEq X] (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] KOG O k) : Continuous φ := by
  have h : ∀ y : X → Matrix (Fin n) (Fin n) O,
      φ y = ∑ x, ∑ p, ∑ q, y x p q • φ (Pi.single x (Matrix.single p q 1)) := by
    intro y
    simp only [← map_smul, ← map_sum]
    congr 1
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single x]
    · simp only [Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (y x)
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  rw [show (φ : _ → _) = _ from funext h]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact (smul_cont hO _).comp (by fun_prop : Continuous fun y : X → Matrix (Fin n) (Fin n) O => y x p q)

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

def tw (g : GE D.nd) : S.X' → MatN D.nd i :=
  fun x' => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rO D.nd i r (S.p x') g

theorem tw_mem (g : GE D.nd) : InR' D.nd r S (tw i r S g) := by
  refine ⟨1, fun _ _ => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => g,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  rw [Fin.sum_univ_one]
  rfl

theorem yg_mem (g : GE D.nd) : InY D.nd r S (yg D.nd r S g) := by
  refine ⟨1, fun _ => tw i r S 1, fun _ => g, fun _ => tw_mem i r S 1, ?_⟩
  rw [Fin.sum_univ_one]
  funext x'
  simp [tw]

theorem yg_mul (g h : GE D.nd) :
    yg D.nd r S (g * h) = yg D.nd r S g + tw i r S g * yg D.nd r S h := by
  funext x'
  simp only [yg, tw, Pi.add_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_smul, mul_assoc]
  rw [smul_comm]
  abel

theorem yg_cont (hr : GoodR D.nd i r) : Continuous fun g => yg D.nd r S g := by
  refine continuous_pi fun x' => ?_
  have hc : Continuous fun g => rO D.nd i r (S.p x') g := (hr (S.p x')).1
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine ((h1.smul (hc.mul (continuous_const (y := Eel D.nd S x')))).sub
    (continuous_const (y := Eel D.nd S x'))).congr fun g => ?_
  simp [yg]

theorem cocW_le (hr : GoodR D.nd i r) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hψ : ∀ g, ψ (tw i r S g) = M g) :
    cocW i r S Xs ψ ≤ Z1 (WKG M) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, -, rfl⟩
  refine ⟨(lin_cont (D.nd.O_adic i) φ).comp (yg_cont i r S hr), fun g h => ?_⟩
  show φ _ = φ _ + WKG M g (φ _)
  rw [yg_mul, map_add, hφ _ (tw_mem i r S g) _ (yg_mem i r S h), hψ]
  rfl

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : GoodCongruenceObjects D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.Coc

end
