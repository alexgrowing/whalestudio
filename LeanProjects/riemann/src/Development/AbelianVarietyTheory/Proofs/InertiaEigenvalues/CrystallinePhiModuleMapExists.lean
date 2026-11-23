import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeInduction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrysEps

theorem shift_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (h : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (k : K) : sh (PowerSeries.C k) = PowerSeries.C (PowerSeries.C k) := by
  refine PowerSeries.ext fun i => ?_
  cases i with
  | zero => simpa using h (PowerSeries.C k) 0
  | succ n =>
    have h1 := h (PowerSeries.C k) (n + 1)
    rw [Function.iterate_succ_apply, PowerSeries.derivative_C,
      Function.iterate_fixed (map_zero _)] at h1
    have h2 : ((n + 1).factorial : K⟦X⟧) ≠ 0 := by
      rw [← map_natCast (PowerSeries.C : K →+* K⟦X⟧), Ne,
        map_eq_zero_iff _ PowerSeries.C_injective]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [(mul_eq_zero.1 h1).resolve_left h2, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

theorem bc_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (p : N → Prop)
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hs : ∀ (r : B) y, p y → p (r • y))
    (hu : ∀ x, p (u x)) (y : N) : p y := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9; revert A B M N h_4 h_5 h_6 h_7 h_8 h_9 f u h p h0 hadd hs hu y; exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction)
  | exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | (apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction ..)

theorem exists_crystalline_epsilon_combination {l : ℕ} [Fact l.Prime] {a e : ℕ} {O K : Type} [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] (Q : Obj l R) (toA : Q.A → ZMod a → K⟦X⟧) {J : Type} [Fintype J] (o : J → O)
    (hspan : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ A O K) → ∃ w : J → Q.A, ∀ τ,
      f τ = ∑ k, PowerSeries.C (algebraMap O K (o k)) * toA (w k) τ)
    (P : PhiMod O K l e a ι) (EE : FCrys l R) (c : EE.M Q →+ Vec K a ι) (hinj : Function.Injective c)
    (hmem : ∀ x, c x ∈ P.M) (hsurj : ∀ m ∈ P.M, ∃ x, c x = m)
    (hw : ∀ (w : Q.A) (x : EE.M Q), c (w • x) = fun τ i => toA w τ * c x τ i)
    (hU : ∀ o : O, ∃ U : FHom EE EE, ∀ x,
      c (U.u Q x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i)
    (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (PP : Obj l R) (p₀ p₁ : GlobalTheory.Prism.Hom Q PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧)
    (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧))
    (hl₀ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i)
    (hl₁ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i)
    (ht₀ : ∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i)))
    (ht₁ : ∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) :
    ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  have hb : ∀ k : ι, (fun _ => Pi.single k 1 : Vec K a ι) ∈ P.M := fun k => mem_tot.2 fun τ i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne h]; exact zero_mem _
  choose b hb using fun k => hsurj _ (hb k)
  choose U hU using hU
  refine ⟨fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i, ?_⟩
  set ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i with hε

  have hU₀ : ∀ o y τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i := by
    intro o y
    refine bc_induction (EE.tr_bc p₀) (fun y => ∀ τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i) ?_ ?_ ?_ ?_ y
    · intro τ i; simp
    · intro y z hy hz τ i
      simp only [map_add, Pi.add_apply, hy, hz, mul_add]
    · intro r y hy τ i
      rw [map_smul, hl₀, hl₀, hy]; ring
    · intro x τ i
      rw [(U o).u_tr, ht₀, ht₀, hU]
      simp only [map_mul, frob_C]
  have hU₁ : ∀ o x τ i, lam₁ ((U o).u PP (EE.tr p₁ x)) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₁ (EE.tr p₁ x) τ i := by
    intro o x τ i
    rw [(U o).u_tr, ht₁, ht₁, hU]
    simp only [map_mul, frob_C, shift_C sh hsh]
  have hS0 : ∀ τ, lam₀ 0 τ = ε τ *ᵥ lam₁ 0 τ := by intro τ; simp
  have hSadd : ∀ y z, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) → (∀ τ, lam₀ z τ = ε τ *ᵥ lam₁ z τ) →
      ∀ τ, lam₀ (y + z) τ = ε τ *ᵥ lam₁ (y + z) τ := by
    intro y z hy hz τ
    simp only [map_add, Pi.add_apply, hy, hz, Matrix.mulVec_add]
  have hSs : ∀ (r : PP.A) y, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) →
      ∀ τ, lam₀ (r • y) τ = ε τ *ᵥ lam₁ (r • y) τ := by
    intro r y hy τ
    have e0 : lam₀ (r • y) τ = j τ r • lam₀ y τ := funext fun i => hl₀ r y τ i
    have e1 : lam₁ (r • y) τ = j τ r • lam₁ y τ := funext fun i => hl₁ r y τ i
    rw [e0, e1, hy, Matrix.mulVec_smul]
  have hSU : ∀ o x, (∀ τ, lam₀ (EE.tr p₁ x) τ = ε τ *ᵥ lam₁ (EE.tr p₁ x) τ) →
      ∀ τ, lam₀ (EE.tr p₁ ((U o).u _ x)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ ((U o).u _ x)) τ := by
    intro o x hx τ
    rw [← (U o).u_tr]
    have e0 : lam₀ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₀ (EE.tr p₁ x) τ :=
      funext fun i => hU₀ o _ τ i
    have e1 : lam₁ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₁ (EE.tr p₁ x) τ :=
      funext fun i => hU₁ o _ τ i
    rw [e0, e1, hx, Matrix.mulVec_smul]
  have hSb : ∀ k τ, lam₀ (EE.tr p₁ (b k)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ (b k)) τ := by
    intro k τ
    have e1 : lam₁ (EE.tr p₁ (b k)) τ = Pi.single k 1 := funext fun i => by
      rw [ht₁, hb]
      rcases eq_or_ne i k with rfl | h
      · simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne h, map_zero]
    rw [e1, Matrix.mulVec_single_one]
    rfl
  refine bc_induction (EE.tr_bc p₁) (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hS0 hSadd hSs fun x => ?_
  choose w hwx using fun i => hspan (fun τ => c x τ i) fun τ => mem_tot.1 (hmem x) τ i
  have hx : x = ∑ i, ∑ k, (U (o k)).u _ (w i k • b i) := by
    apply hinj
    funext τ i
    simp only [map_sum, Finset.sum_apply, hU, hw, hb]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one]
      exact hwx i τ
    · intro i' _ h
      simp only [Pi.single_eq_of_ne h.symm, mul_zero, Finset.sum_const_zero]
    · simp
  rw [hx, map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun k _ => ?_
  refine hSU _ _ ?_
  rw [LinearMap.map_smulₛₗ]
  exact hSs _ _ (hSb i)

theorem exists_eps : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j _
    lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine exists_crystalline_epsilon_combination (ϖ.prism a) (fun w τ => (toAc t K w τ : K⟦X⟧)) (Module.Free.chooseBasis ℤ_[l] O) ?_
    P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  intro f hf
  obtain ⟨w, hw⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) fun τ => ⟨f τ, hf τ⟩
  refine ⟨w, fun τ => ?_⟩
  refine (congrArg Subtype.val (congrFun hw τ)).trans ?_
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, algebraMap_eq_C]

end GlobalTheory.BKGal.CrysEps
