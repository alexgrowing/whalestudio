import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem gam_cocycle {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B)
    (β : G → B × B) (hβ : ∀ g g', β (g * g') = β g + T.M1 g (β g')) (a b c : G) :
    (T.χ2 a : B) * (-(h * omg (β b) (T.M1 b (β c)))) - (-(h * omg (β (a * b)) (T.M1 (a * b) (β c))))
      + (-(h * omg (β a) (T.M1 a (β (b * c))))) - (-(h * omg (β a) (T.M1 a (β b)))) = 0 := by
  have e := T.alternatingForm_adjointSuperdiagRep a (β b) (T.M1 b (β c))
  rw [hβ a b, hβ b c, map_mul, Module.End.mul_apply, map_add]
  generalize T.M1 a (T.M1 b (β c)) = u at e ⊢
  generalize T.M1 a (β b) = w at e ⊢
  simp only [omg, Prod.fst_add, Prod.snd_add] at e ⊢
  linear_combination h * e

theorem UpperTheory.exists_continuous_isGam_of_torus_cocycle :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), ∀ β ∈ Z1 T.M1, ∃ γ : GQ l → B, Continuous γ ∧ T.IsGam h β γ := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β hβ
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  have hχ := Tor.continuous_χ2 hD.ηlc T hT.cont hT.cont_inv
  have hM := Tor.contAction_torus_module hD.ηlc T hT.cont hT.cont_inv
  have hρ : ContAction (resCoef E (chRep T.χ2)) := contAction_chRep hχ
  obtain ⟨-, f2, -, e2⟩ := tateRat hP (v := l) (l := l) (MonoidHom.id (GQ l)) IsOpenEmbedding.id
    (resCoef E (chRep T.χ2)) hρ
  obtain ⟨s, hs, hsi⟩ := ((cycInertia l).2 H hD.isOpen).2
  have hsH : s ∈ H := hs.1
  have hsI : s ∈ Iq l := hs.2
  have hχs : (T.χ2 s : B) = algebraMap E B ((cycA l l E s ^ (2 * e) : Eˣ) : E) := by
    have h0 := hT.ine s hsI 0
    have h2 := hT.ine s hsI 2
    have w0 : wt1 (0 : Fin 3) = 1 := by decide
    have w2 : wt1 (2 : Fin 3) = -1 := by decide
    rw [w0, zpow_one] at h0
    rw [w2, zpow_neg_one] at h2
    have k0 : T.t s 0 = Units.map (algebraMap E B : E →* B) (Ψ s) := Units.ext h0
    have k2 : T.t s 2 = Units.map (algebraMap E B : E →* B) (Ψ s)⁻¹ := Units.ext h2
    rw [Tor.χ2_apply, hD.ηH s hsH, k0, k2, ← map_div, div_inv_eq_mul, hD.ΨH s hsH hsI, ← pow_add, ← two_mul]
    simp
  have hne : ((cycA l l E s ^ (2 * e) : Eˣ) : E) ≠ (cycA l l E s : E) := by
    intro hc
    apply hsi
    have h1 : cycA l l E s ^ (2 * e - 1) = 1 := by
      have := Units.ext hc
      have he := hD.e_pos
      rw [show 2 * e = (2 * e - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.1 this
    have inj : Function.Injective (algebraMap ℤ_[l] E) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e - 1, by have := hD.e_pos; omega, ?_⟩
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) inj
    rw [map_pow, map_one]
    exact h1
  have hbot : H0dual ((cycA l l E).comp (MonoidHom.id (GQ l))) (resCoef E (chRep T.χ2)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have h1 : f ((T.χ2 s : B) * x) = (cycA l l E s : E) * f x := hf s x
    rw [hχs, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 (show (_ - _) * f x = 0 by rw [sub_mul, h1, sub_self])).resolve_left (sub_ne_zero.2 hne)
  rw [hbot, finrank_bot] at e2
  haveI := f2
  have hsub : Subsingleton (H2 (resCoef E (chRep T.χ2))) := Module.finrank_zero_iff.1 e2
  have hc : Continuous fun p : GQ l × GQ l => -(h * omg (β p.1) (T.M1 p.1 (β p.2))) := by
    have a1 : Continuous fun p : GQ l × GQ l => β p.1 := hβ.1.comp continuous_fst
    have a2 : Continuous fun p : GQ l × GQ l => T.M1 p.1 (β p.2) :=
      hM.comp (continuous_fst.prodMk (hβ.1.comp continuous_snd))
    exact (continuous_const.mul ((a1.fst.mul a2.snd).sub (a1.snd.mul a2.fst))).neg
  let z : Z2 (resCoef E (chRep T.χ2)) := ⟨fun p => -(h * omg (β p.1) (T.M1 p.1 (β p.2))), hc,
    fun a b c => gam_cocycle T h β hβ.2 a b c⟩
  have hz : z ∈ (B2 (resCoef E (chRep T.χ2))).comap (Z2 (resCoef E (chRep T.χ2))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨γ, hγ, hγ2⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz
  refine ⟨γ, hγ, fun g g' => ?_⟩
  have h1 : (T.χ2 g : B) * γ g' - γ (g * g') + γ g = -(h * omg (β g) (T.M1 g (β g'))) := congrFun hγ2 (g, g')
  linear_combination -h1
