import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.LieMatrixCoordinates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscriminantGramUnit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpExistsEqAdd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.PGsh.Up
open GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixCoordinates GlobalTheory.TorsionCompare NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AvChartCompare

section Charts

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} {d : ℕ}

end Charts

section Series

variable {O : Type} [CommRing O] {d : ℕ}

variable {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]

def HasFinColength (F : Fin d → PS O 2 d) {s : ℕ} (u : Fin s → Fin d → O) (x : NNReal) : Prop :=
  ∃ S : Set (PS O 1 d), S.Finite ∧ (∀ χ ∈ S, IsMultSeries F χ) ∧
    HasLen v O ((Fin s → O) ⧸
      Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i}) x

variable {v}

theorem hasLen_le_of_surjective (hv : v.Integers O) {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (π : M →ₗ[O] N) (hπ : Function.Surjective π) {x y : NNReal}
    (hx : HasLen v O M x) (hy : HasLen v O N y) : x ≤ y := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, b, ⟨e'⟩, rfl⟩ := hy
  let f := e'.toLinearMap ∘ₗ π ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := e'.surjective.comp (hπ.comp e.symm.surjective)
  let q : Fin m → ((j : Fin n) → O ⧸ Ideal.span {b j}) :=
    fun i => f (Pi.single i (1 : O ⧸ Ideal.span {c i}))
  have hq : Submodule.span O (Set.range q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := hf z
    have hz : z = ∑ i, (Quotient.out (z i) : O) • Pi.single i (1 : O ⧸ Ideal.span {c i}) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out (z k)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne' hb]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hz, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • q i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, q, ← map_smul]
      have : c k • (Pi.single k (1 : O ⧸ Ideal.span {c k}) : (i : Fin m) → O ⧸ Ideal.span {c i}) =
          0 := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, _root_.mul_one,
            Ideal.Quotient.algebraMap_eq]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_zero]
    · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h := det_mem_span_prod n b m q hq (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at h
  simpa only [map_prod] using hv.le_of_dvd (Ideal.mem_span_singleton.1 h)

theorem HasFinColength.le (hv : v.Integers O) {F : Fin d → PS O 2 d} {s : ℕ}
    {u : Fin s → Fin d → O} {x y : NNReal} (hx : HasFinColength v F u x)
    (hy : HasLen v O ((Fin s → O) ⧸ dlogSpan F u) y) : x ≤ y := by
  obtain ⟨S, -, hS, hx⟩ := hx
  have hle : Submodule.span O {l | ∃ χ ∈ S, l = fun i => linCoeff χ ⬝ᵥ u i} ≤ dlogSpan F u :=
    Submodule.span_mono fun l ⟨χ, h, hl⟩ => ⟨χ, hS χ h, hl⟩
  exact hasLen_le_of_surjective hv (Submodule.factor hle) (Submodule.factor_surjective hle) hx hy

end Series

section Emb

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_extend (τ : 𝓞 E →+* C) : ∃! σ : E →+* C, ∀ a : 𝓞 E, σ a = τ a := by
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    obtain ⟨n, hn⟩ := (Submodule.ne_bot_iff _).1
      (Ideal.IsIntegral.comap_ne_bot ℤ (I := RingHom.ker τ) h)
    have h1 : τ (algebraMap ℤ (𝓞 E) n) = 0 := hn.1
    simp [hn.2] at h1
  refine ⟨IsFractionRing.lift (K := E) hτ, fun a => IsFractionRing.lift_algebraMap hτ a,
    fun σ h => IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_⟩
  rw [IsFractionRing.lift_algebraMap]; exact h a

theorem exists_restrict (hv : v.Integers O) (σ : E →+* C) :
    ∃ τ : 𝓞 E →+* O, ∀ a : 𝓞 E, σ a = algebraMap O C (τ a) := by
  have h : ∀ a : 𝓞 E, ∃ z : O, algebraMap O C z = σ a := fun a => by
    have h1 : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
    exact hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h1.tower_top)
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a => (hf a).symm⟩ <;> intros <;> apply hv.hom_inj <;> simp [hf]

def embEquiv (hv : v.Integers O) : (𝓞 E →+* O) ≃ (E →+* C) :=
  Equiv.ofBijective (fun τ => (exists_extend ((algebraMap O C).comp τ)).choose) (by
    constructor
    · intro τ τ' h
      ext a
      apply hv.hom_inj
      have h1 := (exists_extend ((algebraMap O C).comp τ)).choose_spec.1 a
      have h2 := (exists_extend ((algebraMap O C).comp τ')).choose_spec.1 a
      exact h1.symm.trans ((DFunLike.congr_fun h (a : E)).trans h2)
    · intro σ
      obtain ⟨τ, hτ⟩ := exists_restrict hv σ
      exact ⟨τ, ((exists_extend ((algebraMap O C).comp τ)).choose_spec.2 σ hτ).symm⟩)

end Emb

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

def Under (w : AvDefs.Place p (𝓞 E)) (P : Ideal (𝓞 E)) : Prop :=
  IsPrimeUnder (GlobalTheory.CutMultiplicationUnits.placeEquiv w).toPlace P

variable {w : AvDefs.Place p (𝓞 E)} {P : Ideal (𝓞 E)}

end Places

def AvAtCM (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : DegData T (IsLocalRing.maximalIdeal T))
      (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
      (U : UnifPre (IsLocalRing.maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G),
      IsChartJ G F x →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
      (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
    ∀ [Module (𝓞 E) D.toPre.X] (io : RingAct G (𝓞 E))
      (oD : D.OAct (𝓞 E)) (oA : A.OAct (𝓞 E)), U.OLinear (𝓞 E) oD oA io →
    ∀ (act : Germ.OAct (𝓞 E) F), ChartActs G x io act →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
        (iota : T →+* O), IsLocalHom iota →
      ∀ (w : AvDefs.Place p (𝓞 E)) (t : Fin w.n ≃ AvDefs.Emb (O := O) w.e) (vd : ℝ),
        AvDefs.HasVd p v w t vd →
      ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O),
        (∀ j, IsEigBasis (actMap iota act) ((t j : AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (W j)) →
        (∀ τ ∈ AvDefs.Emb (O := O) w.bar,
          ∃ W' : Fin rm → Fin d → O, IsEigBasis (actMap iota act) τ W') →
      ∃ xs : Fin w.n → NNReal, (∀ j, HasAF v (F.mapF iota) (W j) (xs j)) ∧
        v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j

abbrev Conclusion : Type 1 :=
  ∀ {T : Type} [CommRing T] {E : Type} [Field E] [NumberField E] {d : ℕ} (_F : FGLaw T d)
    {C : Type} [Field C] [CharZero C] (_v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (_io : T →+* O) (_w : Ideal (𝓞 E)) {rp : ℕ} (_rm : ℕ)
    (_u : (E →+* C) → Fin rp → Fin d → O), Prop

def OverCharts (p : ℕ) [Fact p.Prime] (Q : Conclusion) : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (D : DegData T (IsLocalRing.maximalIdeal T)) [Module (𝓞 E) D.toPre.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (IsLocalRing.maximalIdeal T) D A G)
    (ιD : D.OAct (𝓞 E)) (ιA : A.OAct (𝓞 E)) (ιG : RingAct G (𝓞 E)),
    U.OLinear (𝓞 E) ιD ιA ιG →
  ∀ (d : ℕ) (x : JetFam G d) (F : FGLaw T d) (α : Germ.OAct (𝓞 E) F),
    IsJetChart G x → IsLawOf G x F → IsActOf G x ιG α →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [IsAdicComplete (Ideal.span {(p : O)}) O],
    v.Integers O →
  ∀ (io : T →+* O), IsLocalHom io →
  ∀ (w : Ideal (𝓞 E)), w.IsPrime → (p : 𝓞 E) ∈ w → w ≠ w.comap (starRingEnd (𝓞 E)) →
  ∀ (rp rm : ℕ) (u : (E →+* C) → Fin rp → Fin d → O) (u' : (E →+* C) → Fin rm → Fin d → O),
    (∀ τ, Induces v τ w → IsEigenBasis α io τ (u τ)) →
    (∀ σ, Induces v σ (w.comap (starRingEnd (𝓞 E))) → IsEigenBasis α io σ (u' σ)) →
    Q F v io w rm u

def bound_vp (p : ℕ) {E : Type} [Field E] [NumberField E] (w : Ideal (𝓞 E)) (r : ℝ) : ℝ :=
  (localDeg p w : ℝ) * r * (1 / ((p : ℝ) - 1) + vd_vp p w / 2)

def ColengthsExist (p : ℕ) : Conclusion := fun {_} _ {_} _ _ {_} F {_} _ _ v {_} _ _ io w {_} _ u =>
  ∀ τ, Induces v τ w → ∃ a : ℝ, HasColength_vp p v F io (u τ) a

open Classical in

def ColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∀ a : (E →+* C) → ℝ, (∀ τ, Induces v τ w → HasColength_vp p v F io (u τ) (a τ)) →
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), a τ ≤ bound_vp p w rm

open Classical in

def FiniteColengthsBounded (p : ℕ) : Conclusion :=
  fun {_} _ {E} _ _ {_} F {C} _ _ v {_} _ _ io w {_} rm u =>
  ∃ xs : (E →+* C) → NNReal, (∀ τ, Induces v τ w → HasFinColength v (F.mapF io) (u τ) (xs τ)) ∧
    v (p : C) ^ bound_vp p w rm ≤
      ∏ τ ∈ Finset.univ.filter (fun τ : E →+* C => Induces v τ w), xs τ

end GlobalTheory.AvChartCompare
