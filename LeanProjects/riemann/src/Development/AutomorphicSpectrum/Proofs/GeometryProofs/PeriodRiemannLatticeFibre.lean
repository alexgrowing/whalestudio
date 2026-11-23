import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

def conjEnd (g : ℕ) : Module.End ℂ (Fin g → ℂ) →+* Module.End ℂ (Fin g → ℂ) where
  toFun f :=
    { toFun := fun x => star (f (star x))
      map_add' := fun x y => by simp only [star_add, map_add]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply] }
  map_one' := by ext x; simp
  map_mul' f f' := by ext x; simp
  map_zero' := by ext x; simp
  map_add' f f' := by ext x; simp

theorem conjEnd_apply {g : ℕ} (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) :
    conjEnd g f x = star (f (star x)) := rfl

theorem mem_eigSp_iff {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ)
    (x : Fin g → ℂ) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem finrank_eigSp_conj {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ) :
    Module.finrank ℂ (eigSp ((conjEnd g).comp ρ) σ) = Module.finrank ℂ (eigSp ρ ((starRingEnd ℂ).comp σ)) := by
  have h1 : ∀ x, x ∈ eigSp ((conjEnd g).comp ρ) σ → star x ∈ eigSp ρ ((starRingEnd ℂ).comp σ) := by
    intro x hx
    rw [mem_eigSp_iff] at hx ⊢
    intro a
    have := congrArg star (hx a)
    simpa [conjEnd_apply, star_smul] using this
  have h2 : ∀ y, y ∈ eigSp ρ ((starRingEnd ℂ).comp σ) → star y ∈ eigSp ((conjEnd g).comp ρ) σ := by
    intro y hy
    rw [mem_eigSp_iff] at hy ⊢
    intro a
    simp [conjEnd_apply, hy a, star_smul]
  let j : eigSp ((conjEnd g).comp ρ) σ ≃+ eigSp ρ ((starRingEnd ℂ).comp σ) :=
    { toFun := fun x => ⟨star x.1, h1 _ x.2⟩
      invFun := fun y => ⟨star y.1, h2 _ y.2⟩
      left_inv := fun x => Subtype.ext (star_star _)
      right_inv := fun y => Subtype.ext (star_star _)
      map_add' := fun x y => Subtype.ext (star_add _ _) }
  have hr := rank_eq_of_equiv_equiv (R := ℂ) (R' := ℂ) (starRingEnd ℂ) j
    (Function.Involutive.bijective (f := starRingEnd ℂ) (fun z => by simp)) (fun r m => Subtype.ext (by simp [j, star_smul]))
  exact congrArg Cardinal.toNat hr

theorem star_herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    star z ⬝ᵥ Hm.map (starRingEnd ℂ) *ᵥ star (star w) = star (z ⬝ᵥ Hm *ᵥ star w) := by
  simp [dotProduct, mulVec, star_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjLat {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := by simp [R.alt x]
  unimod := by
    constructor
    · intro x y h
      exact R.unimod.1 (neg_injective (by simpa using h))
    · intro f
      obtain ⟨x, hx⟩ := R.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  adj a a' h x y := by simp [R.adj a a' h x y]
  P :=
    { toFun := fun x => star (R.P x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := by
    ext i j
    have := R.herm.apply i j
    simp [Matrix.conjTranspose_apply, ← this]
  pos z hz := by
    have h := R.pos (star z) (by simpa using hz)
    have h' := star_herm R.Hm (star z) (star z)
    simp only [star_star] at h'
    rw [h']
    simpa using h
  im x y := by
    have h := R.im x y
    have h' := star_herm R.Hm (R.P x) (R.P y)
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h']
    simp [h]
  B := (conjEnd g).comp R.B
  act a x := by simp [conjEnd_apply, R.act]

theorem conj_rt_iff (H : Host E) (s : E →+* ℂ) :
    ((starRingEnd ℂ).comp s) (H.rt : E) = H.rt0 ↔ ¬ s (H.rt : E) = H.rt0 := by
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h2 : s (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => s (a : E)) H.rt_sq
    simpa using h
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have hi := congrArg Complex.im h0
    have hr := congrArg Complex.re h0
    simp [pow_two] at hi hr
    rcases (by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact mul_eq_zero.1 this) with h | h
    · exact h
    · exfalso; rw [h] at hr; nlinarith [mul_self_nonneg H.rt0.re]
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
    exact H.d_prime.ne_zero h0
  have hpm : s (H.rt : E) = H.rt0 ∨ s (H.rt : E) = -H.rt0 := by
    have : (s (H.rt : E) - H.rt0) * (s (H.rt : E) + H.rt0) = 0 := by
      linear_combination h2 - h0
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    exact hne (by linear_combination -(1 / 2 : ℂ) * h)
  rcases hpm with h | h
  · simp only [RingHom.comp_apply, h, hconj]
    simpa using hneg
  · simp only [RingHom.comp_apply, h, map_neg, hconj, neg_neg]
    simpa using hneg

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open PeriodConj

theorem period_lattice_fibre_and_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  intro E _ _ _ H D l Xo σ g ty FU i P hty hP
  have hty' : IsTypeFn H (FU.Di i).p (FU.Di i).q ty := by
    rw [(FU.sig i).1, (FU.sig i).2]; exact hty
  obtain ⟨R, hRP, hRf, -, hrk⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty P hty' hP
  have hF : FibreLat Xo.univ.t (FU.u i P) R :=
    GlobalTheory.T.family_period_riemann_lattice E H D l Xo σ g ty FU i R P 1 hP hRf (by simp) (fun x => by simp [hRP]) Empty
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
  refine ⟨⟨R, hRf, hF, fun s => ?_⟩, ⟨conjLat R, ?_, ?_, fun s => ?_⟩⟩
  · rw [hrk s, (FU.sig i).1, (FU.sig i).2]
  · show -R.form = _
    rw [hRf]
  · exact (GlobalTheory.T.fibre_lattice_base_change_conj E H Xo.X Xo.X Xo.univ.t Xo.univ.t (𝟙 _) g _ R (conjLat R) (FU.u i P)).2
      (fun _ => rfl) rfl (fun _ _ => rfl) hF
  · have h1 : Module.finrank ℂ (eigSp (conjLat R).B (s.comp (algebraMap (𝓞 E) E))) =
        Module.finrank ℂ (eigSp R.B (((starRingEnd ℂ).comp s).comp (algebraMap (𝓞 E) E))) :=
      finrank_eigSp_conj R.B (s.comp (algebraMap (𝓞 E) E))
    rw [h1, hrk, (FU.sig i).1, (FU.sig i).2]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg (fun h' => (conj_rt_iff H s).1 h' h)]
    · rw [if_neg h, if_pos ((conj_rt_iff H s).2 h)]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
