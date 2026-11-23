import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ]

theorem cuspW_of_conj (R R' : RiemLat E g Λ) (σ σ' : Ψ → (𝓞 E →+* ℂ))
    (h1 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R'.form I ↔ IsIsoSub R.form I)
    (h2 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → ∀ τ, ∀ v ∈ I, ∀ w ∈ I,
      R'.ip (proj R'.B (σ' τ) (R'.P v)) (proj R'.B (σ' τ) (R'.P w)) =
        conj (R.ip (proj R.B (σ τ) (R.P v)) (proj R.B (σ τ) (R.P w)))) : R'.cuspW σ' = R.cuspW σ := by
  have h3 : ∀ I : Submodule (𝓞 E) Λ, IsIsoSub R.form I → R'.nz σ' I = R.nz σ I := by
    intro I hI
    unfold RiemLat.nz
    split_ifs with h
    · have hv := h.choose_spec.choose_spec.2.1
      unfold RiemLat.nzOf
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      have h4 : (R'.gram fun a => eigComp R'.B (σ' τ) (R'.P (h.choose_spec.choose a))) =
          (starRingEnd ℂ).mapMatrix (R.gram fun a => eigComp R.B (σ τ) (R.P (h.choose_spec.choose a))) := by
        ext a b
        simp only [RiemLat.gram, eigComp_eq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
        exact h2 I hI τ _ (hv a) _ (hv b)
      rw [h4, ← RingHom.map_det, Complex.conj_re]
    · rfl
  unfold RiemLat.cuspW RiemLat.IsCusp
  congr 2
  ext x
  constructor
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).1 c⟩, by rw [h3 I ((h1 I).1 c)]⟩
  · rintro ⟨I, ⟨a, b, c⟩, rfl⟩
    exact ⟨I, ⟨a, b, (h1 I).2 c⟩, by rw [h3 I c]⟩

def conjL (f : Module.End ℂ (Fin g → ℂ)) : Module.End ℂ (Fin g → ℂ) where
  toFun x := star (f (star x))
  map_add' x y := by rw [star_add, map_add, star_add]
  map_smul' c x := by rw [star_smul, map_smul, star_smul, star_star, RingHom.id_apply]

theorem conjL_apply (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) : conjL f x = star (f (star x)) := rfl

def conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a := conjL (ρ a)
  map_one' := LinearMap.ext fun x => by simp [conjL_apply]
  map_mul' a b := LinearMap.ext fun x => by simp [conjL_apply]
  map_zero' := LinearMap.ext fun x => by simp [conjL_apply]
  map_add' a b := LinearMap.ext fun x => by simp [conjL_apply]

omit [NumberField E] [IsCMField E] in
theorem conjB_star (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) :
    conjB ρ a (star x) = star (ρ a x) := by
  show star (ρ a (star (star x))) = _
  rw [star_star]

theorem dot_conj (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ H.map (starRingEnd ℂ) *ᵥ star w = conj (star z ⬝ᵥ H *ᵥ star (star w)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_conj]

def conjLat (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := neg_eq_zero.2 (R.alt x)
  unimod := neg_involutive.bijective.comp R.unimod
  adj a a' h x y := congrArg Neg.neg (R.adj a a' h x y)
  P := (starAddEquiv : (Fin g → ℂ) ≃+ (Fin g → ℂ)).toAddMonoidHom.comp R.P
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := R.herm.map _ fun _ => rfl
  pos z hz := by
    rw [dot_conj, Complex.conj_re]
    exact R.pos (star z) (star_ne_zero.2 hz)
  im x y := by
    show (star (R.P x) ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star (R.P y))).im = ((-(R.form x y) : ℤ) : ℝ)
    rw [dot_conj]
    simp only [star_star (R.P x), star_star (R.P y)]
    rw [Complex.conj_im, R.im, Int.cast_neg]
  B := conjB R.B
  act a x := by
    show star (R.P (a • x)) = conjB R.B a (star (R.P x))
    rw [conjB_star, R.act]

theorem conjLat_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (conjLat R).ip (star x) (star y) = conj (R.ip x y) := by
  show star y ⬝ᵥ R.Hm.map (starRingEnd ℂ) *ᵥ star (star x) = conj (y ⬝ᵥ R.Hm *ᵥ star x)
  rw [dot_conj]
  simp only [star_star x, star_star y]

omit [IsCMField E] in
theorem proj_conjB (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    proj (conjB ρ) ((starRingEnd ℂ).comp s) (star x) = star (proj ρ s x) := by
  rw [proj_apply, proj_apply, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjB_star, star_smul, coef_conj]
  rfl

end

theorem riemann_lattice_conjugate_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ _
  refine ⟨cuspW_of_conj R R σ _ (fun _ => Iff.rfl) fun I hI τ v hv w hw => gram_conj R hI (σ τ) hv hw,
    conjLat R, fun _ => rfl, rfl, conjB_star R.B, cuspW_of_conj R _ σ _ (fun I => ?_) fun I _ τ v _ w _ => ?_⟩
  · exact forall₄_congr fun v _ w _ => neg_eq_zero
  · exact (congrArg₂ (conjLat R).ip (proj_conjB R.B (σ τ) (R.P v)) (proj_conjB R.B (σ τ) (R.P w))).trans
      (conjLat_ip R _ _)

end LevelTowerAlt
