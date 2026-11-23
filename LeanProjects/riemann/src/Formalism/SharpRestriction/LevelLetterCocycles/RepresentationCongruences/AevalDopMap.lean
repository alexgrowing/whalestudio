import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

private theorem π₀_cancel (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T : LocLat G Qp LL O}
    {a b : W.DD T} (h : W.π₀ • a = W.π₀ • b) : a = b := by
  obtain ⟨u, hu⟩ := hπ
  have ha : W.π₀ • a = (u : W.EE) • a := by rw [hu, algebraMap_smul]
  have hb : W.π₀ • b = (u : W.EE) • b := by rw [hu, algebraMap_smul]
  calc a = (↑u⁻¹ : W.EE) • ((u : W.EE) • a) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = (↑u⁻¹ : W.EE) • ((u : W.EE) • b) := by rw [← ha, h, hb]
    _ = b := by rw [smul_smul, Units.inv_mul, one_smul]

theorem dop_eq (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y) {x y : W.DD T}
    (h : W.γ T x - x = W.π₀ • y) : dop x = y :=
  π₀_cancel W hπ ((hd x).trans h)

theorem dop_pres (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O) (i : ZMod n)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (dop x) := by
  obtain ⟨y, hy, hxy⟩ := hgN x hx
  rw [dop_eq W hπ T dop hd hxy]
  exact hy

theorem dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (y : W.DD T₁) :
    W.map F (dop₁ y) = dop₂ (W.map F y) := by
  apply π₀_cancel W hπ
  have hs : ∀ z : W.DD T₁, W.π₀ • W.map F z = W.map F (W.π₀ • z) := fun z => by
    rw [← algebraMap_smul W.EE W.π₀ (W.map F z), ← map_smul, algebraMap_smul]
  rw [hs, hd₁, hd₂, map_sub]
  congr 1
  exact W.map_γ F W.gam y

theorem aeval_dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (p : O[X]) (y : W.DD T₁) :
    W.map F (aeval dop₁ p y) = aeval dop₂ p (W.map F y) := by
  have hO : ∀ (c : O) (v : W.DD T₁), W.map F (c • v) = c • W.map F v := by
    intro c v
    rw [← algebraMap_smul (LetA O n) c v, ← algebraMap_smul W.EE (algebraMap O (LetA O n) c) v, map_smul,
      algebraMap_smul, algebraMap_smul]
  have hc : ∀ k : ℕ, ∀ y : W.DD T₁, W.map F ((dop₁ ^ k) y) = (dop₂ ^ k) (W.map F y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, dop_map W hπ F dop₁ hd₁ dop₂ hd₂, ih]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hO, hc]

theorem dop_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (dop₂ z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨dop₁ x₁, dop_pres W hπ T₁ i dop₁ hd₁ hgN₁ hx₁, dop_map W hπ F dop₁ hd₁ dop₂ hd₂ x₁⟩

private theorem nΔi_add' {T : LocLat G Qp LL O} {i : ZMod n} {x y : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T i y) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (x + y) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  exact ⟨(W.NΔ T).add_mem hx.1 hy.1, (W.Nl T i).add_mem hx.2 hy.2⟩

private theorem nΔi_smulO' {T : LocLat G Qp LL O} {i : ZMod n} (c : O) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c • x) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  refine ⟨(W.NΔ T).smul_mem c hx.1, ?_⟩
  rw [← algebraMap_smul (LetA O n) c x]
  exact (W.Nl T i).smul_mem _ hx.2

private theorem nΔi_aeval (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (i : ZMod n) (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    (p : O[X]) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (aeval dop p x) := by
  have hpow : ∀ k : ℕ, ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → Formalism.MainNotions.LiftingTheory.InNΔi W T i ((dop ^ k) x) := by
    intro k
    induction k with
    | zero => intro x hx; rw [pow_zero, Module.End.one_apply]; exact hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact dop_pres W hπ T i dop hd hgN (ih x hx)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_induction _ (Formalism.MainNotions.LiftingTheory.InNΔi W T i) (fun a b ha hb => nΔi_add' W ha hb) ?_ ?_
  · unfold Formalism.MainNotions.LiftingTheory.InNΔi
    exact ⟨(W.NΔ T).zero_mem, (W.Nl T i).zero_mem⟩
  · intro k _
    rw [LinearMap.smul_apply]
    exact nΔi_smulO' W _ (hpow k x hx)

theorem aeval_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (p : O[X]) {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (aeval dop₂ p z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨aeval dop₁ p x₁, nΔi_aeval W hπ T₁ i dop₁ hd₁ hgN₁ p hx₁,
    aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂ p x₁⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
