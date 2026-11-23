import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

section Defs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def detLat {F : Type} [AddCommGroup F] [Module Ω F] (L : Lat ξ F) {r : ℕ} (u : Fin r → F) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p)
    {t | ∃ A : Matrix (Fin r) (Fin r) Ω, L.IsFrameAt (fun i => ∑ j, A i j • u j) p ∧ t = A.det}

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]

structure HodgeLat (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) where

  ρH : 𝓞 E →+* Module.End Ω (V × Module.Dual Ω V)

  HL : Lat ξ (V × Module.Dual Ω V)
  act_fst : ∀ a y, (ρH a y).1 = ρ a y.1
  act_inr : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))
  map_fst : HL.map (LinearMap.fst Ω V (Module.Dual Ω V)) = L
  comap_inr : HL.comap (LinearMap.inr Ω V (Module.Dual Ω V)) = L.dual
  free : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ x : Fin r → V × Module.Dual Ω V,
    ∀ q : Cpt ξ, q.1 ∈ U → HT.IsFreeOn ρH (HL q) x
  vb : L.IsVB (Module.finrank Ω V) ⊤

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def HodgeLat.quot (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) : Lat ξ (V × Module.Dual Ω V) :=
  𝓗.HL.map (HT.eigProj 𝓗.ρH σ)

def HodgeLat.DegZero (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (ϖ : Ω) : Prop :=
  ∀ u : Fin r → V × Module.Dual Ω V, LinearIndependent Ω u →
    Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → NumTrivMod (detLat (𝓗.quot σ) u) ϖ

def IsAdapted {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) {p q : ℕ} (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W) : Prop :=
  (∀ i, u i ∈ HT.eigSp ρH σ) ∧ (∀ i, (u (Fin.castAdd q i)).1 = v i) ∧
    ∀ j, (u (Fin.natAdd p j)).1 = 0 ∧ ∀ j', (u (Fin.natAdd p j)).2 (w j') = if j = j' then 1 else 0

end Defs

namespace HodgeDeterminantLattice

section Det

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ}

theorem mem_span_iff {A : Subring Ω} {t : Ω} (ht : t ≠ 0) {y : Ω} :
    y ∈ Submodule.span A {t} ↔ y / t ∈ A := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [show c • t = (c : Ω) * t from rfl, mul_div_cancel_right₀ _ ht]
    exact c.2
  · intro h
    exact ⟨⟨_, h⟩, div_mul_cancel₀ _ ht⟩

theorem sum_smul_sum (C A : Matrix (Fin r) (Fin r) Ω) (u : Fin r → F) (i : Fin r) :
    ∑ j, C i j • ∑ k, A j k • u k = ∑ k, (C * A) i k • u k := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem det_ne_zero {A : Matrix (Fin r) (Fin r) Ω} {u : Fin r → F}
    (h : LinearIndependent Ω fun i => ∑ j, A i j • u j) : A.det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, e⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine hc (funext (Fintype.linearIndependent_iff.1 h c ?_))
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_smul]
  have := congrFun e k
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
  rw [this, zero_smul]

theorem detLat_of_frame {L : Lat ξ F} {u : Fin r → F} (hu : LinearIndependent Ω u) {p : Cpt ξ}
    {A : Matrix (Fin r) (Fin r) Ω} (hA : L.IsFrameAt (fun i => ∑ j, A i j • u j) p) :
    (detLat L u).IsGenAt p A.det := by
  refine ⟨det_ne_zero hA.1, le_antisymm ?_ ?_⟩
  · rw [detLat, Submodule.span_le]
    rintro _ ⟨B, hB, rfl⟩
    have h1 : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • ∑ k, A j k • u k = ∑ j, B i j • u j := fun i => by
      rw [← Submodule.mem_span_range_iff_exists_fun, ← hA.2, hB.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    choose C hC using h1
    have e : B = (regAt ξ p).subtype.mapMatrix (Matrix.of C) * A := by
      ext i k
      have h2 := (hC i).symm.trans (sum_smul_sum ((regAt ξ p).subtype.mapMatrix (Matrix.of C)) A u i)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
      simp only [← sub_smul] at h2
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h2 k)
    rw [e, Matrix.det_mul, ← RingHom.map_det]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨A, hA, rfl⟩

theorem detLat_eq_bot {L : Lat ξ F} {u : Fin r → F} {p : Cpt ξ}
    (h : ∀ A : Matrix (Fin r) (Fin r) Ω, ¬ L.IsFrameAt (fun i => ∑ j, A i j • u j) p) : detLat L u p = ⊥ := by
  rw [detLat, Submodule.span_eq_bot]
  rintro _ ⟨A, hA, -⟩
  exact absurd hA (h A)

theorem exists_frame_of_isGenAt {L : Lat ξ F} {u : Fin r → F} {p : Cpt ξ} {s : Ω} (h : (detLat L u).IsGenAt p s) :
    ∃ A : Matrix (Fin r) (Fin r) Ω, L.IsFrameAt (fun i => ∑ j, A i j • u j) p := by
  by_contra hc
  exact h.1 (Submodule.span_singleton_eq_bot.1 (h.2.symm.trans (detLat_eq_bot (not_exists.1 hc))))

theorem isGenAt_mul {M L : Lat ξ Ω} {c : Ω} {p : Cpt ξ} {t s : Ω} (hM : M.IsGenAt p t) (hL : L.IsGenAt p (c * t))
    (hs : M.IsGenAt p s) : L.IsGenAt p (c * s) := by
  have hc := left_ne_zero_of_mul hL.1
  refine ⟨mul_ne_zero hc hs.1, ?_⟩
  ext y
  rw [hL.2, mem_span_iff hL.1, mem_span_iff (mul_ne_zero hc hs.1), ← div_div, ← div_div,
    ← mem_span_iff hM.1, ← mem_span_iff hs.1, hM.2.symm.trans hs.2]

theorem isGenAt_change {L : Lat ξ F} {u u' : Fin r → F} (hu : LinearIndependent Ω u) (hu' : LinearIndependent Ω u')
    {B : Matrix (Fin r) (Fin r) Ω} (hB : ∀ i, u' i = ∑ j, B i j • u j) {p : Cpt ξ} {s : Ω}
    (h : (detLat L u').IsGenAt p s) : (detLat L u).IsGenAt p (B.det * s) := by
  obtain ⟨A, hA⟩ := exists_frame_of_isGenAt h
  refine isGenAt_mul (detLat_of_frame hu' hA) ?_ h
  rw [mul_comm, ← Matrix.det_mul]
  apply detLat_of_frame hu
  simpa only [hB, sum_smul_sum] using hA

theorem hasDeg_of_scale {M L : Lat ξ Ω} {c : Ω} (hc : c ≠ 0)
    (h : ∀ p s, M.IsGenAt p s → L.IsGenAt p (c * s)) {ϖ : Ω} {Γ : FibreCurve ξ ϖ} {d : ℤ} (hM : Γ.HasDeg M d) :
    Γ.HasDeg L d := by
  obtain ⟨e, f, t, he, hf, ht, hfin, hd⟩ := hM
  exact ⟨c * e, fun i => c * f i, t, h _ _ he, fun i => ⟨(hf i).1, h _ _ (hf i).2⟩,
    fun i => by rw [mul_div_mul_left _ _ hc]; exact ht i, hfin, hd⟩

theorem hasDeg_detLat {L : Lat ξ F} {u u' : Fin r → F} (hu : LinearIndependent Ω u) (hu' : LinearIndependent Ω u')
    (hsp : ∀ i, u' i ∈ Submodule.span Ω (Set.range u)) {ϖ : Ω} {Γ : FibreCurve ξ ϖ} {d : ℤ}
    (h : Γ.HasDeg (detLat L u') d) : Γ.HasDeg (detLat L u) d := by
  choose B hB using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsp i)
  have hB' : ∀ i, u' i = ∑ j, Matrix.of B i j • u j := fun i => (hB i).symm
  exact hasDeg_of_scale (det_ne_zero (A := Matrix.of B) (u := u) (by simpa only [← hB'] using hu'))
    (fun _ _ => isGenAt_change hu hu' hB') h

theorem detLat_isVB {L : Lat ξ F} {W : Submodule Ω F} (hL : L.IsVB r W) {u : Fin r → F}
    (hu : LinearIndependent Ω u) (hsp : Submodule.span Ω (Set.range u) = W) : (detLat L u).IsVB 1 ⊤ := by
  intro p _
  obtain ⟨U, hU, b, hb, h⟩ := hL p trivial
  have h1 : ∀ i, b i ∈ Submodule.span Ω (Set.range u) := fun i => by
    rw [hsp, ← hb]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose A hA using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h1 i)
  have h2 : ∀ q : Cpt ξ, q.1 ∈ U → (detLat L u).IsGenAt q (Matrix.of A).det := fun q hq =>
    detLat_of_frame hu (by simpa only [Matrix.of_apply, hA] using h q trivial hq)
  refine ⟨U, hU, fun _ => (Matrix.of A).det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · rw [Set.range_const, eq_top_iff]
    exact fun y _ => Submodule.mem_span_singleton.2 ⟨y / (Matrix.of A).det, div_mul_cancel₀ _ (h2 p hU).1⟩
  · rw [linearIndependent_unique_iff]
    exact (h2 q hq).1
  · rw [Set.range_const]
    exact (h2 q hq).2

theorem detLat_one (M : Lat ξ F) {u : F} (hu : u ≠ 0) (p : Cpt ξ) {s : Ω} (hs : s ≠ 0)
    (h : M p = Submodule.span (regAt ξ p) {s • u}) :
    detLat M (fun _ : Fin 1 => u) p = Submodule.span (regAt ξ p) {s} := by
  have := detLat_of_frame (L := M) (u := fun _ : Fin 1 => u) (by rwa [linearIndependent_unique_iff]) (p := p)
    (A := Matrix.of fun _ _ => s) ⟨by rw [linearIndependent_unique_iff]; simpa [hs] using hu, by simp [h]⟩
  simpa using this.2

example (p : Cpt ξ) {a b c d : Ω} (h : LinearIndependent Ω ![(a, b), (c, d)]) :
    (detLat (fun q => Submodule.span (regAt ξ q) (Set.range ![(a, b), (c, d)]) : Lat ξ (Ω × Ω))
      ![(1, 0), (0, 1)]).IsGenAt p (a * d - b * c) := by
  have e : (fun i => ∑ j, !![a, b; c, d] i j • ![((1 : Ω), (0 : Ω)), (0, 1)] j) = ![(a, b), (c, d)] := by
    funext i
    fin_cases i <;> simp
  rw [← Matrix.det_fin_two_of]
  exact detLat_of_frame (by rw [LinearIndependent.pair_iff]; simp) (by rw [e]; exact ⟨h, rfl⟩)

end Det

section Eig

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K V} (σ : E →+* K)

theorem eigProj_act (a : 𝓞 E) (x : V) : HT.eigProj ρ σ (ρ a x) = σ (a : E) • HT.eigProj ρ σ x := by
  rw [← HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ x) a]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

variable {X : Submodule A V} {N : ℕ} {t : Fin N → V}

theorem linearIndependent_eigProj (h : HT.IsFreeOn ρ X t) : LinearIndependent K fun i => HT.eigProj ρ σ (t i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => c q.1 * σ (HT.dualInt E q.2)) (by
    rw [Fintype.sum_prod_type, ← hc]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul])
  have h2 : c i * σ (∑ k, HT.dualInt E k * integralBasis E k) = 0 := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [map_mul, ← mul_assoc, h1 (i, k), zero_mul]
  rwa [HT.LatBasic.sum_dualInt_mul, map_one, mul_one] at h2

theorem span_eigProj (h : HT.IsFreeOn ρ X t) :
    Submodule.span K (Set.range fun i => HT.eigProj ρ σ (t i)) = HT.eigSp ρ σ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact HT.LatBasic.eigProj_mem ρ σ _
  · intro x hx
    have h1 := h.2.1
    rw [h.2.2, Submodule.span_span_of_tower] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (h1.ge (Submodule.mem_top (x := x)))
    rw [← HT.LatBasic.eigProj_of_mem hx, ← hc, map_sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    rw [map_smul, eigProj_act]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.1, rfl⟩))

theorem eigQuot_eq_span (h : HT.IsFreeOn ρ X t) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) :
    HT.eigQuot ρ σ X = Submodule.span A (Set.range fun i => HT.eigProj ρ σ (t i)) := by
  apply le_antisymm
  · rw [HT.eigQuot, h.2.2, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := hσ (RingOfIntegers.basis E q.2)
    change HT.eigProj ρ σ _ ∈ _
    rw [eigProj_act, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.1, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨t i, ?_, rfl⟩
    have e : t i = ρ 1 (t i) := by simp
    rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

end Eig

end HodgeDeterminantLattice

namespace HodgeLat

open HodgeDeterminantLattice

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ} (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω)

include 𝓗 in

theorem finiteDimensional : FiniteDimensional Ω V := by
  obtain ⟨-, -, b, hb, -⟩ := 𝓗.vb ⟨genPt ξ, specializes_rfl⟩ trivial
  exact ⟨hb ▸ Submodule.fg_span (Set.finite_range b)⟩

theorem quot_apply (p : Cpt ξ) : 𝓗.quot σ p = HT.eigQuot 𝓗.ρH σ (𝓗.HL p) := rfl

theorem exists_basis_eigSp : ∃ u : Fin r → V × Module.Dual Ω V, LinearIndependent Ω u ∧
    Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ := by
  obtain ⟨U, hU, x, h⟩ := 𝓗.free ⟨genPt ξ, specializes_rfl⟩
  exact ⟨_, linearIndependent_eigProj σ (h _ hU), span_eigProj σ (h _ hU)⟩

theorem quot_isVB (hσ : ∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) :
    (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) := fun p _ => by
  obtain ⟨U, hU, x, h⟩ := 𝓗.free p
  exact ⟨U, hU, _, span_eigProj σ (h p hU), fun q _ hq => ⟨linearIndependent_eigProj σ (h q hq),
    eigQuot_eq_span σ (h q hq) fun a => ⟨⟨_, hσ q a⟩, rfl⟩⟩⟩

theorem det_isVB (hσ : ∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) {u : Fin r → V × Module.Dual Ω V}
    (hu : LinearIndependent Ω u) (hsp : Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ) :
    (detLat (𝓗.quot σ) u).IsVB 1 ⊤ := detLat_isVB (𝓗.quot_isVB σ hσ) hu hsp

theorem degZero_iff {u : Fin r → V × Module.Dual Ω V} (hu : LinearIndependent Ω u)
    (hsp : Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ) (ϖ : Ω) :
    𝓗.DegZero σ ϖ ↔ NumTrivMod (detLat (𝓗.quot σ) u) ϖ :=
  ⟨fun h => h u hu hsp, fun h _ hu' hsp' Γ => hasDeg_detLat hu' hu
    (fun i => by rw [hsp', ← hsp]; exact Submodule.subset_span ⟨i, rfl⟩) (h Γ)⟩

end HodgeLat

namespace HodgeInh

open HodgeDeterminantLattice

section General

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E]

def scal (W : Type) [AddCommGroup W] [Module Ω W] (χ : 𝓞 E →+* Ω) : 𝓞 E →+* Module.End Ω W :=
  (algebraMap Ω (Module.End Ω W)).comp χ

def chi (σ : E →+* Ω) : 𝓞 E →+* Ω := σ.comp (algebraMap (𝓞 E) E)

def actH (σ : E →+* Ω) (bar : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* Module.End Ω (Ω × Module.Dual Ω Ω) :=
  (LinearMap.prodMapRingHom Ω Ω (Module.Dual Ω Ω)).comp
    (RingHom.prod (scal Ω (chi σ)) (scal (Module.Dual Ω Ω) ((chi σ).comp bar.toRingHom)))

omit [NumberField E] in

theorem actH_apply (σ : E →+* Ω) (bar : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) (y : Ω × Module.Dual Ω Ω) :
    actH σ bar a y = (chi σ a * y.1, chi σ (bar a) • y.2) := rfl

def latH (A : Subring Ω) (δ t : Ω) : Submodule A (Ω × Module.Dual Ω Ω) where
  carrier := {y | y.1 / t ∈ A ∧ y.1 / t / δ - t * y.2 1 ∈ A}
  zero_mem' := by simp [A.zero_mem]
  add_mem' := fun {a b} ha hb => ⟨by simpa [add_div] using A.add_mem ha.1 hb.1, by
    convert A.add_mem ha.2 hb.2 using 1
    simp; ring⟩
  smul_mem' := fun c y hy => ⟨by
    convert A.mul_mem c.2 hy.1 using 1
    change (c : Ω) * y.1 / t = _
    ring, by
    convert A.mul_mem c.2 hy.2 using 1
    change (c : Ω) * y.1 / t / δ - t * ((c : Ω) * y.2 1) = _
    ring⟩

theorem mem_latH {A : Subring Ω} {δ t : Ω} {y : Ω × Module.Dual Ω Ω} :
    y ∈ latH A δ t ↔ y.1 / t ∈ A ∧ y.1 / t / δ - t * y.2 1 ∈ A := Iff.rfl

theorem dual_ext {φ ψ : Module.Dual Ω Ω} (h : φ 1 = ψ 1) : φ = ψ := LinearMap.ext_ring h

theorem dual_apply (φ : Module.Dual Ω Ω) (e : Ω) : φ e = e * φ 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

def gen (δ t : Ω) : Ω × Module.Dual Ω Ω := (t, (δ * t)⁻¹ • LinearMap.id)

variable (σ : E →+* Ω) (bar : 𝓞 E ≃+* 𝓞 E) (ω : 𝓞 E)

theorem isFreeOn_latH (A : Subring Ω) (hA : ∀ a, chi σ a ∈ A) (h2 : Module.finrank ℚ E = 2)
    (hω : ω - bar ω ≠ 0) (hdvd : ∀ a, ω - bar ω ∣ a - bar a) {t : Ω} (ht : t ≠ 0) :
    HT.IsFreeOn (actH σ bar) (latH A (chi σ (ω - bar ω)) t) (fun _ : Fin 1 => gen (chi σ (ω - bar ω)) t) := by
  classical
  set δ := chi σ (ω - bar ω) with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ, chi, RingHom.comp_apply, map_ne_zero, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hω
  have hspan : latH A δ t = Submodule.span A (Set.range
      fun q : Fin 1 × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        actH σ bar (RingOfIntegers.basis E q.2) (gen δ t)) := by
    apply le_antisymm
    · have key : ∀ a, actH σ bar a (gen δ t) ∈ Submodule.span A (Set.range
          fun q : Fin 1 × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
            actH σ bar (RingOfIntegers.basis E q.2) (gen δ t)) := by
        intro a
        rw [← (RingOfIntegers.basis E).sum_repr a, map_sum, LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply]
        exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(0, k), rfl⟩)) _
      rintro y ⟨h1, h2⟩
      have e : y = (⟨y.1 / t - (y.1 / t / δ - t * y.2 1) * chi σ ω, A.sub_mem h1 (A.mul_mem h2 (hA ω))⟩ : A) •
          actH σ bar 1 (gen δ t) + (⟨_, h2⟩ : A) • actH σ bar ω (gen δ t) := by
        have hb : chi σ (bar ω) = chi σ ω - δ := by rw [hδ, map_sub]; ring
        refine Prod.ext ?_ (dual_ext ?_)
        · simp [actH_apply, gen, Subring.smul_def]; field_simp; ring
        · simp [actH_apply, gen, Subring.smul_def, hb]; field_simp; ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (key _)) (Submodule.smul_mem _ _ (key _))
    · rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      obtain ⟨n, hn⟩ := hdvd (RingOfIntegers.basis E q.2)
      have hn' := congrArg (chi σ) hn
      rw [map_sub, map_mul, ← hδ] at hn'
      refine ⟨?_, ?_⟩
      · simpa [actH_apply, gen, ht] using hA _
      · convert hA n using 1
        simp [actH_apply, gen]
        field_simp
        linear_combination hn'
  have htop : Submodule.span Ω (latH A δ t : Set (Ω × Module.Dual Ω Ω)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have h1 : gen δ t ∈ latH A δ t := ⟨by simp [gen, ht, A.one_mem], by
      convert A.zero_mem using 1
      simp [gen]; field_simp; ring⟩
    have h2 : ((0, t⁻¹ • LinearMap.id) : Ω × Module.Dual Ω Ω) ∈ latH A δ t := ⟨by simp [A.zero_mem], by
      simp [ht, A.one_mem]⟩
    have e : y = (y.1 / t) • gen δ t + (t * y.2 1 - y.1 / t / δ) • ((0, t⁻¹ • LinearMap.id) : Ω × Module.Dual Ω Ω) := by
      refine Prod.ext ?_ (dual_ext ?_)
      · simp [gen, ht]
      · simp [gen]; field_simp; ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h1))
      (Submodule.smul_mem _ _ (Submodule.subset_span h2))
  refine ⟨?_, htop, hspan⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [hspan, Submodule.span_span_of_tower] at htop
    exact htop.ge
  · rw [Fintype.card_prod, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, h2]
    simp

theorem eigProj_actH (hω : ω - bar ω ≠ 0) (y : Ω × Module.Dual Ω Ω) :
    HT.eigProj (actH σ bar) σ y = (y.1, 0) := by
  have e : y = (y.1, 0) + (0, y.2) := by simp
  conv_lhs => rw [e, map_add]
  rw [HT.LatBasic.eigProj_of_mem (x := (y.1, 0)) (HT.LatBasic.mem_eigSp.2 fun a => by simp [actH_apply, chi]),
    HT.LatBasic.eigProj_of_eigenSub_ne (χ := (chi σ).comp bar.toRingHom) (x := (0, y.2)) ?_
      (GlobalTheory.EigenSplit.mem_eigenSub.2 fun a => by simp [actH_apply]), add_zero]
  intro h
  have := DFunLike.congr_fun h ω
  apply hω
  rw [sub_eq_zero]
  exact RingOfIntegers.coe_injective (σ.injective this)

theorem mem_eigSp_actH (hω : ω - bar ω ≠ 0) (y : Ω × Module.Dual Ω Ω) :
    y ∈ HT.eigSp (actH σ bar) σ ↔ y.2 = 0 := by
  constructor
  · intro h
    have := HT.LatBasic.eigProj_of_mem h
    rw [eigProj_actH σ bar ω hω] at this
    rw [← this]
  · intro h
    have := HT.LatBasic.eigProj_mem (actH σ bar) σ y
    rwa [eigProj_actH σ bar ω hω, ← h] at this

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def hodge (hA : ∀ p a, chi σ a ∈ regAt ξ p) (h2 : Module.finrank ℚ E = 2)
    (hω : ω - bar ω ≠ 0) (hdvd : ∀ a, ω - bar ω ∣ a - bar a) (L : Lat ξ Ω) (HL : Lat ξ (Ω × Module.Dual Ω Ω))
    (hloc : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ t : Ω, t ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      L q = Submodule.span (regAt ξ q) {t} ∧ HL q = latH (regAt ξ q) (chi σ (ω - bar ω)) t) :
    HodgeLat L (scal Ω (chi σ)) bar 1 where
  ρH := actH σ bar
  HL := HL
  act_fst := fun _ _ => rfl
  act_inr := fun a φ => Prod.ext (by simp [actH_apply]) (dual_ext (by
    change chi σ (bar a) * φ 1 = φ (chi σ (bar a) * 1)
    rw [dual_apply φ (_ * 1), mul_one]))
  map_fst := by
    funext p
    obtain ⟨U, hU, t, ht, h⟩ := hloc p
    obtain ⟨h1, h3⟩ := h p hU
    ext y
    simp only [Lat.map, h1, h3, mem_span_iff ht]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hy
      refine ⟨(y, (y / t / chi σ (ω - bar ω) / t) • LinearMap.id), ⟨hy, ?_⟩, rfl⟩
      convert (regAt ξ p).zero_mem using 1
      simp; field_simp; ring
  comap_inr := by
    funext p
    obtain ⟨U, hU, t, ht, h⟩ := hloc p
    obtain ⟨h1, h3⟩ := h p hU
    ext φ
    change ((0, φ) : Ω × Module.Dual Ω Ω) ∈ HL p ↔ ∀ e ∈ L p, φ e ∈ regAt ξ p
    rw [h1, h3, mem_latH]
    simp only [zero_div, zero_mem, true_and, zero_sub, neg_mem_iff, mem_span_iff ht]
    constructor
    · intro hφ e he
      convert mul_mem he hφ using 1
      rw [dual_apply φ e]; field_simp
    · intro hφ
      rw [← dual_apply]
      exact hφ t (by simp [ht, one_mem])
  free := fun p => by
    obtain ⟨U, hU, t, ht, h⟩ := hloc p
    exact ⟨U, hU, _, fun q hq => (h q hq).2 ▸ isFreeOn_latH σ bar ω _ (hA q) h2 hω hdvd ht⟩
  vb := fun p _ => by
    obtain ⟨U, hU, t, ht, h⟩ := hloc p
    rw [Module.finrank_self]
    refine ⟨U, hU, fun _ => t, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
    · rw [Set.range_const, eq_top_iff]
      exact fun y _ => Submodule.mem_span_singleton.2 ⟨y / t, div_mul_cancel₀ _ ht⟩
    · rwa [linearIndependent_unique_iff]
    · rw [Set.range_const, (h q hq).1]

section

variable (hA : ∀ p a, chi σ a ∈ regAt ξ p) (h2 : Module.finrank ℚ E = 2)
    (hω : ω - bar ω ≠ 0) (hdvd : ∀ a, ω - bar ω ∣ a - bar a) (L : Lat ξ Ω) (HL : Lat ξ (Ω × Module.Dual Ω Ω))
    (hloc : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ t : Ω, t ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      L q = Submodule.span (regAt ξ q) {t} ∧ HL q = latH (regAt ξ q) (chi σ (ω - bar ω)) t)

theorem detLat_hodge :
    detLat ((hodge σ bar ω hA h2 hω hdvd L HL hloc).quot σ) (fun _ : Fin 1 => (1, 0)) = L := by
  funext p
  obtain ⟨U, hU, t, ht, h⟩ := hloc p
  have e1 : (hodge σ bar ω hA h2 hω hdvd L HL hloc).quot σ p =
      (L p).map ((LinearMap.inl Ω Ω (Module.Dual Ω Ω)).restrictScalars (regAt ξ p)) := by
    conv_rhs => rw [← (hodge σ bar ω hA h2 hω hdvd L HL hloc).map_fst]
    rw [Lat.map, ← Submodule.map_comp, HodgeLat.quot, Lat.map]
    congr 1
    exact LinearMap.ext fun y => eigProj_actH σ bar ω hω y
  rw [(h p hU).1]
  refine detLat_one _ (by simp) p ht ?_
  rw [e1, (h p hU).1, Submodule.map_span, Set.image_singleton]
  simp

theorem degZero_hodge (ϖ : Ω) : (hodge σ bar ω hA h2 hω hdvd L HL hloc).DegZero σ ϖ ↔ NumTrivMod L ϖ := by
  rw [HodgeLat.degZero_iff _ σ (u := fun _ => (1, 0)) (by rw [linearIndependent_unique_iff]; simp), detLat_hodge]
  ext y
  rw [Set.range_const, Submodule.mem_span_singleton]
  refine Iff.trans ?_ (mem_eigSp_actH σ bar ω hω y).symm
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · exact fun hy => ⟨y.1, Prod.ext (by simp) (by simp [hy])⟩

end

theorem adapted (σ' : E →+* Ω) (hω : ω - bar ω ≠ 0) (h : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) :
    IsAdapted (actH σ bar) σ (p := 1) (q := 0) (fun _ => 1) Fin.elim0 (fun _ => (1, 0)) ∧
    IsAdapted (actH σ bar) σ' (p := 0) (q := 1) Fin.elim0 (fun _ => 1) (fun _ => (0, LinearMap.id)) ∧
    ¬ ∃ u, IsAdapted (actH σ bar) σ (p := 0) (q := 1) Fin.elim0 (fun _ => 1) u := by
  refine ⟨⟨fun _ => (mem_eigSp_actH σ bar ω hω _).2 rfl, fun _ => rfl, fun j => j.elim0⟩,
    ⟨fun _ => HT.LatBasic.mem_eigSp.2 fun a => by simp [actH_apply, chi, h], fun i => i.elim0,
      fun j => ⟨rfl, fun j' => by simp [Subsingleton.elim j j']⟩⟩, ?_⟩
  rintro ⟨u, h1, -, h3⟩
  have := (h3 0).2 0
  rw [(mem_eigSp_actH σ bar ω hω _).1 (h1 _)] at this
  simp at this

example : IsAdapted (scal (Ω × Module.Dual Ω Ω) (chi σ)) σ (p := 1) (q := 1) (fun _ => 1) (fun _ => 1)
      ![(1, 0), (0, LinearMap.id)] ∧
    ¬ IsAdapted (scal (Ω × Module.Dual Ω Ω) (chi σ)) σ (p := 1) (q := 1) (fun _ => 1) (fun _ => 1)
      ![(0, LinearMap.id), (1, 0)] := by
  refine ⟨⟨fun _ => HT.LatBasic.mem_eigSp.2 fun a => rfl, fun i => ?_, fun j => ?_⟩, fun h => ?_⟩
  · fin_cases i
    rfl
  · fin_cases j
    exact ⟨rfl, fun j' => by fin_cases j'; rfl⟩
  · exact zero_ne_one (h.2.1 0)

end General

section Split

variable {Ω : Type} [Field Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem prod_dual_eq {L : Lat ξ Ω} {q : Cpt ξ} {t δ : Ω} (ht : t ≠ 0) (hδ : δ⁻¹ ∈ regAt ξ q)
    (h : L q = Submodule.span (regAt ξ q) {t}) : L.prod L.dual q = latH (regAt ξ q) δ t := by
  ext y
  change y.1 ∈ L q ∧ (∀ e ∈ L q, y.2 e ∈ regAt ξ q) ↔ _
  rw [mem_latH, h]
  simp only [mem_span_iff ht]
  refine and_congr_right fun h1 => ?_
  have h3 : y.1 / t / δ ∈ regAt ξ q := by rw [div_eq_mul_inv _ δ]; exact mul_mem h1 hδ
  constructor
  · intro hφ
    refine sub_mem h3 ?_
    rw [← dual_apply]
    exact hφ t (by simp [ht, one_mem])
  · intro hφ e he
    convert mul_mem he (sub_mem h3 hφ) using 1
    rw [dual_apply y.2 e]; field_simp; ring

theorem loc_of_isVB {L : Lat ξ Ω} (hL : L.IsVB 1 ⊤) (p : Cpt ξ) : ∃ U : X.Opens, p.1 ∈ U ∧ ∃ t : Ω, t ≠ 0 ∧
    ∀ q : Cpt ξ, q.1 ∈ U → L q = Submodule.span (regAt ξ q) {t} := by
  obtain ⟨U, hU, b, -, h⟩ := hL p trivial
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  exact ⟨U, hU, b 0, (h p trivial hU).1.ne_zero 0, fun q hq => hr ▸ (h q trivial hq).2⟩

end Split

section Gauss

abbrev Ki : Type := CyclotomicField 4 ℚ

theorem cyc : IsCyclotomicExtension {4} ℚ Ki := CyclotomicField.isCyclotomicExtension 4 ℚ

attribute [local instance] cyc

theorem cm : IsCMField Ki := IsCyclotomicExtension.Rat.isCMField Ki (S := {4}) ⟨4, rfl, by norm_num⟩

attribute [local instance] cm

def cj : 𝓞 Ki ≃+* 𝓞 Ki := (IsCMField.ringOfIntegersComplexConj Ki).toRingEquiv

theorem finrank_Ki : Module.finrank ℚ Ki = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Ki (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

theorem exists_i : ∃ ω : 𝓞 Ki, ω - cj ω = 2 * ω ∧ ω ≠ 0 ∧ ∀ a, ω - cj ω ∣ a - cj a := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ Ki
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ Ki := cyc
  have hζ' : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ Ki) (2 ^ 2) := hζ
  set ω : 𝓞 Ki := hζ'.toInteger with hω
  have htop : Algebra.adjoin ℤ {ω} = ⊤ := by
    have := hζ'.integralPowerBasisOfPrimePow.adjoin_gen_eq_top
    rwa [IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen] at this
  have hdvd : ∀ a, ω - cj ω ∣ a - cj a := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ {ω} := htop ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add, add_sub_add_comm]; exact dvd_add hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul, show x * y - cj x * cj y = (x - cj x) * y + cj x * (y - cj y) by ring]
      exact dvd_add (hx.mul_right _) (hy.mul_left _)
  have hsq : ω ^ 2 = -1 := by
    have h := hζ'.toInteger_isPrimitiveRoot
    exact (h.pow (by norm_num) (show 2 ^ 2 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
  have hne : ω - cj ω ≠ 0 := by
    intro h
    apply IsCMField.complexConj_ne_one Ki
    have h1 : ∀ a : 𝓞 Ki, IsCMField.complexConj Ki (a : Ki) = a := fun a => by
      have := hdvd a
      rw [h, zero_dvd_iff, sub_eq_zero] at this
      conv_rhs => rw [this]
      exact (IsCMField.coe_ringOfIntegersComplexConj Ki a).symm
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 Ki) x
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have hsq' : cj ω ^ 2 = -1 := by rw [← map_pow, hsq, map_neg, map_one]
  have : (ω - cj ω) * (ω + cj ω) = 0 := by linear_combination hsq - hsq'
  have h3 := (mul_eq_zero.1 this).resolve_left hne
  refine ⟨ω, by linear_combination -h3, fun h => by simp [h] at hsq, hdvd⟩

theorem not_isUnit_two : ¬ IsUnit (2 : 𝓞 Ki) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ)
  rw [show (2 : 𝓞 Ki) = algebraMap ℤ _ 2 by simp, Algebra.norm_algebraMap, RingOfIntegers.rank, finrank_Ki,
    Int.isUnit_iff] at h1
  norm_num at h1

theorem exists_nonsplit : ∃ 𝓗 : HodgeLat (ξ := CoordModel.gen (𝓞 Ki) Ki)
    (fun p => Submodule.span (regAt _ p) {(1 : Ki)}) (scal Ki (chi (RingHom.id Ki))) cj 1,
    (∃ p, ((1, 0) : Ki × Module.Dual Ki Ki) ∉ 𝓗.HL p ∧ ((1, 0) : Ki × Module.Dual Ki Ki) ∈ 𝓗.quot (RingHom.id Ki) p) ∧
      ∀ ϖ, 𝓗.DegZero (RingHom.id Ki) ϖ := by
  obtain ⟨ω, h2, h0, hdvd⟩ := exists_i
  have hω : ω - cj ω ≠ 0 := by rw [h2]; exact mul_ne_zero two_ne_zero h0
  have hA : ∀ p a, chi (RingHom.id Ki) a ∈ regAt (CoordModel.gen (𝓞 Ki) Ki) p := fun p a =>
    CoordModel.algebraMap_mem_regAt _ _ p a
  refine ⟨hodge (RingHom.id Ki) cj ω hA finrank_Ki hω hdvd _
    (fun p => latH _ (chi (RingHom.id Ki) (ω - cj ω)) 1)
    (fun p => ⟨⊤, trivial, 1, one_ne_zero, fun _ _ => ⟨rfl, rfl⟩⟩), ?_,
    fun ϖ => (degZero_hodge _ _ _ _ _ _ _ _ _ _ ϖ).2 (numTrivMod_of_gen (fun _ => ⟨one_ne_zero, rfl⟩) ϖ)⟩
  obtain ⟨m, hm, hm2⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 not_isUnit_two)
  refine ⟨⟨⟨m, hm.isPrime⟩, CoordModel.spec_all _ _ _⟩, ?_, ?_⟩
  · rintro ⟨-, h⟩
    obtain ⟨r, s, hs, e⟩ := (CoordModel.mem_regAt _ _ _ _).1 h
    apply hs
    have h1 : algebraMap (𝓞 Ki) Ki (ω - cj ω) ≠ 0 := by
      rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    have : s = (ω - cj ω) * r := by
      apply FaithfulSMul.algebraMap_injective (𝓞 Ki) Ki
      rw [map_mul, ← e]
      simp only [chi, RingHom.comp_apply, RingHom.id_apply, LinearMap.zero_apply]
      field_simp
      ring
    rw [this, h2]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hm2)
  · refine ⟨gen (chi (RingHom.id Ki) (ω - cj ω)) 1, ⟨by simp [gen, one_mem], by simp [gen, zero_mem]⟩, ?_⟩
    exact eigProj_actH _ cj ω hω _

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_line (o : Type) [CommRing o] [IsDomain o] [Algebra Ki o] (k : Type) [Field k] [Algebra o k] (ϖ : o)
    (hϖ : algebraMap o k ϖ = 0) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra o Ω) (σ : Ki →+* Ω) (ξ : Spec (CommRingCat.of Ω) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Option (Fin 1)) o)), IsCptGen ξ ∧ ∀ d : ℕ, d ≠ 0 →
      ∃ (L : Lat ξ Ω) (𝓗 : HodgeLat L (scal Ω (chi σ)) cj 1), ¬ 𝓗.DegZero σ (algebraMap o Ω ϖ) := by
  obtain ⟨ω, h2, h0, hdvd⟩ := exists_i
  have hω : ω - cj ω ≠ 0 := by rw [h2]; exact mul_ne_zero two_ne_zero h0
  have hi := IsFractionRing.injective (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o))
  have hx : ∀ c : Option (Fin 1), algebraMap (MvPolynomial (Fin 1) o)
      (FractionRing (MvPolynomial (Fin 1) o)) (c.elim 1 MvPolynomial.X) ≠ 0 := fun c => by
    rw [map_ne_zero_iff _ hi]
    cases c with
    | none => exact one_ne_zero
    | some j => exact MvPolynomial.X_ne_zero j
  have hinj : ∀ (d : ℕ) (g : MvPolynomial (Option (Fin 1)) o), g.IsHomogeneous d →
      MvPolynomial.aeval (fun j : Option (Fin 1) => algebraMap (MvPolynomial (Fin 1) o)
        (FractionRing (MvPolynomial (Fin 1) o)) (j.elim 1 MvPolynomial.X)) g = 0 → g = 0 := fun d g hg h => by
    exact ProjCoord.eq_zero_of_dehom hg ((map_eq_zero_iff _ hi).1
      ((MvPolynomial.aeval_algebraMap_apply _ _ g).symm.trans h))
  obtain ⟨ξ, hT, e⟩ := ProjectiveLinePlaces.coordTie_charts _ hx none hinj (fun a => by
    have key : ∀ p : MvPolynomial (Fin 1) o, algebraMap _ (FractionRing (MvPolynomial (Fin 1) o)) p ∈
        Algebra.adjoin o (Set.range fun j : Option (Fin 1) =>
          algebraMap (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o))
            (j.elim 1 MvPolynomial.X) /
          algebraMap (MvPolynomial (Fin 1) o) (FractionRing (MvPolynomial (Fin 1) o)) 1) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C r =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact Subalgebra.algebraMap_mem _ r
      | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul]
        exact mul_mem hp (Algebra.subset_adjoin ⟨some i, by simp⟩)
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin 1) o) a
    have h0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hv)
    exact ⟨_, key u, _, key v, h0, div_mul_cancel₀ _ h0⟩)
  obtain ⟨Γ, hΓ⟩ := FibLine.line_deg _ hx hinj ξ hT.gen e k ϖ hϖ
  let σ : Ki →+* FractionRing (MvPolynomial (Fin 1) o) := (algebraMap o _).comp (algebraMap Ki o)
  have hσ : ∀ p a, σ a ∈ regAt ξ p := fun p a => by
    obtain ⟨c, hc⟩ := hT.cover p
    exact (hT.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ _) p hc
  refine ⟨_, inferInstance, inferInstance, σ, ξ, hT.gen, fun d hd => ?_⟩
  obtain ⟨L, hL⟩ := Lat.exists_line hT d
  refine ⟨L, hodge σ cj ω (fun p a => hσ p _) finrank_Ki hω hdvd L (L.prod L.dual) (fun p => ?_), fun h => hd ?_⟩
  · obtain ⟨U, hU, t, ht, h⟩ := loc_of_isVB (Lat.isVB_line hT hL) p
    refine ⟨U, hU, t, ht, fun q hq => ⟨h q hq, prod_dual_eq ht ?_ (h q hq)⟩⟩
    rw [chi, RingHom.comp_apply, ← map_inv₀]
    exact hσ q _
  · exact_mod_cast ((hΓ d L hL 0).1 ((degZero_hodge _ _ _ _ _ _ _ _ _ _ _).1 h Γ)).symm

theorem exists_not_degZero : ∃ (X : Scheme.{0}) (Ω : Type) (_ : Field Ω) (σ : Ki →+* Ω) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω)
    (L : Lat ξ Ω) (𝓗 : HodgeLat L (scal Ω (chi σ)) cj 1), IsCptGen ξ ∧ ¬ 𝓗.DegZero σ ϖ := by
  letI : Algebra (Polynomial Ki) Ki := (Polynomial.evalRingHom 0).toAlgebra
  obtain ⟨Ω, _, _, σ, ξ, hξ, h⟩ := exists_line (Polynomial Ki) Ki Polynomial.X (Polynomial.eval_X (x := (0 : Ki)))
  obtain ⟨L, 𝓗, h⟩ := h 1 one_ne_zero
  exact ⟨_, Ω, _, σ, ξ, _, L, 𝓗, hξ, h⟩

end Gauss

end HodgeInh

end GlobalTheory.CompanionTheory.Ar.Flat
