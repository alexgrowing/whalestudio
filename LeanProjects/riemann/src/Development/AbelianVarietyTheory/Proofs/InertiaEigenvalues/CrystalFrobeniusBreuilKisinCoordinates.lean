import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysFrobCoord

theorem span_range_eq_top {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  set S := Submodule.span B (Set.range u)
  obtain ⟨w, -, hu⟩ := h (N ⧸ S) 0
  have h1 := hu S.mkQ (fun x => by
    simpa using (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, rfl⟩))
  have h2 := hu 0 (fun x => by simp)
  rw [eq_top_iff]
  intro y _
  have : S.mkQ y = 0 := by rw [h1, ← h2]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem frac_indep {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    {z : LocalizedModule (Submonoid.powers d) M} {n n' : M} {k k' : ℕ} (h : IsFrac d z n k)
    (h' : IsFrac d z n' k') {b : B} (hb : lam n' = J d ^ k' * b) : lam n = J d ^ k * b := by
  unfold IsFrac at h h'
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := LocalizedModule.mk_eq.1 (h.symm.trans h')
  have h2 := congrArg lam hs
  simp only [Submonoid.smul_def, hlam, map_pow, hb] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero s hd) h2
  refine mul_left_cancel₀ (pow_ne_zero k' hd) ?_
  rw [h3]; ring

theorem frac_formula {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (φ : A →+* A)
    (Φ : M →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) M)
    (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    (F : M →+ B) (hF : ∀ r y, F (r • y) = J (φ r) * F y) (S : Set M) (hS : Submodule.span A S = ⊤)
    (h0 : ∀ y ∈ S, ∀ n k, IsFrac d (Φ y) n k → lam n = J d ^ k * F y) (y n : M) (k : ℕ)
    (h : IsFrac d (Φ y) n k) : lam n = J d ^ k * F y := by
  have key : ∀ y ∈ Submodule.span A S, ∃ n k, IsFrac d (Φ y) n k ∧ lam n = J d ^ k * F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, hn⟩ := exists_isFrac d (Φ y)
      exact ⟨n, k, hn, h0 y hy n k hn⟩
    | zero => exact ⟨0, 0, by simp [IsFrac], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, k, hn, en⟩ := hx
      obtain ⟨m, j, hm, em⟩ := hy
      refine ⟨d ^ j • n + d ^ k • m, k + j, ?_, ?_⟩
      · unfold IsFrac at hn hm ⊢
        rw [map_add, hn, hm, LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add d k j).symm
      · rw [map_add, hlam, hlam, en, em, map_add, map_pow, map_pow]; ring
    | smul r x _ hx =>
      obtain ⟨n, k, hn, en⟩ := hx
      refine ⟨φ r • n, k, ?_, ?_⟩
      · unfold IsFrac at hn ⊢
        rw [map_smulₛₗ, hn, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]
      · rw [hlam, hF, en]; ring
  obtain ⟨n', k', h', e'⟩ := key y (hS ▸ Submodule.mem_top)
  exact frac_indep d J hd lam hlam h h' e'

section Maps

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem coe_toAc_eis (τ : ZMod a) : (toAc t K (eis l a e) τ : K⟦X⟧) = E K l e := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  rw [eis, map_add, map_pow, hX, map_natCast]
  simp [E]

end Maps

theorem frob_in_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c _ hc PP hl p J g φ₂ hJp hJφ hφg hg lam hlam hlamtr y n k h τ i
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg constantCoeff h)
  have hJE : J τ (p.f (eis l a e)) = g (frob K l (E K l e)) := by
    rw [hJp, ← frob_toAc, coe_toAc_eis]
  have hJE0 : g (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hg, map_ne_zero_iff _ (frob_injective l)]; exact hE
  let lam' : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => lam y τ i, map_zero' := by simp, map_add' := by simp }
  let F : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i
      map_zero' := by simp [Matrix.mulVec, dotProduct]
      map_add' := by simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  have hJl : J τ (l : PP.A) = l := map_natCast _ _
  have := frac_formula (l : PP.A) PP.D.φ (EE.Φ PP ⟨l, hl⟩) (J τ) (hJl ▸ hl2) lam'
    (fun r y => hlam r y τ i) F ?_ _ (span_range_eq_top (EE.tr_bc p)) ?_ y n k h
  · rw [hJl] at this; exact this
  · intro r y
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlam, map_mul, hJφ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro _ ⟨x, rfl⟩ n k h
    obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x)
    obtain ⟨r, hr⟩ := EE.Φ_nat p ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ x m' k' n k hm' h
    have h1 := congrArg (fun y => lam y τ i) hr
    simp only [hlam, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hJE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hJE0 hl2)))
    rw [hlamtr, hc x m' k' hm'] at h2
    rw [hJl]
    refine mul_left_cancel₀ (pow_ne_zero k' hJE0) ?_
    change _ * lam n τ i = _
    rw [← h2]
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlamtr, hφg,
      PhiMod.phi_apply, frobV_apply, map_mul, map_pow, map_sum, Matrix.map_apply]
    ring

end GlobalTheory.CrysFrobCoord
