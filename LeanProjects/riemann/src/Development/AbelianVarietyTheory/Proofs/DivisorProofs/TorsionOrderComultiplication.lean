import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTorsionPrechartCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslateOrderStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

section Lemmas

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ}

theorem torsMap_inv' {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (z : Tors G N B) : torsMap φ z⁻¹ = (torsMap φ z)⁻¹ :=
  Subtype.ext (GrpObj.comp_inv _ _)

theorem torsMap_one' {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C) :
    torsMap φ (1 : Tors G N B) = 1 :=
  Subtype.ext (MonObj.comp_one _)

theorem torsMap_mul' {B C : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
    (x y : Tors G N B) : torsMap φ (x * y) = torsMap φ x * torsMap φ y :=
  Subtype.ext (MonObj.comp_mul _ _ _)

theorem torsMap_comp' {B C D : Type} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (φ : C →ₐ[R] D) (ψ : B →ₐ[R] C) (z : Tors G N B) : torsMap (φ.comp ψ) z = torsMap φ (torsMap ψ z) :=
  Subtype.ext (by simp only [torsMap_val]; rw [← spOver_comp, Category.assoc])

theorem tors_pow_N {B : Type} [CommRing B] [Algebra R B] (x : Tors G N B) : x ^ N = 1 :=
  Subtype.ext x.2

theorem finite_tors_of_cover {K : Type} [Field K] [Algebra R K] (Idx : Type) [Finite Idx] (q : Idx → PrimeSpectrum R)
    (c : ∀ i, PreChart G N (q i)) (hcov : ∀ z : Tors G N K, ∃ i, Set.range z.1.left ⊆ (c i).W)
    (hfin : ∀ i, Finite ((c i).C →ₐ[R] K)) : Finite (Tors G N K) := by
  have h : (Set.univ : Set (Tors G N K)) ⊆ ⋃ i, Set.range (fun ψ : (c i).C →ₐ[R] K => torsMap ψ (c i).j) := by
    intro z _
    obtain ⟨i, hi⟩ := hcov z
    obtain ⟨ψ, -, hψ⟩ := ((c i).bij K).surjOn hi
    exact Set.mem_iUnion.2 ⟨i, ψ, hψ⟩
  exact Set.finite_univ_iff.1 ((Set.finite_iUnion fun i => Set.finite_range _).subset h)

variable (K : Type) [Field K] [Algebra R K]

def chartMon {q : PrimeSpectrum R} (c : PreChart G N q) (hc : c.IsGrp) (hr : algebraMap R K c.r ≠ 0) :
    Submonoid (Tors G N K) where
  carrier := Set.range fun ψ : c.C →ₐ[R] K => torsMap ψ c.j
  one_mem' := by
    obtain ⟨ψ₀, h₀⟩ := hc.1
    let ρ : Localization.Away c.r →ₐ[R] K :=
      IsLocalization.liftAlgHom (M := Submonoid.powers c.r) (f := Algebra.ofId R K)
        (fun y => by
          obtain ⟨n, hn⟩ := y.2
          show IsUnit (algebraMap R K y)
          rw [← hn, map_pow]
          exact (IsUnit.mk0 _ hr).pow n)
    exact ⟨ρ.comp ψ₀, by show torsMap (ρ.comp ψ₀) c.j = 1; rw [torsMap_comp', h₀, torsMap_one']⟩
  mul_mem' := by
    rintro _ _ ⟨ψ, rfl⟩ ⟨ψ', rfl⟩
    obtain ⟨ψ'', h⟩ := hc.2 K ψ ψ'
    exact ⟨ψ'', h⟩

def chartSub {q : PrimeSpectrum R} (c : PreChart G N q) (hc : c.IsGrp) (hr : algebraMap R K c.r ≠ 0) (hN : N ≠ 0) :
    Subgroup (Tors G N K) :=
  { chartMon K c hc hr with
    inv_mem' := fun {x} hx => by
      have h : x * x ^ (N - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN), tors_pow_N]
      rw [← eq_inv_of_mul_eq_one_right h]
      exact (chartMon K c hc hr).pow_mem hx _ }

end Lemmas

end GlobalTheory.GroupBplus.Aff

namespace GlobalTheory.GroupBplus.Aff

theorem ord_comul_local : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ f ∈ ord G N K, ∃ (k : ℕ) (T : ord G N K ⊗[R] ord G N K), ∀ a b : Tors G N K, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val) ((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val) (fun _ _ => .all _ _) T = algebraMap R K c.r ^ k * f (a * b) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN q c hc f hf
  classical
  obtain ⟨Idx, hIdx, qs, cs, hcov⟩ := GlobalTheory.T.exists_finite_torsion_prechart_cover R K G hG N hN
  haveI : Finite (Tors G N K) := finite_tors_of_cover Idx qs cs (hcov K)
    (fun i => (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN (qs i) (cs i)).1)
  have hr : algebraMap R K c.r ≠ 0 := by
    intro h
    apply c.hr
    rw [(IsFractionRing.injective R K) (h.trans (map_zero _).symm)]
    exact q.asIdeal.zero_mem
  let H : Subgroup (Tors G N K) := chartSub K c hc hr hN
  haveI : Fintype (Tors G N K ⧸ H) := Fintype.ofFinite _
  let pt : (c.C →ₐ[R] K) → Tors G N K := fun ψ => torsMap ψ c.j
  have hinj : Function.Injective pt := fun ψ ψ' h => (c.bij K).injOn (Set.mem_univ _) (Set.mem_univ _) h
  have hcoset : ∀ (α : Tors G N K ⧸ H) (a : Tors G N K), ((a : Tors G N K ⧸ H) = α) ↔ ∃ ψ, a = α.out * pt ψ := by
    intro α a
    conv_lhs => rw [← QuotientGroup.out_eq' α]
    rw [eq_comm, QuotientGroup.eq]
    constructor
    · rintro ⟨ψ, hψ⟩
      exact ⟨ψ, by rw [show pt ψ = α.out⁻¹ * a from hψ, mul_inv_cancel_left]⟩
    · rintro ⟨ψ, rfl⟩
      exact ⟨ψ, by show pt ψ = _; rw [inv_mul_cancel_left]⟩
  let ev : Tors G N K → Tors G N K → (ord G N K ⊗[R] ord G N K →ₐ[R] K) := fun a b =>
    Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val)
      ((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val) (fun _ _ => .all _ _)
  let Φ : ord G N K ⊗[R] ord G N K →ₗ[R] (Tors G N K → Tors G N K → K) :=
    LinearMap.pi fun a => LinearMap.pi fun b => (ev a b).toLinearMap
  have hΦ : ∀ T a b, Φ T a b = ev a b T := fun _ _ _ => rfl
  let P := LinearMap.range Φ
  suffices h : ∃ k : ℕ, c.r ^ k • (fun a b : Tors G N K => f (a * b)) ∈ P by
    obtain ⟨k, T, hT⟩ := h
    refine ⟨k, T, fun a b => ?_⟩
    have h1 := congrFun (congrFun hT a) b
    rw [hΦ] at h1
    rw [show ev a b T = _ from h1, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_pow]
  have hsum : ∀ (Ix : Type) (S : Finset Ix) (v : Ix → (Tors G N K → Tors G N K → K)),
      (∀ i ∈ S, ∃ k : ℕ, c.r ^ k • v i ∈ P) → ∃ k : ℕ, c.r ^ k • ∑ i ∈ S, v i ∈ P := by
    intro Ix S v hv
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by rw [Finset.sum_empty, smul_zero]; exact P.zero_mem⟩
    | insert i S hi ih =>
      obtain ⟨k1, h1⟩ := hv i (Finset.mem_insert_self _ _)
      obtain ⟨k2, h2⟩ := ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
      refine ⟨k1 + k2, ?_⟩
      rw [Finset.sum_insert hi, smul_add]
      refine P.add_mem ?_ ?_
      · rw [pow_add, mul_comm, mul_smul]; exact P.smul_mem _ h1
      · rw [pow_add, mul_smul]; exact P.smul_mem _ h2

  have hpiece : ∀ s t : Tors G N K, ∃ k : ℕ, c.r ^ k • (fun a b : Tors G N K =>
      if (∃ ψ, a = s * pt ψ) ∧ (∃ ψ, b = t * pt ψ) then f (a * b) else 0) ∈ P := by
    intro s t
    obtain ⟨σ, hσ, hσf⟩ := hf (s * t)
    have ha0 : ∀ ψ : c.C →ₐ[R] K, ψ (σ c.C c.j) = f (s * t * pt ψ) := fun ψ =>
      (hσ c.C K ψ c.j).symm.trans (hσf _)
    obtain ⟨ψ'', hψ''⟩ := hc.2 (c.C ⊗[R] c.C) Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
    have hA : ∀ ψ₁ ψ₂ : c.C →ₐ[R] K,
        Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => .all _ _) (ψ'' (σ c.C c.j)) = f (s * t * (pt ψ₁ * pt ψ₂)) := by
      intro ψ₁ ψ₂
      rw [← AlgHom.comp_apply, ha0]
      congr 2
      show torsMap (((Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => .all _ _))).comp ψ'') c.j = _
      have hL : (Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => .all _ _)).comp
          (Algebra.TensorProduct.includeLeft : c.C →ₐ[R] c.C ⊗[R] c.C) = ψ₁ :=
        AlgHom.ext fun x => by simp
      have hR : (Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => .all _ _)).comp
          (Algebra.TensorProduct.includeRight : c.C →ₐ[R] c.C ⊗[R] c.C) = ψ₂ :=
        AlgHom.ext fun x => by simp
      rw [torsMap_comp', hψ'', torsMap_mul', ← torsMap_comp', ← torsMap_comp', hL, hR]
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset (ψ'' (σ c.C c.j))
    choose k1 g1 hg1 using fun u => GlobalTheory.T.prechart_translate_order R K G hG N hN q c hc s u
    choose k2 g2 hg2 using fun u => GlobalTheory.T.prechart_translate_order R K G hG N hN q c hc t u
    let K1 := S.sup fun x => k1 x.1
    let K2 := S.sup fun x => k2 x.2
    let T : ord G N K ⊗[R] ord G N K := ∑ x ∈ S,
      (⟨c.r ^ (K1 - k1 x.1) • g1 x.1, (ord G N K).smul_mem (hg1 x.1).1 _⟩ : ord G N K) ⊗ₜ
      (⟨c.r ^ (K2 - k2 x.2) • g2 x.2, (ord G N K).smul_mem (hg2 x.2).1 _⟩ : ord G N K)
    refine ⟨K1 + K2, T, ?_⟩
    funext a b
    rw [hΦ, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def]
    simp only [T, ev, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Subalgebra.coe_val,
      Pi.evalAlgHom_apply, Pi.smul_apply]
    simp only [Algebra.smul_def]
    by_cases hab : (∃ ψ, a = s * pt ψ) ∧ (∃ ψ, b = t * pt ψ)
    · rw [if_pos hab]
      obtain ⟨⟨ψ₁, rfl⟩, ⟨ψ₂, rfl⟩⟩ := hab
      have e1 : ∀ x ∈ S, algebraMap R K (c.r ^ (K1 - k1 x.1)) * g1 x.1 (s * pt ψ₁) = algebraMap R K c.r ^ K1 * ψ₁ x.1 := by
        intro x hx
        rw [(hg1 x.1).2.1, map_pow, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := fun x => k1 x.1) hx)]
      have e2 : ∀ x ∈ S, algebraMap R K (c.r ^ (K2 - k2 x.2)) * g2 x.2 (t * pt ψ₂) = algebraMap R K c.r ^ K2 * ψ₂ x.2 := by
        intro x hx
        rw [(hg2 x.2).2.1, map_pow, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := fun x => k2 x.2) hx)]
      rw [Finset.sum_congr rfl fun x hx => by rw [e1 x hx, e2 x hx]]
      have hsumA := hA ψ₁ ψ₂
      rw [hS, map_sum] at hsumA
      simp only [Algebra.TensorProduct.lift_tmul] at hsumA
      rw [map_pow, pow_add, show (s * pt ψ₁) * (t * pt ψ₂) = s * t * (pt ψ₁ * pt ψ₂) from mul_mul_mul_comm _ _ _ _,
        ← hsumA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    · rw [if_neg hab, mul_zero]
      refine Finset.sum_eq_zero fun x _ => ?_
      rcases not_and_or.1 hab with ha | hb
      · rw [(hg1 x.1).2.2 a (fun ψ h => ha ⟨ψ, h⟩), mul_zero, zero_mul]
      · rw [(hg2 x.2).2.2 b (fun ψ h => hb ⟨ψ, h⟩), mul_zero, mul_zero]

  let v : (Tors G N K ⧸ H) × (Tors G N K ⧸ H) → (Tors G N K → Tors G N K → K) := fun p a b =>
    if ((a : Tors G N K ⧸ H), (b : Tors G N K ⧸ H)) = p then f (a * b) else 0
  have hv : (fun a b : Tors G N K => f (a * b)) = ∑ p ∈ Finset.univ, v p := by
    funext a b
    simp only [Finset.sum_apply, v, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hv]
  refine hsum _ _ v fun p _ => ?_
  obtain ⟨k, hk⟩ := hpiece p.1.out p.2.out
  refine ⟨k, ?_⟩
  convert hk using 3
  simp only [v, Prod.ext_iff, hcoset]

end GlobalTheory.GroupBplus.Aff

open GlobalTheory.GroupBplus.Aff in

theorem GlobalTheory.GroupBplus.Aff.ord_hopf_closed : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → (∀ f ∈ ord G N K, ∃ T : ord G N K ⊗[R] ord G N K, ∀ a b : Tors G N K, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val) ((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val) (fun _ _ => .all _ _) T = f (a * b)) ∧ (∀ f ∈ ord G N K, (fun a => f a⁻¹) ∈ ord G N K) ∧ ∀ f ∈ ord G N K, ∃ c : R, algebraMap R K c = f 1 := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    let I : Ideal R :=
      { carrier := {x | ∃ T : ord G N K ⊗[R] ord G N K, ∀ a b : Tors G N K, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val) ((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val) (fun _ _ => .all _ _) T = algebraMap R K x * f (a * b)}
        add_mem' := by
          rintro x y ⟨T, hT⟩ ⟨T', hT'⟩
          exact ⟨T + T', fun a b => by rw [map_add, hT, hT', map_add, add_mul]⟩
        zero_mem' := ⟨0, fun a b => by rw [map_zero, map_zero, zero_mul]⟩
        smul_mem' := by
          rintro c x ⟨T, hT⟩
          exact ⟨c • T, fun a b => by rw [map_smul, hT, smul_eq_mul, map_mul, Algebra.smul_def, _root_.mul_assoc]⟩ }
    have htop : I = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
      let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
      obtain ⟨c⟩ := GlobalTheory.T.exists_torsion_prechart R K G hG N hN q
      obtain ⟨k, T, hT⟩ := ord_comul_local R K G hG N hN q c (GlobalTheory.T.torsion_prechart_group R K G hG N hN q c) f hf
      have hmem : c.r ^ k ∈ I := ⟨T, fun a b => by rw [hT, map_pow]⟩
      exact c.hr (hm.isPrime.mem_of_pow_mem k (hIm hmem))
    obtain ⟨T, hT⟩ : (1 : R) ∈ I := htop ▸ Submodule.mem_top
    exact ⟨T, fun a b => by rw [hT, map_one, _root_.one_mul]⟩
  · intro f hf s
    obtain ⟨σ, hσ, hσf⟩ := hf s⁻¹
    refine ⟨fun B _ _ z => σ B z⁻¹, fun B C _ _ _ _ φ z => ?_, fun x => ?_⟩
    · show σ C (torsMap φ z)⁻¹ = φ (σ B z⁻¹)
      rw [← torsMap_inv', hσ]
    · show σ K x⁻¹ = f (s * x)⁻¹
      rw [hσf, mul_inv]
  · intro f hf
    obtain ⟨σ, hσ, hσf⟩ := hf 1
    refine ⟨σ R 1, ?_⟩
    have h1 := hσ R K (Algebra.ofId R K) 1
    rw [torsMap_one'] at h1
    rw [← _root_.one_mul (1 : Tors G N K), ← hσf, h1]
    rfl
