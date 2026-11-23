import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearRelationSectionsSpanEqStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.GlueSpan

theorem glue_rules {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (ea eb : ι → ℕ) {N : ℕ} (t g : Fin N → Rules pts)
    (ht : ∀ i, t i ∈ secW pts mapR borR eb)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    (hg : ∀ i, g i ∈ secW pts mapR borR (ea + eb)) (hc : ∀ i i', g i * t i' = g i' * t i) :
    ∃ h ∈ secW pts mapR borR ea, ∀ i, h * t i = g i := by
  classical
  have hs0 : ∀ (p : TRing K) (y : pts p.R), ∃ s : Fin N → p.R, ∑ i, s i * t i p y = 1 := by
    intro p y
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      ((hunit p y).symm ▸ Submodule.mem_top (x := (1 : p.R)))
    exact ⟨s, by simpa [smul_eq_mul] using hs⟩
  choose s hs using hs0
  have hc' : ∀ (p : TRing K) (y : pts p.R) i i', g i p y * t i' p y = g i' p y * t i p y :=
    fun p y i i' => congrFun (congrFun (hc i i') p) y
  have indep : ∀ (p : TRing K) (y : pts p.R) (s' : Fin N → p.R), ∑ i, s' i * t i p y = 1 →
      ∑ i, s' i * g i p y = ∑ i, s p y i * g i p y := by
    intro p y s' h'
    calc ∑ i, s' i * g i p y = (∑ i, s' i * g i p y) * (∑ i', s p y i' * t i' p y) := by rw [hs, mul_one]
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i p y * t i' p y) := by
          rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i' p y * t i p y) := by simp_rw [hc']
      _ = (∑ i', s p y i' * g i' p y) * (∑ i, s' i * t i p y) := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]; refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, s p y i * g i p y := by rw [h', mul_one]
  let h : Rules pts := fun p y => ∑ i, s p y i * g i p y
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro p q φ y z hyz
    have e1 : ∑ i, φ (s p y i) * t i q z = 1 := by
      simp_rw [(ht _).1 p q φ y z hyz, ← map_mul, ← map_sum, hs, map_one]
    show ∑ i, s q z i * g i q z = φ (∑ i, s p y i * g i p y)
    rw [← indep q z _ e1, map_sum]
    simp_rw [(hg _).1 p q φ y z hyz, map_mul]
  · intro p u y y' hyy
    have hw : ∀ e : ι → ℕ, wchar e u = ((∏ i, u i ^ e i : (p.R)ˣ) : p.R) := by
      intro e; simp [wchar, Units.coe_prod]
    have hadd : wchar (ea + eb) u = wchar ea u * wchar eb u := by
      simp only [wchar, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    set v : (p.R)ˣ := ∏ i, u i ^ eb i with hv
    have e1 : ∑ i, (s p y i * ((v⁻¹ : (p.R)ˣ) : p.R)) * t i p y' = 1 := by
      simp_rw [(ht _).2 p u y y' hyy, hw eb, ← hv]
      rw [← hs p y]; refine Finset.sum_congr rfl fun i _ => ?_
      calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * ((v : p.R) * t i p y)
          = s p y i * t i p y * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
        _ = s p y i * t i p y := by rw [Units.inv_mul, mul_one]
    show ∑ i, s p y' i * g i p y' = wchar ea u * ∑ i, s p y i * g i p y
    rw [← indep p y' _ e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hg _).2 p u y y' hyy, hadd, hw eb, ← hv]
    calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * (wchar ea u * (v : p.R) * g i p y)
        = wchar ea u * (s p y i * g i p y) * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
      _ = wchar ea u * (s p y i * g i p y) := by rw [Units.inv_mul, mul_one]
  · intro i
    funext p y
    show (∑ i', s p y i' * g i' p y) * t i p y = g i p y
    calc (∑ i', s p y i' * g i' p y) * t i p y = ∑ i', s p y i' * (g i' p y * t i p y) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i', s p y i' * (g i p y * t i' p y) := by simp_rw [hc']
      _ = g i p y * ∑ i', s p y i' * t i' p y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = g i p y := by rw [hs, mul_one]

theorem glue_frPt : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ)
    (t g : Fin N → Rul (T.Q.Xo j) T.Q.c), (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) →
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    (∀ i, g i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) → (∀ i i', g i * t i' = g i' * t i) →
    ∃ h ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ i, h * t i = g i := by
  intro D T j a b n m N t g ht hunit hg hc
  have hg' : ∀ i, g i ∈ secW (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
      (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n + ex (T.Q.Dw j) b m) := by
    intro i; have := hg i; unfold sec at this; rwa [ex_add] at this
  exact glue_rules (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n) (ex (T.Q.Dw j) b m) t g ht hunit hg' hc

theorem exists_evalAt_ne_zero {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    {N : ℕ} (t : Fin N → Rules pts)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    {S : Type} [CommRing S] [Nontrivial S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    ∃ i, evalAt pts mapR (t i) y ≠ 0 := by
  unfold evalAt
  simp only [dif_pos h]
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    ((hunit h.choose h.choose_spec.choose_spec.choose).symm ▸ Submodule.mem_top (x := (1 : h.choose.R)))
  by_contra hall
  push Not at hall
  have h1 := congrArg (fun r => h.choose_spec.choose r) hs
  simp only [map_sum, map_one, smul_eq_mul, map_mul, hall, mul_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

theorem exists_rdU_t_ne_zero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c),
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    ∀ k x, x ∈ ((T.U j σ).X k).dom → ∃ i, rdU (T.U j σ) (t i) k x ≠ 0 := by
  intro D T hT j hj σ hσ N t hunit k x hx
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨i, hi⟩ := exists_evalAt_ne_zero (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) t hunit _ (hT.unTest j hj σ hσ k ⟨x, hx⟩)
  refine ⟨i, ?_⟩
  have e : rdU (T.U j σ) (t i) k x = toC (evR (T.Q.Xo j) T.Q.c (t i) ((T.U j σ).un k ⟨x, hx⟩)) := by
    classical
    exact dif_pos hx
  rw [e]
  exact hi

theorem span_of_products : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom a n → Dom b m → (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) → (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) → ∀ P ∈ offZero (T.U j σ).X, (∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c)))) → P ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T hT j hj σ hσ a b n m N t ha hb ht hunit P hP hPt

  have hrep : ∀ i, ∃ (L : ℕ) (cf : Fin L → ℂ) (g : Fin L → Rul (T.Q.Xo j) T.Q.c),
      (∀ l, g l ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) ∧
      ∑ l, cf l • rdU (T.U j σ) (g l) = P * rdU (T.U j σ) (t i) := by
    intro i
    obtain ⟨L, cf, g, hg⟩ := Submodule.mem_span_set'.1 (hPt i)
    choose g' hg' hg'e using fun l => (g l).2
    exact ⟨L, cf, g', hg', by rw [← hg]; simp [hg'e]⟩
  choose L cf g hg hsum using hrep

  let κ := Σ i : Fin N, Fin (L i)
  let A : κ → Fin N × Fin N → Rul (T.Q.Xo j) T.Q.c := fun q e =>
    (if q.1 = e.1 then g q.1 q.2 * t e.2 else 0) - (if q.1 = e.2 then g q.1 q.2 * t e.1 else 0)
  have hA : ∀ q e, A q e ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) := by
    intro q e
    have hm : ∀ i', g q.1 q.2 * t i' ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) :=
      fun i' => sec_mul _ _ _ _ _ _ (hg q.1 q.2) (ht i')
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;> first | exact hm _ | exact Submodule.zero_mem _
  have hdom : Dom (a + b + b) (n + m + m) :=
    ⟨fun τ => ((ha.1 τ).add (hb.1 τ)).add (hb.1 τ), (ha.2.add hb.2).add hb.2⟩

  have hrow : ∀ (z : κ → ℂ) (e : Fin N × Fin N), ∑ q, z q • rdU (T.U j σ) (A q e) =
      (∑ l, z ⟨e.1, l⟩ • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, z ⟨e.2, l⟩ • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) := by
    intro z e
    have h1 : ∀ q : κ, z q • rdU (T.U j σ) (A q e) =
        (if q.1 = e.1 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.2)) else 0) -
        (if q.1 = e.2 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.1)) else 0) := by
      intro q
      simp only [A]
      split_ifs <;> simp [map_sub, rdU_mul, smul_sub]
    simp only [h1, Finset.sum_sub_distrib]
    congr 1
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.1 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.2 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
  let z : κ → ℂ := fun q => cf q.1 q.2
  have hz : ∀ e, ∑ q, z q • rdU (T.U j σ) (A q e) = 0 := by
    intro e
    rw [hrow]
    show (∑ l, cf e.1 l • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, cf e.2 l • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) = 0
    rw [hsum, hsum]; ring
  have hzspan := GlobalTheory.T.linear_relation_sections_span_eq D T j σ (GlobalTheory.rdIndep_of_lawsM D T.toCore hT.toLawsM j hj σ hσ) _ _ hdom κ (Fin N × Fin N) A hA z hz

  let S := Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c)))
  let Z : Submodule ℂ (κ → ℂ) :=
    { carrier := {z | ∃ Q ∈ S, ∀ i, Q * rdU (T.U j σ) (t i) = ∑ l, z ⟨i, l⟩ • rdU (T.U j σ) (g i l)}
      zero_mem' := ⟨0, S.zero_mem, fun i => by simp⟩
      add_mem' := by
        rintro z1 z2 ⟨Q1, hQ1, e1⟩ ⟨Q2, hQ2, e2⟩
        exact ⟨Q1 + Q2, S.add_mem hQ1 hQ2, fun i => by
          simp only [add_mul, e1, e2, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      smul_mem' := by
        rintro c z1 ⟨Q1, hQ1, e1⟩
        exact ⟨c • Q1, S.smul_mem c hQ1, fun i => by
          simp only [smul_mul_assoc, e1, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]⟩ }
  have hle : Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) ''
      {c | ∀ e, ∑ k, c k • A k e = 0}) ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    let g' : Fin N → Rul (T.Q.Xo j) T.Q.c := fun i => ∑ l, c ⟨i, l⟩ • g i l
    have hg' : ∀ i, g' i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m) :=
      fun i => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hg i l)
    have hcomp : ∀ i i', g' i * t i' = g' i' * t i := by
      intro i i'
      have hrowR : ∑ q, c q • A q (i, i') = g' i * t i' - g' i' * t i := by
        have h1 : ∀ q : κ, c q • A q (i, i') =
            (if q.1 = i then c q • (g q.1 q.2 * t i') else 0) -
            (if q.1 = i' then c q • (g q.1 q.2 * t i) else 0) := by
          intro q
          simp only [A]
          split_ifs <;> simp [smul_sub]
        simp only [h1, Finset.sum_sub_distrib]
        congr 1
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i' (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
      have := hc (i, i')
      rw [hrowR] at this
      exact sub_eq_zero.1 this
    obtain ⟨h, hh, hht⟩ := glue_frPt D T j a b n m N t g' ht hunit hg' hcomp
    refine ⟨rdU (T.U j σ) h, Submodule.subset_span ⟨h, hh, rfl⟩, fun i => ?_⟩
    rw [← rdU_mul, hht]
    simp [g', map_sum, map_smulₛₗ]
  obtain ⟨Q, hQ, hQe⟩ := hle hzspan

  have hQoff : Q ∈ offZero (T.U j σ).X := by
    refine (Submodule.span_le.2 ?_) hQ
    rintro _ ⟨f, _, rfl⟩
    exact rdU_mem_offZero _ f
  have hPQ : P = Q := by
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · obtain ⟨i, hi⟩ := exists_rdU_t_ne_zero D T hT j hj σ hσ N t hunit k x hx
      have e1 := congrFun (congrFun (hQe i) k) x
      have e2 := congrFun (congrFun (hsum i) k) x
      have : Q k x * rdU (T.U j σ) (t i) k x = P k x * rdU (T.U j σ) (t i) k x := by
        rw [show Q k x * rdU (T.U j σ) (t i) k x = (Q * rdU (T.U j σ) (t i)) k x from rfl, e1,
          show P k x * rdU (T.U j σ) (t i) k x = (P * rdU (T.U j σ) (t i)) k x from rfl, ← e2]
      exact (mul_right_cancel₀ hi this).symm
    · rw [hP k x hx, hQoff k x hx]
  rw [hPQ]; exact hQ

end GlobalTheory.GlueSpan
