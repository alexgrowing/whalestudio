import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.WeakApprox

open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.PlaceRestrict

open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem val_aeval_eq_coeff {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (α : σ →₀ ℕ) (hα : α ∈ P.support)
    (hmin : ∀ β ∈ P.support, w (algebraMap Ω U (P.coeff α)) ≤ w (algebraMap Ω U (P.coeff β))) :
    w (MvPolynomial.aeval t P) = w (algebraMap Ω U (P.coeff α)) := by
  classical
  have hc : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have key := val_eval_eq_zero w t ht hind (MvPolynomial.C (P.coeff α)⁻¹ * P) ?_ α ?_
  · have : MvPolynomial.aeval t P =
        algebraMap Ω U (P.coeff α) * MvPolynomial.aeval t (MvPolynomial.C (P.coeff α)⁻¹ * P) := by
      rw [map_mul, MvPolynomial.aeval_C, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    rw [this, AddValuation.map_mul, key, add_zero]
  · intro β
    rw [MvPolynomial.coeff_C_mul, map_mul, AddValuation.map_mul]
    by_cases hβ : β ∈ P.support
    · have h3 := hmin β hβ
      calc (0 : WithTop ℤ) = w (algebraMap Ω U (P.coeff α)⁻¹) + w (algebraMap Ω U (P.coeff α)) := by
            rw [← AddValuation.map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, AddValuation.map_one]
        _ ≤ _ := add_le_add le_rfl h3
    · rw [MvPolynomial.notMem_support_iff.mp hβ, map_zero, AddValuation.map_zero]
      simp
  · rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc]

theorem val_aeval_congr {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w w' : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (ht' : ∀ s, t s ∈ vRing w')
    (hind' : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w') (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w').comap (algebraMap Ω U)))
        (fun s => residue (vRing w') ⟨t s, ht' s⟩))
    (hres : ∀ x : Ω, w (algebraMap Ω U x) = w' (algebraMap Ω U x))
    (P : MvPolynomial σ Ω) : w (MvPolynomial.aeval t P) = w' (MvPolynomial.aeval t P) := by
  classical
  by_cases hP : P = 0
  · subst hP; simp
  have hne : P.support.Nonempty := by
    obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hP
    exact ⟨β, MvPolynomial.mem_support_iff.mpr hβ⟩
  obtain ⟨α, hα, hmin⟩ := P.support.exists_min_image (fun β => w (algebraMap Ω U (P.coeff β))) hne
  rw [val_aeval_eq_coeff w t ht hind P α hα hmin, val_aeval_eq_coeff w' t ht' hind' P α hα
    (fun β hβ => by rw [← hres, ← hres]; exact hmin β hβ), hres]

theorem exists_orders {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (n : X → ℤ) :
    ∃ g : Ω, g ≠ 0 ∧ ∀ w ∈ S, v w g = n w := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w0, hw0⟩
  · exact ⟨1, one_ne_zero, by simp⟩
  haveI := hS.fintype
  let e := (Fintype.equivFin S).symm
  obtain ⟨g, hg⟩ := weak_approx_orders (fun i => v (e i)) (fun i => (hn _ (e i).2).1)
    (fun i => (hn _ (e i).2).2)
    (fun i j hij h => hij (e.injective (Subtype.ext (hinj (e i).2 (e j).2 h)))) (fun i => n (e i))
  have hg' : ∀ w ∈ S, v w g = n w := fun w hw => by
    have := hg (e.symm ⟨w, hw⟩)
    simpa using this
  exact ⟨g, wa_ne_zero_of_coe _ (hg' w0 hw0), hg'⟩

theorem exists_integral_lift {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (w : X) (hw : w ∈ S) (a : Ω) (ha : 0 ≤ v w a) :
    ∃ l : Ω, (∀ w' ∈ S, 0 ≤ v w' l) ∧ 0 < v w (a - l) := by
  classical
  by_cases ha0 : a = 0
  · exact ⟨0, by simp, by simp [ha0]⟩
  have hm : ∀ x, ∃ m : ℤ, x ∈ S → v x a = m := fun x => by
    by_cases hx : x ∈ S
    · obtain ⟨m, hm⟩ := wa_exists_coe (v x) (hn x hx).1 ha0
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose m hm using hm
  obtain ⟨s, hs0, hs⟩ := exists_orders S hS v hinj hn
    (fun x => if x = w then 1 else min (m x) 0 - 1)
  have hsw : v w s = ((1 : ℤ) : WithTop ℤ) := by simpa using hs w hw
  have h1w : v w (1 + s) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_add_eq_of_lt_left _ (by
      rw [AddValuation.map_one, hsw]; exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)),
      AddValuation.map_one, WithTop.coe_zero]
  have h1s : (1 + s) ≠ 0 := wa_ne_zero_of_coe _ h1w
  have hmw : 0 ≤ m w := by
    rw [hm w hw] at ha; exact_mod_cast ha
  refine ⟨a / (1 + s), fun x hx => ?_, ?_⟩
  · by_cases hxw : x = w
    · subst hxw
      rw [wa_div _ (hm x hx) h1w]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - 0)
    · have hsx : v x s = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        have := hs x hx
        rwa [if_neg hxw] at this
      have h1x : v x (1 + s) = ((min (m x) 0 - 1 : ℤ) : WithTop ℤ) := by
        rw [AddValuation.map_add_eq_of_lt_right _ (by
          rw [AddValuation.map_one, hsx]
          exact_mod_cast (by omega : min (m x) 0 - 1 < (0 : ℤ))), hsx]
      rw [wa_div _ (hm x hx) h1x]
      exact_mod_cast (by omega : (0 : ℤ) ≤ m x - (min (m x) 0 - 1))
  · have : a - a / (1 + s) = a * s / (1 + s) := by field_simp; ring
    rw [this, wa_div _ (wa_mul _ (hm w hw) hsw) h1w]
    exact_mod_cast (by omega : (0 : ℤ) < m w + 1 - 0)

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem exists_gauss_variables (d : Data K ι Ω WT A) (hd : d.AxH 𝒜)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) (j0 : Fin (d.N + 1))
    (hw0 : d.w j0 c ≠ 0) :
    ∃ t : SVar d.D d.N → OmS (Ω c) d.D d.N,
      (∀ P : MvPolynomial (SVar d.D d.N) (Ω c), ∃ Q : MvPolynomial (SVar d.D d.N) (Ω c),
        MvPolynomial.aeval t Q = algebraMap _ (OmS (Ω c) d.D d.N) P) ∧
      ∀ w ∈ d.PlOver la c, (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) →
        ∃ ht : ∀ s, t s ∈ vRing w,
          letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          AlgebraicIndependent
            (ResidueField ((vRing w).comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))))
            (fun s => residue (vRing w) ⟨t s, ht s⟩) := by
  classical

  have hex : ∀ j, ∃ a : Ω c, d.w j c = a • d.w (d.jc c) c := by
    intro j
    have hb := hd.w_base c
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL)
      (fun h0 => hb (congrArg Subtype.val h0))).mp (hd.finrank_one c d.wL) ⟨d.w j c, hd.w_mem j c⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  let a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)
  have ha : ∀ j, d.w j c = a j • d.w (d.jc c) c := fun j => by
    obtain ⟨b, hb⟩ := hex j
    rw [show a j = b from ratio_eq (hd.w_base c) hb]
    exact hb
  have ha_jc : a (d.jc c) = 1 := ratio_eq (hd.w_base c) (one_smul _ _).symm
  let f := algebraMap (Ω c) (OmS (Ω c) d.D d.N)
  have ha0 : a j0 ≠ 0 := by
    intro h0
    apply hw0
    rw [ha j0, h0, zero_smul]
  have hf0 : f (a j0) ≠ 0 := (map_ne_zero f).mpr ha0
  let r : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)
  have hr : ∀ j, r j * a j0 = a j := fun j => by
    have : r j = a j / a j0 :=
      ratio_eq hw0 (by rw [ha j, ha j0, smul_smul, div_mul_cancel₀ _ ha0])
    rw [this, div_mul_cancel₀ _ ha0]
  have hr0 : r j0 = 1 := ratio_eq hw0 (one_smul _ _).symm

  let s : TVar d.D d.N → OmS (Ω c) d.D d.N := sImg (D := d.D) (d.jc c) (d.x c)
  have hOT : ∀ p, d.OTtoS c (MvPolynomial.X p) = s p := by
    intro p; simp [Data.OTtoS, OTtoKT, Data.sH, sHom, s]
  have hC : ∀ y : Ω c, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (MvPolynomial.C y) = f y := fun y =>
    (IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) _ y).symm
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 → ∑ j, s (i, j) * f (a j) = 0 := by
    intro i hi
    rw [Fin.sum_univ_succAbove _ (d.jc c)]
    simp only [s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, hi, ↓reduceIte, ha_jc, map_one, mul_one, map_neg, map_sum,
      map_mul, hC]
    rw [neg_add_eq_zero]
    rfl
  have hrel0 : ∀ i : Fin (d.D + 1), i ≠ 0 →
      s (i, j0) = -∑ k, s (i, j0.succAbove k) * f (r (j0.succAbove k)) := by
    intro i hi
    have h1 := hrel i hi
    have e : ∀ j, s (i, j) * f (a j) = (s (i, j) * f (r j)) * f (a j0) := fun j => by
      rw [← hr j, map_mul, mul_assoc]
    simp only [e, ← Finset.sum_mul] at h1
    have h2 := (mul_eq_zero.mp h1).resolve_right hf0
    rw [Fin.sum_univ_succAbove _ j0, hr0, map_one, mul_one] at h2
    exact eq_neg_of_add_eq_zero_left h2

  let q0 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), j0)) (fun ik => (ik.1, j0.succAbove ik.2))
  let t : SVar d.D d.N → OmS (Ω c) d.D d.N := fun x => s (q0 x)
  let p : TVar d.D d.N → MvPolynomial (SVar d.D d.N) (Ω c) := fun ij =>
    Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) j0
      (if ij.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (ij.1, k)) * MvPolynomial.C (r (j0.succAbove k)))
      (fun k => MvPolynomial.X (Sum.inr (ij.1, k))) ij.2
  have hpj0 : ∀ i, p (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (r (j0.succAbove k)) := by
    intro i; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
  have hpk : ∀ i k, p (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
    intro i k; simp only [p, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  have hpu : ∀ ij, MvPolynomial.aeval t (p ij) = s ij := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs with hi
      · subst hi; simp [t, q0]
      · rw [hrel0 i hi]; simp [t, q0]; rfl
    · rw [hpk]; simp [t, q0]
  let q1 : SVar d.D d.N → TVar d.D d.N :=
    Sum.elim (fun _ => ((0 : Fin (d.D + 1)), d.jc c)) (fun ik => (ik.1, (d.jc c).succAbove ik.2))
  have hψ : ∀ P : MvPolynomial (SVar d.D d.N) (Ω c),
      MvPolynomial.aeval t (MvPolynomial.aeval (fun x => p (q1 x)) P) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) P := by
    have e : (MvPolynomial.aeval t).comp (MvPolynomial.aeval (fun x => p (q1 x))) =
        IsScalarTower.toAlgHom (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, IsScalarTower.coe_toAlgHom', hpu]
      rcases x with _ | ⟨i, k⟩
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
      · simp [q1, s, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
    intro P
    exact DFunLike.congr_fun e P
  refine ⟨t, fun P => ⟨_, hψ P⟩, ?_⟩
  rintro w ⟨hNZ, hpl⟩ hrint'
  have hrint : ∀ j, 0 ≤ w (f (r j)) := hrint'
  have hX0 : ∀ p, 0 ≤ w (s p) := fun p => by rw [← hOT]; exact (hpl _).1
  have ht : ∀ x, t x ∈ vRing w := fun x => hX0 _

  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) f
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap f) (algebraMap K (Ω c))
  let k₁ : IntermediateField (ResidueField (((vRing w).comap f).comap (algebraMap K (Ω c))))
      (ResidueField ((vRing w).comap f)) :=
    IntermediateField.adjoin _ {z | ∃ j, ∃ h : r j ∈ (vRing w).comap f,
      z = residue ((vRing w).comap f) ⟨r j, h⟩}
  let R3 : Subring (MvPolynomial (SVar d.D d.N) (Ω c)) :=
    ((MvPolynomial.map (algebraMap k₁ (ResidueField ((vRing w).comap f)))).range.comap
      (MvPolynomial.map (residue ((vRing w).comap f)))).map
        (MvPolynomial.map ((vRing w).comap f).subtype)
  have hR3X : ∀ x, (MvPolynomial.X x : MvPolynomial (SVar d.D d.N) (Ω c)) ∈ R3 := fun x =>
    ⟨MvPolynomial.X x, ⟨MvPolynomial.X x, by simp⟩, by simp⟩
  have hR3C : ∀ j, MvPolynomial.C (r j) ∈ R3 := fun j =>
    ⟨MvPolynomial.C ⟨r j, hrint j⟩,
      ⟨MvPolynomial.C ⟨_, IntermediateField.subset_adjoin _ _ ⟨j, hrint j, rfl⟩⟩, by simp⟩, by simp⟩
  have hpR3 : ∀ ij, p ij ∈ R3 := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · rw [hpj0]
      split_ifs
      · exact hR3X _
      · exact R3.neg_mem (R3.sum_mem fun k _ => R3.mul_mem (hR3X _) (hR3C _))
    · rw [hpk]; exact hR3X _
  have hcoefW : ∀ P ∈ R3, ∀ α, P.coeff α ∈ (vRing w).comap f := by
    intro P hP α
    obtain ⟨Q, -, rfl⟩ := hP
    rw [MvPolynomial.coeff_map]
    exact (Q.coeff α).2
  have hp : ∀ ij α, (p ij).coeff α ∈ (vRing w).comap f := fun ij α => hcoefW _ (hpR3 ij) α

  let u : TVar d.D d.N → vRing w := fun ij => ⟨s ij, hX0 ij⟩
  have hKU : algebraMap K (OmS (Ω c) d.D d.N) = f.comp (algebraMap K (Ω c)) :=
    RingHom.ext fun x => IsScalarTower.algebraMap_apply K (Ω c) _ x
  have hOT' : ∀ P, d.OTtoS c P =
      MvPolynomial.eval₂ (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) s P := by
    intro P
    simp only [Data.OTtoS, OTtoKT, Data.sH, sHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hKU]
    rfl
  have h0 : ∀ P : MvPolynomial (TVar d.D d.N) (𝓞 K), 0 < w (MvPolynomial.eval₂
      (f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) (fun j => (u j : OmS (Ω c) d.D d.N)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal := by
    intro P
    show 0 < w (MvPolynomial.eval₂ _ s P) ↔ _
    rw [← hOT' P, (hpl P).2, laT, MvPolynomial.mem_map_C_iff]
  have h1 : ∀ x : 𝓞 K, 0 ≤ w ((f.comp ((algebraMap K (Ω c)).comp (algebraMap (𝓞 K) K))) x) := by
    intro x
    have := (hpl (MvPolynomial.C x)).1
    rwa [hOT', MvPolynomial.eval₂_C] at this
  have hind_u := indep_u (Ω := Ω c) w la u h0 h1
  have hcard : Fintype.card (TVar d.D d.N) = Fintype.card (SVar d.D d.N) + d.D := by
    simp [Fintype.card_sum, Fintype.card_prod]; ring
  have RT := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K (Ω c) (OmS (Ω c) d.D d.N) d.D (hd.trdeg c)
    (SVar d.D d.N) t (vRing w) ht (TVar d.D d.N) u p hp hcard hpu hind_u
  exact ⟨ht, RT.2.2⟩

theorem wres_injOn (d : Data K ι Ω WT A) (hd : d.AxH 𝒜) (h : d.S1)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Set.InjOn (d.Wres c) (d.PlOver la c) := by
  intro w hw w' hw' heq
  obtain ⟨-, -, j0, hj0, hint, -⟩ := d.admissible_over_prime hd h la c w hw
  obtain ⟨t, hsurj, hG⟩ := exists_gauss_variables d hd la c j0 hj0
  obtain ⟨ht, hi⟩ := hG w hw hint
  obtain ⟨ht', hi'⟩ := hG w' hw' (heq ▸ hint)
  have hres : ∀ x : Ω c, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) x) =
      w' (algebraMap (Ω c) (OmS (Ω c) d.D d.N) x) := fun x => by
    change d.Wres c w x = d.Wres c w' x
    rw [heq]
  have hpoly : ∀ P : MvPolynomial (SVar d.D d.N) (Ω c),
      w (algebraMap _ (OmS (Ω c) d.D d.N) P) = w' (algebraMap _ (OmS (Ω c) d.D d.N) P) := by
    intro P
    obtain ⟨Q, hQ⟩ := hsurj P
    rw [← hQ]
    exact val_aeval_congr w w' t ht hi ht' hi' hres Q
  apply AddValuation.ext
  intro x
  obtain ⟨P, Q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVar d.D d.N) (Ω c)) x
  rw [div_eq_mul_inv, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
    AddValuation.map_inv, hpoly, hpoly]

theorem places_restrict_injective (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
    (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    (d.PlOver la c).Finite ∧ Set.InjOn (d.Wres c) (d.PlOver la c) ∧
      (∀ n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ,
        ∃ g : Ω c, g ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.Wres c w g = n w) ∧
      (∀ G : WT, ∃ e ∈ 𝒜 c G, e ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.ord c (d.Wres c w) G e = 0) ∧
      ∀ w ∈ d.PlOver la c, ∀ a : Ω c, 0 ≤ d.Wres c w a →
        ∃ l : Ω c, (∀ w' ∈ d.PlOver la c, 0 ≤ d.Wres c w' l) ∧ 0 < d.Wres c w (a - l) := by
  have hfin := (d.places_over_la hd h la c).1
  have hinj := wres_injOn d hd h la c
  have hadm : ∀ w ∈ d.PlOver la c, d.admitted c (d.Wres c w) := fun w hw => (d.admissible_over_prime hd h la c w hw).1
  have hn : ∀ w ∈ d.PlOver la c, IsNormDiscrete (d.Wres c w) := fun w hw => (hadm w hw).1
  refine ⟨hfin, hinj, exists_orders _ hfin _ hinj hn, fun G => ?_,
    exists_integral_lift _ hfin _ hinj hn⟩
  haveI : Nontrivial (𝒜 c G) := Module.nontrivial_of_finrank_pos (R := Ω c)
    (by rw [hd.finrank_one c G]; exact zero_lt_one)
  obtain ⟨e0, he0⟩ := exists_ne (0 : 𝒜 c G)
  have he0' : (e0 : A c) ≠ 0 := fun h0 => he0 (Subtype.ext h0)
  obtain ⟨g, hg0, hg⟩ := exists_orders _ hfin _ hinj hn
    (fun w => -d.ord c (d.Wres c w) G (e0 : A c))
  refine ⟨g • (e0 : A c), (𝒜 c G).smul_mem g e0.2, smul_ne_zero hg0 he0', fun w hw => ?_⟩
  have := hd.ord_smul c _ (hadm w hw) g e0.2 he0' hg0
  rw [hg w hw, ← WithTop.coe_add, neg_add_cancel] at this
  exact_mod_cast this

end GlobalTheory.PlaceRestrict
