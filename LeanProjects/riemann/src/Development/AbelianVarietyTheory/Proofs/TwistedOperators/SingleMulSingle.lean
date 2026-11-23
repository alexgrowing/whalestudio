import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.SplitProduct

variable {D : D7}

theorem single_mul_single {u w : FinPl D} (h : u ≠ w) :
    singleV D.host.F u 1 * singleV D.host.F w 1 = 0 := by
  classical
  ext1 z
  show singleV D.host.F u 1 z * singleV D.host.F w 1 z = 0
  by_cases hz : z = u
  · subst hz
    rw [show singleV D.host.F w 1 z = 0 from RestrictedProduct.single_eq_of_ne _ 1 h, mul_zero]
  · rw [show singleV D.host.F u 1 z = 0 from RestrictedProduct.single_eq_of_ne _ 1 hz, zero_mul]

theorem idem_mul_inl {p : Place D} {w : FinPl D} (h : p ≠ .inl w) : idem D p * idem D (.inl w) = 0 := by
  cases p with
  | inl u =>
    have hu : u ≠ w := fun e => h (by rw [e])
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F u 1)) *
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) = 0
    rw [← map_mul]
    convert map_zero (algebraMap (AF D.host.F) (AE D))
    exact Prod.ext (mul_zero _) (single_mul_single hu)
  | inr τ =>
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0) *
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) = 0
    rw [← map_mul]
    convert map_zero (algebraMap (AF D.host.F) (AE D))
    exact Prod.ext (mul_zero _) (zero_mul _)

theorem attach_kill {b : AE D} {w : FinPl D} {p : Place D} (hb : b * idem D (.inl w) = b) (hp : p ≠ .inl w) :
    idem D p * b = 0 := by
  rw [← hb, mul_left_comm, idem_mul_inl hp, mul_zero]

theorem attach_orth {b b' : AE D} {w w' : FinPl D} (hb : b * idem D (.inl w) = b)
    (hb' : b' * idem D (.inl w') = b') (h : w ≠ w') : b * b' = 0 := by
  rw [← hb, mul_assoc, attach_kill hb' (fun e => h (Sum.inl_injective e)), mul_zero]

theorem split_attach {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    e * idem D p = e := by
  linear_combination (-e) * h + he.1 + he.2.1

theorem split_attach_conj {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    cA D e * idem D p = cA D e := by
  have hc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
  linear_combination (-(cA D e)) * h + he.2.1 + hc

theorem smul_sum_single {m n : ℕ} {ι : Type} (s : Finset ι) (b : AE D) (c : ι → AE D) (u : ι → Mx D m n)
    (hu : ∀ j ∈ s, c j • u j = u j) {i : ι} (hi : i ∈ s) (hii : b * c i = c i)
    (hij : ∀ j ∈ s, j ≠ i → b * c j = 0) : b • ∑ j ∈ s, u j = u i := by
  rw [Finset.smul_sum, Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => (h hi).elim),
    ← hu i hi, smul_smul, hii]
  rw [← hu j hj, smul_smul, hij j hj hji, zero_smul]

theorem smul_sum_zero {m n : ℕ} {ι : Type} (s : Finset ι) (b : AE D) (c : ι → AE D) (u : ι → Mx D m n)
    (hu : ∀ j ∈ s, c j • u j = u j) (h : ∀ j ∈ s, b * c j = 0) : b • ∑ j ∈ s, u j = 0 := by
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [← hu j hj, smul_smul, h j hj, zero_smul]

theorem addChar_sum {A : Type*} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (g : ι → A) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

def wave (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (x y : WO S T) :
    WO S T → ℂ :=
  fun t => ψ (symplO S T t y) * halfInd e Λ (t + x)

open Classical in

def prodHalf {S T : HSp D} {ι : Type} (s : Finset ι) (a : ι → AE D) (Φ : ι → WO S T → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf (∑ i ∈ s, a i) t then ∏ i ∈ s, Φ i (a i • t) else 0

theorem prodHalf_update {S T : HSp D} {ι : Type} [DecidableEq ι] (s : Finset ι) (a : ι → AE D)
    (Φ : ι → WO S T → ℂ) {j : ι} (hj : j ∈ s) (c : ℂ) (g h : WO S T → ℂ) :
    prodHalf s a (Function.update Φ j (c • g + h)) =
      c • prodHalf s a (Function.update Φ j g) + prodHalf s a (Function.update Φ j h) := by
  have key : ∀ (G : WO S T → ℂ) t, ∏ i ∈ s, Function.update Φ j G i (a i • t) =
      G (a j • t) * ∏ i ∈ s.erase j, Φ i (a i • t) := by
    intro G t
    rw [← Finset.mul_prod_erase s (fun i => Function.update Φ j G i (a i • t)) hj]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  funext t
  simp only [prodHalf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [key, key, key]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

def IsFam {S T : HSp D} {ι : Type} (s : Finset ι) (v : ι → FinPl D) (f₀ : WO S T → ℂ)
    (Tm : ι → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (Φ : ι → WO S T → ℂ) (x : Place D → WO S T → ℂ) : Prop :=
  (∀ i ∈ s, x (.inl (v i)) = Tm i (Φ i)) ∧ ∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀

theorem isFam_update {S T : HSp D} {ι : Type} [DecidableEq ι] [DecidableEq (Place D)] {s : Finset ι} {v : ι → FinPl D}
    (hv : Set.InjOn v s) {f₀ : WO S T → ℂ} {Tm : ι → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {Φ : ι → WO S T → ℂ}
    {x : Place D → WO S T → ℂ} {j : ι} (hj : j ∈ s) {G : WO S T → ℂ}
    (hx : IsFam s v f₀ Tm (Function.update Φ j G) x) (G' : WO S T → ℂ) :
    IsFam s v f₀ Tm (Function.update Φ j G') (Function.update x (.inl (v j)) (Tm j G')) := by
  refine ⟨fun i hi => ?_, fun p hp => ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
    · have hne : (Sum.inl (v i) : Place D) ≠ .inl (v j) := fun h => hij (hv hi hj (Sum.inl_injective h))
      rw [Function.update_of_ne hne, hx.1 i hi, Function.update_of_ne hij, Function.update_of_ne hij]
  · rw [Function.update_of_ne (hp j hj)]
    exact hx.2 p hp

set_option maxHeartbeats 2000000 in

theorem isPure_of_facts (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hpure0 : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀)
    (hheis : ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f))
    (hlin : ∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ),
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) →
      (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g))
    (hwave : ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 →
      (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → ∀ (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
        IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm →
        Tm (wave ψ S T (latO S T ΛS ΛT fun _ => True) a x y) = heisO ψ S T y (heisO ψ S T x f₀)) ∧
      ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ →
        Φ ∈ Submodule.span ℂ {G | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧
          G = wave ψ S T (latO S T ΛS ΛT fun _ => True) a x y})
    (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D)
    (ha : ∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) (hv : Set.InjOn v s)
    (Φ : ι → WO S T → ℂ) (hΦ : ∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i))
    (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ)
    (hx : ∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i)
      (x (.inl (v i))))
    (hxo : ∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀)
    (hΨ1 : ∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t))
    (hΨ0 : ∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  classical

  have A1 : ∀ i ∈ s, a i * idem D (.inl (v i)) = a i := fun i hi => split_attach (ha i hi).1 (ha i hi).2
  have A2 : ∀ i ∈ s, cA D (a i) * idem D (.inl (v i)) = cA D (a i) := fun i hi =>
    split_attach_conj (ha i hi).1 (ha i hi).2
  have vne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≠ v j := fun i hi j hj hij e => hij (hv hi hj e)
  have hAa : ∀ i ∈ s, (∑ j ∈ s, a j) * a i = a i := by
    intro i hi
    rw [Finset.sum_mul, Finset.sum_eq_single i
      (fun j hj hji => attach_orth (A1 j hj) (A1 i hi) (vne j hj i hi hji)) (fun h => (h hi).elim), (ha i hi).1.1]
  have hAc : ∀ i ∈ s, (∑ j ∈ s, a j) * cA D (a i) = 0 := by
    intro i hi
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      exact (ha j hj).1.2.1
    · exact attach_orth (A1 j hj) (A2 i hi) (vne j hj i hi hji)
  have hcAc : ∀ i ∈ s, cA D (∑ j ∈ s, a j) * cA D (a i) = cA D (a i) := by
    intro i hi
    rw [map_sum, Finset.sum_mul, Finset.sum_eq_single i
      (fun j hj hji => attach_orth (A2 j hj) (A2 i hi) (vne j hj i hi hji)) (fun h => (h hi).elim),
      ← RingHom.map_mul, (ha i hi).1.1]
  have hAA : (∑ j ∈ s, a j) * (∑ j ∈ s, a j) = ∑ j ∈ s, a j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hAa
  have hAcA : (∑ j ∈ s, a j) * cA D (∑ j ∈ s, a j) = 0 := by
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero hAc
  have hAinf : infPart D (∑ j ∈ s, a j) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun j hj => GlobalTheory.SplitScalar.infPart_splitIdem (ha j hj).1
  have wsp : ∀ i ∈ s, _ := fun i hi =>
    hwave (a i) (ha i hi).1.1 (ha i hi).1.2.1 (GlobalTheory.SplitScalar.infPart_splitIdem (ha i hi).1)
  have wspA := hwave (∑ j ∈ s, a j) hAA hAcA hAinf

  obtain ⟨⟨Tm0, hTm0⟩, hfT⟩ := hf
  have hfeq : f = Tm0 Ψ := hfT Tm0 hTm0
  have hmod : ∀ i, ∃ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), i ∈ s →
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨⟨Tm, hTm⟩, -⟩ := hx i hi
      exact ⟨Tm, fun _ => hTm⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose Tmi hTmi using hmod

  have base : ∀ (Φ' : ι → WO S T → ℂ) (x' : Place D → WO S T → ℂ),
      (∀ i ∈ s, ∃ xi yi, IsHalf (a i) xi ∧ IsHalf (cA D (a i)) yi ∧
        Φ' i = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a i) xi yi) →
      IsFam s v f₀ Tmi Φ' x' →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Tm0 (prodHalf s a Φ')) := by
    intro Φ' x' hw hfam
    have hxy : ∀ i, ∃ p : WO S T × WO S T, i ∈ s → IsHalf (a i) p.1 ∧ IsHalf (cA D (a i)) p.2 ∧
        Φ' i = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a i) p.1 p.2 := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨xi, yi, h⟩ := hw i hi
        exact ⟨(xi, yi), fun _ => h⟩
      · exact ⟨0, fun h => (hi h).elim⟩
    choose xy hxy using hxy
    have hX : ∀ i ∈ s, a i • (xy i).1 = (xy i).1 := fun i hi =>
      (GlobalTheory.SplitScalar.isHalf_iff _ _).1 (hxy i hi).1
    have hY : ∀ i ∈ s, cA D (a i) • (xy i).2 = (xy i).2 := fun i hi =>
      (GlobalTheory.SplitScalar.isHalf_iff _ _).1 (hxy i hi).2.1
    have hAX : (∑ j ∈ s, a j) • ∑ i ∈ s, (xy i).1 = ∑ i ∈ s, (xy i).1 := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hX i hi, smul_smul, hAa i hi]
    have hAY : cA D (∑ j ∈ s, a j) • ∑ i ∈ s, (xy i).2 = ∑ i ∈ s, (xy i).2 := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hY i hi, smul_smul, hcAc i hi]
    have haX : ∀ i ∈ s, a i • ∑ j ∈ s, (xy j).1 = (xy i).1 := fun i hi =>
      smul_sum_single s (a i) a (fun j => (xy j).1) hX hi (ha i hi).1.1
        (fun j hj hji => attach_orth (A1 i hi) (A1 j hj) (vne i hi j hj (Ne.symm hji)))
    have hplX : ∀ i ∈ s, wAt (.inl (v i)) (∑ j ∈ s, (xy j).1) = (xy i).1 := fun i hi =>
      (wAt_eq_smul _ _).trans (smul_sum_single s _ a (fun j => (xy j).1) hX hi (by rw [mul_comm, A1 i hi])
        (fun j hj hji => attach_kill (A1 j hj) (fun e => vne j hj i hi hji (Sum.inl_injective e).symm)))
    have hplY : ∀ i ∈ s, wAt (.inl (v i)) (∑ j ∈ s, (xy j).2) = (xy i).2 := fun i hi =>
      (wAt_eq_smul _ _).trans (smul_sum_single s _ (fun j => cA D (a j)) (fun j => (xy j).2) hY hi
        (by rw [mul_comm, A2 i hi])
        (fun j hj hji => attach_kill (A2 j hj) (fun e => vne j hj i hi hji (Sum.inl_injective e).symm)))
    have hoffX : ∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → wAt p (∑ j ∈ s, (xy j).1) = 0 := fun p hp =>
      (wAt_eq_smul _ _).trans (smul_sum_zero s _ a (fun j => (xy j).1) hX fun j hj => attach_kill (A1 j hj) (hp j hj))
    have hoffY : ∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → wAt p (∑ j ∈ s, (xy j).2) = 0 := fun p hp =>
      (wAt_eq_smul _ _).trans (smul_sum_zero s _ (fun j => cA D (a j)) (fun j => (xy j).2) hY
        fun j hj => attach_kill (A2 j hj) (hp j hj))

    have hΨw : prodHalf s a Φ' = wave ψ S T (latO S T ΛS ΛT fun _ => True) (∑ j ∈ s, a j)
        (∑ i ∈ s, (xy i).1) (∑ i ∈ s, (xy i).2) := by
      funext t
      have hprod : ∏ i ∈ s, Φ' i (a i • t) = ∏ i ∈ s, wave ψ S T (latO S T ΛS ΛT fun _ => True) (a i)
          (xy i).1 (xy i).2 (a i • t) := Finset.prod_congr rfl fun i hi => by rw [(hxy i hi).2.2]
      by_cases ht : IsHalf (∑ j ∈ s, a j) t
      · rw [prodHalf, if_pos ht, hprod]
        simp only [wave]
        rw [Finset.prod_mul_distrib]
        congr 1
        · rw [← addChar_sum, show symplO S T t (∑ i ∈ s, (xy i).2) = ∑ i ∈ s, symplO S T t (xy i).2 from
            map_sum (GlobalTheory.LatVac.symplHom S T t) _ _]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [GlobalTheory.SplitScalar.symplO_smul, hY i hi]
        · have ht' := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 ht
          have hsum : t + ∑ i ∈ s, (xy i).1 = ∑ i ∈ s, (a i • t + (xy i).1) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_smul, ht']
          have hhalf : ∀ i ∈ s, IsHalf (a i) (a i • t + (xy i).1) := fun i hi =>
            (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_add, smul_smul, (ha i hi).1.1, hX i hi])
          have hhalfA : IsHalf (∑ j ∈ s, a j) (t + ∑ i ∈ s, (xy i).1) :=
            (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_add, ht', hAX])
          simp only [halfInd]
          by_cases hall : ∀ i ∈ s, a i • t + (xy i).1 ∈ latO S T ΛS ΛT fun _ => True
          · rw [Finset.prod_eq_one fun i hi => if_pos ⟨hall i hi, hhalf i hi⟩,
              if_pos ⟨hsum ▸ AddSubgroup.sum_mem _ hall, hhalfA⟩]
          · push_neg at hall
            obtain ⟨i, hi, hni⟩ := hall
            rw [Finset.prod_eq_zero hi (if_neg fun h => hni h.1), if_neg fun h => hni ?_]
            have := GlobalTheory.PlaceModelSum.idem_smul_latO (ha i hi).1.1 h.1
            rwa [smul_add, haX i hi] at this
      · rw [prodHalf, if_neg ht]
        simp only [wave, halfInd]
        rw [if_neg, mul_zero]
        rintro ⟨-, h2⟩
        apply ht
        refine (GlobalTheory.SplitScalar.isHalf_iff _ _).2 ?_
        have := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 h2
        rw [smul_add, hAX] at this
        exact add_right_cancel this
    have hT0 := wspA.1 _ _ ((GlobalTheory.SplitScalar.isHalf_iff _ _).2 hAX) ((GlobalTheory.SplitScalar.isHalf_iff _ _).2 hAY) Tm0 hTm0
    have hP := hheis _ _ (hheis _ _ hpure0 (∑ i ∈ s, (xy i).1)) (∑ i ∈ s, (xy i).2)
    have hx' : x' = fun p => heisO ψ S T (wAt p (∑ i ∈ s, (xy i).2))
        (heisO ψ S T (wAt p (∑ i ∈ s, (xy i).1)) f₀) := by
      funext p
      by_cases hp : ∃ i ∈ s, p = .inl (v i)
      · obtain ⟨i, hi, rfl⟩ := hp
        rw [hfam.1 i hi, (hxy i hi).2.2, hplX i hi, hplY i hi]
        exact (wsp i hi).1 _ _ (hxy i hi).1 (hxy i hi).2.1 (Tmi i) (hTmi i hi)
      · push_neg at hp
        rw [hfam.2 p hp, hoffX p hp, hoffY p hp, GlobalTheory.SplitScalar.heisO_zero, GlobalTheory.SplitScalar.heisO_zero]
    rw [hΨw, hT0, hx']
    exact hP

  have main : ∀ (s' : Finset ι) (Φ' : ι → WO S T → ℂ) (x' : Place D → WO S T → ℂ),
      (∀ i ∈ s, i ∉ s' → ∃ xi yi, IsHalf (a i) xi ∧ IsHalf (cA D (a i)) yi ∧
        Φ' i = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a i) xi yi) →
      (∀ i ∈ s, i ∈ s' → Φ' i ∈ Submodule.span ℂ {G | ∃ xi yi : WO S T, IsHalf (a i) xi ∧
        IsHalf (cA D (a i)) yi ∧ G = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a i) xi yi}) →
      IsFam s v f₀ Tmi Φ' x' →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Tm0 (prodHalf s a Φ')) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => exact fun Φ' x' hw _ hfam => base Φ' x' (fun i hi => hw i hi (Finset.notMem_empty i)) hfam
    | insert j s' hj ih =>
      intro Φ' x' hw hsp hfam
      by_cases hjs : j ∈ s
      · have lin : ∀ (c : ℂ) (g h : WO S T → ℂ),
            (∀ x'', IsFam s v f₀ Tmi (Function.update Φ' j g) x'' →
              IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x'' (Tm0 (prodHalf s a (Function.update Φ' j g)))) →
            (∀ x'', IsFam s v f₀ Tmi (Function.update Φ' j h) x'' →
              IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x'' (Tm0 (prodHalf s a (Function.update Φ' j h)))) →
            ∀ x'', IsFam s v f₀ Tmi (Function.update Φ' j (c • g + h)) x'' →
              IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x'' (Tm0 (prodHalf s a (Function.update Φ' j (c • g + h)))) := by
          intro c g h Pg Ph x'' hx''
          have hg := Pg _ (isFam_update hv hjs hx'' g)
          have hh := Ph _ (isFam_update hv hjs hx'' h)
          have := hlin _ _ x'' _ _ (.inl (v j)) c hg hh
            (fun p hp => by rw [Function.update_of_ne hp, Function.update_of_ne hp])
            (fun p hp => by rw [Function.update_of_ne hp])
            (by rw [hx''.1 j hjs, Function.update_self, Function.update_self, Function.update_self, map_add,
              map_smul])
          rwa [prodHalf_update s a Φ' hjs, map_add, map_smul]
        have hmem : ∀ G, G ∈ {G | ∃ xi yi : WO S T, IsHalf (a j) xi ∧ IsHalf (cA D (a j)) yi ∧
            G = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a j) xi yi} →
            ∀ x'', IsFam s v f₀ Tmi (Function.update Φ' j G) x'' →
              IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x'' (Tm0 (prodHalf s a (Function.update Φ' j G))) := by
          intro G hG x'' hx''
          refine ih _ x'' (fun i hi his => ?_) (fun i hi his => ?_) hx''
          · by_cases hij : i = j
            · subst hij
              rw [Function.update_self]
              exact hG
            · rw [Function.update_of_ne hij]
              exact hw i hi fun h => by
                rcases Finset.mem_insert.1 h with h | h
                · exact hij h
                · exact his h
          · have hij : i ≠ j := fun e => hj (e ▸ his)
            rw [Function.update_of_ne hij]
            exact hsp i hi (Finset.mem_insert_of_mem his)
        have key : ∀ G ∈ Submodule.span ℂ {G | ∃ xi yi : WO S T, IsHalf (a j) xi ∧ IsHalf (cA D (a j)) yi ∧
            G = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a j) xi yi},
            ∀ x'', IsFam s v f₀ Tmi (Function.update Φ' j G) x'' →
              IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x'' (Tm0 (prodHalf s a (Function.update Φ' j G))) := by
          intro G hG
          induction hG using Submodule.span_induction with
          | mem G hG => exact hmem G hG
          | zero =>
            have h0 : wave ψ S T (latO S T ΛS ΛT fun _ => True) (a j) 0 0 ∈ {G | ∃ xi yi : WO S T,
                IsHalf (a j) xi ∧ IsHalf (cA D (a j)) yi ∧
                G = wave ψ S T (latO S T ΛS ΛT fun _ => True) (a j) xi yi} :=
              ⟨0, 0, fun _ _ => by simp, fun _ _ => by simp, rfl⟩
            have := lin (-1) _ _ (hmem _ h0) (hmem _ h0)
            rwa [neg_one_smul, neg_add_cancel] at this
          | add g h _ _ ihg ihh =>
            have := lin 1 g h ihg ihh
            rwa [one_smul] at this
          | smul c g _ ihg =>
            have := lin (c - 1) g g ihg ihg
            rwa [sub_smul, one_smul, sub_add_cancel] at this
        have := key (Φ' j) (hsp j hjs (Finset.mem_insert_self j s')) x' (by rwa [Function.update_eq_self])
        rwa [Function.update_eq_self] at this
      · exact ih Φ' x' (fun i hi his => hw i hi fun h => by
            rcases Finset.mem_insert.1 h with h | h
            · exact hjs (h ▸ hi)
            · exact his h) (fun i hi his => hsp i hi (Finset.mem_insert_of_mem his)) hfam
  have hΨ : Ψ = prodHalf s a Φ := by
    funext t
    unfold prodHalf
    split_ifs with h
    · exact hΨ1 t h
    · exact hΨ0 t h
  rw [hfeq, hΨ]
  exact main s Φ x (fun i hi his => (his hi).elim) (fun i hi _ => (wsp i hi).2 (Φ i) (hΦ i hi))
    ⟨fun i hi => (hx i hi).2 (Tmi i) (hTmi i hi), hxo⟩

end GlobalTheory.PlaceTensor.SplitProduct

end
