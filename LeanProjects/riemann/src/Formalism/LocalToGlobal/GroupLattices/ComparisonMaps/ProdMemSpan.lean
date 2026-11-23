import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOf
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem prod_mem_span {O Y ι : Type} [CommRing O] [CommRing Y] [Algebra O Y] (t : Finset ι) (A : ι → Set Y) (x : ι → Y)
    (hx : ∀ i ∈ t, x i ∈ Submodule.span O (A i)) :
    ∏ i ∈ t, x i ∈ Submodule.span O {y | ∃ a : ι → Y, (∀ i ∈ t, a i ∈ A i) ∧ y = ∏ i ∈ t, a i} := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    apply Submodule.subset_span
    exact ⟨fun _ => 1, by simp, by simp⟩
  | insert j t hj ih =>
    have h1 : x j ∈ Submodule.span O (A j) := hx j (Finset.mem_insert_self j t)
    have h2 := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert hj]
    have h3 := Submodule.mul_mem_mul h1 h2
    rw [Submodule.span_mul_span] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨b, hb, y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨Function.update a j b, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using hb
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        simpa [Function.update_apply, hne] using ha i hi
    · rw [Finset.prod_insert hj]
      simp only [Function.update_apply, if_pos rfl]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [hne]

theorem tens_span {O Y ι : Type} [CommRing O] [CommRing Y] [Algebra O Y] [Fintype ι] {X : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module O (X i)] (φ : ∀ i, X i →ₗ[O] Y) (M : ∀ i, Submodule O (X i))
    (R : ∀ i, X i → Prop) (h : ∀ i, M i ≤ Submodule.span O {x | x ∈ M i ∧ R i x}) (F : ∀ i, X i)
    (hF : ∀ i, F i ∈ M i) :
    ∏ i, φ i (F i) ∈
      Submodule.span O {y | ∃ F' : ∀ i, X i, (∀ i, F' i ∈ M i ∧ R i (F' i)) ∧ y = ∏ i, φ i (F' i)} := by
  classical
  have key := prod_mem_span (O := O) Finset.univ (fun i => φ i '' {x | x ∈ M i ∧ R i x})
    (fun i => φ i (F i)) (by
      intro i _
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem (h i (hF i)))
  refine Submodule.span_mono ?_ key
  rintro y ⟨a, ha, rfl⟩
  have hex : ∀ i, ∃ z, (z ∈ M i ∧ R i z) ∧ φ i z = a i := fun i => ha i (Finset.mem_univ i)
  choose F' hF' hF'' using hex
  exact ⟨F', hF', by simp [hF'']⟩

section One

variable {O Kf LL : Type} [CommRing O] [Field Kf] [Algebra O Kf] [Field LL] (e : LL →+* Kf)

theorem rowAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {k n : ℕ}
    (U : Matrix (Fin k) (Fin k) R) (f : MvPolynomial (Fin k × Fin n) R) :
    rowAct S (U.map φ) (map φ f) = map φ (rowAct R U f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [rowAct, map_sum, Matrix.map_apply]

theorem glMap_inv {k : ℕ} (g : GL (Fin k) LL) :
    ((g : Matrix (Fin k) (Fin k) LL).map e)⁻¹ = ((g⁻¹ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map e := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul]
  simp

theorem glMap_det {k : ℕ} (g : GL (Fin k) LL) : IsUnit ((g : Matrix (Fin k) (Fin k) LL).map e).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := ((g⁻¹ : GL (Fin k) LL) : Matrix (Fin k) (Fin k) LL).map e)
  rw [← Matrix.map_mul]
  simp

theorem dl_rat (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : GL (Fin (m + 1)) LL) :
    Dl0 O m lam (colSpan O ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ≤
      Submodule.span O {F | F ∈ Dl0 O m lam (colSpan O ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ∧
        ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = F} := by
  set gK : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e with hgK
  have hdet : IsUnit gK.det := glMap_det e g
  rw [dw_eq hinj m lam hlam gK hdet]
  let T : MvPolynomial (Fin (m + 1) × Fin (m + 1)) O →ₗ[O] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    ((LinearMap.lsmul Kf _ (gK.det ^ (-(lam (Fin.last m))))).restrictScalars O) ∘ₗ
      ((rowAct Kf (n := m + 1) gK⁻¹).toLinearMap.restrictScalars O) ∘ₗ
        (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
  have hT : ∀ x, T x = gK.det ^ (-(lam (Fin.last m))) • rowAct Kf gK⁻¹ (map (algebraMap O Kf) x) := fun x => rfl
  have hmem : ∀ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), T f ∈ deltaLTw O Kf m lam gK := by
    intro f hf
    refine ⟨rowAct Kf gK⁻¹ (map (algebraMap O Kf) f), ⟨f, hf, ?_⟩, rfl⟩
    change map (algebraMap O Kf) f = rowAct Kf gK (rowAct Kf gK⁻¹ (map (algebraMap O Kf) f))
    rw [ldlat_rowAct_inv_left rowActMul gK hdet]
  have key : weyl O (m + 1) (m + 1) le_rfl (nuOf lam) ≤
      (Submodule.span O {F | F ∈ deltaLTw O Kf m lam gK ∧
        ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = F}).comap T := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨wd, rfl⟩
    apply Submodule.subset_span
    refine ⟨hmem _ (Submodule.subset_span ⟨wd, rfl⟩), ?_⟩
    refine ⟨C ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ (-(lam (Fin.last m)))) *
      rowAct LL ((g⁻¹ : GL (Fin (m + 1)) LL) : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
        (applyWord LL wd (hw LL le_rfl (nuOf lam))), ?_⟩
    rw [hT, map_mul, map_C, ← rowAct_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map, ← lclosedeq_applyWord_map,
      lclosedeq_hw_map, ← glMap_inv, map_zpow₀, ← smul_eq_C_mul]
    congr 2
    rw [RingHom.map_det]; rfl
  rintro _ ⟨F0, ⟨f, hf, hfe⟩, rfl⟩
  have hfe' : map (algebraMap O Kf) f = rowAct Kf gK F0 := hfe
  have hF0 : F0 = rowAct Kf gK⁻¹ (map (algebraMap O Kf) f) := by
    rw [hfe', ldlat_rowAct_inv_right rowActMul gK hdet]
  have := key hf
  rw [Submodule.mem_comap, hT, ← hF0] at this
  exact this

theorem htenW_rat (hinj : Function.Injective (algebraMap O Kf)) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hdom : ∀ s, Antitone (lamAt lam0 s)) (g : Fin n' → GL (Fin (m + 1)) LL) :
    HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ≤
      Submodule.span O {z | z ∈ HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) ∧
        ∃ Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL, map e Q = z} := by
  have hdef : HtenW O lam0 (fun s => colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)) =
      Submodule.span O {P | ∃ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
        (∀ s, F s ∈ Dl0 O m (lamAt lam0 s) (colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e))) ∧
          P = ∏ s, blockEmb Kf s (F s)} := rfl
  conv_lhs => rw [hdef]
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have h1 := tens_span (O := O) (Y := MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
    (X := fun _ : Fin n' => MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (fun s => (blockEmb Kf s).toLinearMap.restrictScalars O)
    (fun s => Dl0 O m (lamAt lam0 s) (colSpan O ((g s : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map e)))
    (fun _ x => ∃ Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL, map e Q = x)
    (fun s => dl_rat e hinj m (lamAt lam0 s) (hdom s) (g s)) F hF
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨F', hF', rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hdef]
    exact Submodule.subset_span ⟨F', fun s => (hF' s).1, rfl⟩
  · choose Q hQ using fun s => (hF' s).2
    refine ⟨∏ s, blockEmb LL s (Q s), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    show map e (rename _ (Q s)) = rename _ (F' s)
    rw [map_rename, hQ]

end One

section All

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatBasisAt (L : G.P.Tup) : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)), ∃ g : GL (Fin (G.P.m + 1)) LL,
    extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
      colSpan G.O ((g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) LL).map e)

def RatBasis : Prop := ∀ L : G.P.Tup, G.P.IsLatTup L → RatBasisAt G e L

theorem htupW_rat (L : G.P.Tup) (hB : RatBasisAt G e L) :
    G.P.HtupW L ≤ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L ∧ RatX G e ξ} := by
  choose g hg using hB
  have hdef : G.P.HtupW L = Submodule.span G.O {X | ∃ F : ∀ v, Pol G v,
      (∀ v, F v ∈ HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ∧
        X = ∏ v, G.P.vEmb v (F v)} := rfl
  conv_lhs => rw [hdef]
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have hv : ∀ v, (HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ≤
      Submodule.span G.O {z | (z ∈ HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) ∧
        ∃ Q : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL, map e Q = z} := by
    intro v
    have e1 : (fun s : Fin (G.P.n' v) => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) =
        fun s => colSpan G.O ((g v s : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) LL).map e) := funext (hg v)
    rw [e1]
    exact htenW_rat e (lb_inj G v) (G.P.lam0 v) (je_dom G v) (g v)
  have h1 := tens_span (O := G.O) (Y := G.P.Xsp) (X := fun v => Pol G v)
    (fun v => (G.P.vEmb v).toLinearMap.restrictScalars G.O)
    (fun v => HtenW G.O (G.P.lam0 v) fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v))
    (fun v x => ∃ Q : MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL, map e Q = x)
    hv F hF
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨F', hF', rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hdef]
    exact Submodule.subset_span ⟨F', fun v => (hF' v).1, rfl⟩
  · choose Q hQ using fun v => (hF' v).2
    refine ⟨∏ v, rename (fun x => (⟨v, x⟩ : Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1)))) (Q v), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show map e (rename _ (Q v)) = rename _ (F' v)
    rw [map_rename, hQ]

end All

end Formalism.L2.G.Cmp
