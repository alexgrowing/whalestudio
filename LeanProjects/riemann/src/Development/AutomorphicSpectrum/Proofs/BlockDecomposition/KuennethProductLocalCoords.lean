import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubRight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Aff

universe u w

section Algebra

variable {R : Type} [CommRing R]

theorem tensor_sub_left (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have key : ∀ z : M ⊗[R] N, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem tensor_sub_right (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  _root_.UpperTheory.Reformulated.B.Qn17.tensor_sub_right M N

variable {I A : Type} [DecidableEq I] [Fintype A] [DecidableEq A] (M : I → Type u) [∀ t, AddCommMonoid (M t)]
  [∀ t, Module R (M t)] (ι : A → I)

theorem component_lof_ne {i j : I} (h : j ≠ i) (x : M i) : DirectSum.component R I M j (DirectSum.lof R I M i x) = 0 := by
  rw [DirectSum.component.of]
  simp [h.symm]

def sumPi (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) :
    (⨁ t, M t) ≃ₗ[R] ∀ a, M (ι a) :=
  LinearEquiv.ofLinear (LinearMap.pi fun a => DirectSum.component R I M (ι a))
    (∑ a, (DirectSum.lof R I M (ι a)).comp (LinearMap.proj a))
    (by
      refine LinearMap.ext fun f => funext fun b => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply, map_sum]
      rw [Finset.sum_eq_single b]
      · exact DirectSum.component.lof_self R _ _
      · intro a _ hab
        exact component_lof_ne M (fun e => hab (hι e).symm) _
      · intro h
        exact absurd (Finset.mem_univ b) h)
    (by
      refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun x => ?_
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := ht
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
        rw [Finset.sum_eq_single b]
        · rw [DirectSum.component.lof_self]
        · intro a _ hab
          rw [component_lof_ne M (fun e => hab (hι e)) x, map_zero]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · have := hz t ht
        rw [Subsingleton.elim x 0, map_zero, map_zero])

theorem sumPi_lof (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) (b : A) (x : M (ι b)) :
    sumPi (R := R) M ι hι hz (DirectSum.lof R I M (ι b) x) = Pi.single b x := by
  refine funext fun a => ?_
  change DirectSum.component R I M (ι a) (DirectSum.lof R I M (ι b) x) = _
  by_cases h : a = b
  · subst h
    rw [DirectSum.component.lof_self, Pi.single_eq_same]
  · rw [component_lof_ne M (fun e => h (hι e)) x, Pi.single_eq_of_ne h]

end Algebra

variable {K : Type} [Field K]

def diag (c : ℕ) (a : Fin (c + 1)) : Idx c c :=
  ⟨a, a, c - a, c - a, by omega, by omega⟩

theorem diag_inj (c : ℕ) : Function.Injective (diag c) := by
  intro a b h
  exact Fin.ext (congrArg Idx.a h)

theorem kunE_of_diag {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c))
    (hP : ∀ a j, j ≠ a → Subsingleton ((P a).H j)) (hQ : ∀ a j, j ≠ a → Subsingleton ((Q a).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((T a).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((P a).H a) ((Q (c - a)).H (c - a))) ≃ₗ[K] (T c).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (P a).X a) (y : (Q (c - a)).X (c - a))
        (hx : (P a).d a x = 0) (hy : (Q (c - a)).d (c - a) y = 0) (hz : (T c).d c ((pr hc).μ hc x y) = 0),
        e (Pi.single a ((P a).cls x hx ⊗ₜ (Q (c - a)).cls y hy)) = (T c).cls ((pr hc).μ hc x y) hz) :
    KunE pr := by
  intro c n
  have offL : ∀ t : Idx c n, t.i ≠ t.a → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hP t.a t.i h
    exact tensor_sub_left _ _
  have offR : ∀ t : Idx c n, t.j ≠ t.a' → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hQ t.a' t.j h
    exact tensor_sub_right _ _
  by_cases hn : n = c
  · subst hn
    obtain ⟨e, he⟩ := hE n
    have hz : ∀ t, t ∉ Set.range (diag n) → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t ht => by
      refine offL t fun hi => ht ?_
      obtain ⟨a, i, a', j, ha, h⟩ := t
      simp only at hi
      subst hi
      obtain rfl : j = a' := by omega
      obtain rfl : j = n - i := by omega
      exact ⟨⟨i, by omega⟩, rfl⟩
    refine ⟨(sumPi (R := K) (fun t : Idx n n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) (diag n) (diag_inj n) hz).trans e, ?_⟩
    intro t x y hx hy hw
    by_cases ht : t ∈ Set.range (diag n)
    · obtain ⟨b, rfl⟩ := ht
      rw [LinearEquiv.trans_apply, sumPi_lof]
      exact he b (by omega) x y hx hy hw
    · have := hz t ht
      have hi : t.i ≠ t.a := fun hi => ht (by
        obtain ⟨a, i, a', j, ha, h⟩ := t
        simp only at hi
        subst hi
        obtain rfl : j = a' := by omega
        obtain rfl : j = n - i := by omega
        exact ⟨⟨i, by omega⟩, rfl⟩)
      have hB : x ∈ (P t.a).B t.i := by
        have := hP t.a t.i hi
        exact ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 x hx).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim ((P t.a).cls x hx ⊗ₜ[K] (Q t.a').cls y hy) 0, map_zero, map_zero]
      exact (((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hw).2 (CrystallineSemistableComparison.Auxff.memB_left (pr t.ha) t.h x hB y hy)).symm
  · have : Subsingleton ((T c).H n) := hT c n hn
    have hs : ∀ t : Idx c n, Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t => by
      by_cases hi : t.i = t.a
      · refine offR t fun hj => hn ?_
        have := t.ha
        have := t.h
        omega
      · exact offL t hi
    have : Subsingleton (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) := inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem xd_kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (hP : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₁.ι ⋙ E.F₁ a)).H j))
    (hQ : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₂.ι ⋙ E.F₂ a)).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₃.ι ⋙ E.F₃ a)).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((CH.cx (U₁.ι ⋙ E.F₁ a)).H a) ((CH.cx (U₂.ι ⋙ E.F₂ (c - a))).H (c - a))) ≃ₗ[K] (CH.cx (U₃.ι ⋙ E.F₃ c)).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (CH.cx (U₁.ι ⋙ E.F₁ a)).X a) (y : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).X (c - a))
        (hx : (CH.cx (U₁.ι ⋙ E.F₁ a)).d a x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).d (c - a) y = 0)
        (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d c ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) = 0),
        e (Pi.single a ((CH.cx (U₁.ι ⋙ E.F₁ a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).cls y hy)) =
          (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) hz) :
    E.Kun U₁ U₂ U₃ h₁ h₂ :=
  kunE_of_diag (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) hP hQ hT hE

theorem cls_eq {R : Type} [CommRing R] (L : Cx.{w} R) {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0) (hy : L.d n y = 0) :
    L.cls x hx = L.cls y hy := by
  subst e
  rfl

section
variable {X X' P : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q)

theorem hodge_pr_eq (U₁ : ObjectProperty (Thick (smFun X q))) (U₂ : ObjectProperty (Thick (smFun X' q')))
    (U₃ : ObjectProperty (Thick (smFun P (p₁ ≫ q))))
    (h₁ : ∀ T, U₃ T → U₁ ((smS p₁ rfl).G.obj T)) (h₂ : ∀ T, U₃ T → U₂ ((smS p₂ hw).G.obj T)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : CH.Cn (U₁.ι ⋙ G q a) i) (y : CH.Cn (U₂.ι ⋙ G q' a') j) :
    ((hodgeXD q q' p₁ p₂ hw).pr U₁ U₂ U₃ h₁ h₂ ha).μ h x y =
      cupU (p₁ ≫ q) U₃ ha h ((morV p₁ rfl a h₁).pullC i x) ((morV p₂ hw a' h₂).pullC j y) := rfl

end

set_option maxHeartbeats 400000 in

theorem kun_aff : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂  := by
  intro _ hA hK K _ _ X X' P q q' p₁ p₂ hP V V' d d' hc hc' h₁ h₂
  obtain ⟨hZ, hE⟩ := hK K X X' P q q' p₁ p₂ hP V V' d d' hc hc'
  refine xd_kun (hodgeXD q q' p₁ p₂ hP.w.symm) _ _ _ h₁ h₂ ?_ ?_ ?_ ?_
  · exact fun a j hj => (hA K X q V d hc a).1 j hj
  · exact fun a j hj => (hA K X' q' V' d' hc' a).1 j hj
  · exact fun a j hj => (hA K P (p₁ ≫ q) _ (d + d') hZ a).1 j hj
  · intro c
    obtain ⟨e, he⟩ := hE c h₁ h₂
    refine ⟨e, fun a hc x y hx hy hz => ?_⟩
    have eq := hodge_pr_eq q q' p₁ p₂ hP.w.symm (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ hc hc x y
    have hz' : (CH.cx ((inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')).ι ⋙ G (p₁ ≫ q) c)).d c (cupU (p₁ ≫ q) _ hc hc ((morV p₁ rfl a h₁).pullC a x) ((morV p₂ hP.w.symm (c - a) h₂).pullC (c - a) y)) = 0 := by
      rw [← eq]
      exact hz
    exact (he a hc x y hx hy hz').trans (cls_eq _ eq.symm _ _)

end GlobalTheory.CompanionTheory.KunGlue.Aff
