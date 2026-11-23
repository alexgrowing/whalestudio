import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

theorem alg_core {B : Type} [CommRing B] (J F : Ideal B) (hJF : ∀ a ∈ J, ∀ b ∈ J, a * b ∈ F)
    {H H0 D Y0 I0 W : B} (hH : H ∈ J) (hH0 : H0 ∈ J) (hD : D ∈ J) (hI : Y0 * I0 = 1)
    (hW : W * ((1 + H0) * Y0) = 1) :
    (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) ∈ F := by
  set C := W * Y0 with hCdef
  have hC : C * (1 + H0) = 1 := by rw [hCdef]; linear_combination hW
  have hWC : W = C * I0 := by rw [hCdef]; linear_combination (-W) * hI
  set A := H + D * I0 + H * (D * I0) with hA
  have hAJ : A ∈ J := J.add_mem (J.add_mem hH (J.mul_mem_right _ hD)) (J.mul_mem_left _ (J.mul_mem_right _ hD))
  have e : (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) =
      (C * H0) * H0 - (A * C) * H0 + H * (D * I0) := by
    rw [hWC, hA]
    linear_combination (1 + H) * C * hI + (1 - H0 + (H + D * I0 + H * (D * I0))) * hC
  rw [e]
  exact F.add_mem (F.sub_mem (hJF _ (J.mul_mem_left _ hH0) _ hH0) (hJF _ (J.mul_mem_right _ hAJ) _ hH0))
    (hJF _ hH _ (J.mul_mem_right _ hD))

theorem plogK_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (F : Ideal B) {s : ℕ} (hs : 1 ≤ s)
    {x : B} (hx : x ∈ J) (h : ∀ k, 2 ≤ k → δ.dpow k x ∈ F) : plogK δ s x - x ∈ F := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  unfold plogK
  rw [Finset.sum_range_succ']
  have e : (-1 : B) ^ 0 * ((Nat.factorial 0 : ℕ) : B) * δ.dpow (0 + 1) x = x := by
    simp [δ.dpow_one hx]
  rw [e, add_sub_cancel_right]
  exact F.sum_mem fun k _ => F.mul_mem_left _ (h _ (by omega))

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem form_one {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) (x : Φ.A.obj E.D)
    (u : ComposableArrows C 1) :
    E.form σ ![i] x u = E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form
  rw [Fin.prod_univ_one]
  congr 1
  have e : ∀ (h : (Fin.succ (0 : Fin 1)) ⟶ Fin.last 1) (z : Φ.A.obj (u.obj (Fin.last 1))),
      (Φ.A.map (u.map h)).hom z = z := by
    intro h z
    have : h = 𝟙 (Fin.last 1) := Subsingleton.elim _ _
    have e2 : u.map h = 𝟙 (u.obj (Fin.last 1)) := (congrArg u.map this).trans (u.map_id _)
    have e3 : Φ.A.map (u.map h) = 𝟙 (Φ.A.obj (u.obj (Fin.last 1))) := (congrArg Φ.A.map e2).trans (Φ.A.map_id _)
    rw [e3]
    rfl
  exact e _ _

theorem mul2 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) : ∀ a ∈ Φ.J.S T, ∀ b ∈ Φ.J.S T, a * b ∈ (Fil 2).S T := by
  intro a ha b hb
  have h1 : ∀ z ∈ Φ.J.S T, z ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun z hz => by
    rw [Nat.cast_one, hF.one]; exact hz
  exact hF.mul 1 1 T (h1 a ha) (h1 b hb)

theorem const1 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} {E : Frame Φ d} (hc : E.GrConst Fil) {T : C}
    (a b : E.D ⟶ T) (x : Φ.A.obj E.D) : (Φ.A.map a).hom x - (Φ.A.map b).hom x ∈ Φ.J.S T := by
  have h := hc 0 a b (x := x) (by rw [Nat.cast_zero, hF.top 0 le_rfl E.D]; trivial)
  rw [Nat.cast_zero, zero_add, hF.one] at h
  exact h

theorem frame_core {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) {T T' : C} (φ : T ⟶ T') {H H0 W : Φ.A.obj T'}
    (hH : H ∈ Φ.J.S T') (hH0 : H0 ∈ Φ.J.S T')
    (hW : W * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1) :
    (1 + H) * (Φ.A.map (σ T')).hom G * W - 1 -
      (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0)) ∈ (Fil 2).S T' := by
  set v := (Φ.A.map (σ T ≫ φ)).hom with hv
  set w := (Φ.A.map (σ T')).hom with hw
  have hI : v G * v (Ring.inverse G) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hG, map_one]
  have hD : w G - v G ∈ Φ.J.S T' := const1 hF hc _ _ G
  have h1 := alg_core (Φ.J.S T') ((Fil 2).S T') (mul2 hF T') hH hH0 hD hI hW
  have h2 := ((Fil 2).S T').mul_mem_left (v (Ring.inverse G)) (ht T' (σ T') (σ T ≫ φ) G)
  have h3 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) ∈ (Fil 2).S T' :=
    ((Fil 2).S T').sum_mem fun i _ => mul2 hF T' _ (E.mem i _ _) _ (const1 hF hc _ _ _)
  have h4 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) =
      v (Ring.inverse G) * ∑ i, E.a σ i φ * v (p i G) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul v]
    ring
  have h5 : (∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) = ∑ i, E.a σ i φ * v (p i G) := rfl
  rw [h4] at h3
  change v (Ring.inverse G) * (w G - v G - ∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) ∈ _ at h2
  rw [h5] at h2
  have e : (1 + H) * w G * W - 1 - (∑ i, E.a σ i φ * w (Ring.inverse G * p i G) + (H - H0)) =
      ((1 + H) * (v G + (w G - v G)) * W - 1 - ((w G - v G) * v (Ring.inverse G) + H - H0)) +
      v (Ring.inverse G) * (w G - v G - ∑ i, E.a σ i φ * v (p i G)) +
      (v (Ring.inverse G) * (∑ i, E.a σ i φ * v (p i G)) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G)) := by
    ring
  rw [e]
  exact ((Fil 2).S T').add_mem (((Fil 2).S T').add_mem h1 h2) h3

end Fr

section Fr2
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem frame_main {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) (gh : ∀ T, Φ.A.obj T)
    (hg : ∀ T, gh T - (Φ.A.map (σ T)).hom G ∈ Φ.J.S T)
    (hun : ∀ T, ∀ x ∈ Φ.J.S T, IsUnit (1 + x)) :
    (∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T) ∧
    ∀ {T T' : C} (φ : T ⟶ T'),
      (gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 ∈ Φ.J.S T') ∧
      gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 -
        (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) +
          ((gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1) -
            (Φ.A.map φ).hom (gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1))) ∈ (Fil 2).S T' := by
  have hy : ∀ T, IsUnit ((Φ.A.map (σ T)).hom G) := fun T => hG.map (Φ.A.map (σ T)).hom
  have hyi : ∀ T, (Φ.A.map (σ T)).hom G * Ring.inverse ((Φ.A.map (σ T)).hom G) = 1 :=
    fun T => Ring.mul_inverse_cancel _ (hy T)
  have hh : ∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T := by
    intro T
    have e : gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 =
        (gh T - (Φ.A.map (σ T)).hom G) * Ring.inverse ((Φ.A.map (σ T)).hom G) := by
      linear_combination hyi T
    rw [e]
    exact (Φ.J.S T).mul_mem_right _ (hg T)
  refine ⟨hh, ?_⟩
  intro T T' φ
  set H := gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1 with hHd
  set h0 := gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 with hh0
  set H0 := (Φ.A.map φ).hom h0 with hH0d
  have hHm : H ∈ Φ.J.S T' := hh T'
  have hH0m : H0 ∈ Φ.J.S T' := Φ.J.map_mem φ (hh T)
  have e1 : gh T = (1 + h0) * (Φ.A.map (σ T)).hom G := by
    rw [hh0]; linear_combination (-gh T) * hyi T
  have e2 : gh T' = (1 + H) * (Φ.A.map (σ T')).hom G := by
    rw [hHd]; linear_combination (-gh T') * hyi T'
  have hU : IsUnit (gh T) := by
    rw [e1]; exact (hun T _ (hh T)).mul (hy T)
  have e3 : (Φ.A.map φ).hom (gh T) = (1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G := by
    rw [e1, map_mul, map_add, map_one, Φ.A.map_comp]
    rfl
  have hW : Ring.inverse ((Φ.A.map φ).hom (gh T)) * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1 := by
    rw [← e3]
    exact Ring.inverse_mul_cancel _ (hU.map (Φ.A.map φ).hom)
  have key := frame_core hF E hc p ht σ G hG φ hHm hH0m hW
  rw [← e2] at key
  refine ⟨?_, key⟩
  have hle : (Fil 2).S T' ≤ Φ.J.S T' := by
    rw [← hF.one]; exact hF.anti (by norm_num) T'
  have hs : ∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0) ∈ Φ.J.S T' :=
    (Φ.J.S T').add_mem ((Φ.J.S T').sum_mem fun i _ => (Φ.J.S T').mul_mem_right
      ((Φ.A.map (σ T')).hom (Ring.inverse G * p i G)) (E.mem i (σ T ≫ φ) (σ T'))) ((Φ.J.S T').sub_mem hHm hH0m)
  have h6 := (Φ.J.S T').add_mem (hle key) hs
  rw [sub_add_cancel] at h6
  exact h6

end Fr2

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  intro K _ _ X q s hs V V' hVV d t E ε hL p ht σ g hg ĝ hĝ
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  obtain ⟨hc, -, -, h4, -⟩ := hL
  have hG : IsUnit (ε (rs hVV g)) := (hg.map (rs hVV)).map ε
  let gh : ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T :=
    fun T => ĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
  have hgl : ∀ T, gh T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g)) ∈ (sP (KS q s {V})).J.S T := by
    intro T
    have a1 := hĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
    have a2 := h4 T (σ T) (rs hVV g)
    have a3 := GlobalTheory.CompanionTheory.GrForm.ev_res hVV T.obj (ks_in q s V' _ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T).property)
      (ks_in q s V _ T.property) g
    exact Ideal.Quotient.eq.1 (a1.trans (a3.symm.trans a2))
  have hun : ∀ T, ∀ x ∈ (sP (KS q s {V})).J.S T, IsUnit (1 + x) := by
    intro T x hx
    have hn : IsNilpotent (show T.obj.B from x) := by
      obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.ConeZcls.J_nil T.obj
      refine ⟨n, ?_⟩
      have h1 : (show T.obj.B from x) ^ n ∈ T.obj.J ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    exact hn.isUnit_one_add
  obtain ⟨m1, m2⟩ := frame_main hF E hc p ht σ (ε (rs hVV g)) hG gh hgl hun
  refine ⟨fun T => gh T * Ring.inverse (((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g))) - 1, m1, fun u => ?_⟩
  obtain ⟨b1, b2⟩ := m2 (u.map (homOfLE (Fin.zero_le (Fin.last 1))))
  have b3 := plogK_sub_mem (u.obj (Fin.last 1)).obj.δ
    (show Ideal (u.obj (Fin.last 1)).obj.B from (sFil (KS q s {V}) 2).S (u.obj (Fin.last 1)))
    (s := s) (by omega) b1 (fun k hk => hF.anti (by exact_mod_cast hk) _ (hF.dp_mem k _ b1))
  have b4 := ((sFil (KS q s {V}) 2).S (u.obj (Fin.last 1))).add_mem b3 b2
  rw [sub_add_sub_cancel] at b4
  simp only [form_one]
  exact b4

end GlobalTheory.CompanionTheory.ConeLocal.DlogApprox
