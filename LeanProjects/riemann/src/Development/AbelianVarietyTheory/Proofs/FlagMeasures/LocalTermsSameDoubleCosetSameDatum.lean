import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.SameDC

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

lemma unitary_mul {a b : V ≃ₗ[E] V} (ha : IsUnitary H a) (hb : IsUnitary H b) :
    IsUnitary H (a * b) := by
  intro x y
  change H.h (a (b x)) (a (b y)) = _
  rw [ha, hb]

lemma unitary_inv {a : V ≃ₗ[E] V} (ha : IsUnitary H a) : IsUnitary H a⁻¹ := by
  intro x y
  have := ha (a.symm x) (a.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

lemma X_comp (k : V ≃ₗ[E] V) {r : ℕ} (f : Fin (r + 1) → V) :
    H.X (fun b => k (f b)) = (H.X f).map (k : V →ₗ[E] V) := by
  unfold HermSp.X
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

def Good (X : Submodule E V) (u : V ≃ₗ[E] V) : Prop :=
  IsUnitary H u ∧ ∀ v ∈ H.perp X, u v - v ∈ X

lemma good_map_le {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ x ∈ X, u x ∈ X := by
  intro x hx
  have := X.add_mem (hu.2 x (hX hx)) hx
  simpa using this

lemma good_perp {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ v ∈ H.perp X, u v ∈ H.perp X := by
  intro v hv
  have := (H.perp X).add_mem (hX (hu.2 v hv)) hv
  simpa using this

lemma good_inv {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    Good H X u⁻¹ := by
  refine ⟨unitary_inv H hu.1, fun v hv => ?_⟩
  have hv' : u.symm v ∈ H.perp X := by
    intro x hx
    have := hu.1 (u.symm v) x
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    exact hv _ (good_map_le H hX hu x hx)
  have := X.neg_mem (hu.2 _ hv')
  rw [LinearEquiv.apply_symm_apply, neg_sub] at this
  exact this

lemma good_of_NU {r : ℕ} {f : Fin (r + 1) → V} {u : V ≃ₗ[E] V} (hu : u ∈ NU H f) :
    Good H (H.X f) u := ⟨hu.1, hu.2.2⟩

lemma NU_conj {r : ℕ} {f : Fin (r + 1) → V} {u k : V ≃ₗ[E] V} (hk : IsUnitary H k)
    (hu : u ∈ NU H f) : k * u * k⁻¹ ∈ NU H (fun b => k (f b)) := by
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨unitary_mul H (unitary_mul H hk h1) (unitary_inv H hk), fun a => ?_, fun v hv => ?_⟩
  · change k (u (k.symm (k (f a.castSucc)))) - k (f a.castSucc) ∈ _
    rw [LinearEquiv.symm_apply_apply, ← map_sub]
    have := Submodule.mem_map_of_mem (f := (k : V →ₗ[E] V)) (h2 a)
    rw [Submodule.map_span, Set.image_image] at this
    exact this
  · have hv' : k.symm v ∈ H.perp (H.X f) := by
      intro x hx
      rw [← hk (k.symm v) x, LinearEquiv.apply_symm_apply]
      apply hv
      rw [X_comp]
      exact Submodule.mem_map_of_mem hx
    change k (u (k.symm v)) - v ∈ _
    have e : k (u (k.symm v)) - v = k (u (k.symm v) - k.symm v) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]
    rw [e, X_comp]
    exact Submodule.mem_map_of_mem (h3 _ hv')

lemma N_map_X (hM : M.OK) {r : ℕ} (Fr : FrameD H r) (hT : Fr.T ≠ 0) {u : V ≃ₗ[E] V}
    (hu : u ∈ Fr.N) : H.X (fun b => u (Fr.f b)) = H.X Fr.f := by
  have hN := (UnipOnto.unipotent_onto M hM H r Fr hT).1
  have hX := UnipOnto.X_le_perp Fr
  have g1 := good_of_NU H ((hN u).1 hu)
  have g2 := good_of_NU H ((hN u⁻¹).1 (Fr.N.inv_mem hu))
  rw [X_comp]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact good_map_le H hX g1 x hx
  · intro x hx
    exact ⟨u.symm x, good_map_le H hX g2 x hx, u.apply_symm_apply x⟩

lemma perp_map_iff {k : V ≃ₗ[E] V} (hk : IsUnitary H k) (S : Submodule E V) (v : V) :
    k v ∈ H.perp (S.map (k : V →ₗ[E] V)) ↔ v ∈ H.perp S := by
  constructor
  · intro h x hx
    rw [← hk v x]
    exact h _ (Submodule.mem_map_of_mem hx)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, hk]
    exact h x hx

lemma mkW_eq {r : ℕ} {f : Fin (r + 1) → V} (x y : ↥(H.perp (H.X f))) (h : (x : V) - y ∈ H.X f) :
    H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

lemma Lset_img {r : ℕ} {f : Fin (r + 1) → V} {u : V ≃ₗ[E] V} (hX : H.X f ≤ H.perp (H.X f))
    (hu : Good H (H.X f) u) (Λ : Submodule M.L.O V) : H.Lset (img u Λ) f = H.Lset Λ f := by
  have hu' := good_inv H hX hu
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (TermOver.mem_img u Λ x).1 hxΛ
    have hyp : y ∈ H.perp (H.X f) := by
      have := good_perp H hX hu' (x : V) x.2
      rw [← hyx] at this
      change u.symm (u y) ∈ _ at this
      rwa [LinearEquiv.symm_apply_apply] at this
    refine ⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩
    change (x : V) - y ∈ _
    rw [← hyx]
    exact hu.2 y hyp
  · rintro ⟨y, hyΛ, rfl⟩
    exact ⟨⟨u y, good_perp H hX hu y y.2⟩, (TermOver.mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩,
      mkW_eq H _ _ (hu.2 y y.2)⟩

lemma smulLat_img (c : E) (k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    H.smulLat c (img k Λ) = img k (H.smulLat c Λ) := by
  unfold HermSp.smulLat img
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨c • y, ⟨y, hy, rfl⟩, map_smul k c y⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, (map_smul k c y).symm⟩

lemma cong_img {r : ℕ} {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} (k : V ≃ₗ[E] V)
    (hX : H.X f₂ = (H.X f₁).map (k : V →ₗ[E] V)) (hX' : H.X f₂' = (H.X f₁').map (k : V →ₗ[E] V))
    (Λ : Submodule M.L.O V) (v : V) :
    Cong H (img k Λ) f₂ f₂' (k v) ↔ Cong H Λ f₁ f₁' v := by
  unfold Cong
  rw [smulLat_img]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hbX, hcX, he⟩
    obtain ⟨a0, ha0, rfl⟩ := (TermOver.mem_img k _ a).1 ha
    obtain ⟨b0, hb0, rfl⟩ := (TermOver.mem_img k _ b).1 hb
    obtain ⟨c0, hc0, rfl⟩ := (TermOver.mem_img k _ c).1 hc
    refine ⟨a0, ha0, b0, hb0, c0, hc0, ?_, ?_, ?_⟩
    · rw [hX] at hbX
      obtain ⟨y, hy, hyk⟩ := hbX
      rw [LinearEquiv.coe_coe] at hyk
      rwa [← k.injective hyk]
    · rw [hX'] at hcX
      obtain ⟨y, hy, hyk⟩ := hcX
      rw [LinearEquiv.coe_coe] at hyk
      rwa [← k.injective hyk]
    · apply k.injective
      rw [he, map_add, map_add]
  · rintro ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩
    refine ⟨k a, (TermOver.mem_img k _ _).2 ⟨a, ha, rfl⟩, k b, (TermOver.mem_img k _ _).2 ⟨b, hb, rfl⟩,
      k c, (TermOver.mem_img k _ _).2 ⟨c, hc, rfl⟩, ?_, ?_, by rw [map_add, map_add]⟩
    · rw [hX]; exact Submodule.mem_map_of_mem hbX
    · rw [hX']; exact Submodule.mem_map_of_mem hcX

lemma iota_char (gs : SplitG M.L) (hs : M.split = some gs) {r : ℕ} {f f' : Fin (r + 1) → V}
    (T T' : F) (hX : H.X f ≤ H.perp (H.X f)) (hX' : H.X f' ≤ H.perp (H.X f'))
    (Λ : Submodule M.L.O V) (p : H.Wb f' × H.Wb f) :
    p ∈ H.iotaGraph gs ⟨Λ, f, f', T, T'⟩ ↔
      ∃ (x' : ↥(H.perp (H.X f'))) (x : ↥(H.perp (H.X f))), (x' : V) ∈ Λ ∧ (x : V) ∈ Λ ∧
        Cong H Λ f f' ((x : V) - x') ∧ p = (H.mkW f' x', H.mkW f x) := by
  have ht : theta M = (gs.q : F) := by unfold theta; rw [hs]
  constructor
  · rintro ⟨x', x, h1, h2, h3, rfl⟩
    refine ⟨x', x, h1, h2, ⟨(x : V) - x', by rw [ht]; exact h3, 0, Λ.zero_mem, 0, Λ.zero_mem,
      Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩, rfl⟩
  · rintro ⟨x', x, h1, h2, ⟨a, ha, b, hb, c, hc, hbX, hcX, he⟩, rfl⟩
    refine ⟨⟨(x' : V) + c, (H.perp _).add_mem x'.2 (hX' hcX)⟩,
      ⟨(x : V) - b, (H.perp _).sub_mem x.2 (hX hbX)⟩, Λ.add_mem h1 hc, Λ.sub_mem h2 hb, ?_, ?_⟩
    · have e : (x : V) - b - (x' + c) = a := by
        rw [show (x : V) - b - (x' + c) = ((x : V) - x') - b - c by abel, he]; abel
      change (x : V) - b - (x' + c) ∈ _
      rw [e, ← ht]; exact ha
    · refine Prod.ext (mkW_eq H _ _ ?_) (mkW_eq H _ _ ?_)
      · change (x' : V) - (x' + c) ∈ _
        rw [show (x' : V) - (x' + c) = -c by abel]; exact Submodule.neg_mem _ hcX
      · change (x : V) - (x - b) ∈ _
        rw [show (x : V) - (x - b) = b by abel]; exact hbX

lemma tri_map (k : V ≃ₗ[E] V) {n : ℕ} {f g : Fin n → V} (h : Tri E f g) :
    Tri E (fun b => k (f b)) (fun b => k (g b)) := by
  obtain ⟨A, hA, hC⟩ := h
  exact ⟨A, hA, fun b => by
    show k (g b) = ∑ a, A a b • k (f a)
    rw [hC b, map_sum]; simp only [map_smul]⟩

lemma tri_trans {n : ℕ} {f g h : Fin n → V} (h1 : Tri E f g) (h2 : Tri E g h) : Tri E f h := by
  obtain ⟨A, ⟨hA0, hA1⟩, hA⟩ := h1
  obtain ⟨B, ⟨hB0, hB1⟩, hB⟩ := h2
  refine ⟨A * B, ⟨fun a b hab => ?_, fun a => ?_⟩, fun c => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j < a
    · rw [hA0 a j hj, zero_mul]
    · rw [hB0 j b (lt_of_lt_of_le hab (not_lt.1 hj)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA1, hB1, one_mul]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hA0 a j h, zero_mul]
      · rw [hB0 j a h, mul_zero]
    · simp
  · have hA' : ∀ b, g b = ∑ a, A a b • f a := hA
    show h c = ∑ a, (A * B) a c • f a
    rw [hB c]
    simp only [hA', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

lemma isTerm_move {r : ℕ} {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {t : Term V M r} (ht : H.IsTerm t) :
    H.IsTerm (move g t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  have hZ : H.Zhat (move g t).f (move g t).f' = H.Zhat t.f t.f' := by
    ext a b
    simp only [HermSp.Zhat, Matrix.of_apply, move]
    exact hg _ _
  have hD : ∀ l, H.Dl (move g t).f (move g t).f' l = H.Dl t.f t.f' l := by
    intro l; unfold HermSp.Dl; rw [hZ]
  refine ⟨TermOver.img_selfDual H hg h1, TermOver.img_frame H hg h2, TermOver.img_frame H hg h3,
    by rw [hD]; exact h4, ?_, fun gs hgs => ?_⟩
  · unfold HermSp.Gdet; rw [hD, hD]; exact h5
  · obtain ⟨a, b, c⟩ := h6 gs hgs
    refine ⟨a, b, fun j => ?_⟩
    change g (t.f' j) - g (t.f j) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub, smulLat_img]
    exact (TermOver.mem_img g _ _).2 ⟨_, c j, rfl⟩

end GlobalTheory.LocOver.SameDC

namespace GlobalTheory.LocOver.SameDC

theorem same_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (t₁ t₂ : Term V M r), H.IsTerm t₁ → H.IsTerm t₂ → t₂.abelian₂ = t₁.abelian₂ → t₂.T = t₁.T → t₂.T' = t₁.T' → ∀ n ∈ NU H t₁.f, ∀ m ∈ NU H t₁.f', img (n * m) t₁.abelian₂ = t₁.abelian₂ → Tri E t₁.f t₂.f → Tri E (fun b => (n * m) (t₁.f' b)) t₂.f' → (M.split ≠ none → ∀ x' ∈ t₁.abelian₂, ∀ x ∈ t₁.abelian₂, x' ∈ H.perp (H.X t₁.f') → x ∈ H.perp (H.X t₁.f) → (Cong H t₁.abelian₂ t₁.f t₁.f' (x - x') ↔ Cong H t₁.abelian₂ t₂.f t₂.f' (x - (n * m) x'))) → ∀ d : Datum P, Over P d t₁ → Over P d t₂ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP t₁ t₂ ht₁ ht₂ hΛ hT hT' n hn m hm hnm htri htri'
    hcong d hov
  obtain ⟨g, hg, d', hdd', hT1, hT1', ⟨n₁, hn₁, hf₁, hΛ₁⟩, ⟨n₁', hn₁', hf₁', hΛ₁'⟩, hsp⟩ := hov
  have hAT : P.A.T ≠ 0 := hP.2.2.2.2.2.2.2.1
  have hBT : P.B.T ≠ 0 := hP.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hNA, hTA, hOA⟩ := UnipOnto.unipotent_onto M hM H r P.A hAT
  obtain ⟨hNB, hTB, hOB⟩ := UnipOnto.unipotent_onto M hM H r P.B hBT
  have hXA := UnipOnto.X_le_perp P.A
  have hXB := UnipOnto.X_le_perp P.B
  have ef₁ : (fun b => g (t₁.f b)) = fun b => n₁ (P.A.f b) := hf₁
  have ef₁' : (fun b => g (t₁.f' b)) = fun b => n₁' (P.B.f b) := hf₁'
  have hXA1 : H.X P.A.f = (H.X t₁.f).map (g : V →ₗ[E] V) := by
    rw [← X_comp, ef₁, N_map_X H hM P.A hAT hn₁]
  have hXB1 : H.X P.B.f = (H.X t₁.f').map (g : V →ₗ[E] V) := by
    rw [← X_comp, ef₁', N_map_X H hM P.B hBT hn₁']

  have ha : g * n * g⁻¹ ∈ NU H (fun b => n₁ (P.A.f b)) := by
    rw [← ef₁]; exact NU_conj H hg hn
  have hb : g * m * g⁻¹ ∈ NU H (fun b => n₁' (P.B.f b)) := by
    rw [← ef₁']; exact NU_conj H hg hm
  have gA : Good H (H.X P.A.f) (g * n * g⁻¹) := by
    have := good_of_NU H ha; rwa [N_map_X H hM P.A hAT hn₁] at this
  have gB : Good H (H.X P.B.f) (g * m * g⁻¹) := by
    have := good_of_NU H hb; rwa [N_map_X H hM P.B hBT hn₁'] at this
  have gA' : Good H (H.X P.A.f) (g * n⁻¹ * g⁻¹) := by
    have := good_inv H hXA gA
    rwa [show (g * n * g⁻¹)⁻¹ = g * n⁻¹ * g⁻¹ by group] at this
  have gB' := good_inv H hXB gB

  have hn₁u : IsUnitary H n₁ := ((hNA n₁).1 hn₁).1
  have hn₁u' : IsUnitary H n₁' := ((hNB n₁').1 hn₁').1
  have hc : n₁⁻¹ * (g * n * g⁻¹) * n₁⁻¹⁻¹ ∈ NU H P.A.f := by
    have := NU_conj H (unitary_inv H hn₁u) ha
    have e : (fun b => n₁⁻¹ (n₁ (P.A.f b))) = P.A.f := by
      funext b; exact n₁.symm_apply_apply _
    rwa [e] at this
  have hd : n₁'⁻¹ * (g * m * g⁻¹) * n₁'⁻¹⁻¹ ∈ NU H P.B.f := by
    have := NU_conj H (unitary_inv H hn₁u') hb
    have e : (fun b => n₁'⁻¹ (n₁' (P.B.f b))) = P.B.f := by
      funext b; exact n₁'.symm_apply_apply _
    rwa [e] at this
  have hn₂ : n₁ * (n₁⁻¹ * (g * n * g⁻¹) * n₁⁻¹⁻¹)⁻¹ ∈ P.A.N :=
    P.A.N.mul_mem hn₁ (P.A.N.inv_mem ((hNA _).2 hc))
  have hn₂' : n₁' * (n₁'⁻¹ * (g * m * g⁻¹) * n₁'⁻¹⁻¹) ∈ P.B.N :=
    P.B.N.mul_mem hn₁' ((hNB _).2 hd)
  have hTri1 : Tri E P.A.f (fun b => (g * n⁻¹) (t₁.f b)) := by
    have := hTA _ hn₂
    have e : (fun b => (n₁ * (n₁⁻¹ * (g * n * g⁻¹) * n₁⁻¹⁻¹)⁻¹) (P.A.f b)) =
        fun b => (g * n⁻¹) (t₁.f b) := by
      funext b
      rw [show n₁ * (n₁⁻¹ * (g * n * g⁻¹) * n₁⁻¹⁻¹)⁻¹ = g * n⁻¹ * g⁻¹ * n₁ by group]
      change (g * n⁻¹ * g⁻¹) (n₁ (P.A.f b)) = _
      rw [← congrFun ef₁ b]
      change g (n⁻¹ (g.symm (g (t₁.f b)))) = _
      rw [LinearEquiv.symm_apply_apply]; rfl
    rwa [e] at this
  have hTri2 : Tri E P.B.f (fun b => (g * m) (t₁.f' b)) := by
    have := hTB _ hn₂'
    have e : (fun b => (n₁' * (n₁'⁻¹ * (g * m * g⁻¹) * n₁'⁻¹⁻¹)) (P.B.f b)) =
        fun b => (g * m) (t₁.f' b) := by
      funext b
      rw [show n₁' * (n₁'⁻¹ * (g * m * g⁻¹) * n₁'⁻¹⁻¹) = g * m * g⁻¹ * n₁' by group]
      change (g * m * g⁻¹) (n₁' (P.B.f b)) = _
      rw [← congrFun ef₁' b]
      change g (m (g.symm (g (t₁.f' b)))) = _
      rw [LinearEquiv.symm_apply_apply]; rfl
    rwa [e] at this
  have hTriA : Tri E P.A.f (fun b => (g * n⁻¹) (t₂.f b)) := tri_trans hTri1 (tri_map (g * n⁻¹) htri)
  have hTriB : Tri E P.B.f (fun b => (g * n⁻¹) (t₂.f' b)) := by
    refine tri_trans hTri2 ?_
    have := tri_map (g * n⁻¹) htri'
    have e : (fun b => (g * n⁻¹) ((n * m) (t₁.f' b))) = fun b => (g * m) (t₁.f' b) := by
      funext b
      rw [← LinearEquiv.mul_apply (g * n⁻¹), show g * n⁻¹ * (n * m) = g * m by group]
    rwa [e] at this

  have hg₂ : IsUnitary H (g * n⁻¹) := unitary_mul H hg (unitary_inv H hn.1)
  have htt : H.IsTerm (move (g * n⁻¹) t₂) := isTerm_move H hg₂ ht₂
  obtain ⟨d'', hd''⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames M hM H r P (move (g * n⁻¹) t₂) htt
    (by change t₂.T = P.A.T; rw [hT]; exact hT1) (by change t₂.T' = P.B.T; rw [hT']; exact hT1')
    hTriA hTriB

  have hlamA : img (g * n⁻¹) t₂.abelian₂ = img (g * n⁻¹ * g⁻¹) (img g t₁.abelian₂) := by
    rw [hΛ, ← TermOver.img_mul]; congr 1; group
  have hnm' : img n⁻¹ t₁.abelian₂ = img m t₁.abelian₂ := by
    conv_lhs => rw [← hnm]
    rw [← TermOver.img_mul]; congr 1; group
  have hlamM : img (g * n⁻¹) t₂.abelian₂ = img (g * m) t₁.abelian₂ := by
    rw [hΛ, TermOver.img_mul, hnm', ← TermOver.img_mul]
  have hlamB : img (g * n⁻¹) t₂.abelian₂ = img (g * m * g⁻¹) (img g t₁.abelian₂) := by
    rw [hlamM, ← TermOver.img_mul]; congr 1; group

  obtain ⟨n₃, hn₃m, hn₃⟩ := hOA _ hTriA
  obtain ⟨n₃', hn₃m', hn₃'⟩ := hOB _ hTriB
  have hXA2 : H.X P.A.f = (H.X t₂.f).map ((g * n⁻¹ : V ≃ₗ[E] V) : V →ₗ[E] V) := by
    rw [← X_comp, hn₃, N_map_X H hM P.A hAT hn₃m]
  have hXB2 : H.X P.B.f = (H.X t₂.f').map ((g * n⁻¹ : V ≃ₗ[E] V) : V →ₗ[E] V) := by
    rw [← X_comp, hn₃', N_map_X H hM P.B hBT hn₃m']

  have hLA : H.Lset (move (g * n⁻¹) t₂).abelian₂ P.A.f = H.Lset (move g t₁).abelian₂ P.A.f := by
    change H.Lset (img (g * n⁻¹) t₂.abelian₂) P.A.f = H.Lset (img g t₁.abelian₂) P.A.f
    rw [hlamA]; exact Lset_img H hXA gA' _
  have hLB : H.Lset (move (g * n⁻¹) t₂).abelian₂ P.B.f = H.Lset (move g t₁).abelian₂ P.B.f := by
    change H.Lset (img (g * n⁻¹) t₂.abelian₂) P.B.f = H.Lset (img g t₁.abelian₂) P.B.f
    rw [hlamB]; exact Lset_img H hXB gB _

  have hio : ∀ gs, M.split = some gs →
      H.iotaGraph gs ⟨(move (g * n⁻¹) t₂).abelian₂, P.A.f, P.B.f, (move (g * n⁻¹) t₂).T,
        (move (g * n⁻¹) t₂).T'⟩ =
      H.iotaGraph gs ⟨(move g t₁).abelian₂, P.A.f, P.B.f, (move g t₁).T, (move g t₁).T'⟩ := by
    intro gs hs
    have hc := hcong (by rw [hs]; exact Option.some_ne_none _)
    ext p
    rw [iota_char H gs hs _ _ hXA hXB, iota_char H gs hs _ _ hXA hXB]
    constructor
    · rintro ⟨y', y, hy', hy, hC, rfl⟩
      obtain ⟨x, hx, hyx⟩ := (TermOver.mem_img (g * n⁻¹) t₂.abelian₂ _).1 hy
      have hy'' : (y' : V) ∈ img (g * m) t₁.abelian₂ := by rw [← hlamM]; exact hy'
      obtain ⟨x', hx', hyx'⟩ := (TermOver.mem_img (g * m) t₁.abelian₂ _).1 hy''
      rw [hΛ] at hx
      have hgx : g x = (g * n * g⁻¹) y := by
        rw [← hyx, ← LinearEquiv.mul_apply, show g * n * g⁻¹ * (g * n⁻¹) = g by group]
      have hgx' : g x' = (g * m * g⁻¹)⁻¹ y' := by
        rw [← hyx', ← LinearEquiv.mul_apply, show (g * m * g⁻¹)⁻¹ * (g * m) = g by group]
      have hxp : x ∈ H.perp (H.X t₁.f) := by
        rw [← perp_map_iff H hg, ← hXA1, hgx]; exact good_perp H hXA gA _ y.2
      have hxp' : x' ∈ H.perp (H.X t₁.f') := by
        rw [← perp_map_iff H hg, ← hXB1, hgx']; exact good_perp H hXB gB' _ y'.2
      have e1 : (y : V) - y' = (g * n⁻¹) (x - (n * m) x') := by
        rw [map_sub, hyx, ← hyx', ← LinearEquiv.mul_apply (g * n⁻¹),
          show g * n⁻¹ * (n * m) = g * m by group]
      change Cong H (img (g * n⁻¹) t₂.abelian₂) P.A.f P.B.f _ at hC
      rw [e1, cong_img H (g * n⁻¹) hXA2 hXB2, hΛ] at hC
      have hC1 := (hc x' hx' x hx hxp' hxp).2 hC
      refine ⟨⟨g x', by rw [hXB1, perp_map_iff H hg]; exact hxp'⟩,
        ⟨g x, by rw [hXA1, perp_map_iff H hg]; exact hxp⟩,
        (TermOver.mem_img g _ _).2 ⟨x', hx', rfl⟩, (TermOver.mem_img g _ _).2 ⟨x, hx, rfl⟩, ?_, ?_⟩
      · change Cong H (img g t₁.abelian₂) P.A.f P.B.f (g x - g x')
        rw [← map_sub, cong_img H g hXA1 hXB1]; exact hC1
      · refine Prod.ext (mkW_eq H _ _ ?_) (mkW_eq H _ _ ?_)
        · change (y' : V) - g x' ∈ _
          rw [hgx', ← neg_sub]; exact Submodule.neg_mem _ (gB'.2 _ y'.2)
        · change (y : V) - g x ∈ _
          rw [hgx, ← neg_sub]; exact Submodule.neg_mem _ (gA.2 _ y.2)
    · rintro ⟨y', y, hy', hy, hC, rfl⟩
      obtain ⟨x, hx, hyx⟩ := (TermOver.mem_img g t₁.abelian₂ _).1 hy
      obtain ⟨x', hx', hyx'⟩ := (TermOver.mem_img g t₁.abelian₂ _).1 hy'
      have hxp : x ∈ H.perp (H.X t₁.f) := by
        rw [← perp_map_iff H hg, ← hXA1, hyx]; exact y.2
      have hxp' : x' ∈ H.perp (H.X t₁.f') := by
        rw [← perp_map_iff H hg, ← hXB1, hyx']; exact y'.2
      change Cong H (img g t₁.abelian₂) P.A.f P.B.f _ at hC
      rw [← hyx, ← hyx', ← map_sub, cong_img H g hXA1 hXB1] at hC
      have hC2 := (hc x' hx' x hx hxp' hxp).1 hC
      rw [← hΛ, ← cong_img H (g * n⁻¹) hXA2 hXB2] at hC2
      refine ⟨⟨(g * m * g⁻¹) y', good_perp H hXB gB _ y'.2⟩,
        ⟨(g * n⁻¹ * g⁻¹) y, good_perp H hXA gA' _ y.2⟩, ?_, ?_, ?_, ?_⟩
      · change _ ∈ img (g * n⁻¹) t₂.abelian₂
        rw [hlamM]
        exact (TermOver.mem_img _ _ _).2 ⟨x', hx', by
          change (g * m) x' = (g * m * g⁻¹) (y' : V)
          rw [← hyx', ← LinearEquiv.mul_apply, show g * m * g⁻¹ * g = g * m by group]⟩
      · change _ ∈ img (g * n⁻¹) t₂.abelian₂
        exact (TermOver.mem_img _ _ _).2 ⟨x, by rw [hΛ]; exact hx, by
          change (g * n⁻¹) x = (g * n⁻¹ * g⁻¹) (y : V)
          rw [← hyx, ← LinearEquiv.mul_apply, show g * n⁻¹ * g⁻¹ * g = g * n⁻¹ by group]⟩
      · change Cong H (img (g * n⁻¹) t₂.abelian₂) P.A.f P.B.f ((g * n⁻¹ * g⁻¹) y - (g * m * g⁻¹) y')
        have e : (g * n⁻¹ * g⁻¹) (y : V) - (g * m * g⁻¹) y' = (g * n⁻¹) (x - (n * m) x') := by
          rw [← hyx, ← hyx', map_sub, ← LinearEquiv.mul_apply (g * n⁻¹ * g⁻¹),
            ← LinearEquiv.mul_apply (g * m * g⁻¹), ← LinearEquiv.mul_apply (g * n⁻¹) (n * m),
            show g * n⁻¹ * g⁻¹ * g = g * n⁻¹ by group, show g * m * g⁻¹ * g = g * m by group,
            show g * n⁻¹ * (n * m) = g * m by group]
        rw [e]; exact hC2
      · refine Prod.ext (mkW_eq H _ _ ?_) (mkW_eq H _ _ ?_)
        · change (y' : V) - (g * m * g⁻¹) y' ∈ _
          rw [← neg_sub]; exact Submodule.neg_mem _ (gB.2 _ y'.2)
        · change (y : V) - (g * n⁻¹ * g⁻¹) y ∈ _
          rw [← neg_sub]; exact Submodule.neg_mem _ (gA'.2 _ y.2)
  have hdd : d'' = d' := (TermLat.datum_of_lattice M hM H r k P hk hP).2 d'' d' _ _ hd''
    ⟨hT1, hT1', ⟨n₁, hn₁, hf₁, hΛ₁⟩, ⟨n₁', hn₁', hf₁', hΛ₁'⟩, hsp⟩ hLA hLB hio
  subst hdd
  exact ⟨g * n⁻¹, hg₂, d'', hdd', hd''⟩

end GlobalTheory.LocOver.SameDC
