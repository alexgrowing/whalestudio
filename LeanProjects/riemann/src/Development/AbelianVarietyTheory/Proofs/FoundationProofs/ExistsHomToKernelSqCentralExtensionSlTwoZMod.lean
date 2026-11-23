import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CentralExtensionCommutatorSqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
open scoped MatrixGroups TensorProduct commutatorElement
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.CentralExt

theorem exists_ker_mul_commutator {E G : Type*} [Group E] [Group G] (π : E →* G)
    (hs : Function.Surjective π) (hG : commutator G = ⊤) (e : E) :
    ∃ a ∈ π.ker, ∃ c ∈ commutator E, e = a * c := by
  have h1 : (commutator E).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hs,
      ← commutator_def, hG]
  have h2 : π e ∈ (commutator E).map π := h1 ▸ Subgroup.mem_top _
  obtain ⟨c, hc, hce⟩ := h2
  refine ⟨e * c⁻¹, ?_, c, hc, by simp⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hce, mul_inv_cancel]

theorem exists_hom_sq {E G : Type*} [Group E] [Group G] (π : E →* G)
    (hs : Function.Surjective π) (hG : commutator G = ⊤) (hc : π.ker ≤ Subgroup.center E)
    (h2 : ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) :
    ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  choose a ha c hcm hac using exists_ker_mul_commutator π hs hG
  have key : ∀ e, ∀ b ∈ π.ker, ∀ d ∈ commutator E, e = b * d → a e ^ 2 = b ^ 2 := by
    intro e b hb d hd he
    have h3 : b⁻¹ * a e = d * (c e)⁻¹ := by
      have h4 : a e = b * d * (c e)⁻¹ := by
        rw [← he, eq_mul_inv_iff_mul_eq]; exact (hac e).symm
      rw [h4]; group
    have h5 := h2 (b⁻¹ * a e) (mul_mem (inv_mem hb) (ha e))
      (h3 ▸ mul_mem hd (inv_mem (hcm e)))
    have hcomm : Commute b⁻¹ (a e) :=
      ((Subgroup.mem_center_iff.1 (hc (ha e))) b⁻¹)
    rw [hcomm.mul_pow, inv_pow, inv_mul_eq_one] at h5
    exact h5.symm
  refine ⟨MonoidHom.mk' (fun e => a e ^ 2) ?_, fun e => (by exact pow_mem (ha e) 2), fun x hx => ?_⟩
  · intro e f
    have hcomm : Commute (a e) (a f) := ((Subgroup.mem_center_iff.1 (hc (ha f))) (a e))
    rw [← hcomm.mul_pow]
    refine key (e * f) _ (mul_mem (ha e) (ha f)) (c e * c f) (mul_mem (hcm e) (hcm f)) ?_
    have h6 : c e * a f = a f * c e := ((Subgroup.mem_center_iff.1 (hc (ha f))) (c e))
    calc e * f = a e * c e * (a f * c f) := by rw [← hac e, ← hac f]
      _ = a e * (c e * a f) * c f := by group
      _ = a e * a f * (c e * c f) := by rw [h6]; group
  · exact key x x hx 1 (one_mem _) (mul_one x).symm

theorem commutator_sl2_zmod (m : ℕ) (hm : Nat.Coprime m 6) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) = ⊤ := by
  have h2 : Nat.Coprime 2 m := (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hm).symm
  have h3 : Nat.Coprime 3 m := (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hm).symm
  obtain ⟨u, hu⟩ : ∃ u : ZMod m, 2 * u = 1 :=
    ⟨((ZMod.unitOfCoprime 2 h2)⁻¹ : (ZMod m)ˣ), by
      simpa using (ZMod.unitOfCoprime 2 h2).mul_inv⟩
  obtain ⟨v, hv⟩ : ∃ v : ZMod m, 3 * v = 1 :=
    ⟨((ZMod.unitOfCoprime 3 h3)⁻¹ : (ZMod m)ˣ), by
      simpa using (ZMod.unitOfCoprime 3 h3).mul_inv⟩
  set ρ : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) with hρ
  have hs : Function.Surjective ρ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) m
  let d : Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    ⟨!![2, 0; 0, u], by rw [Matrix.det_fin_two_of]; linear_combination hu⟩
  let t : Matrix.SpecialLinearGroup (Fin 2) (ZMod m) :=
    ⟨!![1, v; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hT : ρ ModularGroup.T ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) := by
    have : ρ ModularGroup.T = ⁅d, t⁆ := by
      have h : ρ ModularGroup.T * t * d = d * t := by
        have hT' : (ρ ModularGroup.T).1 = !![1, 1; 0, 1] := by
          ext i j
          change ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod m) = _
          fin_cases i <;> fin_cases j <;> simp
        apply Subtype.ext
        change (ρ ModularGroup.T).1 * !![1, v; 0, 1] * !![2, 0; 0, u] =
          !![2, 0; 0, u] * !![1, v; 0, 1]
        rw [hT', Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e : (1 * 1 + 1 * 0) * 0 + (1 * v + 1 * 1) * u = 2 * v + 0 * 1 := by
          linear_combination (-u) * hv + (2 * v) * hu
        rw [e]
        simp
      rw [commutatorElement_def, ← h]; group
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hS : ρ ModularGroup.S ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) := by
    have h : ModularGroup.S = ModularGroup.T⁻¹ *
        (ModularGroup.S⁻¹ * ModularGroup.T⁻¹ * ModularGroup.S⁻¹⁻¹) * ModularGroup.T⁻¹ := by
      decide
    rw [h]
    simp only [map_mul, map_inv]
    refine mul_mem (mul_mem (inv_mem hT) ?_) (inv_mem hT)
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem hT) _
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective ρ hs, ← _root_.SpecialLinearGroup.SL2Z_generators,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | rfl
  · exact hS
  · exact hT

theorem slTwo_zmod_mul_crt_exists_and_eq_one : ∀ a b : ℕ, Nat.Coprime a b → (∀ (g₁ : Matrix.SpecialLinearGroup (Fin 2) (ZMod a)) (g₂ : Matrix.SpecialLinearGroup (Fin 2) (ZMod b)), ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (a * b)), Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right a b) (ZMod a)) g = g₁ ∧ Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left b a) (ZMod b)) g = g₂) ∧ (∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (a * b)), Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right a b) (ZMod a)) g = 1 → Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left b a) (ZMod b)) g = 1 → g = 1) := by
  intro a b h
  have h1 : ∀ x, ((ZMod.chineseRemainder h) x).1 = ZMod.castHom (dvd_mul_right a b) (ZMod a) x := by
    intro x
    exact RingHom.congr_fun (Subsingleton.elim ((RingHom.fst _ _).comp (ZMod.chineseRemainder h).toRingHom) (ZMod.castHom (dvd_mul_right a b) (ZMod a))) x
  have h2 : ∀ x, ((ZMod.chineseRemainder h) x).2 = ZMod.castHom (dvd_mul_left b a) (ZMod b) x := by
    intro x
    exact RingHom.congr_fun (Subsingleton.elim ((RingHom.snd _ _).comp (ZMod.chineseRemainder h).toRingHom) (ZMod.castHom (dvd_mul_left b a) (ZMod b))) x
  constructor
  · intro g₁ g₂
    let M : Matrix.SpecialLinearGroup (Fin 2) (ZMod a × ZMod b) :=
      ⟨Matrix.of fun i j => (g₁ i j, g₂ i j), by
        have e1 := g₁.det_coe
        have e2 := g₂.det_coe
        rw [Matrix.det_fin_two] at e1 e2 ⊢
        exact Prod.ext e1 e2⟩
    refine ⟨Matrix.SpecialLinearGroup.map (ZMod.chineseRemainder h).symm.toRingHom M, ?_, ?_⟩
    · ext i j
      change ZMod.castHom (dvd_mul_right a b) (ZMod a) ((ZMod.chineseRemainder h).symm (g₁ i j, g₂ i j)) = _
      rw [← h1, RingEquiv.apply_symm_apply]
    · ext i j
      change ZMod.castHom (dvd_mul_left b a) (ZMod b) ((ZMod.chineseRemainder h).symm (g₁ i j, g₂ i j)) = _
      rw [← h2, RingEquiv.apply_symm_apply]
  · intro g e1 e2
    ext i j
    apply (ZMod.chineseRemainder h).injective
    have f1 : ZMod.castHom (dvd_mul_right a b) (ZMod a) (g i j) = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod a)) i j := by
      rw [← e1]; rfl
    have f2 : ZMod.castHom (dvd_mul_left b a) (ZMod b) (g i j) = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod b)) i j := by
      rw [← e2]; rfl
    refine Prod.ext ?_ ?_
    · rw [h1, h1, f1]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · rw [h2, h2, f2]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem glue : ∀ (k : ℕ) (G G₁ G₂ : Type) [Group G] [Group G₁] [Group G₂] (ρ₁ : G →* G₁) (ρ₂ : G →* G₂), (∀ g₁ g₂, ∃ g, ρ₁ g = g₁ ∧ ρ₂ g = g₂) → (∀ g, ρ₁ g = 1 → ρ₂ g = 1 → g = 1) → commutator G₁ = ⊤ → (∀ (E : Type) [Group E] (π : E →* G₁), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) → (∀ (E : Type) [Group E] (π : E →* G₂), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) → (∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ k = 1) → ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1) := by
  intro k G G₁ G₂ _ _ _ ρ₁ ρ₂ hsur hinj hperf Q₁ Q₂ E _ π hs hc hk x hx hxc
  let E₁ : Subgroup E := (ρ₂.comp π).ker
  let E₂ : Subgroup E := (ρ₁.comp π).ker
  let π₁ : E₁ →* G₁ := (ρ₁.comp π).comp E₁.subtype
  let π₂ : E₂ →* G₂ := (ρ₂.comp π).comp E₂.subtype
  have s₁ : Function.Surjective π₁ := by
    intro g
    obtain ⟨g', h1, h2⟩ := hsur g 1
    obtain ⟨e, rfl⟩ := hs g'
    exact ⟨⟨e, h2⟩, h1⟩
  have s₂ : Function.Surjective π₂ := by
    intro g
    obtain ⟨g', h1, h2⟩ := hsur 1 g
    obtain ⟨e, rfl⟩ := hs g'
    exact ⟨⟨e, h1⟩, h2⟩
  have k₁ : ∀ y ∈ π₁.ker, (y : E) ∈ π.ker := fun y hy => hinj _ hy y.2
  have k₂ : ∀ y ∈ π₂.ker, (y : E) ∈ π.ker := fun y hy => hinj _ y.2 hy
  have q₁ := Q₁ E₁ π₁ s₁ (fun y hy => Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc (k₁ y hy)) z))
    (fun y hy => Subtype.ext (hk y (k₁ y hy)))
  have q₂ := Q₂ E₂ π₂ s₂ (fun y hy => Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc (k₂ y hy)) z))
    (fun y hy => Subtype.ext (hk y (k₂ y hy)))
  have cen : ∀ (y : E₁) (z : E₂), ⁅(y : E), (z : E)⁆ ∈ Subgroup.center E := by
    intro y z
    apply hc
    have hy : ρ₂ (π y) = 1 := y.2
    have hz : ρ₁ (π z) = 1 := z.2
    apply hinj
    · simp [map_commutatorElement, hz]
    · simp [map_commutatorElement, hy]
  have comm : ∀ (y : E₁) (z : E₂), (y : E) * z = z * y := by
    intro y z
    let φ : E₁ →* Subgroup.center E := MonoidHom.mk' (fun y => ⟨_, cen y z⟩) (by
      intro y y'
      apply Subtype.ext
      have h := Subgroup.mem_center_iff.1 (cen y' z) y
      have h' := Subgroup.mem_center_iff.1 (cen y' z) ⁅(y : E), (z : E)⁆
      change ⁅(y : E) * y', (z : E)⁆ = ⁅(y : E), (z : E)⁆ * ⁅(y' : E), (z : E)⁆
      rw [h']
      calc ⁅(y : E) * y', (z : E)⁆ = (y * ⁅(y' : E), (z : E)⁆) * (z * (y : E)⁻¹ * (z : E)⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = _ := by rw [h]; simp only [commutatorElement_def]; group)
    obtain ⟨a, ha, c, hc', rfl⟩ := exists_ker_mul_commutator π₁ s₁ hperf y
    have h1 : φ c = 1 := by
      have h0 : (commutator E₁).map φ = ⊥ := by
        rw [commutator_def, Subgroup.map_commutator,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro e _
        exact Subgroup.mem_centralizer_iff.2 fun g _ =>
          Subtype.ext (Subgroup.mem_center_iff.1 e.2 g)
      exact (Subgroup.map_eq_bot_iff _).1 h0 hc'
    have h2 : (c : E) * z = z * c := commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h1)
    have h3 : (z : E) * a = a * z := Subgroup.mem_center_iff.1 (hc (k₁ a ha)) z
    change (a : E) * c * z = z * (a * c)
    rw [mul_assoc, h2, ← mul_assoc, ← h3, mul_assoc]
  let μ : E₁ × E₂ →* E := MonoidHom.noncommCoprod E₁.subtype E₂.subtype comm
  have sμ : Function.Surjective μ := by
    intro e
    obtain ⟨y, hy⟩ := s₁ (ρ₁ (π e))
    have hy' : ρ₁ (π y) = ρ₁ (π e) := hy
    refine ⟨(y, ⟨(y : E)⁻¹ * e, ?_⟩), ?_⟩
    · change ρ₁ (π _) = 1
      simp [hy']
    · change (y : E) * ((y : E)⁻¹ * e) = e
      group
  have h1 : (commutator (E₁ × E₂)).map μ = commutator E := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective μ sμ,
      ← commutator_def]
  rw [← h1] at hxc
  obtain ⟨⟨y, z⟩, hyz, rfl⟩ := hxc
  have hy : y ∈ commutator E₁ := by
    have : (commutator (E₁ × E₂)).map (MonoidHom.fst E₁ E₂) ≤ commutator E₁ := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact this ⟨_, hyz, rfl⟩
  have hz : z ∈ commutator E₂ := by
    have : (commutator (E₁ × E₂)).map (MonoidHom.snd E₁ E₂) ≤ commutator E₂ := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact this ⟨_, hyz, rfl⟩
  have hx' : π y * π z = 1 := by rw [← map_mul]; exact hx
  have hy0 : ρ₂ (π y) = 1 := y.2
  have hz0 : ρ₁ (π z) = 1 := z.2
  have hy1 : y ∈ π₁.ker := by
    have := congrArg ρ₁ hx'
    rw [map_mul, hz0, mul_one, map_one] at this
    exact this
  have hz1 : z ∈ π₂.ker := by
    have := congrArg ρ₂ hx'
    rw [map_mul, hy0, one_mul, map_one] at this
    exact this
  rw [← map_pow, Prod.pow_mk, q₁ y hy1 hy, q₂ z hz1 hz]
  exact map_one μ

theorem sq_eq_one (l n : ℕ) (hl : l.Prime) (m : ℕ) : 0 < m → Nat.Coprime m (6 * l) →
    ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) →
      ∀ x ∈ π.ker, x ∈ commutator E → x ^ 2 = 1 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    intro _ hm
    have hp' : Nat.Coprime p (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_pow_self p ha.ne') hm
    have hnd : ¬ p ∣ 6 * l := (Nat.Prime.coprime_iff_not_dvd hp).1 hp'
    refine GlobalTheory.T.sq_eq_one_of_mem_ker_commutator_central_ext_sl l n p a hl hp ?_ ?_
    · refine hp.five_le_of_ne_two_of_ne_three ?_ ?_ <;> rintro rfl <;> apply hnd <;> omega
    · rintro rfl
      exact hnd (dvd_mul_left _ _)
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _ E _ π _ hc _ x _ hxc
    have hcen : ∀ e : E, e ∈ Subgroup.center E := fun e => hc (by
      rw [MonoidHom.mem_ker]; ext i j; exact Subsingleton.elim _ _)
    have : commutator E = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro e _
      exact Subgroup.mem_centralizer_iff.2 fun g _ => Subgroup.mem_center_iff.1 (hcen e) g
    rw [this, Subgroup.mem_bot] at hxc
    rw [hxc, one_pow]
  | coprime a b ha hb hab iha ihb =>
    intro _ hm
    have hma : Nat.Coprime a (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hm
    have hmb : Nat.Coprime b (6 * l) := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hm
    exact glue (l ^ n) _ _ _ _ _ (slTwo_zmod_mul_crt_exists_and_eq_one a b hab).1 (slTwo_zmod_mul_crt_exists_and_eq_one a b hab).2
      (commutator_sl2_zmod a (Nat.Coprime.coprime_dvd_right (dvd_mul_right 6 l) hma))
      (iha (by omega) hma) (ihb (by omega) hmb)

theorem exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  intro l n m hl hm hc E _ π hs hcen hk
  exact exists_hom_sq π hs
    (commutator_sl2_zmod m (Nat.Coprime.coprime_dvd_right (dvd_mul_right 6 l) hc)) hcen
    (sq_eq_one l n hl m hm hc E π hs hcen hk)

end GlobalTheory.CentralExt
