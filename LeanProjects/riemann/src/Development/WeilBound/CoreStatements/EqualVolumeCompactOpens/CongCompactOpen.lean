import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.LocGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichAlongSub
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PHypPairExists
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cmp
open scoped TensorProduct

open ReciprocityTheory.ChartRestriction.G.SA

theorem eich_mul {R : Type} [CommRing R] {N : ℕ} {σ : R →+* R} {J : Matrix (Fin N) (Fin N) R}
    (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e u u' : Fin N → R} (c c' : R) (he : hf σ J e e = 0)
    (hue : hf σ J u e = 0) (hue' : hf σ J u' e = 0) :
    eich σ J e u c * eich σ J e u' c' = eich σ J e (u + u') (c + c' - hf σ J u' u) := by
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ, hue, map_zero]
  rw [ext_iff_mulVec]
  intro x
  rw [← mulVec_mulVec, eich_mulVec σ J e u, eich_mulVec σ J e u', eich_mulVec σ J e (u + u')]
  simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, he, hue', heu, mul_zero, add_zero, sub_zero]
  module

theorem eich_root {E : Type} [Field E] [CharZero E] {N : ℕ} {σ : E →+* E} {J : Matrix (Fin N) (Fin N) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : Fin N → E} (he : hf σ J e e = 0)
    {M : Matrix (Fin N) (Fin N) E} (hM : M ∈ eichAlong σ J e f) (n : ℕ) (hn : 0 < n) :
    ∃ Y ∈ eichAlong σ J e f, Y ^ n = M := by
  obtain ⟨u, c, hue, huf, hc, rfl⟩ := hM
  have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set h := hf σ J u u with hh
  have hσh : σ h = h := by rw [hh, hf_symm hσ hJ]
  set t : E := (n : E)⁻¹ with ht
  have hσt : σ t = t := by rw [ht, map_inv₀, map_natCast]
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  have hpow : ∀ k : ℕ, eich σ J e (t • u) (t * (c + h / 2) - t ^ 2 * h / 2) ^ k =
      eich σ J e ((k * t) • u) (k * t * (c + h / 2) - (k * t) ^ 2 * h / 2) := by
    intro k
    induction k with
    | zero => simp [eich, Function.comp_def]; ext i j; simp [vecMulVec_apply, mulVec, dotProduct]
    | succ k ih =>
      rw [pow_succ, ih, eich_mul hσ hJ _ _ he (by rw [hf_smul_left, hue, mul_zero])
        (by rw [hf_smul_left, hue, mul_zero]), hf_smul_left, hf_smul_right, ← hh, map_mul, map_natCast, hσt, ← add_smul]
      congr 1
      · push_cast; ring_nf
      · push_cast; ring
  refine ⟨_, ⟨t • u, t * (c + h / 2) - t ^ 2 * h / 2, by rw [hf_smul_left, hue, mul_zero],
    by rw [hf_smul_left, huf, mul_zero], ?_, rfl⟩, ?_⟩
  · rw [hf_smul_left, hf_smul_right, ← hh]
    simp only [map_sub, map_mul, map_add, map_div₀, map_pow, hσt, hσh, hσ2]
    linear_combination t * hc
  · rw [hpow, ht, mul_inv_cancel₀ hn', one_smul]
    congr 1
    ring

theorem divisible : Divisible := by
  intro F E _ _ _ _ _ N c J ⟨h2, hc, hJ, hu, e, he0, he⟩ γ hγ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = c := fun g => by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
    by_cases h : g = 1
    · exact Or.inl h
    · exact Or.inr ((hy g h).trans (hy c hc).symm)
  have hcc : ∀ x, c (c x) = x := fun x => by
    rcases hall (c * c) with h | h
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (mul_left_cancel (h.trans (mul_one c).symm)) hc
  have hfix : ∀ x, c x = x ↔ x ∈ Set.range (algebraMap F E) := fun x => by
    refine ⟨fun h => (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun g => ?_, ?_⟩
    · rcases hall g with rfl | rfl
      · rfl
      · exact h
    · rintro ⟨y, rfl⟩
      exact c.commutes y
  obtain ⟨f, hff, hef⟩ := GroundTheory.Heights₂.Heights.StrongApprox.HypPairExists.proof E c.toRingHom hcc two_ne_zero N J hJ hu
    e he0 he
  have hgen := locGen F E c.toAlgHom hcc hfix h2 inferInstance two_ne_zero N J hJ hu e f he hff hef
  have hmem : (γ : Matrix (Fin N) (Fin N) E) ∈ Submonoid.closure (eichSet c.toRingHom J e f) :=
    hgen.le ⟨congrArg Units.val (show Matrix.GeneralLinearGroup.det γ = 1 from hγ.2), hγ.1⟩
  replace he : hf c.toRingHom J e e = 0 := he
  replace hcc : ∀ x, c.toRingHom (c.toRingHom x) = x := hcc
  replace hJ : Jᵀ = J.map c.toRingHom := hJ
  have key : ∀ M ∈ Submonoid.closure (eichSet c.toRingHom J e f), ∃ g : GL (Fin N) E, g.val = M ∧
      g ∈ Subgroup.closure {x : GL (Fin N) E | ∀ n : ℕ, 0 < n → ∃ y ∈ suGrp c.toRingHom J, y ^ n = x} := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem x hx =>
      have hx1 := eichSet_sub hcc hJ he hff hx
      refine ⟨Matrix.nonsingInvUnit x (by rw [hx1.1]; exact isUnit_one), rfl, Subgroup.subset_closure fun n hn => ?_⟩
      obtain ⟨Y, hY, hYn⟩ : ∃ Y ∈ SU c.toRingHom J, Y ^ n = x := by
        rcases hx with hx | hx
        · obtain ⟨Y, h1, h3⟩ := eich_root hcc hJ he hx n hn
          exact ⟨Y, eichAlong_sub hcc hJ he h1, h3⟩
        · obtain ⟨Y, h1, h3⟩ := eich_root hcc hJ hff hx n hn
          exact ⟨Y, eichAlong_sub hcc hJ hff h1, h3⟩
      exact ⟨Matrix.nonsingInvUnit Y (by rw [hY.1]; exact isUnit_one), ⟨hY.2, Units.ext hY.1⟩,
        Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hYn)⟩
    | one => exact ⟨1, rfl, one_mem _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl, ha⟩ := hx
      obtain ⟨b, rfl, hb⟩ := hy
      exact ⟨a * b, rfl, mul_mem ha hb⟩
  obtain ⟨g, hg, hg'⟩ := key _ hmem
  rwa [← Units.ext hg]

theorem congCompactOpen : CongCompactOpen := by
  intro R _ _ _ _ N Λ Λ' hc ho ho' ⟨u, hu⟩
  have tube : ∀ (φ : GL (Fin N) R → Matrix (Fin N) (Fin N) R) (T : Set (Fin N → R)), Continuous φ → IsOpen T →
      IsOpen {g | ∀ x ∈ Λ, φ g *ᵥ x ∈ T} := by
    intro φ T hφ hT
    rw [isOpen_iff_mem_nhds]
    intro g hg
    refine hc.eventually_forall_of_forall_eventually (P := fun g x => φ g *ᵥ x ∈ T) fun x hx => ?_
    have : Continuous fun p : GL (Fin N) R × (Fin N → R) => φ p.1 *ᵥ p.2 :=
      (hφ.comp continuous_fst).matrix_mulVec continuous_snd
    exact this.continuousAt.preimage_mem_nhds (hT.mem_nhds (hg x hx))
  have hinv : ∀ (g : GL (Fin N) R) x, ((g⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ
      ((g : Matrix (Fin N) (Fin N) R) *ᵥ x) = x := fun g x => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hopen : IsOpen (congGrp Λ Λ' : Set (GL (Fin N) R)) := by
    have := ((tube (fun g => g) Λ Units.continuous_val ho).inter
      (tube (fun g => ((g⁻¹ : GL (Fin N) R) : Matrix _ _ R)) Λ Units.continuous_coe_inv ho)).inter
      (tube (fun g => (g : Matrix _ _ R) - 1) Λ' (Units.continuous_val.sub continuous_const) ho')
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq, sub_mulVec, one_mulVec]
    constructor
    · intro hg
      exact ⟨⟨fun x hx => (hg.1 x).1 hx, fun x hx => ((congGrp Λ Λ').inv_mem hg).1 x |>.1 hx⟩, hg.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun x => ⟨h1 x, fun hx => hinv g x ▸ h2 _ hx⟩, h3⟩
  refine ⟨?_, hopen⟩
  let C : Set (Matrix (Fin N) (Fin N) R) :=
    (fun y : Fin N → Fin N → R => Matrix.of fun i j => ((u⁻¹ : Rˣ) : R) * y j i) '' Set.univ.pi fun _ => (Λ : Set _)
  have hC : IsCompact C := (isCompact_univ_pi fun _ => hc).image
    (continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop)
  have hmem : ∀ g ∈ congGrp Λ Λ', (g : Matrix (Fin N) (Fin N) R) ∈ C := fun g hg =>
    ⟨fun j => (g : Matrix (Fin N) (Fin N) R) *ᵥ Pi.single j (u : R), fun j _ => (hg.1 _).1 (hu j), by
      ext i j
      simp only [Matrix.of_apply, mulVec, dotProduct_single]
      rw [mul_comm, Units.mul_inv_cancel_right]⟩
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin N) (Fin N) R)) ⁻¹' (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  exact hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun g hg =>
    ⟨hmem g hg, _, hmem _ ((congGrp Λ Λ').inv_mem hg), rfl⟩

end PositivityTheory.EqVol
