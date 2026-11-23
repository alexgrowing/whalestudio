import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open Matrix NumberField
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisLines

section Linear

variable {k R : Type} [Field k] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma inv_mulVec_of_mulVec (A : GL ι k) (b : kˣ) (u w : ι → k)
    (h : (A : Matrix ι ι k) *ᵥ u = (b : k) • w) :
    ((A⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ w = ((b⁻¹ : kˣ) : k) • u := by
  have h1 : ((A⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ ((A : Matrix ι ι k) *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at h1
  rw [← h1, smul_smul, Units.inv_mul, one_smul]

lemma mulVec_ne_zero (A : GL ι k) {u : ι → k} (hu : u ≠ 0) : (A : Matrix ι ι k) *ᵥ u ≠ 0 := by
  intro h0
  apply hu
  have h1 : ((A⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ ((A : Matrix ι ι k) *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← h1, h0, Matrix.mulVec_zero]

lemma single_ne_zero (i : ι) : (Pi.single i 1 : ι → k) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

private lemma mulVec_single_apply_hermitian_block_frames {S : Type} [CommRing S] (M : Matrix ι ι S) (j r : ι) :
    (M *ᵥ Pi.single j 1) r = M r j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma map_mem_stab_iff (φ : k →+* R) (hφ : Function.Injective φ) (A : GL ι k) (i : ι) :
    Matrix.GeneralLinearGroup.map (n := ι) φ A ∈ stab R ({i} : Set ι) ↔
      ∃ b : kˣ, (A : Matrix ι ι k) *ᵥ Pi.single i 1 = (b : k) • Pi.single i 1 := by
  have hent : ∀ (C : GL ι k) (r c : ι),
      ((Matrix.GeneralLinearGroup.map (n := ι) φ C : GL ι R) : Matrix ι ι R) r c = φ ((C : Matrix ι ι k) r c) :=
    fun _ _ _ => rfl
  have hinv : ∀ r c : ι, (((Matrix.GeneralLinearGroup.map (n := ι) φ A)⁻¹ : GL ι R) : Matrix ι ι R) r c =
      φ (((A⁻¹ : GL ι k) : Matrix ι ι k) r c) := by
    intro r c
    have := hent A⁻¹ r c
    rw [map_inv] at this
    exact this
  have hz : ∀ x : k, φ x = 0 → x = 0 := fun x h => hφ (by rw [h, map_zero])
  constructor
  · intro hA
    have hA' : ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
        ((Matrix.GeneralLinearGroup.map (n := ι) φ A : GL ι R) : Matrix ι ι R) r c = 0 ∧
        (((Matrix.GeneralLinearGroup.map (n := ι) φ A)⁻¹ : GL ι R) : Matrix ι ι R) r c = 0 := hA
    have hcol : ∀ r, r ≠ i → (A : Matrix ι ι k) r i = 0 := by
      intro r hr
      have := (hA' r (by simpa using hr) i (Set.mem_singleton i)).1
      rw [hent] at this
      exact hz _ this
    have hv : (A : Matrix ι ι k) *ᵥ Pi.single i 1 = (A : Matrix ι ι k) i i • Pi.single i 1 := by
      funext r
      rw [mulVec_single_apply_hermitian_block_frames, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs with h
      · rw [h, mul_one]
      · rw [hcol r h, mul_zero]
    have hii : (A : Matrix ι ι k) i i ≠ 0 := by
      intro h0
      apply GlobalTheory.CompanionTheory.RgEisLines.mulVec_ne_zero A (GlobalTheory.CompanionTheory.RgEisLines.single_ne_zero (k := k) i)
      rw [hv, h0, zero_smul]
    exact ⟨Units.mk0 _ hii, by rw [Units.val_mk0]; exact hv⟩
  · rintro ⟨b, hb⟩
    have hb' := GlobalTheory.CompanionTheory.RgEisLines.inv_mulVec_of_mulVec A b _ _ hb
    have goal : ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
        ((Matrix.GeneralLinearGroup.map (n := ι) φ A : GL ι R) : Matrix ι ι R) r c = 0 ∧
        (((Matrix.GeneralLinearGroup.map (n := ι) φ A)⁻¹ : GL ι R) : Matrix ι ι R) r c = 0 := by
      intro r hr c hc
      rw [Set.mem_singleton_iff] at hr hc
      rw [hc]
      refine ⟨?_, ?_⟩
      · rw [hent, ← mulVec_single_apply_hermitian_block_frames (A : Matrix ι ι k) i r, hb, Pi.smul_apply,
          Pi.single_eq_of_ne hr, smul_zero, map_zero]
      · rw [hinv, ← mulVec_single_apply_hermitian_block_frames ((A⁻¹ : GL ι k) : Matrix ι ι k) i r, hb', Pi.smul_apply,
          Pi.single_eq_of_ne hr, smul_zero, map_zero]
    exact goal

lemma map_mul_inv_mem_stab_iff (φ : k →+* R) (hφ : Function.Injective φ) (B C : GL ι k) (i : ι) :
    Matrix.GeneralLinearGroup.map (n := ι) φ (C * B⁻¹) ∈ stab R ({i} : Set ι) ↔
      ∃ b : kˣ, (b : k) • (((C⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) =
        ((B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1 := by
  rw [GlobalTheory.CompanionTheory.RgEisLines.map_mem_stab_iff φ hφ]
  have hCC : ∀ v : ι → k, (C : Matrix ι ι k) *ᵥ (((C⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hCC' : ∀ v : ι → k, ((C⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ ((C : Matrix ι ι k) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hmul : ((C * B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1 =
      (C : Matrix ι ι k) *ᵥ (((B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) := by
    rw [Units.val_mul, Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hmul] at hb
    rw [← hCC' (((B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1), hb, Matrix.mulVec_smul]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [hmul, ← hb, Matrix.mulVec_smul, hCC]

private lemma exists_GL_mulVec_single_eq_of_ne_zero (m : ι) (v : ι → k) (hv : v m ≠ 0) :
    ∃ G : GL ι k, (G : Matrix ι ι k) *ᵥ Pi.single m 1 = v ∧
      ∀ c, c ≠ m → (G : Matrix ι ι k) *ᵥ Pi.single c 1 = Pi.single c 1 := by
  have hact : ∀ x : ι → k,
      (1 + Matrix.vecMulVec (v - Pi.single m 1) (Pi.single m 1) : Matrix ι ι k) *ᵥ x =
        x + x m • (v - Pi.single m 1) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    congr 1
    funext r
    simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Pi.single_apply, mul_comm]
  have hunit : IsUnit (1 + Matrix.vecMulVec (v - Pi.single m 1) (Pi.single m 1) : Matrix ι ι k) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hact] at hx
    have hxm : x m = 0 := by
      have e := congrFun hx m
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul,
        Pi.zero_apply] at e
      have e2 : x m * v m = 0 := by linear_combination e
      exact (mul_eq_zero.1 e2).resolve_right hv
    apply hx0
    funext r
    simpa [hxm] using congrFun hx r
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hact]
    simp
  · intro c hc
    rw [IsUnit.unit_spec, hact]
    simp [Pi.single_apply, hc.symm]

lemma exists_inv_mulVec_eq (i : ι) {ξ : ι → k} (hξ : ξ ≠ 0) :
    ∃ g : GL ι k, ((g⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1 = ξ := by
  by_cases hi : ξ i = 0
  · obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
      by_contra hne
      exact hξ (funext fun x => by
        by_contra hx
        exact hne ⟨x, hx⟩)
    have hji : j ≠ i := fun h => hj (by rw [h]; exact hi)
    obtain ⟨G₂, hG₂, -⟩ := exists_GL_mulVec_single_eq_of_ne_zero i (Pi.single i 1 + Pi.single j 1 : ι → k)
      (by
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji.symm, add_zero]
        exact one_ne_zero)
    obtain ⟨G₁, hG₁, hG₁'⟩ := exists_GL_mulVec_single_eq_of_ne_zero j (ξ - Pi.single i 1 : ι → k)
      (by simp [Pi.single_apply, hji, hj])
    refine ⟨(G₁ * G₂)⁻¹, ?_⟩
    rw [inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hG₂, Matrix.mulVec_add, hG₁, hG₁' i hji.symm]
    abel
  · obtain ⟨G, hG, -⟩ := exists_GL_mulVec_single_eq_of_ne_zero i ξ hi
    exact ⟨G⁻¹, by rw [inv_inv, hG]⟩

end Linear

section Adelic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma algebraMap_injective : Function.Injective (algebraMap k 𝔸[k]) := by
  intro x y h
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace k))
  have h1 := congrArg (fun a : 𝔸[k] =>
    (Prod.fst (show InfiniteAdeleRing k × IsDedekindDomain.FiniteAdeleRing (𝓞 k) k from a)) v) h
  exact (algebraMap k v.Completion).injective h1

lemma ratV_smul (a : kˣ) (w : ι → k) :
    ratV (a • w) = algebraMap k 𝔸[k] a • (ratV w : ι → 𝔸[k]) := by
  funext j
  simp [ratV, Units.smul_def, map_mul]

lemma vec_map (B : GL ι k) (i : ι) :
    MG.vec (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap k 𝔸[k]) B) i =
      ratV (((B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) := by
  funext r
  change ((((B⁻¹ : GL ι k) : Matrix ι ι k).map (algebraMap k 𝔸[k])) *ᵥ Pi.single i 1) r =
    algebraMap k 𝔸[k] ((((B⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) r)
  rw [mulVec_single_apply_hermitian_block_frames, mulVec_single_apply_hermitian_block_frames, Matrix.map_apply]

theorem lines : Lines := by
  intro G _ _ _ _ K _ k _ _ ι _ _ π Γ P i ω d c η hS
  have alg_inj : Function.Injective (algebraMap k 𝔸[k]) := GlobalTheory.CompanionTheory.RgEisLines.algebraMap_injective
  have hpick : ∀ γ : Γ, ∃ B : GL ι k,
      Matrix.GeneralLinearGroup.map (n := ι) (algebraMap k 𝔸[k]) B = π γ := by
    intro γ
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.mp (hS.piΓ γ γ.2)
    exact ⟨B, hB⟩
  choose Bf hBf using hpick
  have hne : ∀ γ : Γ, (((Bf γ)⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1 ≠ 0 := fun γ =>
    GlobalTheory.CompanionTheory.RgEisLines.mulVec_ne_zero _ (GlobalTheory.CompanionTheory.RgEisLines.single_ne_zero i)
  let f : Γ → Projectivization k (ι → k) := fun γ => Projectivization.mk k _ (hne γ)
  have key : ∀ γ γ' : Γ, f γ = f γ' ↔ ((γ' : G) * (γ : G)⁻¹) ∈ P := by
    intro γ γ'
    show Projectivization.mk k _ (hne γ) = Projectivization.mk k _ (hne γ') ↔ _
    rw [Projectivization.mk_eq_mk_iff, hS.mem, map_mul, map_inv, ← hBf γ, ← hBf γ', ← map_inv, ← map_mul,
      GlobalTheory.CompanionTheory.RgEisLines.map_mul_inv_mem_stab_iff _ alg_inj]
    simp only [Units.smul_def]
  let F : Cos P Γ → Projectivization k (ι → k) := Quotient.lift f (fun a b h => by
    rw [key]
    have h' := QuotientGroup.rightRel_apply.mp h
    rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h')
  have hFinj : Function.Injective F := by
    intro q₁ q₂ h
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep q₂
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (key γ γ').1 h
  have hFsurj : Function.Surjective F := by
    intro l
    obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.RgEisLines.exists_inv_mulVec_eq (k := k) i l.rep_nonzero
    have hmem : Matrix.GeneralLinearGroup.map (n := ι) (algebraMap k 𝔸[k]) g ∈ (adStd k).ratGL ι :=
      MonoidHom.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨γ, hγ, hst⟩ := hS.trans _ hmem
    have h2 : Matrix.GeneralLinearGroup.map (n := ι) (algebraMap k 𝔸[k]) (g * (Bf ⟨γ, hγ⟩)⁻¹) ∈
        stab 𝔸[k] ({i} : Set ι) := by
      rw [map_mul, map_inv, hBf]
      exact hst
    obtain ⟨b, hb⟩ := (GlobalTheory.CompanionTheory.RgEisLines.map_mul_inv_mem_stab_iff _ alg_inj _ _ i).1 h2
    refine ⟨Quotient.mk _ ⟨γ, hγ⟩, ?_⟩
    refine Eq.trans ?_ (Projectivization.mk_rep l)
    show Projectivization.mk k _ (hne ⟨γ, hγ⟩) = _
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨b, by rw [Units.smul_def, ← hg]; exact hb⟩
  refine ⟨Equiv.ofBijective F ⟨hFinj, hFsurj⟩, fun q => ?_⟩
  have hq : F q = f (Quotient.out q) := by
    calc F q = F (Quotient.mk _ (Quotient.out q)) := by rw [Quotient.out_eq]
      _ = f (Quotient.out q) := rfl
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := k) _ (hne (Quotient.out q))
  refine ⟨a, ?_⟩
  have e1 : (Equiv.ofBijective F ⟨hFinj, hFsurj⟩ q).rep =
      a • ((((Bf (Quotient.out q))⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) := by
    rw [ha]
    exact congrArg Projectivization.rep hq
  have e2 : MG.vec (π (rep q)) i = ratV ((((Bf (Quotient.out q))⁻¹ : GL ι k) : Matrix ι ι k) *ᵥ Pi.single i 1) := by
    rw [show π (rep q) = Matrix.GeneralLinearGroup.map (n := ι) (algebraMap k 𝔸[k]) (Bf (Quotient.out q)) from
      (hBf (Quotient.out q)).symm, GlobalTheory.CompanionTheory.RgEisLines.vec_map]
  rw [e1, GlobalTheory.CompanionTheory.RgEisLines.ratV_smul, e2]

end Adelic

end GlobalTheory.CompanionTheory.RgEisLines
