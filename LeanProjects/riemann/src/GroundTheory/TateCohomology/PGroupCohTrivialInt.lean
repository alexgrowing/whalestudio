import Mathlib
import GroundTheory.TateCohomology.PGroupCohTrivial
import GroundTheory.TateCohomology.TateAddEquivAbelianizationTateClass
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupHomology

universe u

section H1

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]

theorem isZero_groupHomology_one_iff (A : Rep.{u} k G) :
    IsZero (groupHomology A 1) ↔ ∀ y : G →₀ A, d₁₀ A y = 0 → ∃ c : G × G →₀ A, d₂₁ A c = y := by
  constructor
  · intro h y hy
    have h0 : H1π A ⟨y, LinearMap.mem_ker.mpr hy⟩ = 0 :=
      @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h) _ _
    exact LinearMap.mem_range.mp ((H1π_eq_zero_iff _).mp h0)
  · intro h
    have : Subsingleton (groupHomology A 1) := by
      suffices hz : ∀ z : groupHomology A 1, z = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
      intro z
      induction z using H1_induction_on with
      | h z =>
        apply (H1π_eq_zero_iff z).mpr
        exact LinearMap.mem_range.mpr (h z.1 (LinearMap.mem_ker.mp z.2))
    exact ModuleCat.isZero_of_subsingleton _

variable {A : Rep.{u} k G} {B : Rep.{u} k' G}

theorem d₁₀_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (y : G →₀ A) : d₁₀ B (Finsupp.mapRange e (map_zero e) y) = e (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add, h₁, h₂]
  | single g a => rw [Finsupp.mapRange_single, d₁₀_single, d₁₀_single, map_sub, he]

theorem d₂₁_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange e (map_zero e) c) = Finsupp.mapRange e (map_zero e) (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange_single, d₂₁_single, d₂₁_single, Finsupp.mapRange_add (map_add e),
      Finsupp.mapRange_sub (map_sub e), Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single, he]

theorem isZero_groupHomology_one_of_addEquiv (e : A.V ≃+ B.V)
    (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a)) (h : IsZero (groupHomology A 1)) :
    IsZero (groupHomology B 1) := by
  rw [isZero_groupHomology_one_iff] at h ⊢
  intro y hy
  have hyy : Finsupp.mapRange e (map_zero e) (Finsupp.mapRange e.symm (map_zero e.symm) y) = y := by
    ext g; simp
  have hy' : d₁₀ A (Finsupp.mapRange e.symm (map_zero e.symm) y) = 0 := by
    apply e.injective
    rw [← d₁₀_mapRange_addEquiv e he, hyy, hy, map_zero]
  obtain ⟨c, hc⟩ := h _ hy'
  exact ⟨Finsupp.mapRange e (map_zero e) c, by rw [d₂₁_mapRange_addEquiv e he, hc, hyy]⟩

end H1

section Torsion

variable {k G : Type u} [CommRing k] [Group G]

theorem nsmul_id_hom_apply (M : Rep.{u} k G) (n : ℕ) (x : M) : (n • 𝟙 M).hom x = n • x := by
  rw [Rep.nsmul_hom]; rfl

theorem nsmul_eq_zero_of_surjective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) {n : ℕ} (hA : ∀ x : A, n • x = 0) (y : B) : n • y = 0 := by
  obtain ⟨x, rfl⟩ := hf y
  change n • f.hom.toLinearMap x = 0
  rw [← map_nsmul, hA, map_zero]

theorem nsmul_eq_zero_of_injective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) {n : ℕ} (hB : ∀ y : B, n • y = 0) (x : A) : n • x = 0 := by
  apply hf
  change f.hom.toLinearMap (n • x) = f.hom.toLinearMap 0
  rw [map_nsmul, map_zero]
  exact hB _

theorem nsmul_eq_zero_coind (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0)
    (x : coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M)) : n • x = 0 :=
  Subtype.ext (funext fun g => hM (x.1 g))

theorem nsmul_eq_zero_coindShift (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : coindShift M, n • y = 0 :=
  nsmul_eq_zero_of_surjective (coindSES.obj M).g
    ((Rep.epi_iff_surjective _).1 (coindSES_shortExact M).epi_g) (nsmul_eq_zero_coind M hM)

theorem nsmul_eq_zero_indShift [Fintype G] (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : indShift M, n • y = 0 := by
  classical
  let e := indCoindIso (G := G) (res (⊥ : Subgroup G).subtype M)
  have he : Function.Injective e.hom.hom := (Rep.mono_iff_injective e.hom).1 inferInstance
  have h₂ := nsmul_eq_zero_of_injective e.hom he (nsmul_eq_zero_coind M hM)
  exact nsmul_eq_zero_of_injective (indSES.obj M).f
    ((Rep.mono_iff_injective _).1 (indSES_shortExact M).mono_f) h₂

end Torsion

section ZMod

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]

noncomputable def zmodRep (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) : Rep (ZMod p) G :=
  letI : Module (ZMod p) M := AddCommGroup.zmodModule hM
  Rep.of (X := M)
    { toFun := fun g => AddMonoidHom.toZModLinearMap p (M.ρ g).toAddMonoidHom
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }

variable [Fintype G]

theorem tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0)
    (h : IsZero (tateCohomology M (-2))) : TateAcyclic M ∧ CohTrivial M := by
  have h1 : IsZero (groupHomology M 1) := h.of_iso (tateNegTwoIsoH1 M).symm
  have h1' : IsZero (groupHomology (zmodRep p M hM) 1) :=
    isZero_groupHomology_one_of_addEquiv (AddEquiv.refl M.V) (fun _ _ => rfl) h1
  obtain ⟨ι, ⟨e⟩⟩ := exists_iso_free_of_isZero_groupHomology_one hG _ h1'
  have := free_asModule_of_iso_free e
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis (zmodRep p M hM) (Module.Free.chooseBasis _ _)
  refine ⟨tateAcyclic_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ,
    cohTrivial_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ⟩
  all_goals
    intro n x
    have hmod : M.hV2 = AddCommGroup.toIntModule M.V := Subsingleton.elim _ _
    rw [hmod]
    exact map_zsmul φ n x

theorem tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) (q : ℤ)
    (hq : IsZero (tateCohomology M q)) : TateAcyclic M ∧ CohTrivial M :=
  tateAcyclic_cohTrivial_of_isZero_of_shift (fun M => ∀ x : M, p • x = 0)
    (fun M hM => nsmul_eq_zero_coindShift M hM) (fun M hM => nsmul_eq_zero_indShift M hM)
    (fun M hM h => tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero hG M hM h) q M hM hq

end ZMod

end GroundTheory.GroupCoh
