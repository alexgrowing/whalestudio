import Development.EtaleCohomology.EtaleSheaves.stupidPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.inclPf

universe v u

set_option linter.dupNamespace false in
abbrev E (M : ℤ) := ComplexShape.embeddingUpIntGE M

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (M : ℤ)

lemma xiso_indep {i j : ℕ} {p : ℤ} (hi : (E M).f i = p) (hj : (E M).f j = p) :
    K.stupidTruncXIso (E M) hi = K.stupidTruncXIso (E M) hj := by
  obtain rfl : i = j := (E M).injective_f (hi.trans hj.symm)
  rfl

lemma trd (i j : ℕ) :
    (K.stupidTrunc (E M)).d ((E M).f i) ((E M).f j) ≫ (K.stupidTruncXIso (E M) (i := j) rfl).hom =
      (K.stupidTruncXIso (E M) (i := i) rfl).hom ≫ K.d ((E M).f i) ((E M).f j) := by
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.extend_d_eq _ _ rfl rfl, HomologicalComplex.restriction]
  erw [eqToIso_refl, eqToIso_refl]; simp

open Classical in

def iotaf (p : ℤ) : (K.stupidTrunc (E M)).X p ⟶ K.X p :=
  if h : ∃ i, (E M).f i = p then (K.stupidTruncXIso (E M) h.choose_spec).hom else 0

lemma iotaf_eq (i : ℕ) : iotaf K M ((E M).f i) = (K.stupidTruncXIso (E M) (i := i) rfl).hom := by
  have h : ∃ j, (E M).f j = (E M).f i := ⟨i, rfl⟩
  rw [iotaf, dif_pos h, xiso_indep K M h.choose_spec rfl]

lemma stupidTruncation_GE_isZero_below_bound (p : ℤ) (hp : p < M) : IsZero ((K.stupidTrunc (E M)).X p) :=
  HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun i h => by simp [E] at h; omega)

lemma mem (p : ℤ) (hp : M ≤ p) : (E M).f (p - M).toNat = p := by simp [E]; omega

def iota : K.stupidTrunc (E M) ⟶ K where
  f := iotaf K M
  comm' p q hpq := by
    simp only [ComplexShape.up_Rel] at hpq
    by_cases hp : M ≤ p
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (E M).f j = q := ⟨i + 1, by simp [E] at hpq ⊢; omega⟩
      rw [iotaf_eq, iotaf_eq]
      exact (trd K M i j).symm
    · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _

lemma iota_iso (p : ℤ) (hp : M ≤ p) : IsIso ((iota K M).f p) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
  show IsIso (iotaf K M _)
  rw [iotaf_eq]; infer_instance

lemma iota_nat {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (E M) ≫ iota L M = iota K M ≫ g := by
  ext p
  simp only [HomologicalComplex.comp_f]
  by_cases hp : M ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
    show _ ≫ iotaf L M _ = iotaf K M _ ≫ _
    rw [iotaf_eq, iotaf_eq]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom _ _ rfl
  · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _
end

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {A B I : CochainComplex C ℤ} (φ : A ⟶ B) (M : ℤ)

def P (m : ℤ) (c : Cochain B I m) : Cochain A I m := (Cochain.ofHom φ).comp c (zero_add m)

lemma precomp_injective [I.IsStrictlyGE 0] (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (m : ℤ) (hm : m + M ≤ 0) :
    Function.Injective (P (I := I) φ m) := by
  intro c c' h
  ext p q hpq
  by_cases hp : M ≤ p
  · have := hiso p hp
    have h' := congrArg (fun x : Cochain A I m => x.v p q hpq) h
    simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    exact (cancel_epi _).1 h'
  · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

lemma precomp_surjective₂ (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (hz : ∀ p, p < M → IsZero (A.X p)) (m : ℤ) :
    Function.Surjective (P (I := I) φ m) := by
  intro d
  refine ⟨Cochain.mk (fun p q hpq => if h : M ≤ p then (haveI := hiso p h; inv (φ.f p)) ≫ d.v p q hpq else 0), ?_⟩
  ext p q hpq
  simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  by_cases hp : M ≤ p
  · rw [dif_pos hp]; simp
  · exact (hz p (by omega)).eq_of_src _ _
end

section
variable {R : Type} [CommRing R] {A B I : Cx R} (φ : A ⟶ B)

lemma cpull_mk (n : ℤ) (z : Cocycle B I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (Cocycle.mk (P φ n z) (n + 1) rfl
      (by simp [P, Cocycle.δ_eq_zero])) := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1

lemma cpull_bij [I.IsStrictlyGE 0] (M : ℤ) (hiso : ∀ p, M ≤ p → IsIso (φ.f p))
    (hz : ∀ p, p < M → IsZero (A.X p)) (n : ℤ) (hn : n + 1 + M ≤ 0) :
    Function.Bijective (cpull φ I n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := precomp_surjective₂ φ M hiso hz (n - 1) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨β', precomp_injective φ M hiso n (by omega) ?_⟩
    rw [Cocycle.mk_coe] at hβ
    rw [← hβ, P, P, δ_ofHom_comp]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨c, hc⟩ := precomp_surjective₂ φ M hiso hz n (z : Cochain A I n)
    have hδ : δ n (n + 1) c = 0 := by
      apply precomp_injective φ M hiso (n + 1) (by omega)
      have : P φ (n + 1) (δ n (n + 1) c) = δ n (n + 1) (P φ n c) := by simp [P]
      rw [this, hc, Cocycle.δ_eq_zero]; simp [P]
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hδ), ?_⟩
    rw [cpull_mk]
    congr 1
    apply Cocycle.ext
    simp only [Cocycle.mk_coe]
    exact hc
end

theorem incl_of : LateralTheory.E.stupidPf.incl := by
  intro R _ I _ K L g N
  refine ⟨iota K (-(N : ℤ)), iota L (-(N : ℤ)), iota_nat _ g, fun n hn => ⟨?_, ?_⟩⟩
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso K _) (stupidTruncation_GE_isZero_below_bound K _) n (by omega)
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso L _) (stupidTruncation_GE_isZero_below_bound L _) n (by omega)

end LateralTheory.E.inclPf
