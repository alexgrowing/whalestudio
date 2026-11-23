import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.GenEigIdem

open Polynomial Module

section SlopeTestRemainingChoices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def stabAlg (Z B : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {f | (∀ z ∈ Z, f z ∈ Z) ∧ ∀ z ∈ B, f z ∈ B}
  mul_mem' := fun {f g} hf hg =>
    ⟨fun z hz => hf.1 _ (hg.1 z hz), fun z hz => hf.2 _ (hg.2 z hz)⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun z hz => Z.add_mem (hf.1 z hz) (hg.1 z hz),
     fun z hz => B.add_mem (hf.2 z hz) (hg.2 z hz)⟩
  algebraMap_mem' := fun c =>
    ⟨fun z hz => by simpa [Module.algebraMap_end_apply] using Z.smul_mem c hz,
     fun z hz => by simpa [Module.algebraMap_end_apply] using B.smul_mem c hz⟩

def quotAlgHom (Z B : Submodule K V) :
    stabAlg Z B →ₐ[K] Module.End K (Z ⧸ B.comap Z.subtype) where
  toFun f := (B.comap Z.subtype).mapQ (B.comap Z.subtype)
    ((f : Module.End K V).restrict f.2.1) (fun z hz => f.2.2 _ hz)
  map_one' := by ext z; rfl
  map_mul' f g := by ext z; rfl
  map_zero' := by ext z; rfl
  map_add' f g := by ext z; rfl
  commutes' c := by ext z; rfl

theorem quotAlgHom_mk (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(f : Module.End K V) z, f.2.1 z z.2⟩ := rfl

theorem quotAlgHom_mk_eq_zero (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) = 0 ↔ (f : Module.End K V) z ∈ B := by
  rw [quotAlgHom_mk, Submodule.Quotient.mk_eq_zero]; rfl

theorem exists_poly_genEig (M : Type) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A : Module.End K M) (c : K) :
    ∃ p : K[X], p.eval c = 1 ∧
      ∀ w, aeval A ((X - C c) ^ finrank K M) (aeval A p w) = 0 := by
  set χ := A.charpoly with hχdef
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  set a := χ.rootMultiplicity c
  set r := χ /ₘ (X - C c) ^ a
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hχ
  have hfac : (X - C c) ^ a * r = χ := pow_mul_divByMonic_rootMultiplicity_eq χ c
  have ha : a ≤ finrank K M := by
    have h1 : (X - C c) ^ a ∣ χ := ⟨r, hfac.symm⟩
    have h2 := natDegree_le_of_dvd h1 hχ
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one, hχdef, LinearMap.charpoly_natDegree] at h2
  refine ⟨C (r.eval c)⁻¹ * r, by simp [hr], fun w => ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (X - C c) ^ finrank K M * (C (r.eval c)⁻¹ * r) =
      C (r.eval c)⁻¹ * (X - C c) ^ (finrank K M - a) * χ := by
    rw [← hfac]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_add]
    ring
  rw [this, map_mul, LinearMap.aeval_self_charpoly, mul_zero, LinearMap.zero_apply]

end SlopeTestRemainingChoices

end GlobalTheory.GenEigIdem

namespace GlobalTheory

open Polynomial Module GlobalTheory.GenEigIdem

theorem exists_genEig_idem_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  intro K _ V _ _ Z B ι S T lam _hBZ hfd hZ hB hcomm hgen
  let Tg : {t // S t} → stabAlg Z B := fun t => ⟨T t.1, hZ t.1 t.2, hB t.1 t.2⟩
  let φ := quotAlgHom Z B
  let d := finrank K (Z ⧸ B.comap Z.subtype)
  have hex : ∀ t : {t // S t}, ∃ p : K[X], p.eval (lam t.1) = 1 ∧
      ∀ w, aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d) (aeval (φ (Tg t)) p w) = 0 :=
    fun t => exists_poly_genEig _ _ _
  choose p hp1 hp2 using hex
  let N : {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun t =>
    LinearMap.ker (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d))
  let Ninf : Finset {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun F => ⨅ t ∈ F, N t
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset {t // S t} => finrank K (Ninf F)).wf.has_min
    Set.univ ⟨∅, trivial⟩
  classical
  have hFle : ∀ s, Ninf F ≤ N s := by
    intro s
    have hins : Ninf (insert s F) = N s ⊓ Ninf F := Finset.iInf_insert _ _ _
    have hmin : ¬ finrank K (Ninf (insert s F)) < finrank K (Ninf F) := hF (insert s F) trivial
    have heq : Ninf (insert s F) = Ninf F := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hins]; exact inf_le_right
      · exact not_lt.mp hmin
    rw [← heq, hins]; exact inf_le_left
  have hinv : ∀ (s t : {t // S t}) (q : K[X]) (w : Z ⧸ B.comap Z.subtype), w ∈ N t →
      aeval (φ (Tg s)) q w ∈ N t := by
    intro s t q w hw
    have hc : Commute (φ (Tg s)) (φ (Tg t)) := by
      refine LinearMap.ext fun w => Submodule.Quotient.induction_on _ w fun z => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, quotAlgHom_mk, quotAlgHom_mk, quotAlgHom_mk,
        quotAlgHom_mk, Submodule.Quotient.eq]
      exact hcomm s.1 t.1 s.2 t.2 z z.2
    have hc2 : Commute (aeval (φ (Tg s)) q) (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d)) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
        (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
          hc.symm).symm
    have hw' := LinearMap.mem_ker.mp hw
    refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hw', map_zero]
  have hprod : ∀ (l : List {t // S t}) (w : Z ⧸ B.comap Z.subtype) (t : {t // S t}), t ∈ l →
      φ (l.map fun s => aeval (Tg s) (p s)).prod w ∈ N t := by
    intro l
    induction l with
    | nil => intro w t ht; simp at ht
    | cons a l ih =>
      intro w t ht
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← aeval_algHom_apply]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact LinearMap.mem_ker.mpr (hp2 _ _)
      · exact hinv _ _ _ _ (ih _ _ ht')
  let P : FreeAlgebra K ι := (F.toList.map fun t => aeval (FreeAlgebra.ι K t.1) (p t)).prod
  let Q : stabAlg Z B := (F.toList.map fun t => aeval (Tg t) (p t)).prod
  have hPQ : FreeAlgebra.lift K T P = (Q : Module.End K V) := by
    rw [show (Q : Module.End K V) = (stabAlg Z B).val Q from rfl]
    simp only [P, Q, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
    rfl
  have hPmem : P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}) := by
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem (FreeAlgebra.ι K) (show t.1 ∈ {t | S t} from t.2)))
      (aeval_mem_adjoin_singleton K _)
  have hPlam : FreeAlgebra.lift K lam P = 1 := by
    simp only [P, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply, coe_aeval_eq_eval, hp1]
  refine ⟨P, hPmem, hPlam, fun z hz s hs => ?_⟩
  rw [hPQ]
  have hQz : (Q : Module.End K V) z ∈ Z := Q.2.1 z hz
  refine hgen _ hQz d (fun t ht => ?_) s hs
  let U : stabAlg Z B := (Tg ⟨t, ht⟩ - algebraMap K (stabAlg Z B) (lam t)) ^ d
  have hU : (U : Module.End K V) = (T t - lam t • 1) ^ d := by
    simp [U, Tg, Algebra.algebraMap_eq_smul_one]
  rw [← hU]
  have key : φ U (Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩) = 0 := by
    have h1 : φ Q (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩ := quotAlgHom_mk _ _ _ _
    rw [← h1]
    have hφU : φ U = aeval (φ (Tg ⟨t, ht⟩)) ((X - C (lam t)) ^ d) := by
      simp [U]
    rw [hφU]
    refine LinearMap.mem_ker.mp (hFle ⟨t, ht⟩ ?_)
    simp only [Ninf, Submodule.mem_iInf]
    intro s' hs'
    exact hprod _ _ _ (Finset.mem_toList.mpr hs')
  exact (quotAlgHom_mk_eq_zero Z B U _).mp key

end GlobalTheory
