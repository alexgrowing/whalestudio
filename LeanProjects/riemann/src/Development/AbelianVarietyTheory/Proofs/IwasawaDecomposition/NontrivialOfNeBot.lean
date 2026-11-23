import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.Pairs

section Abstract

variable {H S F P P' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']

def img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : Submodule ℂ F := Submodule.span ℂ {φ | ∃ p v, j p v = φ}

theorem apply_mem_img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) : j p v ∈ img j :=
  Submodule.subset_span ⟨p, v, rfl⟩

variable {ι : Type} [Fintype ι]

def total (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : (ι → P) →ₗ[ℂ] F :=
  ∑ a, (LinearMap.applyₗ (b a)) ∘ₗ j ∘ₗ LinearMap.proj a

theorem total_apply (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (c : ι → P) :
    total b j c = ∑ a, j (c a) (b a) := by
  simp [total, LinearMap.sum_apply]

theorem total_repr (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) :
    total b j (fun a => b.repr v a • p) = j p v := by
  rw [total_apply]
  conv_rhs => rw [← b.sum_repr v, map_sum]
  simp

theorem range_total (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) :
    LinearMap.range (total b j) = img j := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, rfl⟩
    rw [total_apply]
    exact Submodule.sum_mem _ fun a _ => apply_mem_img j _ _
  · rintro _ ⟨p, v, rfl⟩
    exact ⟨_, total_repr b j p v⟩

theorem coeff_mem {ρ : Representation ℂ H S} (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F}
    {j : P →ₗ[ℂ] S →ₗ[ℂ] F} (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {U : Submodule ℂ F}
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (b : Module.Basis ι ℂ S) {c : ι → P} (h : total b j c ∈ U) (a : ι) (w : S) :
    j (c a) w ∈ U := by
  classical
  have key : ∀ T : Module.End ℂ S, ∑ a, j (c a) (T (b a)) ∈ U := fun T => by
    have hT : T ∈ Submodule.span ℂ (Set.range ρ) := hsp ▸ Submodule.mem_top
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e : ∑ a, j (c a) (ρ g (b a)) = R g (total b j c) := by
        rw [total_apply, map_sum]
        exact Finset.sum_congr rfl fun a _ => hj _ _ _
      rw [e]
      exact hU _ _ h
    | zero => simp
    | add x y _ _ hx hy => simpa [Finset.sum_add_distrib] using add_mem hx hy
    | smul r x _ hx => simpa [Finset.smul_sum] using U.smul_mem r hx
  have h1 := key ((b.coord a).smulRight w)
  rw [Finset.sum_eq_single a (fun a' _ h' => by simp [Module.Basis.coord_apply, Finsupp.single_apply, h'])
    (fun h' => absurd (Finset.mem_univ a) h')] at h1
  simpa [Module.Basis.coord_apply] using h1

theorem eq_bot_or_eq_img [FiniteDimensional ℂ S] {K : Type} {ρ : Representation ℂ H S}
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F} {j : P →ₗ[ℂ] S →ₗ[ℂ] F}
    (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {Q : K → Module.End ℂ P}
    {T : K → Module.End ℂ F} (hQ : ∀ k p v, j (Q k p) v = T k (j p v))
    (hP : ∀ N : Submodule ℂ P, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤) {U : Submodule ℂ F} (hle : U ≤ img j)
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (hT : ∀ k, ∀ u ∈ U, T k u ∈ U) : U = ⊥ ∨ U = img j := by
  let N : Submodule ℂ P := ⨅ v : S, U.comap ((LinearMap.applyₗ v) ∘ₗ j)
  have hN : ∀ p, p ∈ N ↔ ∀ v, j p v ∈ U := fun p => by simp [N, Submodule.mem_iInf]
  rcases hP N fun k p hp => (hN _).2 fun v => by
      rw [hQ]
      exact hT _ _ ((hN p).1 hp v) with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    let b := Module.finBasis ℂ S
    obtain ⟨c, rfl⟩ : φ ∈ LinearMap.range (total b j) := by
      rw [range_total]
      exact hle hφ
    have hc : ∀ a, c a = 0 := fun a => by
      have : c a ∈ N := (hN _).2 fun w => coeff_mem hsp hj hU b hφ a w
      rwa [h, Submodule.mem_bot] at this
    rw [total_apply]
    simp [hc]
  · right
    refine le_antisymm hle (Submodule.span_le.2 ?_)
    rintro _ ⟨p, v, rfl⟩
    exact (hN p).1 (h ▸ Submodule.mem_top) v

def part (Alg : Submodule ℂ (S →ₗ[ℂ] F)) (A : Submodule ℂ F) : Submodule ℂ Alg :=
  ⨅ v : S, A.comap ((LinearMap.applyₗ v).comp Alg.subtype)

theorem mem_part {Alg : Submodule ℂ (S →ₗ[ℂ] F)} {A : Submodule ℂ F} {f : Alg} : f ∈ part Alg A ↔ ∀ v, f.1 v ∈ A :=
  Submodule.mem_iInf _

def partVal (Alg : Submodule ℂ (S →ₗ[ℂ] F)) (A : Submodule ℂ F) : part Alg A →ₗ[ℂ] S →ₗ[ℂ] A where
  toFun f := f.1.1.codRestrict A (mem_part.1 f.2)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_smul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

def partMap {Alg : Submodule ℂ (S →ₗ[ℂ] F)} {A B : Submodule ℂ F} (t : A →ₗ[ℂ] B)
    (ht : ∀ f : part Alg A, B.subtype ∘ₗ t ∘ₗ partVal Alg A f ∈ Alg) : part Alg A →ₗ[ℂ] part Alg B :=
  LinearMap.codRestrict _ (LinearMap.codRestrict Alg
    ((LinearMap.llcomp ℂ S A F (B.subtype ∘ₗ t)) ∘ₗ partVal Alg A) ht)
    fun f => mem_part.2 fun v => (t (partVal Alg A f v)).2

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_inf_mul_fin (x : UA E n) : ∃ a ∈ infU E n, ∃ k ∈ finU E n, x = a * k := by
  let y : GL (Fin n) (Cinf E) := cInf x
  have hx : cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 : x.1.val.map (pInf E) = y.val := rfl
  have h3 : (cT (conjAd E) x.1.val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have hy : y.valᴴ * y.val = 1 := by
    rw [mul_one] at hx
    rw [← h3, ← h1, ← Matrix.map_mul, hx]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let a : UA E n := ⟨infGL E n y, infGL_mem_UA y hy⟩
  refine ⟨a, pFin_infGL y, a⁻¹ * x, ?_, (mul_inv_cancel_left a x).symm⟩
  have h4 : cInf a = y := pInf_infGL y
  refine MonoidHom.mem_ker.2 ?_
  rw [map_mul, map_inv, h4]
  exact inv_mul_cancel y

theorem stable_of {U : Submodule ℂ (UA E n → ℂ)} (h1 : ∀ x : infU E n, ∀ φ ∈ U, RU E n x.1 φ ∈ U)
    (h2 : ∀ k : finU E n, ∀ φ ∈ U, RU E n k.1 φ ∈ U) (x : UA E n) (φ : UA E n → ℂ) (hφ : φ ∈ U) : RU E n x φ ∈ U := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_inf_mul_fin x
  rw [← RU_RU]
  exact h1 ⟨a, ha⟩ _ (h2 ⟨k, hk⟩ _ hφ)

theorem exists_cAll (g : InfinitePlace E → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, cAll y.1 = g := by
  classical
  let J : Subgroup (InfinitePlace E → GL (Fin n) ℂ) := (cAll.comp (infU E n).subtype).range
  let Hs : InfinitePlace E → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb v'.embedding x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) v'.embedding).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v'.embedding) (by simpa using h)
      change cEmb v'.embedding x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rep (W : Wt E n) [Nontrivial W.Sp] : Submodule.span ℂ (Set.range W.rep) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ W.rep ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := exists_cAll g hg
      exact hU y x hx⟩)

def jOf (W : Wt E n) (M : Submodule ℂ (algForms W)) : M →ₗ[ℂ] W.Sp →ₗ[ℂ] (UA E n → ℂ) :=
  (algForms W).subtype ∘ₗ M.subtype

theorem jOf_injective (W : Wt E n) (M : Submodule ℂ (algForms W)) : Function.Injective (jOf W M) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem jOf_rep (W : Wt E n) (M : Submodule ℂ (algForms W)) (p : M) (x : infU E n) (v : W.Sp) :
    jOf W M p (W.rep x v) = RU E n x.1 (jOf W M p v) := p.1.2.2 x v

theorem nontrivial_of_ne_bot {W : Wt E n} {M : Submodule ℂ (algForms W)} (h : M ≠ ⊥) :
    Nontrivial W.Sp ∧ img (jOf W M) ≠ ⊥ := by
  obtain ⟨p, hp, h0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : jOf W M ⟨p, hp⟩ ≠ 0 := fun e => h0 (congrArg Subtype.val (jOf_injective W M (e.trans (map_zero _).symm)))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h1
  refine ⟨⟨v, 0, fun e => hv (by rw [e, map_zero]; rfl)⟩, fun e => hv ?_⟩
  have := apply_mem_img (jOf W M) ⟨p, hp⟩ v
  rw [e, Submodule.mem_bot] at this
  exact this

theorem img_stable {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M) (x : UA E n)
    (φ : UA E n → ℂ) (hφ : φ ∈ img (jOf W M)) : RU E n x φ ∈ img (jOf W M) := by
  refine stable_of (fun a => ?_) (fun k => ?_) x φ hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n a.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      change RU E n a.1 _ ∈ img (jOf W M)
      rw [← jOf_rep]
      exact apply_mem_img _ _ _)
    exact fun φ hφ => h1 hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n k.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact apply_mem_img (jOf W M) ⟨algRep W k p.1, hM k _ p.2⟩ v)
    exact fun φ hφ => h1 hφ

theorem V_eq_img (π : AutSub E n) {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M)
    (h0 : M ≠ ⊥) (hle : M ≤ π.finPart W) : π.V = img (jOf W M) := by
  have h1 : img (jOf W M) ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨p, v, rfl⟩
    exact AutSub.mem_finPart.1 (hle p.2) v)
  exact ((π.isAut.irred _ h1 (img_stable hM)).resolve_left (nontrivial_of_ne_bot h0).2).symm

theorem finPart_stable (π : AutSub E n) (W : Wt E n) : ∀ k, ∀ f ∈ π.finPart W, algRep W k f ∈ π.finPart W :=
  fun k _ h => AutSub.mem_finPart.2 fun v => π.isAut.stable k _ (AutSub.mem_finPart.1 h v)

section Iso

variable {π π' : AutSub E n} {W : Wt E n} (e : π.finPart W ≃ₗ[ℂ] π'.finPart W) (T : π.V ≃ₗ[ℂ] π'.V)
  (hA : π.V = img (jOf W (π.finPart W)))
  (hT : ∀ p v (h : jOf W (π.finPart W) p v ∈ π.V), (T ⟨jOf W (π.finPart W) p v, h⟩ : UA E n → ℂ) = jOf W (π'.finPart W) (e p) v)

include hA hT

end Iso

end Concrete

end GlobalTheory.DefU.Pairs

end
