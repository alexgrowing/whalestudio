import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullTotMemBTot

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

theorem eq_of_zsmul_add {A : Type*} [AddCommGroup A] {x y : A} (h : (1 : ℤ) • x + (-1 : ℤ) • y = 0) :
    x = y := by
  rw [one_smul, neg_one_smul, add_neg_eq_zero] at h; exact h

theorem zsmul_add_cancel {A : Type*} [AddCommGroup A] (x : A) : (1 : ℤ) • x + (-1 : ℤ) • x = 0 := by
  rw [one_smul, neg_one_smul, add_neg_cancel]

section Zero

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem map_cochain_congr (M : C ⥤ ModuleCat.{0} R) (f : CatH.Cn M 0) {t t' : ComposableArrows C 0}
    (h : t = t') {Y : C} (u : t.obj (Fin.last 0) ⟶ Y) (u' : t'.obj (Fin.last 0) ⟶ Y) (hu : HEq u u') :
    (M.map u).hom (f t) = (M.map u').hom (f t') := by
  subst h
  rw [eq_of_heq hu]

theorem compat_of_d_eq_zero (M : C ⥤ ModuleCat.{0} R) {f : CatH.Cn M 0} (hf : CatH.d M 0 f = 0)
    {T T' : C} (φ : T ⟶ T') :
    (M.map φ).hom (f (ComposableArrows.mk₀ T)) = f (ComposableArrows.mk₀ T') := by
  let s := ComposableArrows.mk₁ φ
  have h0 : (M.map (CatH.toLast 0 s)).hom (f (CatH.face 0 s)) = f (ComposableArrows.mk₀ T') :=
    (map_cochain_congr M f (t := CatH.face 0 s) (t' := ComposableArrows.mk₀ T')
      (ComposableArrows.ext₀ rfl) (CatH.toLast 0 s) (𝟙 T') HEq.rfl).trans
      (congrArg (fun g : M.obj T' ⟶ M.obj T' ↦ g.hom (f (ComposableArrows.mk₀ T'))) (M.map_id T'))
  have h1 : (M.map (CatH.toLast 1 s)).hom (f (CatH.face 1 s)) =
      (M.map φ).hom (f (ComposableArrows.mk₀ T)) :=
    map_cochain_congr M f (t := CatH.face 1 s) (t' := ComposableArrows.mk₀ T)
      (ComposableArrows.ext₀ rfl) (CatH.toLast 1 s) φ HEq.rfl
  have e : ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (M.map (CatH.toLast i s)).hom (f (CatH.face i s)) = 0 :=
    congrFun hf s
  rw [Fin.sum_univ_two, h0, h1] at e
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at e
  exact (eq_of_zsmul_add e).symm

variable (F : C ⥤ CommAlgCat.{0} R)

theorem BF_self : ∀ n : ℕ, BF F n n = ⊥
  | 0 => rfl
  | n + 1 => by
    change (TotF F (n + 1) n).map _ = ⊥
    rw [TotF_eq_bot F (Nat.lt_succ_self n), Submodule.map_bot]

theorem HypF.toHyp_zero_bijective (n : ℕ) : Function.Bijective (HypF.toHyp F 0 n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    LinearMap.range_eq_top.1 (Hyp.fil_zero F n)⟩
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F 0 n x
  have h : c.1 ∈ BTot F n := Hyp.mk_eq_zero.1 hx
  refine HypF.mk_eq_zero.2 ?_
  rcases n with _ | n
  · exact h
  · obtain ⟨e, he⟩ := h
    exact ⟨e, by rw [TotF_zero]; trivial, he⟩

def ofTop (n : ℕ) : Term F 0 n →ₗ[R] Tot F n :=
  LinearMap.single R (fun b : Bidegree n ↦ Term F b.1.1 b.1.2) ⟨(0, n), zero_add n⟩

variable {F}

theorem ofTop_same {n : ℕ} (c : Term F 0 n) (h : 0 + n = n) : ofTop F n c ⟨(0, n), h⟩ = c :=
  Pi.single_eq_same (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) _ _

theorem ofTop_mem_TotF {n : ℕ} (c : Term F 0 n) : ofTop F n c ∈ TotF F n n := fun b hb ↦
  Pi.single_eq_of_ne (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2)
    (fun e ↦ by rw [e] at hb; exact lt_irrefl _ hb) _

theorem eq_ofTop {n : ℕ} {c : Tot F n} (hc : c ∈ TotF F n n) :
    c = ofTop F n (c ⟨(0, n), zero_add n⟩) := by
  funext ⟨(a, q), h⟩
  rcases a with _ | a
  · obtain rfl : q = n := by simpa using h
    exact (ofTop_same _ _).symm
  · have hq : q < n := by dsimp only at h; omega
    rw [hc _ hq, ofTop_mem_TotF _ _ hq]

theorem ofTop_mem_ZF {n : ℕ} {c : Term F 0 n} (h1 : dH F 0 n c = 0) (h2 : dV F 0 n c = 0) :
    ofTop F n c ∈ ZF F n n := by
  refine ⟨ofTop_mem_TotF c, funext fun ⟨(a, q), h⟩ ↦ ?_⟩
  dsimp only at h
  have hH : totH F n (ofTop F n c) ⟨(a, q), h⟩ = 0 := by
    rcases a with _ | _ | a
    · rfl
    · obtain rfl : q = n := by omega
      rw [totH_succ, ofTop_same, h1]
    · rw [totH_succ, ofTop_mem_TotF c _ (by dsimp only; omega), map_zero]
  have hV : totV F n (ofTop F n c) ⟨(a, q), h⟩ = 0 := by
    rcases q with _ | q
    · rfl
    rcases a with _ | a
    · obtain rfl : q = n := by omega
      rw [totV_succ, ofTop_same, h2, smul_zero]
    · rw [totV_succ, ofTop_mem_TotF c _ (by dsimp only; omega), map_zero, smul_zero]
  rw [dTot_apply, hH, hV, add_zero]; rfl

theorem dTot_top {n : ℕ} (c : Tot F n) (h : 0 + (n + 1) = n + 1) :
    dTot F n c ⟨(0, n + 1), h⟩ = dV F 0 n (c ⟨(0, n), zero_add n⟩) := by
  rw [dTot_apply, totH_zero, totV_succ, zero_add, pow_zero, one_smul]

end Zero

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

def coneTerm (q : ℕ) : Om R B q →ₗ[R] Term F 0 q :=
  LinearMap.pi fun s ↦ (SemiHom.of_algHom (e (s.obj (Fin.last 0)))).mOm q

theorem coneTerm_apply {q : ℕ} (ω : Om R B q) (s : ComposableArrows C 0) :
    coneTerm e q ω s = (SemiHom.of_algHom (e (s.obj (Fin.last 0)))).mOm q ω := rfl

include he in

theorem dH_coneTerm {q : ℕ} (ω : Om R B q) : dH F 0 q (coneTerm e q ω) = 0 := by
  funext s
  have k : ∀ i : Fin 2, ((OmF F q).map (CatH.toLast i s)).hom (coneTerm e q ω (CatH.face i s)) =
      (SemiHom.of_algHom (e (s.obj (Fin.last 1)))).mOm q ω := fun i ↦
    SemiHom.mOm_mOm _ (semiHom_mp F (CatH.toLast i s)) _ (he _) ω
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    ((OmF F q).map (CatH.toLast i s)).hom (coneTerm e q ω (CatH.face i s)) = 0
  rw [Fin.sum_univ_two, k, k]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  exact zsmul_add_cancel _

theorem dV_coneTerm {q : ℕ} (ω : Om R B q) :
    dV F 0 q (coneTerm e q ω) = coneTerm e (q + 1) (dOm R B q ω) :=
  funext fun _ ↦ (SemiHom.mOm_dOm _ ω).symm

def coneZ (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] ZF F n n :=
  ((ofTop F n ∘ₗ coneTerm e n).domRestrict _).codRestrict _ fun ω ↦
    ofTop_mem_ZF (dH_coneTerm e he ω.1)
      (by rw [dV_coneTerm]; exact (congrArg (coneTerm e (n + 1)) ω.2).trans (map_zero _))

def coneF (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] HypF F n n := HypF.mk F n n ∘ₗ coneZ e he n

def coneCl (n : ℕ) : LinearMap.ker (dOm R B n) →ₗ[R] Hyp F n := HypF.toHyp F n n ∘ₗ coneF e he n

theorem coneCl_mem_fil {n : ℕ} (ω : LinearMap.ker (dOm R B n)) : coneCl e he n ω ∈ Hyp.fil F n n :=
  ⟨coneF e he n ω, rfl⟩

theorem coneCl_dOm {n : ℕ} (η : Om R B n) : coneCl e he (n + 1) ⟨dOm R B n η, dOm_dOm η⟩ = 0 := by
  refine Hyp.mk_eq_zero.2 ⟨ofTop F n (coneTerm e n η), ?_⟩
  have hm : dTot F n (ofTop F n (coneTerm e n η)) ∈ TotF F (n + 1) (n + 1) := by
    rintro ⟨⟨a, q⟩, h⟩ hq
    dsimp only at h hq
    have hH : totH F n (ofTop F n (coneTerm e n η)) ⟨(a, q), h⟩ = 0 := by
      rcases a with _ | _ | a
      · rfl
      · obtain rfl : q = n := by omega
        rw [totH_succ, ofTop_same, dH_coneTerm e he]
      · rw [totH_succ, ofTop_mem_TotF _ _ (by dsimp only; omega), map_zero]
    have hV : totV F n (ofTop F n (coneTerm e n η)) ⟨(a, q), h⟩ = 0 := by
      rcases q with _ | q
      · rfl
      · rw [totV_succ, ofTop_mem_TotF _ _ (by dsimp only; omega), map_zero, smul_zero]
    rw [dTot_apply, hH, hV, add_zero]
  rw [eq_ofTop hm, dTot_top, ofTop_same, dV_coneTerm]
  rfl

variable {T₀ : C} (hb : Function.Bijective (e T₀))

def backOm (q : ℕ) : Om R (F.obj T₀) q →ₗ[R] Om R B q :=
  (SemiHom.of_algHom (AlgEquiv.ofBijective _ hb).symm.toAlgHom).mOm q

theorem backOm_coneTerm {q : ℕ} (ω : Om R B q) :
    backOm e hb q (coneTerm e q ω (ComposableArrows.mk₀ T₀)) = ω :=
  (SemiHom.mOm_mOm (SemiHom.of_algHom (e T₀)) _ (SemiHom.of_algHom (AlgHom.id R B))
    (fun b ↦ (AlgEquiv.ofBijective _ hb).symm_apply_apply b) ω).trans
    (SemiHom.mOm_id _ (fun _ ↦ rfl) ω)

include hb in

theorem coneCl_eq_zero_iff {n : ℕ} (ω : LinearMap.ker (dOm R B (n + 1))) :
    coneCl e he (n + 1) ω = 0 ↔ ∃ η, dOm R B n η = ω.1 := by
  refine ⟨fun h ↦ ?_, fun ⟨η, hη⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := Hyp.mk_eq_zero.1 h
    have h1 := congrFun hc ⟨(0, n + 1), zero_add _⟩
    rw [dTot_top] at h1
    have h2 := congrFun (h1.trans (ofTop_same (coneTerm e (n + 1) ω.1) _)) (ComposableArrows.mk₀ T₀)
    refine ⟨backOm e hb n (c ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)), ?_⟩
    rw [← backOm_coneTerm e hb ω.1, ← h2]
    exact (SemiHom.mOm_dOm _ _).symm
  · rw [show ω = ⟨dOm R B n η, dOm_dOm η⟩ from Subtype.ext hη.symm, coneCl_dOm]

include hb in

theorem coneF_bijective (h : Limits.IsInitial T₀) (n : ℕ) : Function.Bijective (coneF e he n) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ω hω ↦ ?_, fun x ↦ ?_⟩
  · have h1 : ofTop F n (coneTerm e n ω.1) ∈ BF F n n := HypF.mk_eq_zero.1 hω
    rw [BF_self] at h1
    have h2 := (ofTop_same (coneTerm e n ω.1) (zero_add n)).symm.trans
      (congrFun (show ofTop F n (coneTerm e n ω.1) = 0 from h1) _)
    refine Subtype.ext ?_
    rw [← backOm_coneTerm e hb ω.1, h2]
    exact map_zero _
  · obtain ⟨c, rfl⟩ := HypF.mk_surjective F n n x
    have h1 := dH_lead F (zero_add n) c
    have h2 := (dTot_top c.1 (zero_add _)).symm.trans
      (congrFun (show dTot F n c.1 = 0 from c.2.2) _)
    refine ⟨⟨backOm e hb n (c.1 ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)), ?_⟩, ?_⟩
    · refine (SemiHom.mOm_dOm _ _).symm.trans ?_
      have h3 : dOm R (F.obj T₀) n (c.1 ⟨(0, n), zero_add n⟩ (ComposableArrows.mk₀ T₀)) = 0 :=
        congrFun h2 (ComposableArrows.mk₀ T₀)
      exact (congrArg (backOm e hb (n + 1)) h3).trans (map_zero _)
    · refine congrArg (HypF.mk F n n) (Subtype.ext ?_)
      refine (congrArg (ofTop F n) (funext fun s ↦ ?_)).trans (eq_ofTop c.2.1).symm
      obtain ⟨T, rfl⟩ := s.mk₀_surjective
      refine Eq.trans ?_ (compat_of_d_eq_zero (OmF F n) h1 (h.to T))
      exact SemiHom.mOm_mOm _ (SemiHom.of_algHom (e T)) (semiHom_mp F (h.to T))
        (fun b ↦ (he (h.to T) _).symm.trans
          (congrArg (mp F (h.to T)) ((AlgEquiv.ofBijective _ hb).apply_symm_apply b))) _

include hb in

theorem coneCl_zero_bijective (h : Limits.IsInitial T₀) : Function.Bijective (coneCl e he 0) :=
  (HypF.toHyp_zero_bijective F 0).comp (coneF_bijective e he hb h 0)

end Cone

section Low

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def fn0 (B : Type) [CommRing B] [Algebra R B] : Om R B 0 ≃ₗ[R] B :=
  (exteriorPower.zeroEquiv B Ω[B⁄R]).restrictScalars R

def fm1 (B : Type) [CommRing B] [Algebra R B] : Om R B 1 ≃ₗ[R] Ω[B⁄R] :=
  (exteriorPower.oneEquiv B Ω[B⁄R]).restrictScalars R

def toTot1 : Tot F 1 →ₗ[R] Tot1 F where
  toFun c := (fun _ T' φ ↦ fn0 (F.obj T') (c ⟨(1, 0), rfl⟩ (ComposableArrows.mk₁ φ)),
    fun T ↦ fm1 (F.obj T) (c ⟨(0, 1), rfl⟩ (ComposableArrows.mk₀ T)))
  map_add' _ _ := Tot1.ext (fun _ T' _ ↦ map_add (fn0 (F.obj T')) _ _)
    fun T ↦ map_add (fm1 (F.obj T)) _ _
  map_smul' _ _ := Tot1.ext (fun _ _ _ ↦ LinearEquiv.map_smul _ _ _) fun _ ↦ LinearEquiv.map_smul _ _ _

def toTot2 : Tot F 2 →ₗ[R] Tot2 F where
  toFun c := (fun _ _ T'' φ ψ ↦ fn0 (F.obj T'') (c ⟨(2, 0), rfl⟩ (ComposableArrows.mk₂ φ ψ)),
    fun _ T' φ ↦ fm1 (F.obj T') (c ⟨(1, 1), rfl⟩ (ComposableArrows.mk₁ φ)),
    fun T ↦ c ⟨(0, 2), rfl⟩ (ComposableArrows.mk₀ T))
  map_add' _ _ := Tot2.ext (fun _ _ T'' _ _ ↦ map_add (fn0 (F.obj T'')) _ _)
    (fun _ T' _ ↦ map_add (fm1 (F.obj T')) _ _) fun _ ↦ rfl
  map_smul' _ _ := Tot2.ext (fun _ _ _ _ _ ↦ LinearEquiv.map_smul _ _ _)
    (fun _ _ _ ↦ LinearEquiv.map_smul _ _ _) fun _ ↦ rfl

end Low

end GlobalTheory.HodgeCoh
