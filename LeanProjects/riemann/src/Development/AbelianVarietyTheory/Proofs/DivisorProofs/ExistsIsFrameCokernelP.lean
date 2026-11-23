import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open scoped Classical

namespace GlobalTheory.GrFilt

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}

def genSpan (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (k : ℕ) : Submodule X.functionField (genStalk L) :=
  Submodule.span X.functionField {v | ∃ a, o a < k ∧ ∃ (V : X.Opens) (h : genericPoint X ∈ V) (s : Γ(E a, V)),
    L.presheaf.germ V _ h ((T a).app V s) = v}

def filtSub (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (k : ℕ) : Sub L := Sub.ofGeneric (genSpan o T k)

def AdaptedAt (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) {V : X.Opens} (f : ∀ a, Fin (r a) → Γ(E a, V))
    (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V))
    (hc : IsFrame c) : Prop :=
  ∀ a i, (∀ z : Σ a, Fin (r a), o a < o z.1 → (hc.basis le_rfl).repr ((T a).app V (f a i)) z = 0) ∧
    ∀ j, (hc.basis le_rfl).repr ((T a).app V (f a i)) ⟨a, j⟩ = ((hf' a).basis le_rfl).repr ((u a).app V (f a i)) j

theorem locAdapted_iff (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) (V : X.Opens) :
    LocAdapted r o T u V ↔ ∃ (f : ∀ a, Fin (r a) → Γ(E a, V)) (_ : ∀ a, IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
      (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc :=
  Iff.rfl

theorem genSpan_mono (o : ι → ℕ) (T : ∀ a, E a ⟶ L) {k l : ℕ} (h : k ≤ l) : genSpan o T k ≤ genSpan o T l :=
  Submodule.span_mono fun _ ⟨a, ha, rest⟩ => ⟨a, lt_of_lt_of_le ha h, rest⟩

theorem app_mem_filtSub (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (a : ι) {k : ℕ} (hk : o a < k) (V : X.Opens) (s : Γ(E a, V)) :
    (T a).app V s ∈ (filtSub o T k).sec V :=
  fun h => Submodule.subset_span ⟨a, hk, V, h, s, rfl⟩

def stepMap (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (k : ℕ) : (filtSub o T k).toMod ⟶ (filtSub o T (k + 1)).toMod :=
  (filtSub o T (k + 1)).lift (filtSub o T k).incl fun V s h =>
    genSpan_mono o T (Nat.le_succ k) ((filtSub o T k).incl_app_mem s h)

@[reassoc (attr := simp)] theorem stepMap_incl (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (k : ℕ) :
    stepMap o T k ≫ (filtSub o T (k + 1)).incl = (filtSub o T k).incl := rfl

def liftT (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (a : ι) : E a ⟶ (filtSub o T (o a + 1)).toMod :=
  (filtSub o T (o a + 1)).lift (T a) fun V s => app_mem_filtSub o T a (Nat.lt_succ_self _) V s

@[reassoc (attr := simp)] theorem liftT_incl (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (a : ι) :
    liftT o T a ≫ (filtSub o T (o a + 1)).incl = T a := rfl

end GlobalTheory.GrFilt

namespace GlobalTheory.GrFilt

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {κ : Type} [Fintype κ]

theorem exists_isFrame_subP (P : Sub F) (c : κ → Γ(F, U)) (hc : IsFrame c) (Q : κ → Prop) [DecidablePred Q]
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : κ → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j, ¬ Q j → a j = 0) :
    ∃ t : {z // Q z} → Γ(P.toMod, U), IsFrame t ∧ ∀ j, P.incl.app U (t j) = c j := by
  have hmem (j : {z // Q z}) : c j ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (j : κ) 1)).2 fun j' hj' => by
      rw [Pi.single_apply, if_neg (by rintro rfl; exact hj' j.2)]
    simpa [Pi.single_apply, resM_self] using this
  refine ⟨fun j => P.mkSec _ (hmem j), isFrame_iff.2 fun V h => ⟨?_, fun t _ => ?_⟩, fun _ => rfl⟩
  · refine LinearIndependent.of_comp (QCoh.appLinear P.incl V) ?_
    have := (hc.basis h).linearIndependent.comp _ (Subtype.val_injective (p := Q))
    convert this using 1
    funext j
    simp only [Function.comp_apply, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM, Sub.incl_app_mkSec]
  · have h1 := P.incl_app_mem t
    rw [← (hc.basis h).sum_repr (P.incl.app V t)] at h1
    simp only [IsFrame.basis_apply] at h1
    have h2 := (hP V h _).1 h1
    have h3 : t = ∑ j : {z // Q z}, (hc.basis h).repr (P.incl.app V t) j • resM P.toMod h (P.mkSec _ (hmem j)) := by
      apply P.incl_app_injective V
      conv_lhs => rw [← (hc.basis h).sum_repr (P.incl.app V t)]
      simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec, IsFrame.basis_apply]
      symm
      refine Finset.sum_of_injOn Subtype.val Subtype.val_injective.injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_) (fun _ _ => rfl)
      rw [h2 j (fun hq => hj ⟨⟨j, hq⟩, by simp, rfl⟩), zero_smul]
    rw [h3]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def qFirst (Q : κ → Prop) [DecidablePred Q] : κ ≃ Fin (Fintype.card {z // Q z} + Fintype.card {z // ¬ Q z}) :=
  (Equiv.sumCompl Q).symm.trans ((Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv)

theorem qFirst_lt_iff (Q : κ → Prop) [DecidablePred Q] (z : κ) : ((qFirst Q z : ℕ) < Fintype.card {z // Q z}) ↔ Q z := by
  by_cases h : Q z
  · simp [qFirst, h, Equiv.sumCompl_symm_apply_of_pos]
  · simp [qFirst, h, Equiv.sumCompl_symm_apply_of_neg]

theorem exists_isFrame_cokernelP (P : Sub F) (c : κ → Γ(F, U)) (hc : IsFrame c) (Q : κ → Prop) [DecidablePred Q]
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : κ → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j, ¬ Q j → a j = 0) :
    ∃ e : Fin (Fintype.card {z // ¬ Q z}) → Γ(cokernel P.incl, U), IsFrame e := by
  set σ := qFirst Q
  obtain ⟨e, he⟩ := exists_isFrame_cokernel_of_frame P (c ∘ σ.symm) (hc.comp_equiv σ.symm) (Fintype.card {z // Q z})
    (Nat.le_add_right _ _) fun V h a => by
      have e1 : (∑ j, a j • resM F h ((c ∘ σ.symm) j)) = ∑ z, a (σ z) • resM F h (c z) :=
        (Equiv.sum_comp σ (fun j => a j • resM F h ((c ∘ σ.symm) j))).symm.trans (by simp)
      rw [e1]
      refine (hP V h (fun z => a (σ z))).trans ?_
      constructor
      · intro H j hj
        have := H (σ.symm j) (fun hq => by
          have := (qFirst_lt_iff Q (σ.symm j)).2 hq
          simp only [σ, Equiv.apply_symm_apply] at this
          omega)
        simpa using this
      · intro H z hz
        exact H (σ z) (Nat.le_of_not_lt (mt (qFirst_lt_iff Q z).1 hz))
  have hn : Fintype.card {z // Q z} + Fintype.card {z // ¬ Q z} - Fintype.card {z // Q z} = Fintype.card {z // ¬ Q z} :=
    Nat.add_sub_cancel_left _ _
  exact ⟨e ∘ (finCongr hn).symm, he.comp_equiv _⟩

end GlobalTheory.GrFilt

namespace GlobalTheory.GrFilt

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules}

variable (r : ι → ℕ) in

def FrameMem (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) : Prop :=
  ∀ (k : ℕ) (V : X.Opens) (f : ∀ a, Fin (r a) → Γ(E a, V)) (_ : ∀ a, IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
    (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc →
    ∀ (V' : X.Opens) (h : V' ≤ V) (a : (Σ a, Fin (r a)) → Γ(X, V')),
      (∑ z, a z • resM L h (c z)) ∈ (filtSub o T k).sec V' ↔ ∀ z, k ≤ o z.1 → a z = 0

variable (r : ι → ℕ) in

def GenSpanEq (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) : Prop :=
  ∀ (V : X.Opens) (f : ∀ a, Fin (r a) → Γ(E a, V)) (_ : ∀ a, IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
    (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc →
    ∀ (hV : genericPoint X ∈ V) (k : ℕ),
      genSpan o T k = Submodule.span X.functionField ((fun z => L.presheaf.germ V _ hV (c z)) '' {z | o z.1 < k})

variable (r : ι → ℕ) in

def IsProj (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) (b : ι) (κ : (filtSub o T (o b + 1)).toMod ⟶ E' b) :
    Prop :=
  ∀ (V : X.Opens) (f : ∀ a, Fin (r a) → Γ(E a, V)) (_ : ∀ a, IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
    (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c), AdaptedAt o T u f f' hf' c hc →
    ∀ (z : Σ a, Fin (r a)) (t : Γ((filtSub o T (o b + 1)).toMod, V)), (filtSub o T (o b + 1)).incl.app V t = c z →
      κ.app V t = if h : z.1 = b then f' b (Fin.cast (congrArg r h) z.2) else 0

end GlobalTheory.GrFilt

end
