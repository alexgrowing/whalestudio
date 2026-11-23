import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.Twist RingTheory.Sequence
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Adelic

namespace GlobalTheory.CutDegree

section Sheaf

variable {X : Scheme.{0}} {L : LB X}

theorem injective_stalkLinear_cutHom (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i)
    (h : IsSMulRegular (F.presheaf.stalk x :) (X.presheaf.germ _ x hx (s.f i))) :
    Function.Injective (stalkLinear (cutHom F hL s) x) := by
  let e := stalkEquivOfLinear (F := twistZ F L (-1)) (G := F) (fun V hV => zchartEquiv hL (-1) i hV)
    (fun hV h' t => zchartEquiv_resM hL i hV h' t) hx
  have key : ⇑(stalkLinear (cutHom F hL s) x) = (X.presheaf.germ _ x hx (s.f i) • ·) ∘ e := funext fun u => by
    obtain ⟨V, hV, hxV, u, rfl⟩ := exists_germ_eq_of_mem hx u
    rw [stalkLinear_germ, cutHom_app F hL s i hV, QCoh.germ_smul, Function.comp_apply,
      stalkEquivOfLinear_germ _ _ hx hV]
    exact congrArg (· • _) (Cartier.germ_resG hV x hxV _)
  rw [key]
  exact h.comp e.injective

theorem nonempty_stalk_cut_equiv (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    Nonempty (QuotSMulTop (X.presheaf.germ _ x hx (s.f i)) (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x]
      ((cut F hL s).presheaf.stalk x :)) := by
  refine ⟨(Submodule.quotEquivOfEq _ _ ?_).trans
    ((stalkLinear (cutπ F hL s) x).quotKerEquivOfSurjective (stalkLinear_surjective _ x))⟩
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker]
  refine Iff.trans ?_ ((isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx t).symm
  simp

theorem topologicalKrullDim_le_zero_of_subset {T : Type} [TopologicalSpace T] {S : Finset T}
    (hc : ∀ x ∈ S, IsClosed ({x} : Set T)) {s : Set T} (hs : s ⊆ S) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := (S.finite_toSet.subset hs).to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 (hs x.2)).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

variable {k : Type} [Field k] (f : X ⟶ Sp k)

theorem interNum_sub_eq (hf : IsProjOver f) {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : G ⟶ F) {d : ℕ}
    {P : Fin d → LB X} (hP : ∀ i, (P i).IsLB) :
    letI := algebraΓOfHom f
    interNum k F P - interNum k G P = interNum k (cokernel φ) P - interNum k (kernel φ) P := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have fin : ∀ (H : X.Modules) [IsFiniteQC H], FiniteCohTwists k H := fun H _ =>
    finiteCohTwists_of_isProjOver (fun _ => rfl) H hf
  have h₁ := interNum_cokernel (kernel.ι φ) hP (fin _) (fin _)
  have h₂ := interNum_cokernel (kernel.ι (cokernel.π φ)) hP (fin _) (fin _)
  have e₁ : cokernel (kernel.ι φ) ≅ kernel (cokernel.π φ) := Abelian.coimageIsoImage φ
  have e₂ : cokernel (kernel.ι (cokernel.π φ)) ≅ cokernel φ :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (cokernel.π φ)))
  rw [interNum_congr k e₁] at h₁
  rw [interNum_congr k e₂] at h₂
  omega

theorem interNum_eq_sum_length (hf : IsProjOver f) (hL : L.IsLB) (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x))
    (S : Finset X) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (l : List L.Sec) (F : X.Modules) [IsFiniteQC F]
    (hz : ∀ x ∈ support F, (∀ s ∈ l, x ∉ nonzeroLocus s) → x ∈ S)
    (hr : ∀ x ∈ S, IsWeaklyRegular (F.presheaf.stalk x :) (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x)))) :
    letI := algebraΓOfHom f
    interNum k F (fun _ : Fin l.length => L) = (∑ x ∈ S, (Module.length (X.presheaf.stalk x)
      ((F.presheaf.stalk x :) ⧸ (Ideal.ofList (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x))) • ⊤ :
        Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))).toNat * f.residueDegree x : ℕ) := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  induction l generalizing F with
  | nil =>
    have hs : support F ⊆ S := fun x hx => hz x hx (by simp)
    have hd : suppDim F ≤ 0 := topologicalKrullDim_le_zero_of_subset hS hs
    have : IsEmpty (Fin ([] : List L.Sec).length) := inferInstanceAs (IsEmpty (Fin 0))
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd, hdim_zero_eq_sum_toNat f hd hs]
    refine congrArg _ <| Finset.sum_congr rfl fun x _ => ?_
    rw [(Submodule.quotEquivOfEqBot (Ideal.ofList [] • ⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
      (by simp only [Ideal.ofList_nil]; exact Submodule.bot_smul _)).length_eq.symm]
    rfl
  | cons s l ih =>
    have := isFiniteQC_twist (F := F) (isLB_lbZPow hL (-1))
    have e : (fun _ : Fin (s :: l).length => L) = (Fin.cons L (fun _ => L) : Fin (l.length + 1) → LB X) :=
      funext (Fin.cases rfl fun _ => rfl)
    have h0 : ∀ x ∈ S, Subsingleton ((kernel (cutHom F hL s)).presheaf.stalk x :) := fun x hx => by
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).1
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    have hK := ih (kernel (cutHom F hL s)) (fun x hx hl => ?_) fun x hx => ?_
    have hC := ih (cut F hL s) (fun x hx hl => ?_) fun x hx => ?_
    · rw [e, interNum_cons k F hL fun _ => hL, interNum_sub_eq f hf (cutHom F hL s) fun _ => hL, hK]
      rw [Finset.sum_eq_zero (fun x hx => ?_), Nat.cast_zero, sub_zero]
      · refine hC.trans (congrArg _ <| Finset.sum_congr rfl fun x _ => ?_)
        obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
        rw [List.map_cons, (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner _ _ _).length_eq,
          (Submodule.Quotient.equiv _ _ q (by rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).length_eq]
      · have := h0 x hx
        rw [Module.length_eq_zero]
        simp
    · rw [support_cut] at hx
      exact hz x hx.1 (List.forall_mem_cons.2 ⟨hx.2, hl⟩)
    · obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
      exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).2
    · have h₁ := support_subset_of_mono (kernel.ι (cutHom F hL s)) hx
      rw [support_twist (isLB_lbZPow hL (-1))] at h₁
      refine hz x h₁ (List.forall_mem_cons.2 ⟨fun hs => notMem_support_iff.2 ?_ hx, hl⟩)
      have hu := (X.mem_basicOpen _ x (hc x)).1 ((Cartier.mem_nonzeroLocus_iff s _ (hc x)).1 hs)
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) (hu.isSMulRegular _)
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    · have := h0 x hx
      exact ⟨fun _ _ _ _ _ => Subsingleton.elim _ _⟩

end Sheaf

section Algebra

variable {K R : Type} [Field K] [CommRing R]

def Leibniz (ev : R →+* K) (δ : R →+ K) : Prop := ∀ a b, δ (a * b) = ev a * δ b + ev b * δ a

def Leibniz.kerSubring {ev : R →+* K} {δ : R →+ K} (h : Leibniz ev δ) : Subring R where
  carrier := {r | δ r = 0}
  mul_mem' {a b} (ha : δ a = 0) (hb : δ b = 0) := by
    change δ (a * b) = 0
    rw [h, ha, hb, mul_zero, mul_zero, add_zero]
  one_mem' := by
    have := h 1 1
    rw [mul_one, ev.map_one, one_mul] at this
    exact left_eq_add.1 this
  add_mem' {a b} (ha : δ a = 0) (hb : δ b = 0) := by
    change δ (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  zero_mem' := map_zero δ
  neg_mem' {a} (ha : δ a = 0) := by
    change δ (-a) = 0
    rw [map_neg, ha, neg_zero]

end Algebra

section BaseChange

variable {k K : Type} [Field k] [Field K] {X X' : Scheme.{0}} {f : X ⟶ Sp k} {f' : X' ⟶ Sp K} {π : X' ⟶ X}
  {φ : k →+* K}

def stalkConst (f' : X' ⟶ Sp K) (z : X') : K →+* X'.presheaf.stalk z :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop ≫ X'.presheaf.germ ⊤ z trivial).hom

theorem stalkClosedPointTo_stalkConst {p : Sp K ⟶ X'} (hp : p ≫ f' = 𝟙 _) (a : K) :
    (Scheme.stalkClosedPointTo p).hom (stalkConst f' _ a) = a := by
  have e : p.appTop (f'.appTop ((Scheme.ΓSpecIso (.of K)).inv a)) = (Scheme.ΓSpecIso (.of K)).inv a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
    rfl
  refine (congrArg (stalkClosedPointIso (.of K)).hom ((Scheme.Hom.germ_stalkMap_apply p ⊤ _ trivial _).trans
    (congrArg ((Sp K).presheaf.germ ⊤ _ trivial) e))).trans ?_
  exact (ConcreteCategory.congr_hom (germ_stalkClosedPointIso_hom (.of K)) _).trans (Iso.inv_hom_id_apply _ _)

theorem ringKrullDim_stalk {d : ℕ} (h : SmoothOfRelativeDimension d f') {z : X'} (hz : IsClosed ({z} : Set X')) :
    ringKrullDim (X'.presheaf.stalk z) = d := by
  have := (StabFlat.stalk_of_smooth_local K X' f' d h z hz _ (Spec.map_preimage _).symm inferInstance).2.2.2
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at this
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).symm.trans this

theorem residueDegree_eq_one {p : Sp K ⟶ X'} (hp : p ≫ f' = 𝟙 _) :
    f'.residueDegree (p (IsLocalRing.closedPoint K)) = 1 := by
  rw [residueDegree_eq_finrank]
  letI := algebraΓOfHom f'
  letI := residueFieldAlgebraOver K (p (IsLocalRing.closedPoint K))
  let r := (Scheme.descResidueField (Scheme.stalkClosedPointTo p)).hom
  have h : ∀ a, r (algebraMap K _ a) = a := stalkClosedPointTo_stalkConst hp
  exact Module.finrank_of_bijective_algebraMap
    ⟨(algebraMap K _).injective, fun b => ⟨r b, r.injective (h _)⟩⟩

end BaseChange

section Count

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} {f : X ⟶ Sp K} {L : LB X}

end Count

section Cut

variable {F : Type} [Field F] (Y : Var F) {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)

omit Y in

theorem valAt_algebraMap {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h, IsFractionRing.injective _ Z.functionField h.choose_spec]

end Cut

end GlobalTheory.CutDegree
