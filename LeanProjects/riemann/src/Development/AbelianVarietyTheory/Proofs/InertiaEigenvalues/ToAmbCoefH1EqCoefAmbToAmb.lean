import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import BuildAid.D3

noncomputable section
namespace GlobalTheory.AdmFinite
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open scoped LaurentSeries PowerSeries
open ReciprocityTheory.Def (Z1 B1 H1)

section Alg
variable {O : Type} [CommRing O]

theorem eq_zero_of_res [IsLocalRing O] {m : Ideal O} (hm : m = IsLocalRing.maximalIdeal O) {C : Type} [AddCommGroup C] [Module O C]
    (A : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (C ⊗[O] X))
    (hmap : ∀ (X X' : Type) [AddCommGroup X] [Module O X] [Finite X] [AddCommGroup X'] [Module O X'] [Finite X']
      (f : X →ₗ[O] X') (c : C ⊗[O] X), (c ∈ A X → f.lTensor C c ∈ A X') ∧
        (Function.Injective f → f.lTensor C c ∈ A X' → c ∈ A X))
    (hk : Finite (O ⧸ m) → ∀ c ∈ A (O ⧸ m), c = 0) :
    ∀ (N : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Finite X], Nat.card X = N → ∀ c ∈ A X, c = 0 := by
  subst hm
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro X _ _ _ hN c hc
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact Subsingleton.elim _ _
  have : IsArtinian O X := isArtinian_of_finite
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule O X)).resolve_left top_ne_bot
  have hs : IsSimpleModule O S := isSimpleModule_iff_isAtom.mpr hS
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  have hfin : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Finite.of_equiv _ e.toEquiv
  have : Finite (X ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
  have hcard : Nat.card (X ⧸ S) < N := by
    have h1 := Submodule.card_eq_card_quotient_mul_card S
    have h2 : 1 < Nat.card S := by
      have := IsSimpleModule.nontrivial O S
      exact Finite.one_lt_card
    have h3 : 0 < Nat.card (X ⧸ S) := Nat.card_pos
    rw [← hN, h1]
    nlinarith
  have h0 : S.mkQ.lTensor C c = 0 := ih _ hcard (X ⧸ S) rfl _ ((hmap X (X ⧸ S) S.mkQ c).1 hc)
  let j : (O ⧸ IsLocalRing.maximalIdeal O) →ₗ[O] X := S.subtype ∘ₗ e.symm.toLinearMap
  have hj : Function.Injective j := S.injective_subtype.comp e.symm.injective
  have hex : Function.Exact j S.mkQ := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx => ⟨e ⟨x, hx⟩, by simp [j]⟩, by rintro ⟨y, rfl⟩; exact (e.symm y).2⟩
  obtain ⟨c₀, rfl⟩ := (lTensor_exact C hex S.mkQ_surjective c).mp h0
  rw [hk hfin c₀ ((hmap _ X j c₀).2 hj hc), map_zero]

theorem indep_cons [IsLocalRing O] {lam : O} (hl : Ideal.span {lam} = IsLocalRing.maximalIdeal O)
    {H : Type} [AddCommGroup H] [Module O H] {F C : Submodule O H} (h : IsCompl F C) {d : ℕ}
    (b : Module.Basis (Fin d) O F) (c : C ⊗[O] (O ⧸ Ideal.span {lam})) (hc : c ≠ 0) :
    IndepMod lam (Fin.cons (C.subtype.rTensor _ c) (fun a => (b a : H) ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam})) :
      Fin (d + 1) → H ⊗[O] (O ⧸ Ideal.span {lam})) := by
  intro x hx
  rw [Fin.sum_univ_succ] at hx
  simp only [Fin.cons_zero, Fin.cons_succ] at hx
  have hC : (C.projectionOnto F h.symm).rTensor _ (C.subtype.rTensor _ c) = c := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, Submodule.projectionOnto_comp_subtype]; simp
  have hF : (F.projectionOnto C h).rTensor _ (C.subtype.rTensor _ c) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : F.projectionOnto C h ∘ₗ C.subtype = 0 := by ext y; simp
    rw [this]; simp
  refine Fin.cases ?_ (fun a => ?_)
  · have h1 := congrArg ((C.projectionOnto F h.symm).rTensor _) hx
    simp only [map_add, map_smul, map_sum, hC, LinearMap.rTensor_tmul, map_zero] at h1
    simp only [Submodule.projectionOnto_apply_right, zero_tmul, smul_zero, Finset.sum_const_zero, add_zero] at h1
    rw [← Ideal.mem_span_singleton, hl]
    by_contra hu
    have hu' : IsUnit (x 0) := by simpa using hu
    exact hc (hu'.smul_eq_zero.mp h1)
  · have h1 := congrArg (fun y => TensorProduct.lid O _ ((b.coord a).rTensor _ ((F.projectionOnto C h).rTensor _ y))) hx
    simp only [map_add, map_smul, map_sum, hF, LinearMap.rTensor_tmul, map_zero] at h1
    simp only [Submodule.projectionOnto_apply_left, lid_tmul, smul_zero, zero_add, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul, smul_ite, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← h1, Algebra.smul_def, mul_one]
    rfl

theorem mem_range_of_bound [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    {H : Type} [AddCommGroup H] [Module O H] [Module.Free O H] [Module.Finite O H] {F C : Submodule O H}
    (h : IsCompl F C) (A : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H ⊗[O] X))
    (hmap : ∀ (X X' : Type) [AddCommGroup X] [Module O X] [Finite X] [AddCommGroup X'] [Module O X'] [Finite X']
      (f : X →ₗ[O] X') (c : H ⊗[O] X), (c ∈ A X → f.lTensor H c ∈ A X') ∧
        (Function.Injective f → f.lTensor H c ∈ A X' → c ∈ A X))
    (hsub : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∀ c ∈ A X, ∀ c' ∈ A X, c - c' ∈ A X)
    (hF : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (y : F ⊗[O] X), F.subtype.rTensor X y ∈ A X)
    (hk : Finite (O ⧸ Ideal.span {lam}) → ∀ (s : ℕ) (c : Fin s → H ⊗[O] (O ⧸ Ideal.span {lam})),
      (∀ a, c a ∈ A _) → IndepMod lam c → s ≤ Module.finrank O F)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] (c : H ⊗[O] X) (hc : c ∈ A X) :
    ∃ y : F ⊗[O] X, F.subtype.rTensor X y = c := by
  have hm : Ideal.span {lam} = IsLocalRing.maximalIdeal O := hl.maximalIdeal_eq.symm
  have key := eq_zero_of_res hm (C := C) (fun X _ _ => {y | C.subtype.rTensor X y ∈ A X})
    (fun X X' _ _ _ _ _ _ f y => by
      have e : C.subtype.rTensor X' (f.lTensor C y) = f.lTensor H (C.subtype.rTensor X y) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          LinearMap.lTensor_comp_rTensor]
      simp only [Set.mem_setOf_eq, e]
      exact hmap X X' f _)
    (fun hfin y hy => by
      by_contra hne
      have h1 := hk hfin _ _ (Fin.cases hy fun a => hF _ (Module.finBasis O F a ⊗ₜ[O] 1))
        (indep_cons hm h (Module.finBasis O F) y hne)
      omega)
  have hdec : c - F.subtype.rTensor X ((F.projectionOnto C h).rTensor X c) =
      C.subtype.rTensor X ((C.projectionOnto F h.symm).rTensor X c) := by
    rw [sub_eq_iff_eq_add', ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp, ← LinearMap.add_apply, ← LinearMap.rTensor_add]
    have : F.subtype ∘ₗ F.projectionOnto C h + C.subtype ∘ₗ C.projectionOnto F h.symm = LinearMap.id := by
      ext x
      exact Submodule.projection_add_projection_eq_self h x
    rw [this]; simp
  have h0 := key _ X rfl ((C.projectionOnto F h.symm).rTensor X c) (by
    change _ ∈ A X
    rw [← hdec]
    exact hsub X _ hc _ (hF X _))
  rw [h0, map_zero, sub_eq_zero] at hdec
  exact ⟨_, hdec.symm⟩

end Alg

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    (L : Lattice (O := O) ρ) (χ : G →* Oˣ)

def coefAmb {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) {X X' : Type} [AddCommGroup X]
    [Module O X] [AddCommGroup X'] [Module O X'] (f : X →ₗ[O] X') :
    Amb (twCoef W χ X) →ₗ[O] Amb (twCoef W χ X') :=
  Submodule.mapQ _ _ ((f.lTensor M).compLeft G) (by
    rintro z ⟨b, -, hb⟩
    refine ⟨f.lTensor M b, Submodule.mem_top, ?_⟩
    funext g
    have h1 : twCoef W χ X g b - b = z g := congrFun hb g
    change twCoef W χ X' g (f.lTensor M b) - f.lTensor M b = f.lTensor M (z g)
    rw [← h1, map_sub]
    congr 1
    clear h1 hb
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [coefRep_tmul]
    | add a b ha hb => simp only [map_add, ha, hb])

theorem toAmb_coefH1_eq_coefAmb_toAmb {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M) {X X' : Type}
    [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X'] (f : X →ₗ[O] X') (c : H1 (twCoef W χ X) ⊤) :
    toAmb (twCoef W χ X') (coefH1 W χ f c) = coefAmb χ W f (toAmb (twCoef W χ X) c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

theorem tensAmb_lTensor {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']
    (f : X →ₗ[O] X') (y : H1tw L χ ⊗[O] X) :
    tensAmb L χ X' (f.lTensor _ y) = coefAmb χ (latRep L) f (tensAmb L χ X y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c x =>
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    rfl

theorem subset_of_bound [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    [Module.Free O (H1tw L χ)] [Module.Finite O (H1tw L χ)] {F C : Submodule O (H1tw L χ)} (h : IsCompl F C)
    (hT : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], TensIso L χ X)
    (A : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H1 (twCoef (latRep L) χ X) ⊤))
    (hmap : ∀ (X X' : Type) [AddCommGroup X] [Module O X] [Finite X] [AddCommGroup X'] [Module O X'] [Finite X']
      (f : X →ₗ[O] X') (c : H1 (twCoef (latRep L) χ X) ⊤), (c ∈ A X → coefH1 (latRep L) χ f c ∈ A X') ∧
        (Function.Injective f → coefH1 (latRep L) χ f c ∈ A X' → c ∈ A X))
    (hsub : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      ∃ B : Submodule O (H1 (twCoef (latRep L) χ X) ⊤), A X = B)
    (hF : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      (((LinearMap.range ((tensAmb L χ X).comp (F.subtype.rTensor X))).comap
        (toAmb (twCoef (latRep L) χ X)) : Submodule O _) : Set _) ⊆ A X)
    (hk : ∀ (s : ℕ) (c : Fin s → H1 (twCoef (latRep L) χ (O ⧸ Ideal.span {lam})) ⊤),
      (∀ a, c a ∈ A _) → IndepMod lam c → s ≤ Module.finrank O F)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] :
    A X = (((LinearMap.range ((tensAmb L χ X).comp (F.subtype.rTensor X))).comap
        (toAmb (twCoef (latRep L) χ X)) : Submodule O _) : Set _) := by
  refine Set.Subset.antisymm (fun c hc => ?_) (hF X)
  have hex : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (y : H1tw L χ ⊗[O] X),
      ∃ c, toAmb (twCoef (latRep L) χ X) c = tensAmb L χ X y := fun X _ _ _ y => by
    have h1 := LinearMap.mem_range_self (tensAmb L χ X) y
    rw [(hT X).2] at h1
    exact h1
  have h1 := LinearMap.mem_range_self (toAmb (twCoef (latRep L) χ X)) c
  rw [← (hT X).2] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨y', hy'⟩ := mem_range_of_bound hl h
    (fun X _ _ => {y | ∃ c ∈ A X, toAmb (twCoef (latRep L) χ X) c = tensAmb L χ X y})
    (fun X X' _ _ _ _ _ _ f y => ⟨fun ⟨c, hc, e⟩ => ⟨_, (hmap X X' f c).1 hc, by
        rw [toAmb_coefH1_eq_coefAmb_toAmb, tensAmb_lTensor, e]⟩, fun hf ⟨c', hc', e⟩ => by
        obtain ⟨c, e'⟩ := hex X y
        refine ⟨c, (hmap X X' f c).2 hf ?_, e'⟩
        rwa [toAmb_injective _ (show toAmb (twCoef (latRep L) χ X') (coefH1 (latRep L) χ f c) =
            toAmb (twCoef (latRep L) χ X') c' by
          rw [toAmb_coefH1_eq_coefAmb_toAmb, e, tensAmb_lTensor, e'])]⟩)
    (fun X _ _ _ y ⟨c, hc, e⟩ y' ⟨c', hc', e'⟩ => ⟨c - c', by
        obtain ⟨B, hB⟩ := hsub X
        rw [hB] at hc hc' ⊢
        exact B.sub_mem hc hc', by rw [map_sub, map_sub, e, e']⟩)
    (fun X _ _ _ y => by
      obtain ⟨c, e⟩ := hex X (F.subtype.rTensor X y)
      exact ⟨c, hF X ⟨y, e.symm⟩, e⟩)
    (fun hfin s y hy hind => by
      choose c hc e using hy
      refine hk s c hc fun x hx => hind x ((hT _).1 ?_)
      have h2 := congrArg (toAmb (twCoef (latRep L) χ (O ⧸ Ideal.span {lam}))) hx
      simp only [map_sum, map_smul, e, map_zero] at h2
      simp only [map_sum, map_smul, map_zero, h2])
    X y ⟨c, hc, hy.symm⟩
  exact ⟨y', by rw [LinearMap.comp_apply, hy', hy]⟩

end Gal

section Data

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (Γ : GalData G Qp LL O) (t d : ℕ) (Ut : ZMod n → Multiset ℤ)

open GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing in

theorem adm_eq_H1fX (hO : IsDomain O) (hdvr : IsDiscreteValuationRing O) (hl : Irreducible Γ.lam)
    (hf1 : Module.Free O (HH Γ)) (hf2 : Module.Finite O (HH Γ))
    (hC : ∃ C : Submodule O (HH Γ), IsCompl (Hf PD Γ) C) (hd : Module.finrank O ↥(Hf PD Γ) = d)
    (hT : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], TensIso Γ.T₀.L Γ.χ₁ X)
    (hmap : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (X' : Type) [AddCommGroup X'] [Module O X']
      [Finite X'] (f : X →ₗ[O] X') (c : H1 (twCoef Γ.W₀ Γ.χ₁ X) ⊤),
      (c ∈ adm PD emb Γ t Ut Γ.W₀ X → coefH1 Γ.W₀ Γ.χ₁ f c ∈ adm PD emb Γ t Ut Γ.W₀ X') ∧
      (Function.Injective f → coefH1 Γ.W₀ Γ.χ₁ f c ∈ adm PD emb Γ t Ut Γ.W₀ X' → c ∈ adm PD emb Γ t Ut Γ.W₀ X))
    (hsub : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      ∃ A : Submodule O (H1 (twCoef Γ.W₀ Γ.χ₁ X) ⊤), adm PD emb Γ t Ut Γ.W₀ X = A)
    (hF : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _) ⊆ adm PD emb Γ t Ut Γ.W₀ X)
    (hk : ∀ (s : ℕ) (c : Fin s → H1 (twCoef Γ.W₀ Γ.χ₁ (resK Γ)) ⊤),
      (∀ a, c a ∈ adm PD emb Γ t Ut Γ.W₀ (resK Γ)) → IndepMod Γ.lam c → s ≤ d)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] :
    adm PD emb Γ t Ut Γ.W₀ X = (finiteSelmer PD Γ.T₀.L Γ.χ₁ X : Set _) := by
  obtain ⟨C, hC⟩ := hC
  exact subset_of_bound Γ.T₀.L Γ.χ₁ hl hC hT (fun X _ _ => adm PD emb Γ t Ut Γ.W₀ X)
    (fun X X' _ _ _ _ _ _ f c => hmap X X' f c) hsub hF (fun s c hc hi => (hk s c hc hi).trans hd.ge) X

end Data

theorem cls_eq_H1fX : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Lem0 S.Γ.W₀ → S.FreeH →
    S.FSummand → S.FinAdm → S.ResBound S.Γ.W₀ S.D.dsum → ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    S.cls S.Γ.W₀ X = (finiteSelmer (P.PD S.K) S.Γ.T₀.L S.Γ.χ₁ X : Set _) := by
  intro l _ P S h0 hfree hsum hfin hres X _ _ _
  have hg := (GlobalTheory.LocalIntegers.goodO_integers l S.LL).1
  exact adm_eq_H1fX (P.PD S.K) S.emb S.Γ S.D.t S.D.dsum S.D.Ut hg.choose hg.choose_spec.1
    S.hyp.1.2.2.2.2.2 hfree.1.1 hfree.1.2.1
    hsum.1 hsum.2 hfree.2 (fun X _ _ _ => (h0 X).2.2) (fun X _ _ _ => (h0 X).1) hfin hres X

end GlobalTheory.AdmFinite
