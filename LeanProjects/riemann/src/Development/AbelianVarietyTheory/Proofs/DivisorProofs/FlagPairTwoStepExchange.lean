import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.VB (IsVB IsSubbundle)
open GlobalTheory.CechPic

namespace GlobalTheory.Vert.Flag

variable {X : Scheme.{0}} {E : X.Modules} {r : ℕ} (fl : Flag E r) (m : ℕ) (hm : m + 2 ≤ r)

def step₂ : fl.F ⟨m, by omega⟩ ⟶ fl.F ⟨m + 2, by omega⟩ :=
  fl.step ⟨m, by omega⟩ ≫ fl.step ⟨m + 1, by omega⟩

@[reassoc]
theorem step₂_ι : fl.step₂ m hm ≫ fl.ι ⟨m + 2, by omega⟩ = fl.ι ⟨m, by omega⟩ :=
  (Category.assoc _ _ _).trans ((congrArg (fl.step ⟨m, by omega⟩ ≫ ·) (fl.step_ι ⟨m + 1, by omega⟩)).trans
    (fl.step_ι ⟨m, by omega⟩))

def quot₂ : X.Modules := cokernel (fl.step₂ m hm)

abbrev quot₂Seq : ShortComplex X.Modules :=
  (kernelCokernelCompSequence.snakeInput (fl.step ⟨m, by omega⟩) (fl.step ⟨m + 1, by omega⟩)).L₃

theorem quot₂Seq_shortExact : (fl.quot₂Seq m hm).ShortExact :=
  shortExact_cokernel_comp _ _

theorem isVB_quot₂ : IsVB (fl.quot₂ m hm) 2 :=
  (VBExt.isVB_and_cls_det_of_shortExact X _ 1 1 (fl.quot₂Seq_shortExact m hm) (fl.isVB_gr _)
    (fl.isVB_gr _)).1

def quot₂GrIso : cokernel (fl.quot₂Seq m hm).f ≅ fl.gr ⟨m + 1, by omega⟩ :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (fl.quot₂Seq_shortExact m hm).gIsCokernel

@[reassoc]
theorem π_quot₂GrIso : cokernel.π _ ≫ (fl.quot₂GrIso m hm).hom = (fl.quot₂Seq m hm).g :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

open ZeroObject in

def quotTwo : Flag (fl.quot₂ m hm) 2 where
  F := ![0, fl.gr ⟨m, by omega⟩, fl.quot₂ m hm]
  ι := Fin.cons 0 (Fin.cons (fl.quot₂Seq m hm).f (Fin.cons (𝟙 _) finZeroElim))
  isSubbundle := Fin.cons
    ⟨(isZero_zero _).mono _, 2, (fl.isVB_quot₂ m hm).of_iso cokernelZeroIsoTarget.symm⟩
    (Fin.cons (by exact VB.isSubbundle_of_shortExact (fl.quot₂Seq_shortExact m hm) (fl.isVB_gr _))
      (Fin.cons (VB.isSubbundle_of_isIso (𝟙 _)) finZeroElim))
  isVB := Fin.cons (VB.isVB_zero_iff.2 (isZero_zero _))
    (Fin.cons (fl.isVB_gr _) (Fin.cons (fl.isVB_quot₂ m hm) finZeroElim))
  step := Fin.cons 0 (Fin.cons (fl.quot₂Seq m hm).f finZeroElim)
  step_ι := Fin.cons zero_comp (Fin.cons (Category.comp_id _) finZeroElim)
  isIso_last := IsIso.id _

def quotTwoGr₀ : (fl.quotTwo m hm).gr 0 ≅ fl.gr ⟨m, by omega⟩ := cokernelZeroIsoTarget

def quotTwoGr₁ : (fl.quotTwo m hm).gr 1 ≅ fl.gr ⟨m + 1, by omega⟩ := fl.quot₂GrIso m hm

theorem π_quotTwoGr₀ : (fl.quotTwo m hm).π 0 = (fl.quotTwoGr₀ m hm).inv :=
  cokernelZeroIsoTarget_inv.symm

theorem π_π_quotTwoGr₁ : cokernel.π (fl.step₂ m hm) ≫ (fl.quotTwo m hm).π 1 ≫
    (fl.quotTwoGr₁ m hm).hom = fl.π ⟨m + 1, by omega⟩ := by
  change cokernel.π _ ≫ cokernel.π _ ≫ (fl.quot₂GrIso m hm).hom = _
  rw [π_quot₂GrIso]
  simp [quot₂Seq, Flag.π, step₂]

theorem π_quot₂Seq_f : fl.π ⟨m, by omega⟩ ≫ (fl.quot₂Seq m hm).f =
    fl.step ⟨m + 1, by omega⟩ ≫ cokernel.π (fl.step₂ m hm) := by
  simp [quot₂Seq, Flag.π, step₂]

theorem smallCls_root_eq_of_iso {E₁ E₂ : X.Modules} {N₁ N₂ : ℕ} (fl₁ : Flag E₁ N₁)
    (fl₂ : Flag E₂ N₂) (i : Fin N₁) (j : Fin N₂) (e : fl₁.gr i ≅ fl₂.gr j) :
    smallCls _ (fl₁.isLB_root i) = smallCls _ (fl₂.isLB_root j) :=
  (smallCls_eq_iff _ _).2 ((fl₁.isVB_gr i).lbIso_det_of_iso e)

end GlobalTheory.Vert.Flag

namespace GlobalTheory.Vert.Model.FlagPair

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : Model O}
  {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {r : ℕ}

section QuotTwo

variable (P : FlagPair φ r) (m : ℕ) (hm : m + 2 ≤ r)

theorem gen_step₂ : Z.genRes.map (P.fl.step₂ m hm) ≫ (P.gen ⟨m + 2, by omega⟩).hom =
    (P.gen ⟨m, by omega⟩).hom ≫ Z.genRes.map (P.fl'.step₂ m hm) := by
  have h₀ := P.gen_step ⟨m, by omega⟩
  have h₁ := P.gen_step ⟨m + 1, by omega⟩
  simp only [Fin.succ_mk, Fin.castSucc_mk] at h₀ h₁
  simp only [Flag.step₂, Functor.map_comp, Category.assoc]
  rw [h₁, reassoc_of% h₀]

def quotTwoIso : Z.GenIso (P.fl.quot₂ m hm) (P.fl'.quot₂ m hm) :=
  PreservesCokernel.iso Z.genRes (P.fl.step₂ m hm) ≪≫
    cokernel.mapIso _ _ (P.gen _) (P.gen _) (P.gen_step₂ m hm) ≪≫
      (PreservesCokernel.iso Z.genRes (P.fl'.step₂ m hm)).symm

@[reassoc]
theorem π_quotTwoIso_hom : Z.genRes.map (cokernel.π (P.fl.step₂ m hm)) ≫ (P.quotTwoIso m hm).hom =
    (P.gen ⟨m + 2, by omega⟩).hom ≫ Z.genRes.map (cokernel.π (P.fl'.step₂ m hm)) := by
  simp [quotTwoIso, Flag.quot₂]

theorem quotTwo_gen_ι₁ : (P.grIso ⟨m, by omega⟩).hom ≫ Z.genRes.map (P.fl'.quot₂Seq m hm).f =
    Z.genRes.map (P.fl.quot₂Seq m hm).f ≫ (P.quotTwoIso m hm).hom := by
  rw [← cancel_epi (Z.genRes.map (P.fl.π ⟨m, by omega⟩)), reassoc_of% (P.π_grIso_hom _),
    ← Functor.map_comp, ← Functor.map_comp_assoc, Flag.π_quot₂Seq_f, Flag.π_quot₂Seq_f,
    Functor.map_comp, Functor.map_comp_assoc, π_quotTwoIso_hom]
  have h₁ := P.gen_step ⟨m + 1, by omega⟩
  simp only [Fin.succ_mk, Fin.castSucc_mk] at h₁
  rw [reassoc_of% h₁]
  rfl

open ZeroObject in

def quotTwo : FlagPair (P.quotTwoIso m hm) 2 where
  fl := P.fl.quotTwo m hm
  fl' := P.fl'.quotTwo m hm
  gen := Fin.cons (Iso.refl _) (Fin.cons (P.grIso ⟨m, by omega⟩)
    (Fin.cons (P.quotTwoIso m hm) finZeroElim))
  gen_ι := Fin.cons ((Z.genRes.map_isZero (isZero_zero _)).eq_of_src _ _)
    (Fin.cons (P.quotTwo_gen_ι₁ m hm) (Fin.cons (by
      change (P.quotTwoIso m hm).hom ≫ Z.genRes.map (𝟙 _) = Z.genRes.map (𝟙 _) ≫ _
      simp) finZeroElim))

theorem cls_div_eq_of_comm {A A' C C' : Z.X.Modules} (ψ₁ : Z.GenIso A A') (ψ₂ : Z.GenIso C C')
    (e : A ≅ C) (e' : A' ≅ C') (h : ψ₁.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ ψ₂.hom)
    (hA : IsVB A 1) (hA' : IsVB A' 1) (hC : IsVB C 1) (hC' : IsVB C' 1) :
    (GenIso.div ψ₁ hA hA').cls = (GenIso.div ψ₂ hC hC').cls := by
  have hψ : ψ₁ = Z.genRes.mapIso e ≪≫ (ψ₂ ≪≫ Z.genRes.mapIso e'.symm) := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← reassoc_of% h, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [hψ, GenIso.cls_div_trans (hE' := hC), GenIso.cls_div_trans (hE' := hC'),
    FlagPairPull.cls_div_mapIso, FlagPairPull.cls_div_mapIso, zero_add, add_zero]

theorem cls_div_quotTwo_zero : ((P.quotTwo m hm).div 0).cls = (P.div ⟨m, by omega⟩).cls := by
  refine cls_div_eq_of_comm _ _ (P.fl.quotTwoGr₀ m hm) (P.fl'.quotTwoGr₀ m hm) ?_ _ _ _ _
  have h := (P.quotTwo m hm).π_grIso_hom 0
  change Z.genRes.map ((P.fl.quotTwo m hm).π 0) ≫ _ =
    (P.grIso ⟨m, by omega⟩).hom ≫ Z.genRes.map ((P.fl'.quotTwo m hm).π 0) at h
  rw [Flag.π_quotTwoGr₀, Flag.π_quotTwoGr₀] at h
  rw [← cancel_epi (Z.genRes.map (P.fl.quotTwoGr₀ m hm).inv), reassoc_of% h,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp]

theorem cls_div_quotTwo_one : ((P.quotTwo m hm).div 1).cls = (P.div ⟨m + 1, by omega⟩).cls := by
  refine cls_div_eq_of_comm _ _ (P.fl.quotTwoGr₁ m hm) (P.fl'.quotTwoGr₁ m hm) ?_ _ _ _ _
  have h := (P.quotTwo m hm).π_grIso_hom 1
  change Z.genRes.map ((P.fl.quotTwo m hm).π 1) ≫ _ =
    (P.quotTwoIso m hm).hom ≫ Z.genRes.map ((P.fl'.quotTwo m hm).π 1) at h
  have h₂ := P.π_grIso_hom ⟨m + 1, by omega⟩
  rw [← P.fl.π_π_quotTwoGr₁ m hm, ← P.fl'.π_π_quotTwoGr₁ m hm] at h₂
  simp only [Functor.map_comp, Category.assoc] at h₂
  rw [← cancel_epi (Z.genRes.map ((P.fl.quotTwo m hm).π 1)),
    ← cancel_epi (Z.genRes.map (cokernel.π (P.fl.step₂ m hm))), reassoc_of% h]
  exact (P.π_quotTwoIso_hom_assoc m hm _).trans h₂.symm

end QuotTwo

def transportAlongIso {W₁ W₁' W₂ W₂' : Z.X.Modules} {ψ₁ : Z.GenIso W₁ W₁'} {ψ₂ : Z.GenIso W₂ W₂'} {N : ℕ}
    (R : FlagPair ψ₂ N) (α : W₂ ≅ W₁) (α' : W₂' ≅ W₁')
    (h : ψ₂.hom ≫ Z.genRes.map α'.hom = Z.genRes.map α.hom ≫ ψ₁.hom) : FlagPair ψ₁ N where
  fl := R.fl.ofIso α
  fl' := R.fl'.ofIso α'
  gen := R.gen
  gen_ι i := by
    change (R.gen i).hom ≫ Z.genRes.map (R.fl'.ι i ≫ α'.hom) =
      Z.genRes.map (R.fl.ι i ≫ α.hom) ≫ ψ₁.hom
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% (R.gen_ι i), h, Category.assoc]

theorem gen_comm_of_ι (P P' : FlagPair φ r) (i : Fin (r + 1)) (e : P.fl.F i ⟶ P'.fl.F i)
    (he : e ≫ P'.fl.ι i = P.fl.ι i) (e' : P.fl'.F i ⟶ P'.fl'.F i)
    (he' : e' ≫ P'.fl'.ι i = P.fl'.ι i) :
    (P.gen i).hom ≫ Z.genRes.map e' = Z.genRes.map e ≫ (P'.gen i).hom := by
  rw [← cancel_mono (Z.genRes.map (P'.fl'.ι i)), Category.assoc, Category.assoc,
    ← Functor.map_comp, he', gen_ι, gen_ι, ← Functor.map_comp_assoc, he]

end GlobalTheory.Vert.Model.FlagPair

namespace GlobalTheory.Vert.Flag

theorem exists_quot₂_iso {X : Scheme.{0}} {E : X.Modules} {r : ℕ} (fl fl' : Flag E r) (m : ℕ)
    (hm : m + 2 ≤ r) (h₀ : fl.SameStep fl' ⟨m, by omega⟩)
    (e₂ : fl.F ⟨m + 2, by omega⟩ ≅ fl'.F ⟨m + 2, by omega⟩)
    (he₂ : e₂.hom ≫ fl'.ι _ = fl.ι _) :
    ∃ α : fl.quot₂ m hm ≅ fl'.quot₂ m hm,
      cokernel.π (fl.step₂ m hm) ≫ α.hom = e₂.hom ≫ cokernel.π (fl'.step₂ m hm) := by
  obtain ⟨e₀, he₀⟩ := h₀
  have w : fl.step₂ m hm ≫ e₂.hom = e₀.hom ≫ fl'.step₂ m hm := by
    rw [← cancel_mono (fl'.ι ⟨m + 2, by omega⟩), Category.assoc, Category.assoc, he₂, step₂_ι,
      step₂_ι, he₀]
  exact ⟨cokernel.mapIso (fl.step₂ m hm) (fl'.step₂ m hm) e₀ e₂ w, cokernel.π_desc _ _ _⟩

end GlobalTheory.Vert.Flag

section Main

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option linter.overlappingInstances false in

theorem GlobalTheory.Vert.Model.FlagPair.exists_rankTwo_subquotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (E E' : B.X.Modules) (φ : B.GenIso E E') (r m : ℕ) (hm : m + 2 ≤ r) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), P.fl.SameStep P'.fl ⟨m, by omega⟩ → P.fl.SameStep P'.fl ⟨m + 2, by omega⟩ → P.fl'.SameStep P'.fl' ⟨m, by omega⟩ → P.fl'.SameStep P'.fl' ⟨m + 2, by omega⟩ → ∃ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2), ((R.toFPair p).x 0 = (P.toFPair p).x ⟨m, by omega⟩ ∧ (R.toFPair p).x' 0 = (P.toFPair p).x' ⟨m, by omega⟩ ∧ (R.toFPair p).Dv 0 = (P.toFPair p).Dv ⟨m, by omega⟩ ∧ (R.toFPair p).x 1 = (P.toFPair p).x ⟨m + 1, by omega⟩ ∧ (R.toFPair p).x' 1 = (P.toFPair p).x' ⟨m + 1, by omega⟩ ∧ (R.toFPair p).Dv 1 = (P.toFPair p).Dv ⟨m + 1, by omega⟩) ∧ ((R'.toFPair p).x 0 = (P'.toFPair p).x ⟨m, by omega⟩ ∧ (R'.toFPair p).x' 0 = (P'.toFPair p).x' ⟨m, by omega⟩ ∧ (R'.toFPair p).Dv 0 = (P'.toFPair p).Dv ⟨m, by omega⟩ ∧ (R'.toFPair p).x 1 = (P'.toFPair p).x ⟨m + 1, by omega⟩ ∧ (R'.toFPair p).x' 1 = (P'.toFPair p).x' ⟨m + 1, by omega⟩ ∧ (R'.toFPair p).Dv 1 = (P'.toFPair p).Dv ⟨m + 1, by omega⟩) := by
  intro O _ _ _ p _ _ _ B E E' φ r m hm P P' h₀ h₂ h₀' h₂'
  have key (Q : GlobalTheory.Vert.Model.FlagPair φ r) :
      ((Q.quotTwo m hm).toFPair p).x 0 = (Q.toFPair p).x ⟨m, by omega⟩ ∧
      ((Q.quotTwo m hm).toFPair p).x' 0 = (Q.toFPair p).x' ⟨m, by omega⟩ ∧
      ((Q.quotTwo m hm).toFPair p).Dv 0 = (Q.toFPair p).Dv ⟨m, by omega⟩ ∧
      ((Q.quotTwo m hm).toFPair p).x 1 = (Q.toFPair p).x ⟨m + 1, by omega⟩ ∧
      ((Q.quotTwo m hm).toFPair p).x' 1 = (Q.toFPair p).x' ⟨m + 1, by omega⟩ ∧
      ((Q.quotTwo m hm).toFPair p).Dv 1 = (Q.toFPair p).Dv ⟨m + 1, by omega⟩ :=
    ⟨Flag.smallCls_root_eq_of_iso _ _ _ _ (Q.fl.quotTwoGr₀ m hm),
      Flag.smallCls_root_eq_of_iso _ _ _ _ (Q.fl'.quotTwoGr₀ m hm),
      congrArg GlobalTheory.Vert.Model.toQ (Q.cls_div_quotTwo_zero m hm),
      Flag.smallCls_root_eq_of_iso _ _ _ _ (Q.fl.quotTwoGr₁ m hm),
      Flag.smallCls_root_eq_of_iso _ _ _ _ (Q.fl'.quotTwoGr₁ m hm),
      congrArg GlobalTheory.Vert.Model.toQ (Q.cls_div_quotTwo_one m hm)⟩
  obtain ⟨e₂, he₂⟩ := h₂.symm
  obtain ⟨e₂', he₂'⟩ := h₂'.symm
  obtain ⟨α, hα⟩ := Flag.exists_quot₂_iso P'.fl P.fl m hm h₀.symm e₂ he₂
  obtain ⟨α', hα'⟩ := Flag.exists_quot₂_iso P'.fl' P.fl' m hm h₀'.symm e₂' he₂'
  have hc : (P'.quotTwoIso m hm).hom ≫ B.genRes.map α'.hom =
      B.genRes.map α.hom ≫ (P.quotTwoIso m hm).hom := by
    rw [← cancel_epi (B.genRes.map (cokernel.π (P'.fl.step₂ m hm))),
      Model.FlagPair.π_quotTwoIso_hom_assoc, ← Functor.map_comp, hα', ← Functor.map_comp_assoc,
      hα, Functor.map_comp, Functor.map_comp_assoc, Model.FlagPair.π_quotTwoIso_hom,
      reassoc_of% (Model.FlagPair.gen_comm_of_ι P' P _ _ he₂ _ he₂')]
  exact ⟨_, _, P.quotTwoIso m hm, P.quotTwo m hm, (P'.quotTwo m hm).transportAlongIso α α' hc,
    key P, key P'⟩

end Main
