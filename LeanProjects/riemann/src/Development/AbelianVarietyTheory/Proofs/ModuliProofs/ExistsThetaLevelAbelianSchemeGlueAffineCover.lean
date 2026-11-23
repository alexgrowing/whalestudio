import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ThetaAffineGlue

section Bundles

variable {X Y Z : Scheme.{0}}

theorem lbIso_pull {A : LB Y} {B : LB X} {φ : Y ⟶ X} (H : LBIso A (B.pull φ)) (χ : Z ⟶ Y) :
    LBIso (A.pull χ) (B.pull (χ ≫ φ)) :=
  H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A χ χ rfl) (chartPullSame B (fun _ => χ ≫ φ) (fun _ => φ) _ χ fun _ => rfl)

theorem lbIso_comp {C : LB Z} {A : LB Y} {B : LB X} (hC : C.IsLB) (hA : A.IsLB) (hB : B.IsLB) {φ : Y ⟶ X}
    {χ : Z ⟶ Y} (H' : LBIso C (A.pull χ)) (H : LBIso A (B.pull φ)) : LBIso C (B.pull (χ ≫ φ)) :=
  H'.trans hC (pull_isLB hA _) (pull_isLB hB _) (lbIso_pull H χ)

theorem lbIso_cancel {C : LB Z} {A : LB Y} {B : LB X} (hC : C.IsLB) (hA : A.IsLB) (hB : B.IsLB) {φ : Y ⟶ X}
    {χ : Z ⟶ Y} (H' : LBIso C (B.pull (χ ≫ φ))) (H : LBIso A (B.pull φ)) : LBIso C (A.pull χ) :=
  H'.trans hC (pull_isLB hB _) (pull_isLB hA _) (lbIso_pull H χ).symm

theorem lbIso_pull_id {A : LB X} (hA : A.IsLB) : LBIso A (A.pull (𝟙 X)) :=
  (GlobalTheory.PolBaseChange.lbIso_refl hA).chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A _ _ rfl)

theorem lbIso_of_local (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (rL : Out.Rigidified A L) (rM : Out.Rigidified A M)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ LBIso (L.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) :
    LBIso L M := by
  refine GlobalTheory.exists_gen_of_local_of_section A.left S A.hom (eSec A) (LB.div M L) (LB.isLB_div hM hL)
    (Over.w η[A]) (GlobalTheory.surjective_app_of_isAbelianScheme hG A hA) (fun s => ?_) ?_
  · obtain ⟨U, hU, w, hw⟩ := h s
    exact ⟨U, hU, gen_chartPull (GlobalTheory.IsoDescent.chartPullDiv M L _) w hw⟩
  · obtain ⟨a, ha⟩ := rL
    obtain ⟨c, hc⟩ := rM
    obtain ⟨w, hw⟩ := GlobalTheory.IsoDescent.lbIso_of_gens hL hM _ _ _ _ a ha c hc
    exact gen_chartPull (GlobalTheory.IsoDescent.chartPullDiv M L _) w hw

end Bundles

section Charts

theorem covers_of_isPullback {X Y : Scheme.{0}} {p : X ⟶ Y} {κ : Type} {X' Y' : κ → Scheme.{0}}
    {χ : ∀ i, X' i ⟶ X} {p' : ∀ i, X' i ⟶ Y' i} {a : ∀ i, Y' i ⟶ Y} (ha : ∀ y, ∃ i z, a i z = y)
    (h : ∀ i, IsPullback (χ i) (p' i) p (a i)) (x : X) : ∃ i z, χ i z = x := by
  obtain ⟨i, z, hz⟩ := ha (p x)
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (h i) x z hz.symm
  exact ⟨i, w, hw⟩

theorem hom_ext_of_charts {X Z : Scheme.{0}} {κ : Type} {X' : κ → Scheme.{0}} (χ : ∀ i, X' i ⟶ X)
    (ho : ∀ i, IsOpenImmersion (χ i)) (hc : ∀ x, ∃ i z, χ i z = x) {f g : X ⟶ Z}
    (h : ∀ i, χ i ≫ f = χ i ≫ g) : f = g :=
  Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers κ X' χ hc) f g h

theorem exists_hom_of_charts {X Z : Scheme.{0}} {κ : Type} {X' : κ → Scheme.{0}} (χ : ∀ i, X' i ⟶ X)
    (ho : ∀ i, IsOpenImmersion (χ i)) (hc : ∀ x, ∃ i z, χ i z = x) (φ : ∀ i, X' i ⟶ Z)
    (h : ∀ i j, pullback.fst (χ i) (χ j) ≫ φ i = pullback.snd (χ i) (χ j) ≫ φ j) :
    ∃ f : X ⟶ Z, ∀ i, χ i ≫ f = φ i :=
  ⟨Scheme.Cover.glueMorphisms (Scheme.Cover.mkOfCovers κ X' χ hc) φ h,
    Scheme.Cover.ι_glueMorphisms (Scheme.Cover.mkOfCovers κ X' χ hc) φ h⟩

theorem isGrpPullback_of_charts {T S : Scheme.{0}} {G : Over T} {H : Over S} [GrpObj G] [GrpObj H] {f : T ⟶ S}
    {φ : G.left ⟶ H.left} {κ : Type} {T' : κ → Scheme.{0}} {G' : ∀ i, Over (T' i)} [∀ i, GrpObj (G' i)]
    {a : ∀ i, T' i ⟶ T} (ho : ∀ i, IsOpenImmersion (a i)) (ha : ∀ y, ∃ i z, a i z = y)
    {χ : ∀ i, (G' i).left ⟶ G.left} (hχ : ∀ i, IsGrpPullback (G' i) G (a i) (χ i))
    (hφ : ∀ i, IsGrpPullback (G' i) H (a i ≫ f) (χ i ≫ φ)) : IsGrpPullback G H f φ := by
  refine ⟨IsPullback.flip ?_, fun P x y x₀ y₀ hx hy => ?_⟩
  · refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers κ T' a ha) fun i ↦ ?_
    change IsPullback (pullback.snd G.hom (a i)) (pullback.fst G.hom (a i) ≫ φ) (a i ≫ f) H.hom
    refine (hφ i).1.flip.of_iso (hχ i).1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp
  · refine hom_ext_of_charts (fun i => pullback.fst P.hom (a i)) (fun i => inferInstance)
      (covers_of_isPullback ha fun i => IsPullback.of_hasPullback P.hom (a i)) fun i => ?_
    let Q : Over (T' i) := Over.mk (pullback.snd P.hom (a i))
    have w : ∀ x : P ⟶ G, (pullback.fst P.hom (a i) ≫ x.left) ≫ G.hom = pullback.snd P.hom (a i) ≫ a i := fun x => by
      rw [Category.assoc, Over.w x, pullback.condition]
    let l : (P ⟶ G) → (Q ⟶ G' i) := fun x => Over.homMk ((hχ i).1.lift _ _ (w x)) ((hχ i).1.lift_snd _ _ _)
    have hl : ∀ x, (l x).left ≫ χ i = pullback.fst P.hom (a i) ≫ x.left := fun x => (hχ i).1.lift_fst _ _ _
    let c : Over.mk (Q.hom ≫ a i) ⟶ P := Over.homMk (pullback.fst P.hom (a i)) pullback.condition
    let d : Over.mk (Q.hom ≫ a i ≫ f) ⟶ Over.mk (P.hom ≫ f) :=
      Over.homMk (pullback.fst P.hom (a i)) (pullback.condition_assoc _)
    have hk : ∀ (x : P ⟶ G) (x₀ : Over.mk (P.hom ≫ f) ⟶ H), x₀.left = x.left ≫ φ →
        (d ≫ x₀).left = (l x).left ≫ χ i ≫ φ := fun x x₀ hx =>
      (congrArg (pullback.fst P.hom (a i) ≫ ·) hx).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φ) (hl x).symm).trans (Category.assoc _ _ _)))
    have e₁ := (hχ i).2 Q (l x) (l y) (c ≫ x) (c ≫ y) (hl x).symm (hl y).symm
    have e₂ := (hφ i).2 Q (l x) (l y) (d ≫ x₀) (d ≫ y₀)
      (hk x x₀ hx) (hk y y₀ hy)
    rw [← MonObj.comp_mul] at e₁ e₂
    exact (e₂.trans (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ φ) e₁.symm).trans (Category.assoc _ _ _))

end Charts

section Theta

variable {o : Type} [CommRing o] {J : Type} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
  {s'' : S'' ⟶ Sp o}

section

variable {g k : ℕ} {b : TBase o k}

def IsMap (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

variable {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''}

theorem pt_hom (t : TObj g k J b s) (i : Fin (2 * g)) : (t.pt i).left ≫ t.A.hom = 𝟙 S := Over.w (t.pt i)

theorem IsMap.id (t : TObj g k J b s) : IsMap t t (𝟙 S) (𝟙 _) :=
  haveI : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  ⟨isGrpPullback_of_iso (Iso.refl t.A), lbIso_pull_id t.isLB, fun _ => by simp, fun _ => by simp⟩

theorem IsMap.comp {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : t'.A.left ⟶ t.A.left} {χ : t''.A.left ⟶ t'.A.left}
    (h' : IsMap t'' t' f' χ) (h : IsMap t' t f φ) : IsMap t'' t (f' ≫ f) (χ ≫ φ) :=
  ⟨h'.1.comp h.1, lbIso_comp t''.isLB t'.isLB t.isLB h'.2.1 h.2.1,
    fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (h'.2.2.1 i))).trans
      ((Category.assoc _ _ _).trans ((congrArg (f' ≫ ·) (h.2.2.1 i)).trans (Category.assoc _ _ _).symm)),
    fun j => by rw [← Category.assoc, h'.2.2.2 j, Category.assoc, h.2.2.2 j, Category.assoc]⟩

theorem IsMap.cancel {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : t'.A.left ⟶ t.A.left} {ρ : t''.A.left ⟶ t.A.left}
    (h' : IsMap t'' t (f' ≫ f) ρ) (h : IsMap t' t f φ) : ∃ χ, χ ≫ φ = ρ ∧ IsMap t'' t' f' χ := by
  have hp := h.1.1
  obtain ⟨χ, e, w⟩ : ∃ χ : t''.A.left ⟶ t'.A.left, χ ≫ φ = ρ ∧ χ ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ρ (t''.A.hom ≫ f') (by rw [h'.1.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst e
  refine ⟨χ, rfl, h.1.cancel h'.1 w, lbIso_cancel t''.isLB t'.isLB t.isLB h'.2.1 h.2.1, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · exact ((Category.assoc _ _ _).trans (h'.2.2.1 i)).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (h.2.2.1 i).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, w, ← Category.assoc, pt_hom]
      exact (Category.id_comp _).trans (((Category.assoc _ _ _).trans
        (congrArg (f' ≫ ·) (pt_hom t' i))).trans (Category.comp_id _)).symm
  · apply hp.hom_ext
    · rw [Category.assoc, h'.2.2.2 j, Category.assoc, Category.assoc, h.2.2.2 j]
    · rw [Category.assoc, w, ← Category.assoc, Over.w, Category.assoc, Over.w, w]

theorem tMap_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) :=
  let ⟨_, h'⟩ := h'
  let ⟨_, h⟩ := h
  ⟨_, IsMap.comp h' h⟩

theorem tMap_cancel {f : S' ⟶ S} {f' : S'' ⟶ S'} (h' : TMap t'' t (f' ≫ f)) (h : TMap t' t f) : TMap t'' t' f' :=
  let ⟨_, h'⟩ := h'
  let ⟨_, h⟩ := h
  let ⟨χ, _, e⟩ := IsMap.cancel h' h
  ⟨χ, e⟩

end

theorem exists_affine (T : Scheme.{0}) (p : T) :
    ∃ (R : Type) (_ : CommRing R) (a : Sp R ⟶ T), IsOpenImmersion a ∧ p ∈ Set.range a := by
  obtain ⟨R, a, ha, hp, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := p) (U := ⊤) trivial
  exact ⟨R, inferInstance, a, ha, hp⟩

variable (h₁ : Out.Laws) (h₂ : Out.Laws2) {g N' m : ℕ} {b : TBase o (N' ^ 2)} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N')
  (hN : Odd N')
include h₁ h₂ hm hd hN

theorem unique_affine {R : Type} [CommRing R] [_root_.IsReduced R] {r : Sp R ⟶ Sp o} (u : TObj g (N' ^ 2) J b r)
    (t : TObj g (N' ^ 2) J b s) {f : Sp R ⟶ S} {φ φ' : u.A.left ⟶ t.A.left} (a : IsGrpPullback u.A t.A f φ)
    (a' : IsGrpPullback u.A t.A f φ') (c : LBIso u.L (t.L.pull φ)) (c' : LBIso u.L (t.L.pull φ'))
    (d : ∀ i, (u.pt i).left ≫ φ = (u.pt i).left ≫ φ') : φ = φ' := by
  obtain ⟨β, rfl⟩ : ∃ β : o →+* R, r = spMap β := ⟨(Spec.preimage r).hom, (Spec.map_preimage r).symm⟩
  obtain ⟨ψ, e, w⟩ : ∃ ψ : u.A.left ⟶ u.A.left, ψ ≫ φ = φ' ∧ ψ ≫ u.A.hom = u.A.hom :=
    ⟨a.1.lift φ' u.A.hom a'.1.w, a.1.lift_fst _ _ _, a.1.lift_snd _ _ _⟩
  subst e
  have H := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres h₁ h₂ o g N' J b m R β u u hm hd hN (fun p => subset_closure (by
    obtain ⟨v, hv⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) u rfl
    exact ⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, v,
      ((Sp R).range_fromSpecResidueField p).ge rfl, hv, hv⟩))).2 (𝟙 _) ψ (IsMap.id u).1
    (a.cancel (a'.congr (Category.id_comp _).symm rfl) (w.trans (Category.comp_id _).symm))
    (lbIso_pull_id u.isLB) (lbIso_cancel u.isLB u.isLB t.isLB c' c) (fun i => by
      apply a.1.hom_ext
      · rw [Category.comp_id, Category.assoc]; exact d i
      · rw [Category.comp_id, Category.assoc, w])
  rw [← H, Category.id_comp]

theorem unique [IsReduced S'] (u : TObj g (N' ^ 2) J b s')
    (t : TObj g (N' ^ 2) J b s) {f : S' ⟶ S} {φ φ' : u.A.left ⟶ t.A.left} (a : IsGrpPullback u.A t.A f φ)
    (a' : IsGrpPullback u.A t.A f φ') (c : LBIso u.L (t.L.pull φ)) (c' : LBIso u.L (t.L.pull φ'))
    (d : ∀ i, (u.pt i).left ≫ φ = (u.pt i).left ≫ φ') : φ = φ' := by
  choose R _ y hy hp using exists_affine S'
  choose v χ hχ using fun p => GlobalTheory.tObj_pull o g _ J b _ _ _ _ (y p) u rfl
  refine hom_ext_of_charts χ (fun p => MorphismProperty.of_isPullback (hχ p).1.1.flip (hy p))
    (covers_of_isPullback (fun p => ⟨p, hp p⟩) fun p => (hχ p).1.1) fun p => ?_
  have := hy p
  have : IsReduced (Sp (R p)) := isReduced_of_isOpenImmersion (y p)
  have : _root_.IsReduced (R p) := (affine_isReduced_iff (CommRingCat.of (R p))).1 this
  refine unique_affine h₁ h₂ hm hd hN (v p) t ((hχ p).1.comp a) ((hχ p).1.comp a')
    (lbIso_comp (v p).isLB u.isLB t.isLB (hχ p).2.1 c) (lbIso_comp (v p).isLB u.isLB t.isLB (hχ p).2.1 c') fun i => ?_
  rw [← Category.assoc, ← Category.assoc, (hχ p).2.2.1 i]
  exact (Category.assoc _ _ _).trans ((congrArg (y p ≫ ·) (d i)).trans (Category.assoc _ _ _).symm)

theorem tMap_of_local [IsReduced S'] (u : TObj g (N' ^ 2) J b s') (t : TObj g (N' ^ 2) J b s) (f : S' ⟶ S)
    (h : ∀ p : S', ∃ (V : Scheme.{0}) (a : V ⟶ S') (r : V ⟶ Sp o) (v : TObj g (N' ^ 2) J b r),
      IsOpenImmersion a ∧ p ∈ Set.range a ∧ TMap v u a ∧ TMap v t (a ≫ f)) : TMap u t f := by
  choose V a r v ha hp hu ht using h
  choose χ hχ using hu
  choose ψ hψ using ht
  have ho : ∀ p, IsOpenImmersion (χ p) := fun p => MorphismProperty.of_isPullback (hχ p).1.1.flip (ha p)
  have hc' : ∀ y, ∃ p z, a p z = y := fun p => ⟨p, hp p⟩
  have hc := covers_of_isPullback hc' fun p => (hχ p).1.1
  obtain ⟨φ, hφ⟩ := exists_hom_of_charts χ ho hc ψ fun p q => by
    obtain ⟨w, ρ, hρ⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ _ (pullback.fst (a p) (a q)) (v p) rfl
    have k := IsMap.comp hρ (hχ p)
    rw [pullback.condition] at k
    obtain ⟨ρ', e, hρ'⟩ := IsMap.cancel k (hχ q)
    have k₁ := IsMap.comp hρ (hψ p)
    have k₂ := IsMap.comp hρ' (hψ q)
    rw [← pullback.condition_assoc] at k₂
    have : IsReduced (pullback (a p) (a q)) := isReduced_of_isOpenImmersion (pullback.fst (a p) (a q) ≫ a p)
    have E := unique h₁ h₂ hm hd hN w t k₁.1 k₂.1 k₁.2.1 k₂.2.1 fun i => (k₁.2.2.1 i).trans (k₂.2.2.1 i).symm
    let l : pullback (χ p) (χ q) ⟶ w.A.left := hρ.1.1.lift (pullback.fst _ _)
      (pullback.lift (pullback.fst _ _ ≫ (v p).A.hom) (pullback.snd _ _ ≫ (v q).A.hom) (by
        rw [Category.assoc, Category.assoc, ← (hχ p).1.1.w, ← (hχ q).1.1.w, pullback.condition_assoc]))
      (pullback.lift_fst _ _ _).symm
    have l₁ : l ≫ ρ = pullback.fst _ _ := hρ.1.1.lift_fst _ _ _
    have l₂ : l ≫ ρ' = pullback.snd _ _ := by
      rw [← cancel_mono (χ q), Category.assoc, e, ← Category.assoc, l₁, pullback.condition]
    rw [← l₁, ← l₂, Category.assoc, Category.assoc, E]
  have gp : IsGrpPullback u.A t.A f φ :=
    isGrpPullback_of_charts ha hc' (fun p => (hχ p).1) fun p => (hψ p).1.congr rfl (hφ p).symm
  refine ⟨φ, gp, ?_, fun i => ?_, fun j => ?_⟩
  · refine lbIso_of_local h₁.globalFns u.A u.ab u.isLB (pull_isLB t.isLB _) u.rigid
      (GlobalTheory.PolBaseChange.rigidified_pull gp t.rigid) fun p => ⟨(a p).opensRange, hp p, ?_⟩
    have hr : Set.range ((u.A.hom ⁻¹ᵁ (a p).opensRange).ι ≫ u.A.hom) ⊆ Set.range (a p) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    obtain ⟨j, hj⟩ : ∃ j, j ≫ χ p = (u.A.hom ⁻¹ᵁ (a p).opensRange).ι :=
      ⟨(hχ p).1.1.lift _ _ (IsOpenImmersion.lift_fac (a p) _ hr).symm, (hχ p).1.1.lift_fst _ _ _⟩
    have c : LBIso (v p).L ((t.L.pull φ).pull (χ p)) := lbIso_cancel (v p).isLB (pull_isLB t.isLB _) t.isLB
      (by rw [hφ]; exact (hψ p).2.1) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB t.isLB _))
    rw [← hj]
    exact (lbIso_pull (hχ p).2.1 j).symm.trans (pull_isLB u.isLB _) (pull_isLB (v p).isLB _)
      (pull_isLB (pull_isLB t.isLB _) _) (lbIso_pull c j)
  · refine hom_ext_of_charts a ha hc' fun p => ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) ((hχ p).2.2.1 i).symm)).trans ?_
    refine ((Category.assoc _ _ _).trans (congrArg (((v p).pt i).left ≫ ·) (hφ p))).trans ?_
    exact ((hψ p).2.2.1 i).trans (Category.assoc _ _ _)
  · refine hom_ext_of_charts χ ho hc fun p => ?_
    rw [← Category.assoc, ← (hχ p).2.2.2 j, Category.assoc, hφ, (hψ p).2.2.2 j, ← Category.assoc, hφ]

end Theta

theorem exists_glue : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (m : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (I : Type) (R : I → Type) [∀ i, CommRing (R i)] (x : ∀ i, Sp (R i) ⟶ S) (t : ∀ i, TObj g (N' ^ 2) J b (x i ≫ s)), 2 ≤ m → m ^ 2 ∣ N' → Odd N' → (∀ i, IsOpenImmersion (x i)) → (∀ p : S, ∃ i, p ∈ Set.range (x i)) → (∀ i i' (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R i)) (a' : Sp T ⟶ Sp (R i')) (u : TObj g (N' ^ 2) J b (a ≫ x i ≫ s)), IsOpenImmersion a → a ≫ x i = a' ≫ x i' → TMap u (t i) a → TMap u (t i') a') → ∃ t₀ : TObj g (N' ^ 2) J b s, ∀ i, TMap (t i) t₀ (x i) := by
  intro h₁ h₂ o _ g N' J b m S _ s I R _ x t hm hd hN hx hc H
  let U : I → S.Opens := fun i => (x i).opensRange
  let e : ∀ i, Sp (R i) ≅ (U i).toScheme := fun i => (x i).isoOpensRange
  have e₁ : ∀ i, (e i).hom ≫ (U i).ι = x i := fun i => (x i).isoOpensRange_hom_ι
  have e₂ : ∀ i, (e i).inv ≫ x i = (U i).ι := fun i => (x i).isoOpensRange_inv_comp
  choose t' ht' using fun i => GlobalTheory.tObj_pull o g _ J b _ _ _ ((U i).ι ≫ s) (e i).inv (t i)
    (by rw [← Category.assoc, e₂])
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_glue_openCover o g _ J b S s I U t'
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 (hc p))
    (fun i j => by
      obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ ((U i ⊓ U j).ι ≫ s) (S.homOfLE inf_le_left) (t' i)
        (by rw [← Category.assoc, Scheme.homOfLE_ι])
      refine ⟨u, hu, tMap_of_local h₁ h₂ hm hd hN u (t' j) _ fun p => ?_⟩
      obtain ⟨T, _, a, ha, hp⟩ := exists_affine _ p
      obtain ⟨v, hv⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _
        (((a ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) ≫ (e i).inv) ≫ x i ≫ s) a u
        (by simp only [Category.assoc, reassoc_of% e₂, Scheme.homOfLE_ι_assoc])
      refine ⟨_, a, _, v, ha, hp, hv, tMap_cancel (H i j T _ _ v inferInstance ?_
        (tMap_comp (tMap_comp hv hu) (ht' i))) (ht' j)⟩
      simp only [Category.assoc, e₂, Scheme.homOfLE_ι])
    (fun T i f u φ φ' hf a a' c c' d => by
      have : IsReduced T := isReduced_of_isOpenImmersion (f ≫ (U i).ι)
      exact unique h₁ h₂ hm hd hN u (t' i) a a' c c' d)
  refine ⟨t₀, fun i => ?_⟩
  have k : TMap (t i) (t' i) (e i).hom := tMap_cancel (by rw [Iso.hom_inv_id]; exact ⟨_, IsMap.id _⟩) (ht' i)
  have := tMap_comp k (ht₀ i)
  rwa [e₁] at this

end GlobalTheory.ThetaAffineGlue
