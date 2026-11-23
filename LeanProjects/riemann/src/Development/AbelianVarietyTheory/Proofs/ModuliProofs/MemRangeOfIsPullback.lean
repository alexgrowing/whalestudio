import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppOfPullbackSnd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackLocalOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.UnivProp

set_option backward.isDefEq.respectTransparency false

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_geomPt (X : Scheme.{0}) (p : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (y : Sp K ⟶ X), p ∈ Set.range y := by
  refine ⟨AlgebraicClosure (X.residueField p), inferInstance, inferInstance,
    spMap (algebraMap (X.residueField p) _) ≫ X.fromSpecResidueField p, ⟨(default : PrimeSpectrum _), ?_⟩⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply p _

theorem exists_lift_field {X V : Scheme.{0}} (x : V ⟶ X) [IsOpenImmersion x] {K : Type} [Field K] (y : Sp K ⟶ X)
    {p : X} (hy : p ∈ Set.range y) (hx : p ∈ Set.range x) : ∃ z : Sp K ⟶ V, z ≫ x = y := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ⟨IsOpenImmersion.lift x y ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨a', rfl⟩ := hy
  rwa [Subsingleton.elim a a']

theorem hom_ext_affine {X Y : Scheme.{0}} (f g : X ⟶ Y)
    (h : ∀ p : X, ∃ (V : Scheme.{0}) (x : V ⟶ X), IsOpenImmersion x ∧ p ∈ Set.range x ∧ x ≫ f = x ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun p => ?_
  obtain ⟨V, x, hx, hp, e⟩ := h p
  refine ⟨x.opensRange, hp, ?_⟩
  rw [← x.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_glue {X Y : Scheme.{0}} {I : Type} (V : I → Scheme.{0}) (x : ∀ i, V i ⟶ X) (hx : ∀ i, IsOpenImmersion (x i))
    (hc : ∀ p : X, ∃ i, p ∈ Set.range (x i)) (f : ∀ i, V i ⟶ Y)
    (h : ∀ i j (T : Type) [CommRing T] (z : Sp T ⟶ V i) (z' : Sp T ⟶ V j), z ≫ x i = z' ≫ x j → z ≫ f i = z' ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, x i ≫ F = f i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers I V x hc hx
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 f fun i j => ?_, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 f _ i⟩
  refine hom_ext_affine _ _ fun p => ?_
  obtain ⟨W, hW, hp, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
  refine ⟨_, hW.fromSpec, inferInstance, by rw [hW.range_fromSpec]; exact hp, ?_⟩
  have := h i j Γ(pullback (x i) (x j), W) (hW.fromSpec ≫ pullback.fst (x i) (x j)) (hW.fromSpec ≫ pullback.snd (x i) (x j))
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  rw [Category.assoc, Category.assoc] at this
  exact this

theorem exists_glue' {X Y : Scheme.{0}} {I : Type} (V : I → Scheme.{0}) (x : ∀ i, V i ⟶ X) (hx : ∀ i, IsOpenImmersion (x i))
    (hc : ∀ p : X, ∃ i, p ∈ Set.range (x i)) (f : ∀ i, V i ⟶ Y)
    (h : ∀ i j (p : X), p ∈ Set.range (x i) → p ∈ Set.range (x j) → ∃ (k : I) (c : V k ⟶ V i) (c' : V k ⟶ V j),
      p ∈ Set.range (x k) ∧ c ≫ x i = x k ∧ c' ≫ x j = x k ∧ c ≫ f i = c' ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, x i ≫ F = f i := by
  refine exists_glue V x hx hc f fun i j T _ z z' e => hom_ext_affine _ _ fun p => ?_
  obtain ⟨k, c, c', hp, e₁, e₂, e₃⟩ := h i j ((z ≫ x i) p) ⟨z p, by simp⟩ (by rw [e]; exact ⟨z' p, by simp⟩)
  have := hx i
  have := hx j
  have := hx k
  refine ⟨_, pullback.fst (z ≫ x i) (x k), inferInstance, by rw [Scheme.Pullback.range_fst]; exact hp, ?_⟩
  have a₁ : pullback.fst (z ≫ x i) (x k) ≫ z = pullback.snd (z ≫ x i) (x k) ≫ c := by
    rw [← cancel_mono (x i), Category.assoc, Category.assoc, e₁, pullback.condition]
  have a₂ : pullback.fst (z ≫ x i) (x k) ≫ z' = pullback.snd (z ≫ x i) (x k) ≫ c' := by
    rw [← cancel_mono (x j), Category.assoc, Category.assoc, e₂, ← e, pullback.condition]
  rw [← Category.assoc, ← Category.assoc, a₁, a₂, Category.assoc, Category.assoc, e₃]

variable {o : Type} [CommRing o] {g : ℕ} {J : Type}

def TBy {k : ℕ} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s')
    (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem TBy.comp {k : ℕ} {b : TBase o k} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ} {φ'}
    (h' : TBy t'' t' f' φ') (h : TBy t' t f φ) : TBy t'' t (f' ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.comp h.1, LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) h'.2.1
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 φ' rfl), fun i => ?_, fun j => ?_⟩
  · rw [← Category.assoc, h'.2.2.1, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, h'.2.2.2, Category.assoc, h.2.2.2, Category.assoc]

variable {N' : ℕ} {b : TBase o (N' ^ 2)} {m : ℕ}

theorem TBy.unique (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {R : Type} [CommRing R] [_root_.IsReduced R] {β : o →+* R} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {t : TObj g (N' ^ 2) J b s} {u : TObj g (N' ^ 2) J b (spMap β)} {x : Sp R ⟶ S} {φ φ'}
    (h : TBy u t x φ) (h' : TBy u t x φ') : φ = φ' := by
  obtain ⟨e, he, e₁⟩ := grpPullback_iso h'.1 h.1
  have : IsMonHom (Iso.refl u.A).hom := inferInstanceAs (IsMonHom (𝟙 u.A))
  have hd := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β u u hm hd ho (fun p => subset_closure (by
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt _ p
    obtain ⟨w, hw⟩ := GlobalTheory.tObj_pull o g _ J b _ _ (spMap β) _ y u rfl
    exact ⟨K, inferInstance, y, w, hy, hw, hw⟩))).2 e.hom.left (Iso.refl u.A).hom.left
    (isGrpPullback_of_iso e) (isGrpPullback_of_iso (Iso.refl u.A))
    (LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB u.isLB _) h'.2.1
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 _ e₁.symm).symm)
    (LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB u.isLB _) h.2.1
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 _ (by simp)).symm) (fun i => by
      apply h.1.1.hom_ext
      · rw [Category.assoc, e₁, h'.2.2.1]
        simpa using (h.2.2.1 i).symm
      · simp)
  rw [← e₁, hd]
  simp

theorem exists_common (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t t' : TObj g (N' ^ 2) J b s}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g (N' ^ 2) J b (y ≫ s)), TMap u t y → TMap u t' y)
    {R : Type} [CommRing R] [_root_.IsReduced R] (x : Sp R ⟶ S) (β : o →+* R) (hβ : x ≫ s = spMap β) :
    ∃ (u : TObj g (N' ^ 2) J b (spMap β)) (a : _) (φ : _), TBy u t x a ∧ TBy u t' x φ := by
  obtain ⟨u, a, ha⟩ := GlobalTheory.tObj_pull o g _ J b _ _ s _ x t hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ s _ x t' hβ
  have h' : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (sy : Sp K ⟶ Sp o) (u : TObj g (N' ^ 2) J b sy),
      y ≫ s = sy → TMap u t y → TMap u t' y := by
    intro K _ _ y sy u e
    subst e
    exact h K y u
  have h₁ : TMap u u' (𝟙 _) := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β u u' hm hd ho (fun p => subset_closure (by
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt _ p
    obtain ⟨w, hw⟩ := GlobalTheory.tObj_pull o g _ J b _ _ (spMap β) _ y u rfl
    refine ⟨K, inferInstance, y, w, hy, hw, ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t' u' w).2 x y hu').2 ?_⟩
    exact h' K _ _ w (by rw [Category.assoc, hβ])
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t u w).2 x y ⟨a, ha⟩).1 hw)))).1
  have h₂ := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t' u' u).2 x _ hu').1 h₁
  rw [Category.id_comp] at h₂
  obtain ⟨φ, hφ⟩ := h₂
  exact ⟨u, a, φ, ha, hφ⟩

theorem mem_range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {x : Y ⟶ Z}
    (h : IsPullback a q f x) (p : X) : p ∈ Set.range a ↔ f p ∈ Set.range x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨q z, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h p y hy.symm
    exact ⟨z, hz⟩

theorem tMap_id_of_geomPt (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp o} {t t' : TObj g (N' ^ 2) J b s}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g (N' ^ 2) J b (y ≫ s)), TMap u t y → TMap u t' y) :
    TMap t t' (𝟙 S) := by
  let x : ∀ V : S.affineOpens, Sp Γ(S, V) ⟶ S := fun V => V.2.fromSpec
  have hx : ∀ V, IsOpenImmersion (x V) := fun V => inferInstanceAs (IsOpenImmersion V.2.fromSpec)
  have rx : ∀ V, Set.range (x V) = V.1 := fun V => V.2.range_fromSpec
  choose β hβ using fun V => exists_spMap (x V ≫ s)
  choose u a φ ha hφ using fun V => exists_common hL hL2 hm hd ho h (x V) (β V) (hβ V)
  have cov : ∀ p : S, ∃ V, p ∈ Set.range (x V) := fun p => by
    obtain ⟨W, hW, hp, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    exact ⟨⟨W, hW⟩, by rw [rx]; exact hp⟩
  have res : ∀ V W : S.affineOpens, W.1 ≤ V.1 → ∃ c : (u W).A.left ⟶ (u V).A.left, c ≫ a V = a W ∧ c ≫ φ V = φ W := by
    intro V W hle
    have := hx V
    have e := IsOpenImmersion.lift_fac (x V) (x W) (by rw [rx, rx]; exact hle)
    obtain ⟨c, hc⟩ := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t (u V) (u W)).2 (x V) _ ⟨_, ha V⟩).2
      (by rw [e]; exact ⟨_, ha W⟩)
    have h₁ := TBy.comp hc (ha V)
    have h₂ := TBy.comp hc (hφ V)
    rw [e] at h₁ h₂
    exact ⟨c, h₁.unique hL hL2 hm hd ho (ha W), h₂.unique hL hL2 hm hd ho (hφ W)⟩
  have ref : ∀ (V V' : S.affineOpens) (p : S), p ∈ Set.range (x V) → p ∈ Set.range (x V') →
      ∃ (W : S.affineOpens) (c : (u W).A.left ⟶ (u V).A.left) (c' : (u W).A.left ⟶ (u V').A.left),
        p ∈ Set.range (x W) ∧ c ≫ a V = a W ∧ c ≫ φ V = φ W ∧ c' ≫ a V' = a W ∧ c' ≫ φ V' = φ W := by
    intro V V' p hp hp'
    rw [rx] at hp hp'
    obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := V.1 ⊓ V'.1) (x := p) ⟨hp, hp'⟩
    obtain ⟨c, e₁, e₂⟩ := res V ⟨W, hW⟩ fun z hz => (hle hz).1
    obtain ⟨c', e₁', e₂'⟩ := res V' ⟨W, hW⟩ fun z hz => (hle hz).2
    exact ⟨⟨W, hW⟩, c, c', by rw [rx]; exact hpW, e₁, e₂, e₁', e₂'⟩
  have oa : ∀ V, IsOpenImmersion (a V) := fun V => MorphismProperty.of_isPullback (ha V).1.1.flip (hx V)
  have oφ : ∀ V, IsOpenImmersion (φ V) := fun V => MorphismProperty.of_isPullback (hφ V).1.1.flip (hx V)
  have ca : ∀ p : t.A.left, ∃ V, p ∈ Set.range (a V) := fun p => by
    obtain ⟨V, hV⟩ := cov (t.A.hom p)
    exact ⟨V, (mem_range_of_isPullback (ha V).1.1 p).2 hV⟩
  have cφ : ∀ p : t'.A.left, ∃ V, p ∈ Set.range (φ V) := fun p => by
    obtain ⟨V, hV⟩ := cov (t'.A.hom p)
    exact ⟨V, (mem_range_of_isPullback (hφ V).1.1 p).2 hV⟩
  obtain ⟨Φ, hΦ⟩ := exists_glue' _ a oa ca φ fun V V' p hp hp' => by
    obtain ⟨W, c, c', hW, e₁, e₂, e₃, e₄⟩ := ref V V' _ ((mem_range_of_isPullback (ha V).1.1 p).1 hp)
      ((mem_range_of_isPullback (ha V').1.1 p).1 hp')
    exact ⟨W, c, c', (mem_range_of_isPullback (ha W).1.1 p).2 hW, e₁, e₃, e₂.trans e₄.symm⟩
  obtain ⟨Ψ, hΨ⟩ := exists_glue' _ φ oφ cφ a fun V V' p hp hp' => by
    obtain ⟨W, c, c', hW, e₁, e₂, e₃, e₄⟩ := ref V V' _ ((mem_range_of_isPullback (hφ V).1.1 p).1 hp)
      ((mem_range_of_isPullback (hφ V').1.1 p).1 hp')
    exact ⟨W, c, c', (mem_range_of_isPullback (hφ W).1.1 p).2 hW, e₂, e₄, e₁.trans e₃.symm⟩
  have exta : ∀ {Y : Scheme.{0}} (f f' : t.A.left ⟶ Y), (∀ V, a V ≫ f = a V ≫ f') → f = f' := fun f f' e =>
    hom_ext_affine f f' fun p => by
      obtain ⟨V, hV⟩ := ca p
      exact ⟨_, a V, oa V, hV, e V⟩
  have iso : IsIso Φ := ⟨Ψ, exta _ _ fun V => by rw [← Category.assoc, hΦ, hΨ, Category.comp_id],
    hom_ext_affine _ _ fun p => by
      obtain ⟨V, hV⟩ := cφ p
      exact ⟨_, φ V, oφ V, hV, by rw [← Category.assoc, hΨ, hΦ, Category.comp_id]⟩⟩
  have grp : IsGrpPullback t.A t'.A (𝟙 S) Φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S t.A t'.A Φ iso
    (exta _ _ fun V => by rw [← Category.assoc, hΦ, (hφ V).1.1.w, (ha V).1.1.w]) fun p => by
      obtain ⟨V, hV⟩ := cov p
      exact ⟨_, x V, (u V).A, inferInstance, a V, hx V, hV, (ha V).1, by rw [hΦ]; exact (hφ V).1⟩
  refine ⟨Φ, grp, GlobalTheory.RigidLocal.lbIso_of_local hL.globalFns S t.A t'.A t.L t'.L Φ t.ab t.isLB t'.isLB t.rigid t'.rigid grp fun p => ?_,
    fun i => hom_ext_affine _ _ fun p => ?_, fun j => exta _ _ fun V => ?_⟩
  · obtain ⟨V, hV⟩ := cov p
    refine ⟨_, _, x V, (u V).A.hom, a V, hx V, hV, (ha V).1.1, ?_⟩
    rw [hΦ]
    exact LBIso.trans (pull_isLB t.isLB _) (u V).isLB (pull_isLB t'.isLB _) (ha V).2.1.symm (hφ V).2.1
  · obtain ⟨V, hV⟩ := cov p
    refine ⟨_, x V, hx V, hV, ?_⟩
    rw [← Category.assoc, ← (ha V).2.2.1, Category.assoc, hΦ, (hφ V).2.2.1, Category.id_comp]
  · rw [← Category.assoc, ← (ha V).2.2.2, Category.assoc, hΦ, (hφ V).2.2.2, ← Category.assoc, hΦ]

end GlobalTheory.ZM.UnivProp
