import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldOfFieldPointsSamePoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

section TorPart

variable {T T' : Scheme.{0}} {G₀ : Over T} [GrpObj G₀] {G₁ : Over T'} [GrpObj G₁] {X X' : Type} [AddCommGroup X]
  [AddCommGroup X']

def IsTorPart (tι : splitTorus T X ⟶ G₀) : Prop :=
  IsMonHom tι ∧ ∃ (B : Over T) (_ : GrpObj B) (q : G₀ ⟶ B), IsProper B.hom ∧ IsMonHom q ∧ IsPullback tι (toUnit _) q η[B]

theorem isTorPart_id : IsTorPart (𝟙 (splitTorus T X)) :=
  ⟨inferInstance, 𝟙_ _, inferInstance, toUnit _, inferInstanceAs (IsProper (𝟙 T)), inferInstance,
    haveI : IsIso η[𝟙_ (Over T)] := by rw [show η[𝟙_ (Over T)] = 𝟙 _ from toUnit_unique _ _]; infer_instance
    IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩⟩

theorem IsTorPart.mono {tι : splitTorus T X ⟶ G₀} (h : IsTorPart tι) : Mono tι := by
  obtain ⟨-, B, _, q, -, -, hk⟩ := h
  exact ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩

theorem IsTorPart.pull {f : T' ⟶ T} {φ : G₁.left ⟶ G₀.left} (hφ : IsGrpPullback G₁ G₀ f φ) {tι : splitTorus T X ⟶ G₀}
    (h : IsTorPart tι) : IsTorPart (pullTorus hφ tι) := by
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus hφ tι q hk
  exact ⟨inferInstance, _, inferInstance, q', inferInstanceAs (IsProper (pullback.snd _ _)), hq', hk'⟩

theorem IsTorPart.equiv {tι : splitTorus T X ⟶ G₀} (h : IsTorPart tι) (e : X ≃+ X') :
    IsTorPart (torusMap T e.toAddMonoidHom ≫ tι) := by
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  have : IsIso (torusMap T e.toAddMonoidHom) := ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩
  refine ⟨inferInstance, B, inferInstance, q, hB, hq, ?_⟩
  have h1 : IsPullback (torusMap T e.toAddMonoidHom) (toUnit _) (toUnit _) (𝟙 (𝟙_ (Over T))) :=
    IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  simpa using h1.paste_horiz hk

theorem isTorPart_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup; IsTorPart E.i :=
  ⟨E.i_hom, E.B, E.grpB, E.q, E.isAbelian.proper, E.q_hom, E.isKernel⟩

theorem isTorPart_gtTorus {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type} [CommRing A] {ρ : R →+* A}
    {D : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {H : Over (Sp A)} [GrpObj H]
    {φ : H.left ⟶ G.left} (g : GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback H G (spMap ρ) φ) : IsTorPart (gtTorus g hρ h) :=
  IsTorPart.pull (isGrpPullback_thickLift hρ h) ⟨g.i_hom, _, inferInstance, g.q, by
    have := D.P.isAb.proper
    exact inferInstanceAs (IsProper (pullback.snd _ _)), g.q_hom, g.isKernel⟩

theorem IsTorPart.factor {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {H : Over (Sp A)} [GrpObj H]
    {tι : splitTorus (Sp A) X ⟶ H} (h : IsTorPart tι) [Module.Free ℤ X'] [Module.Finite ℤ X']
    (i : splitTorus (Sp A) X' ⟶ H) (hi : IsMonHom i) : ∃ r : X →+ X', i = torusMap _ r ≫ tι := by
  have hm := h.mono
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have ht : i ≫ q = toUnit _ ≫ η[_] := splitTorus_hom_proper_trivial_local A X' _ (i ≫ q) inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ tι = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono tι, MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc, Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem IsTorPart.cancel {A : Type} [CommRing A] [Nontrivial A] {H : Over (Sp A)} [GrpObj H]
    {tι : splitTorus (Sp A) X ⟶ H} (h : IsTorPart tι) {r r' : X →+ X'} (e : torusMap _ r ≫ tι = torusMap _ r' ≫ tι) :
    r = r' := by
  have := h.mono
  exact GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono tι).1 e)

theorem IsTorPart.exists_equiv {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {H : Over (Sp A)} [GrpObj H]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ X'] [Module.Finite ℤ X'] {tι : splitTorus (Sp A) X ⟶ H}
    {tι' : splitTorus (Sp A) X' ⟶ H} (h : IsTorPart tι) (h' : IsTorPart tι') :
    ∃ e : X ≃+ X', tι' = torusMap _ e.toAddMonoidHom ≫ tι := by
  obtain ⟨r, hr⟩ := h.factor tι' h'.1
  obtain ⟨s, hs⟩ := h'.factor tι h.1
  have e₁ : s.comp r = AddMonoidHom.id X := h.cancel (by
    rw [GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, ← hr, ← hs, GlobalTheory.SplitTorus.torusMap_id, Category.id_comp])
  have e₂ : r.comp s = AddMonoidHom.id X' := h'.cancel (by
    rw [GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, ← hs, ← hr, GlobalTheory.SplitTorus.torusMap_id, Category.id_comp])
  exact ⟨⟨⟨r, s, fun x => DFunLike.congr_fun e₁ x, fun x => DFunLike.congr_fun e₂ x⟩, map_add r⟩, hr⟩

end TorPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z}

def IsExt (gγ : Over.mk M.pt ⟶ G) (W : M.Z.Opens) (h : W.toScheme ⟶ G.left) : Prop :=
  h ≫ G.hom = W.ι ∧ ∀ x : Sp Ω ⟶ W.toScheme, x ≫ W.ι = M.pt → x ≫ h = gγ.left

def ExtNear (gγ : Over.mk M.pt ⟶ G) (w : M.Z) : Prop := ∃ W h, w ∈ W ∧ IsExt gγ W h

def ValAt (gγ : Over.mk M.pt ⟶ G) {T : Scheme.{0}} (s : T ⟶ M.Z) (v : T ⟶ G.left) : Prop :=
  ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ G.left) (s' : T ⟶ W.toScheme), IsExt gγ W h ∧ s' ≫ W.ι = s ∧ s' ≫ h = v

theorem extNear_of_section (σ : M.Z ⟶ G.left) (hσ : σ ≫ G.hom = 𝟙 _) (w : M.Z) :
    ExtNear (Over.homMk (M.pt ≫ σ) (by simp [hσ]) : Over.mk M.pt ⟶ G) w :=
  ⟨⊤, (⊤ : M.Z.Opens).ι ≫ σ, trivial, by rw [Category.assoc, hσ, Category.comp_id],
    fun x hx => by rw [← Category.assoc, hx]; rfl⟩

theorem ValAt.over {gγ : Over.mk M.pt ⟶ G} {T : Scheme.{0}} {s : T ⟶ M.Z} {v : T ⟶ G.left} (h : ValAt gγ s v) :
    v ≫ G.hom = s := by
  obtain ⟨W, h, s', ⟨h1, -⟩, rfl, rfl⟩ := h
  rw [Category.assoc, h1]

theorem ValAt.comp {gγ : Over.mk M.pt ⟶ G} {T T' : Scheme.{0}} {s : T ⟶ M.Z} {v : T ⟶ G.left} (h : ValAt gγ s v)
    (g : T' ⟶ T) : ValAt gγ (g ≫ s) (g ≫ v) := by
  obtain ⟨W, h, s', h1, rfl, rfl⟩ := h
  exact ⟨W, h, g ≫ s', h1, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem ExtNear.exists_valAt {gγ : Over.mk M.pt ⟶ G} {A : Type} [CommRing A] [IsLocalRing A] (s : Sp A ⟶ M.Z)
    (h : ExtNear gγ (s (closedPoint A))) : ∃ v, ValAt gγ s v := by
  obtain ⟨W, h, hw, he⟩ := h
  have hr : Set.range s ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open W.isOpen hw
  exact ⟨_, W, h, IsOpenImmersion.lift W.ι s hr, he, IsOpenImmersion.lift_fac _ _ _, rfl⟩

theorem ValAt.unique [IsSeparated G.hom] {gγ : Over.mk M.pt ⟶ G} {T : Scheme.{0}} {s : T ⟶ M.Z} {v v' : T ⟶ G.left}
    (h : ValAt gγ s v) (h' : ValAt gγ s v') : v = v' := by
  obtain ⟨W, h, t, ⟨h1, h2⟩, ht, rfl⟩ := h
  obtain ⟨W', h', t', ⟨h1', h2'⟩, ht', rfl⟩ := h'
  by_cases hT : IsEmpty T
  · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
  obtain ⟨x₀⟩ := not_isEmpty_iff.1 hT
  have hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨s x₀, by rw [← ht]; exact (t x₀).2, by rw [← ht']; exact (t' x₀).2⟩
  have : Nonempty (W ⊓ W' : M.Z.Opens).toScheme := ⟨⟨_, hne.some_mem⟩⟩
  have : IsIntegral (W ⊓ W' : M.Z.Opens).toScheme := isIntegral_of_isOpenImmersion (W ⊓ W').ι
  have hr : Set.range M.pt ⊆ Set.range (W ⊓ W').ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x := IsOpenImmersion.lift (W ⊓ W').ι M.pt hr
  have hx : x ≫ (W ⊓ W').ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (x ≫ (W ⊓ W').ι) := hx ▸ M.isDominant_pt
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion x (W ⊓ W').ι
  have key : M.Z.homOfLE (inf_le_left : W ⊓ W' ≤ W) ≫ h = M.Z.homOfLE (inf_le_right : W ⊓ W' ≤ W') ≫ h' := by
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x ?_
    · rw [Category.assoc, Category.assoc, h1, h1', Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    · rw [← Category.assoc, ← Category.assoc, h2 _ (by rw [Category.assoc, Scheme.homOfLE_ι, hx]),
        h2' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hx])]
  have hs : Set.range s ⊆ Set.range (W ⊓ W').ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨by rw [← ht]; exact (t w).2, by rw [← ht']; exact (t' w).2⟩
  let u := IsOpenImmersion.lift (W ⊓ W').ι s hs
  have hu : u ≫ (W ⊓ W').ι = s := IsOpenImmersion.lift_fac _ _ _
  have e : t = u ≫ M.Z.homOfLE inf_le_left := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hu, ht]
  have e' : t' = u ≫ M.Z.homOfLE inf_le_right := by
    rw [← cancel_mono W'.ι, Category.assoc, Scheme.homOfLE_ι, hu, ht']
  rw [e, e', Category.assoc, Category.assoc, key]

variable {I T : Type} (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ)

def Compat {X : Type} [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) {A : Type} [CommRing A] (s : Sp A ⟶ M.Z)
    (a : o →+* A) {G₀ : Over (Sp A)} (φ : G₀.left ⟶ G.left) (tι : splitTorus (Sp A) X ⟶ G₀) : Prop :=
  (∀ e, tι.left ≫ φ ≫ (f e).left = (torusMap (Sp A) (m e) ≫ tι).left ≫ φ) ∧
  ∀ t, ∃ z : Over.mk (𝟙 (Sp A)) ⟶ splitTorus (Sp A) X,
    (∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val)) ∧ ValAt (gγ t) s ((z ≫ tι).left ≫ φ)

variable [GrpObj G]

def LatAt {X : Type} [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w : M.Z) : Prop :=
  ∃ (κ : Type) (_ : Field κ) (s : Sp κ ⟶ M.Z) (a : o →+* κ) (G₀ : Over (Sp κ)) (_ : GrpObj G₀) (φ : G₀.left ⟶ G.left)
    (tι : splitTorus (Sp κ) X ⟶ G₀), s (closedPoint κ) = w ∧ s ≫ M.s = spMap a ∧ IsGrpPullback G₀ G s φ ∧ IsTorPart tι ∧
    Compat f gγ ζ L m c s a φ tι

variable (G) in

def RkAt (w : M.Z) (r : ℕ) : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (κ : Type) (_ : Field κ)
    (s : Sp κ ⟶ M.Z) (G₀ : Over (Sp κ)) (_ : GrpObj G₀) (φ : G₀.left ⟶ G.left) (tι : splitTorus (Sp κ) X ⟶ G₀),
    s (closedPoint κ) = w ∧ IsGrpPullback G₀ G s φ ∧ IsTorPart tι ∧ Module.finrank ℤ X = r

variable {f gγ ζ L}

theorem LatAt.rkAt {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : I → X →+ X}
    {c : T → X →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w) : RkAt G w (Module.finrank ℤ X) := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, h1, -, h2, h3, -⟩ := h
  exact ⟨X, _, inferInstance, inferInstance, κ, _, s, G₀, _, φ, tι, h1, h2, h3, rfl⟩

example (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : M.Z) :
    RkAt (splitTorus M.Z X) w (Module.finrank ℤ X) :=
  ⟨X, _, inferInstance, inferInstance, M.Z.residueField w, inferInstance, M.Z.fromSpecResidueField w, _, inferInstance, _, 𝟙 _,
    Scheme.fromSpecResidueField_apply _ _, GlobalTheory.SplitTorus.isGrpPullback_bcMap _ X, isTorPart_id, rfl⟩

omit [GrpObj G] in

theorem Compat.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {A : Type} [CommRing A] {s : Sp A ⟶ M.Z} {a : o →+* A}
    {G₀ : Over (Sp A)} {φ : G₀.left ⟶ G.left} {tι : splitTorus (Sp A) X ⟶ G₀} (h : Compat f gγ ζ L m c s a φ tι)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) :
    Compat f gγ ζ L m' c' s a φ (torusMap _ e.toAddMonoidHom ≫ tι) := by
  refine ⟨fun i => ?_, fun t => ?_⟩
  · rw [Over.comp_left, Category.assoc, h.1 i, ← Category.assoc, ← Over.comp_left, ← Category.assoc, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
    congr 4
    ext x
    exact hm i x
  · obtain ⟨z, hz, hv⟩ := h.2 t
    refine ⟨z ≫ torusMap _ e.symm.toAddMonoidHom, fun χ => ?_, ?_⟩
    · obtain ⟨χ, rfl⟩ := e.surjective χ
      rw [hc, ← hz]
      ext
      rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
        ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]
      simp
    · rw [Category.assoc, ← Category.assoc (torusMap _ _), ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
      exact hv

omit [GrpObj G] in

theorem Compat.pull {X : Type} [AddCommGroup X] {m : I → X →+ X} {c : T → X →+ ZMod L} {A B : Type} [CommRing A]
    [CommRing B] {s : Sp A ⟶ M.Z} {a : o →+* A} {G₀ : Over (Sp A)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {tι : splitTorus (Sp A) X ⟶ G₀} (h : Compat f gγ ζ L m c s a φ tι) (b : A →+* B) {G₁ : Over (Sp B)} [GrpObj G₁]
    {ψ : G₁.left ⟶ G₀.left} (hψ : IsGrpPullback G₁ G₀ (spMap b) ψ) :
    Compat f gγ ζ L m c (spMap b ≫ s) (b.comp a) (ψ ≫ φ) (pullTorus hψ tι) := by
  refine ⟨fun i => ?_, fun t => ?_⟩
  · rw [← pullTorus_torusMap_comp, ← Category.assoc, ← Category.assoc, ← Category.assoc, pullTorus_left, pullTorus_left]
    simp only [Category.assoc]
    rw [h.1 i]
  · obtain ⟨z, hz, hv⟩ := h.2 t
    have hw : (spMap b ≫ z.left) ≫ (splitTorus (Sp A) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp B)) ⟶ splitTorus (Sp B) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left := (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    refine ⟨z', fun χ => ?_, ?_⟩
    · ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Aˣ) : A))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    · have := hv.comp (spMap b)
      convert this using 1
      rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc (pullTorus hψ tι).left, pullTorus_left,
        Category.assoc, ← Category.assoc, hz']
      simp only [Category.assoc]

end GlobalTheory.Poinc.FibLat
