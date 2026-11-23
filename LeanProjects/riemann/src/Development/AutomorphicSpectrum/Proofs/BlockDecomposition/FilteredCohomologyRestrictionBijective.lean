import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace GlobalTheory.CompanionTheory.PDTrunc

section Gen
universe w w' v u v' u'
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem pull_bij_of_adj {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w} R} (m : CH.Mor F F' (RingHom.id R))
    (L : C ⥤ C') (a : L ⊣ m.G)
    (hb : ∀ T, Function.Bijective fun x => m.τ (L.obj T) ((F.map (a.unit.app T)).hom x)) (n : ℕ) :
    Function.Bijective (m.pull n) := by
  let τ : ∀ T, F.obj T →ₗ[R] (L ⋙ F').obj T := fun T => (m.τ (L.obj T)).comp (F.map (a.unit.app T)).hom
  let α : F ⟶ L ⋙ F' :=
    { app := fun T => ModuleCat.ofHom (τ T)
      naturality := fun T T' f => by
        ext x
        change m.τ (L.obj T') ((F.map (a.unit.app T')).hom ((F.map f).hom x)) =
          (F'.map (L.map f)).hom (m.τ (L.obj T) ((F.map (a.unit.app T)).hom x))
        rw [← m.nat]
        have e := a.unit.naturality f
        simp only [Functor.id_map, Functor.comp_map] at e
        have e1 : (F.map (a.unit.app T')).hom ((F.map f).hom x) = (F.map (f ≫ a.unit.app T')).hom x := by
          rw [F.map_comp]; rfl
        have e2 : (F.map (m.G.map (L.map f))).hom ((F.map (a.unit.app T)).hom x) =
            (F.map (a.unit.app T ≫ m.G.map (L.map f))).hom x := by
          rw [F.map_comp]; rfl
        rw [e1, e2, e]
        rfl }
  have hR := CrystallineSemistableComparison.P.adj F' L m.G a n
  have hα : Function.Bijective ((CH.Mor.ofNatTrans α).pull n) := by
    have h1 := CrystallineSemistableComparison.P.coef_upTo α 1
      (fun T => (CrystallineSemistableComparison.P.upTo_alg (α.app T).hom LinearMap.id 1 1).2.2.2.2.2 (hb T)) n
    rw [one_pow] at h1
    exact (CrystallineSemistableComparison.P.upTo_alg _ LinearMap.id 1 1).2.2.2.2.1 h1
  have key : ∀ x, (CH.Mor.restrict F' L).pull n (m.pull n x) = (CH.Mor.ofNatTrans α).pull n x := by
    intro x
    have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m (CH.Mor.restrict F' L) n x).1
    have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.ofNatTrans α) (m.comp (σ'' := RingHom.id R) (CH.Mor.restrict F' L)) a.unit
      (fun T x => rfl) n x
    rw [h2, h1]
  have hc : (CH.Mor.restrict F' L).pull n ∘ m.pull n = (CH.Mor.ofNatTrans α).pull n := funext key
  have := hR
  exact (Function.Bijective.of_comp_iff' hR _).1 (hc ▸ hα)

theorem H_subsingleton {F : C ⥤ ModuleCat.{w} R} (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) : Subsingleton (CH.H F n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : Subsingleton (CH.Cn F n) := ⟨fun f g => funext fun s => (h _).elim _ _⟩
  exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))

end Gen

section Quot

theorem dp_lift {B C : Type} [CommRing B] [CommRing C] {J : Ideal B} (δ : DividedPowers J) {𝔟 : Ideal B}
    (hinf : δ.IsSubDPIdeal (𝔟 ⊓ J)) {J'' : Ideal C} (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C)
    (hg : IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟))) : IsDPMorphism (Quotient.dividedPowers δ hinf) δ'' g := by
  refine ⟨?_, fun {n} y hy => ?_⟩
  · rw [Ideal.map_map]; exact hg.1
  · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    rw [Quotient.dpow_apply δ hinf ha]
    exact hg.2 a ha

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem sub_inf (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) : T.δ.IsSubDPIdeal (T.pdPow s ⊓ T.J) := by
  have h : T.δ.IsSubDPIdeal (T.pdPow s) := FubiniStudyChowHeightFormula₂.Adr.Fil.fil_isSubDPIdeal T.δ s hs
  rw [inf_eq_left.mpr h.isSubideal]
  exact h

abbrev redMap (T : Thick (nlFun γ 0 X q κ)) (s : ℕ) :
    T.B ⧸ T.J →+* (T.B ⧸ T.pdPow s) ⧸ T.J.map (Ideal.Quotient.mk (T.pdPow s)) :=
  Ideal.quotientMap _ (Ideal.Quotient.mk (T.pdPow s)) Ideal.le_comap_map

def qT (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) : Thick (nlFun γ 0 X q κ) :=
  mkT (T.B ⧸ T.pdPow s) ((Ideal.Quotient.mk (T.pdPow s)).comp T.i) (T.J.map (Ideal.Quotient.mk (T.pdPow s)))
    (Quotient.dividedPowers T.δ (sub_inf T hs))
    ⟨fun h => absurd rfl h, fun _ => by
      obtain ⟨n, hn⟩ := T.adm.2 rfl
      exact ⟨n, by
        change (T.J.map (Ideal.Quotient.mk (T.pdPow s))) ^ n = ⊥
        rw [← Ideal.map_pow]
        have hn' : T.J ^ n = ⊥ := hn
        rw [hn', Ideal.map_bot]⟩⟩
    (IsDPMorphism.comp _ (Quotient.isDPMorphism T.δ (sub_inf T hs)) T.compat)
    ((nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom (redMap T s)) T.y)
    (fun r => congrArg (redMap T s) (T.w r))

def unitH (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) : T ⟶ qT T hs :=
  mkH (T' := qT T hs) (Ideal.Quotient.mk (T.pdPow s)) (fun _ => rfl) (Quotient.isDPMorphism T.δ (sub_inf T hs))
    Ideal.le_comap_map rfl

theorem map_le {T T' : Thick (nlFun γ 0 X q κ)} (f : T ⟶ T') (s : ℕ) : T.pdPow s ≤ (T'.pdPow s).comap f.φ :=
  fun _ hx => dividedPowerFiltration_map f.dp s hx

abbrev qRing {T T' : Thick (nlFun γ 0 X q κ)} (f : T ⟶ T') (s : ℕ) : T.B ⧸ T.pdPow s →+* T'.B ⧸ T'.pdPow s :=
  Ideal.quotientMap _ f.φ (map_le f s)

theorem q_le {T T' : Thick (nlFun γ 0 X q κ)} (f : T ⟶ T') {s : ℕ} (hs : 1 ≤ s) :
    (qT T hs).J ≤ (qT T' hs).J.comap (qRing f s) := by
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (T'.pdPow s)) (f.hle hx)

theorem pt_map_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) (c : A →+* C)
    (h : b.comp a = c) (y : (nlFun γ 0 X q κ).Pt.obj (CommRingCat.of A)) :
    (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom b) ((nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom a) y) =
      (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom c) y := by
  subst h
  rw [CommRingCat.ofHom_comp, (nlFun γ 0 X q κ).Pt.map_comp]
  rfl

theorem qRing_dp {T T' : Thick (nlFun γ 0 X q κ)} (f : T ⟶ T') {s : ℕ} (hs : 1 ≤ s) :
    IsDPMorphism (qT T hs).δ (qT T' hs).δ (qRing f s) := by
  refine dp_lift T.δ (sub_inf T hs) _ _ ?_
  have e : (qRing f s).comp (Ideal.Quotient.mk (T.pdPow s)) = (Ideal.Quotient.mk (T'.pdPow s)).comp f.φ := by
    ext; rfl
  rw [e]
  exact IsDPMorphism.comp _ (Quotient.isDPMorphism T'.δ (sub_inf T' hs)) f.dp

def qMap {T T' : Thick (nlFun γ 0 X q κ)} (f : T ⟶ T') {s : ℕ} (hs : 1 ≤ s) : qT T hs ⟶ qT T' hs :=
  mkH (qRing f s) (fun r => congrArg (Ideal.Quotient.mk _) (f.comm r)) (qRing_dp f hs) (q_le f hs) (by
    have e1 : (qT T' hs).y = (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom (redMap T' s)) T'.y := rfl
    have e0 : (qT T hs).y = (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom (redMap T s)) T.y := rfl
    rw [e1, e0, ← f.pt]
    refine (pt_map_map _ _ _ rfl _).trans (Eq.trans ?_ (pt_map_map _ _ _ rfl _).symm)
    refine congrArg (fun u => (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom u) T.y) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl))

abbrev cRing (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (h0 : T.pdPow s = ⊥) : T.B ⧸ T.pdPow s →+* T.B :=
  Ideal.Quotient.lift _ (RingHom.id _) fun a ha => by rw [h0] at ha; exact (Ideal.mem_bot.1 ha)

theorem c_le (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) (h0 : T.pdPow s = ⊥) :
    (qT T hs).J ≤ T.J.comap (cRing T h0) := by
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  exact hx

def counitH (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) (h0 : T.pdPow s = ⊥) : qT T hs ⟶ T :=
  mkH (cRing T h0) (fun _ => rfl) (dp_lift T.δ (sub_inf T hs) _ _ (by
      have e : (cRing T h0).comp (Ideal.Quotient.mk (T.pdPow s)) = RingHom.id _ := by ext; rfl
      rw [e]
      exact (DPMorphism.id T.δ).isDPMorphism))
    (c_le T hs h0) (by
    have e0 : (qT T hs).y = (nlFun γ 0 X q κ).Pt.map (CommRingCat.ofHom (redMap T s)) T.y := rfl
    rw [e0]
    refine (pt_map_map _ _ (RingHom.id _) ?_ _).trans ?_
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)
    · rw [CommRingCat.ofHom_id, (nlFun γ 0 X q κ).Pt.map_id]
      rfl)

theorem pdPow_q (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) (r : ℕ) :
    (qT T hs).pdPow r = (T.pdPow r).map (Ideal.Quotient.mk (T.pdPow s)) :=
  le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil T.B T.J T.δ _ _ (qT T hs).δ _
      (Quotient.isDPMorphism T.δ (sub_inf T hs)) rfl r)
    (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le T.δ (qT T hs).δ _ (Quotient.isDPMorphism T.δ (sub_inf T hs)) r)

theorem q_bot (T : Thick (nlFun γ 0 X q κ)) {s : ℕ} (hs : 1 ≤ s) : (qT T hs).pdPow s = ⊥ := by
  rw [pdPow_q, Ideal.map_quotient_self]

theorem inU_q {V : X.Opens} {T : Thick (nlFun γ 0 X q κ)} (h : InU V T) {s : ℕ} (hs : 1 ≤ s) : InU V (qT T hs) := by
  intro x _
  have e : pt (qT T hs) = Spec.map (CommRingCat.ofHom (redMap T s)) ≫ pt T := rfl
  change (pt (qT T hs)) x ∈ V
  rw [e]
  exact h (show (Spec.map (CommRingCat.ofHom (redMap T s))) x ∈ (⊤ : (Spec _).Opens) from trivial)

end Quot

section Fun

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Q Q' : ObjectProperty (Thick (nlFun γ 0 X q κ))}

def trunc {s : ℕ} (hs : 1 ≤ s) (hq : ∀ T, Q T → Q' (qT T hs)) : Q.FullSubcategory ⥤ Q'.FullSubcategory where
  obj T := ⟨qT T.obj hs, hq _ T.property⟩
  map f := ObjectProperty.homMk (qMap f.hom hs)
  map_id T := ObjectProperty.hom_ext _ (hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)))
  map_comp f g := ObjectProperty.hom_ext _ (hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)))

def truncAdj {s : ℕ} (hs : 1 ≤ s) (hq : ∀ T, Q T → Q' (qT T hs)) (h : Q' ≤ Q) (h0 : ∀ T, Q' T → T.pdPow s = ⊥) :
    trunc hs hq ⊣ ObjectProperty.ιOfLE h where
  unit :=
    { app := fun T => ObjectProperty.homMk (unitH T.obj hs)
      naturality := fun T T' f => ObjectProperty.hom_ext _ (hom_ext (RingHom.ext fun x => rfl)) }
  counit :=
    { app := fun T => ObjectProperty.homMk (counitH T.obj hs (h0 _ T.property))
      naturality := fun T T' f => ObjectProperty.hom_ext _ (hom_ext
        (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl))) }
  left_triangle_components T := ObjectProperty.hom_ext _ (hom_ext
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl)))
  right_triangle_components T := ObjectProperty.hom_ext _ (hom_ext (RingHom.ext fun x => rfl))

theorem mem_of_mk (T : Thick (nlFun γ 0 X q κ)) {s t : ℕ} (hs : 1 ≤ s) (ht : t ≤ s) {y : T.B}
    (hy : Ideal.Quotient.mk (T.pdPow s) y ∈ (qT T hs).pdPow t) : y ∈ T.pdPow t := by
  rw [pdPow_q] at hy
  obtain ⟨z, hz, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  have h1 : z - y ∈ T.pdPow s := Ideal.Quotient.eq.1 e
  have h2 := (T.pdPow t).sub_mem hz (T.pdPow_anti ht h1)
  simpa using h2

theorem q_tf (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hs : 1 ≤ s)
    (h : l = 1 ∨ ∀ (r : ℕ) (x : T.B), (l : T.B) * x ∈ T.pdPow r → x ∈ T.pdPow r) (r : ℕ) (x : (qT T hs).B)
    (hx : (l : (qT T hs).B) * x ∈ (qT T hs).pdPow r) : x ∈ (qT T hs).pdPow r := by
  rcases h with rfl | h
  · simpa using hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : Ideal.Quotient.mk (T.pdPow s) ((l : T.B) * y) ∈ (qT T hs).pdPow (min r s) := by
    refine (qT T hs).pdPow_anti (min_le_left r s) ?_
    rw [map_mul, map_natCast]
    exact hx
  have h2 := h _ _ (mem_of_mk T hs (min_le_right r s) h1)
  rw [pdPow_q]
  rcases le_total r s with hrs | hrs
  · rw [min_eq_left hrs] at h2
    exact Ideal.mem_map_of_mem _ h2
  · rw [min_eq_right hrs] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h2]
    exact Ideal.zero_mem _

theorem unit_bij {s : ℕ} (hs : 1 ≤ s) (hq : ∀ T, Q T → Q' (qT T hs)) (h : Q' ≤ Q) (h0 : ∀ T, Q' T → T.pdPow s = ⊥)
    (r r' : ℤ) (hr : r' ≤ s) (T : Q.FullSubcategory) :
    Function.Bijective fun x => ((incl h).sq (incl_fil h r) (incl_fil h r')).τ ((trunc hs hq).obj T)
      (((sq (sFil Q r) (sFil Q r')).map ((truncAdj hs hq h h0).unit.app T)).hom x) := by
  have ht : r'.toNat ≤ s := Int.toNat_le.2 hr
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ e
    obtain ⟨y₁, hy₁, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h₁
    obtain ⟨y₂, hy₂, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h₂
    have e' := congrArg Subtype.val e
    have e'' : Ideal.Quotient.mk (T.obj.pdPow s) y₁ - Ideal.Quotient.mk (T.obj.pdPow s) y₂ ∈
        (qT T.obj hs).pdPow r'.toNat := Ideal.Quotient.eq.1 e'
    rw [← map_sub] at e''
    exact Subtype.ext (Ideal.Quotient.eq.2 (mem_of_mk T.obj hs ht e''))
  · rintro ⟨u, hu⟩
    obtain ⟨v, hv, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hu
    have hv' : v ∈ (qT T.obj hs).pdPow r.toNat := hv
    rw [pdPow_q] at hv'
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hv'
    exact ⟨⟨Ideal.Quotient.mk _ y, Ideal.mem_map_of_mem _ hy⟩, rfl⟩

theorem sq_sub (Q : ObjectProperty (Thick (nlFun γ 0 X q κ))) (r r' : ℤ) (hr : r' ≤ 0) (T : Q.FullSubcategory) :
    Subsingleton ((sq (sFil Q r) (sFil Q r')).obj T) := by
  have e : (sFil Q r').S T = ⊤ := by
    have : r'.toNat = 0 := Int.toNat_of_nonpos hr
    change T.obj.pdPow r'.toNat = ⊤
    rw [this, Thick.pdPow_zero]
  have : Subsingleton ((sP Q).A.obj T ⧸ (sFil Q r').S T) := Ideal.Quotient.subsingleton_iff.2 e
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim (α := (sP Q).A.obj T ⧸ (sFil Q r').S T) a.1 b.1)⟩

end Fun

theorem pull_incl_bijective : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ 0 X q κ))) (l s : ℕ)
    (hQ : (Q₀ = ⊤ ∧ l = 1) ∨ ∃ s', s ≤ s' ∧ Q₀ = TF l s') (𝒱 : Set X.Opens) (h : St (TF l s) 𝒱 ≤ St Q₀ 𝒱) (r r' : ℤ) (hr : r' ≤ s) (j : ℕ),
    Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j) := by
  intro O R _ _ I γ X q κ Q₀ l s hQ 𝒱 h r r' hr j
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hr0 : r' ≤ 0 := by exact_mod_cast hr
    have h1 := H_subsingleton (sq_sub (St Q₀ 𝒱) r r' hr0) j
    have h2 := H_subsingleton (sq_sub (St (γ := γ) (p := 0) (q := q) (κ := κ) (TF l 0) 𝒱) r r' hr0) j
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · have hq : ∀ T, St Q₀ 𝒱 T → St (TF l s) 𝒱 (qT T hs) := by
      rintro T ⟨hT, V, hV, hU⟩
      refine ⟨⟨q_bot T hs, q_tf T hs ?_⟩, V, hV, inU_q hU hs⟩
      rcases hQ with ⟨-, rfl⟩ | ⟨s', -, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr hT.2
    have h0 : ∀ T : Thick (nlFun γ 0 X q κ), St (TF l s) 𝒱 T → T.pdPow s = ⊥ := fun T hT => hT.1.1
    exact pull_bij_of_adj ((incl h).sq (incl_fil h r) (incl_fil h r')) (trunc hs hq) (truncAdj hs hq h h0)
      (unit_bij hs hq h h0 r r' hr) j

end GlobalTheory.CompanionTheory.PDTrunc
