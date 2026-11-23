import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.LiftsNonempty

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace FormNaturality

variable {K : Type} [Field K] {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)}
  {q : Y ⟶ Spec (CommRingCat.of K)}

def phi (u : Y ⟶ Z) (hu : u ≫ p = q) {V : Z.Opens} {V' : Y.Opens} (hV : V' ≤ u ⁻¹ᵁ V) :
    Sec p V →ₐ[K] Sec q V' :=
  { ((u.appLE V V' hV).hom : Γ(Z, V) →+* Γ(Y, V')) with
    commutes' := fun r => by
      have e : p.appLE ⊤ V le_top ≫ u.appLE V V' hV = q.appLE ⊤ V' le_top := by
        rw [Scheme.Hom.appLE_comp_appLE]
        subst hu
        rfl
      exact congrArg (fun f => ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f).hom r) e }

theorem ev_mor (u : Y ⟶ Z) (hu : u ≫ p = q) {V : Z.Opens} {V' : Y.Opens} (hV : V' ≤ u ⁻¹ᵁ V)
    (T : Thick (smFun Y q)) (hT : inU q V' T) (hT' : inU p V ((smS u hu).G.obj T)) (g : Γ(Z, V)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := p) (κ := Ideal.Quotient.mk ⊥) ((smS u hu).G.obj T) hT' g =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T hT ((u.appLE V V' hV).hom g) := by
  unfold ev GlobalTheory.Cris.evalAt
  have e : (pt (γ := dividedPowersBot K) (p := 0) (q := p) (κ := Ideal.Quotient.mk ⊥) ((smS u hu).G.obj T)).appLE V ⊤ hT' =
      u.appLE V V' hV ≫ (pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE V' ⊤ hT := by
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [e]
  rfl

def cl (q : Y ⟶ Spec (CommRingCat.of K)) (V : Y.Opens) : Lifts q V where
  v T g := OmegaRestriction.anyLift q T g
  hv T g := OmegaRestriction.anyLift_spec q T g

theorem cl_mor (u : Y ⟶ Z) (hu : u ≫ p = q) {V : Z.Opens} {V' : Y.Opens} (hV : V' ≤ u ⁻¹ᵁ V)
    (h : ∀ T, inU q V' T → inU p V ((smS u hu).G.obj T)) (T : (inU q V').FullSubcategory) (g : Sec p V) :
    (cl p V).v ⟨(smS u hu).G.obj T.obj, h _ T.property⟩ g = (cl q V').v T (phi u hu hV g) :=
  congrArg (fun x : T.obj.B ⧸ T.obj.J => (Ideal.Quotient.mk_surjective (I := T.obj.J) x).choose)
    (ev_mor u hu hV T.obj T.property (h _ T.property) g)

theorem form_mor (u : Y ⟶ Z) (hu : u ≫ p = q) {V : Z.Opens} {V' : Y.Opens} (hV : V' ≤ u ⁻¹ᵁ V)
    (h : ∀ T, inU q V' T → inU p V ((smS u hu).G.obj T)) {a : ℕ} (g₀ : Sec p V) (g : Fin a → Sec p V)
    (s : ComposableArrows (inU q V').FullSubcategory a) :
    (cl p V).form g₀ g (s ⋙ (morV u hu a h).G) =
      (cl q V').form (phi u hu hV g₀) (fun j => phi u hu hV (g j)) s := by
  have hv : ∀ (j : Fin (a + 1)) (x : Sec p V),
      (cl p V).v ((s ⋙ (morV u hu a h).G).obj j) x = (cl q V').v (s.obj j) (phi u hu hV x) :=
    fun j x => cl_mor u hu hV h (s.obj j) x
  simp only [Lifts.form, hv]
  rfl

theorem pull_rep (u : Y ⟶ Z) (hu : u ≫ p = q) {V : Z.Opens} {V' : Y.Opens} (hV : V' ≤ u ⁻¹ᵁ V)
    (h : ∀ T, inU q V' T → inU p V ((smS u hu).G.obj T)) {a : ℕ} (g₀ : Sec p V) (g : Fin a → Sec p V)
    (c : HV p V a a)
    (hc : Rep ((thFil (smFun Z p) (a : ℤ)).res (inU p V).ι) ((thFil (smFun Z p) ((a : ℤ) + 1)).res (inU p V).ι)
      ((cl p V).form g₀ g) c) :
    Rep ((thFil (smFun Y q) (a : ℤ)).res (inU q V').ι) ((thFil (smFun Y q) ((a : ℤ) + 1)).res (inU q V').ι)
      ((cl q V').form (phi u hu hV g₀) (fun j => phi u hu hV (g j))) ((morV u hu a h).pull a c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(morV u hu a h).pullC a f, ?_, rfl, fun s => ?_⟩
  · exact (CH.Mor.d_pullC _ a f).trans ((congrArg _ hf).trans (map_zero _))
  · have e1 := hfs (s ⋙ (morV u hu a h).G)
    rw [← form_mor u hu hV h g₀ g s]
    change Ideal.quotientMap _ (RingHom.id _) _ (f (s ⋙ (morV u hu a h).G)).1 = _
    rw [e1, Ideal.quotientMap_mk]
    rfl

theorem uniqV {V' : Y.Opens} {a : ℕ} (z : ∀ s : ComposableArrows (inU q V').FullSubcategory a, (s.obj (Fin.last a)).obj.B)
    (c c' : HV q V' a a)
    (hc : Rep ((thFil (smFun Y q) (a : ℤ)).res (inU q V').ι) ((thFil (smFun Y q) ((a : ℤ) + 1)).res (inU q V').ι) z c)
    (hc' : Rep ((thFil (smFun Y q) (a : ℤ)).res (inU q V').ι) ((thFil (smFun Y q) ((a : ℤ) + 1)).res (inU q V').ι) z c') :
    c = c' := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  obtain ⟨f', hf', rfl, hfs'⟩ := hc'
  have e : f = f' := funext fun s => Subtype.ext ((hfs s).trans (hfs' s).symm)
  subst e
  rfl

end FormNaturality

theorem omNatB_pf : OmNat := by
  intro K _ Z Y p q u hu V V' hV h
  refine ⟨FormNaturality.phi u hu hV, fun g => rfl, fun a e e' he he' ω => ?_⟩
  have hFL := GlobalTheory.T.onto_form_laws
  have key : ((morV u hu a h).pull a).comp e = e'.comp (omMap (FormNaturality.phi u hu hV) a) := by
    refine LinearMap.ext_on (hFL K (Sec p V) (Sec q V') a).1 ?_
    rintro _ ⟨g₀, g, rfl⟩
    change (morV u hu a h).pull a (e (form K g₀ g)) = e' (omMap (FormNaturality.phi u hu hV) a (form K g₀ g))
    rw [((hFL K (Sec p V) (Sec q V') a).2 (FormNaturality.phi u hu hV)).1]
    have h1 := FormNaturality.pull_rep u hu hV h g₀ g (e (form K g₀ g)) (he g₀ g (FormNaturality.cl p V))
    have h2 := he' (FormNaturality.phi u hu hV g₀) (fun j => FormNaturality.phi u hu hV (g j)) (FormNaturality.cl q V')
    exact FormNaturality.uniqV _ _ _ h1 h2
  exact LinearMap.congr_fun key ω

end CrystallineSemistableComparison.Onto

end
