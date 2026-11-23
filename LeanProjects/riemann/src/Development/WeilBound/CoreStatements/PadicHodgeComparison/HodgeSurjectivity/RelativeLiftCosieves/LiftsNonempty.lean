import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLawsStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace OmegaRestriction

variable {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K))

def phi {V V' : Z.Opens} (h : V' ≤ V) : Sec q V →ₐ[K] Sec q V' :=
  { (rs h : Γ(Z, V) →+* Γ(Z, V')) with
    commutes' := fun r => by
      have e : q.appLE ⊤ V le_top ≫ Z.presheaf.map (homOfLE h).op = q.appLE ⊤ V' le_top :=
        Scheme.Hom.appLE_map _ _ _
      exact congrArg (fun f => ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f).hom r) e }

theorem ev_res {V V' : Z.Opens} (h : V' ≤ V) (T : Thick (smFun Z q)) (hT : inU q V' T) (hT' : inU q V T)
    (g : Γ(Z, V)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T hT (rs h g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T hT' g := by
  unfold ev GlobalTheory.Cris.evalAt rs
  have e : (pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE V ⊤ hT' =
      Z.presheaf.map (homOfLE h).op ≫
        (pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE V' ⊤ hT := by
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rfl

def anyLift {V : Z.Opens} (T : (inU q V).FullSubcategory) (g : Sec q V) : T.obj.B :=
  (Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose

theorem anyLift_spec {V : Z.Opens} (T : (inU q V).FullSubcategory) (g : Sec q V) :
    Ideal.Quotient.mk T.obj.J (anyLift q T g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g :=
  (Ideal.Quotient.mk_surjective _).choose_spec

theorem lifts_nonempty (V : Z.Opens) : Nonempty (Lifts q V) :=
  ⟨{ v := fun T g => anyLift q T g
     hv := fun T g => anyLift_spec q T g }⟩

open Classical in

def ext {V V' : Z.Opens} (h : V' ≤ V) (Λ' : Lifts q V') : Lifts q V where
  v T g := if hT : inU q V' T.obj then Λ'.v ⟨T.obj, hT⟩ (rs h g) else anyLift q T g
  hv T g := by
    by_cases hT : inU q V' T.obj
    · rw [dif_pos hT]
      exact (Λ'.hv ⟨T.obj, hT⟩ (rs h g)).trans (ev_res q h T.obj hT T.property g)
    · rw [dif_neg hT]
      exact anyLift_spec q T g

theorem ext_v {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (Λ' : Lifts q V')
    (T : (inU q V').FullSubcategory) (g : Sec q V) :
    (ext q h Λ').v ((ObjectProperty.ιOfLE k).obj T) g = Λ'.v T (rs h g) :=
  dif_pos T.property

theorem ext_form {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (Λ' : Lifts q V') {a : ℕ}
    (g₀ : Sec q V) (g : Fin a → Sec q V) (s : ComposableArrows (inU q V').FullSubcategory a) :
    (ext q h Λ').form g₀ g (s ⋙ ObjectProperty.ιOfLE k) = Λ'.form (rs h g₀) (fun j => rs h (g j)) s := by
  have hv : ∀ (j : Fin (a + 1)) (x : Sec q V),
      (ext q h Λ').v ((s ⋙ ObjectProperty.ιOfLE k).obj j) x = Λ'.v (s.obj j) (rs h x) :=
    fun j x => ext_v q h k Λ' (s.obj j) x
  simp only [Lifts.form, hv]
  rfl

theorem form_uniq {V : Z.Opens} {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V} {c c' : HV q V a a}
    (hc : IsForm q V g₀ g c) (hc' : IsForm q V g₀ g c') : c = c' := by
  obtain ⟨Λ⟩ := lifts_nonempty q V
  obtain ⟨f, hf, rfl, hfs⟩ := hc Λ
  obtain ⟨f', hf', rfl, hfs'⟩ := hc' Λ
  have e : f = f' := funext fun s => Subtype.ext ((hfs s).trans (hfs' s).symm)
  subst e
  rfl

theorem isForm_res {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) {a : ℕ} (g₀ : Sec q V)
    (g : Fin a → Sec q V) (c : HV q V a a) (hc : IsForm q V g₀ g c) :
    IsForm q V' (phi q h g₀) (fun j => phi q h (g j)) ((resU (G q a) k).pull a c) := by
  intro Λ'
  obtain ⟨f, hf, rfl, hfs⟩ := hc (ext q h Λ')
  refine ⟨(resU (G q a) k).pullC a f, ?_, rfl, fun s => ?_⟩
  · exact (CH.Mor.d_pullC _ a f).trans ((congrArg _ hf).trans (map_zero _))
  · exact (hfs (s ⋙ ObjectProperty.ιOfLE k)).trans (congrArg _ (ext_form q h k Λ' g₀ g s))

theorem isOm_res {V V' : Z.Opens} (h : V' ≤ V) (k : inU q V' ≤ inU q V) (hFL : FormLaws) (a : ℕ)
    (e : Om K (Sec q V) a →ₗ[K] HV q V a a) (e' : Om K (Sec q V') a →ₗ[K] HV q V' a a)
    (he : IsOm q V a e) (he' : IsOm q V' a e') (ω : Om K (Sec q V) a) :
    (resU (G q a) k).pull a (e ω) = e' (omMap (phi q h) a ω) := by
  have key : ((resU (G q a) k).pull a).comp e = e'.comp (omMap (phi q h) a) := by
    refine LinearMap.ext_on (hFL K (Sec q V) (Sec q V') a).1 ?_
    rintro _ ⟨g₀, g, rfl⟩
    change (resU (G q a) k).pull a (e (form K g₀ g)) = e' (omMap (phi q h) a (form K g₀ g))
    rw [((hFL K (Sec q V) (Sec q V') a).2 (phi q h)).1]
    exact form_uniq q (isForm_res q h k g₀ g _ (he g₀ g)) (he' _ _)
  exact LinearMap.congr_fun key ω

end OmegaRestriction

theorem omRes_pf : OmRes := by
  intro K _ Z q V V' h k
  exact ⟨OmegaRestriction.phi q h, fun g => rfl, fun a g₀ g c hc => OmegaRestriction.isForm_res q h k g₀ g c hc,
    fun a e e' he he' ω => OmegaRestriction.isOm_res q h k GlobalTheory.T.onto_form_laws a e e' he he' ω⟩

end CrystallineSemistableComparison.Onto

end
