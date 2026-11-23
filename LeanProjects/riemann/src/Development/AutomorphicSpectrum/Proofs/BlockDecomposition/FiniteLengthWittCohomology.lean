import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LevelOne

universe w w'

theorem mapH_injective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (hi : ∀ n, Function.Injective (φ.f n)) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ) :
    Function.Injective (φ.mapH n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : φ.mapZ n z ∈ (L.B n).submoduleOf (L.Z n) := (Submodule.Quotient.mk_eq_zero _).1 hx
  have h1 : φ.f n z.1 ∈ L.B n := h0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change z.1 ∈ K.B n
  cases n with
  | zero =>
    have h2 : φ.f 0 z.1 = 0 := h1
    exact hi 0 (h2.trans (map_zero _).symm)
  | succ n =>
    obtain ⟨w, hw⟩ := h1
    obtain ⟨w', rfl⟩ := hs n w
    rw [φ.comm] at hw
    exact ⟨w', hi _ hw⟩

theorem isNoetherian_of_surj {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (h : Function.Surjective (algebraMap R S)) [IsNoetherian S M] : IsNoetherian R M := by
  let f : Submodule R M →o Submodule S M :=
    { toFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun c x hx => by
            obtain ⟨r, rfl⟩ := h c
            rw [algebraMap_smul]
            exact N.smul_mem r hx }
      monotone' := fun _ _ h => h }
  have hf : StrictMono f := Monotone.strictMono_of_injective f.monotone fun N N' e => by
    ext x
    exact iff_of_eq (congrArg (fun P : Submodule S M => x ∈ P) e)
  rw [isNoetherian_iff']
  exact hf.wellFoundedGT

section Witt

variable (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l]

theorem span_l_isMaximal : (Ideal.span {(l : WittVector l k) ^ 1}).IsMaximal := by
  have e : Ideal.span {(l : WittVector l k) ^ 1} = RingHom.ker (WittVector.constantCoeff (p := l) (R := k)) := by
    ext x
    rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero, RingHom.mem_ker, WittVector.constantCoeff_apply]
  rw [e]
  exact RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective l)

theorem wm_artinian : IsArtinianRing (Wc.Wm l k 1) := by
  haveI := span_l_isMaximal l k
  letI := Ideal.Quotient.field (Ideal.span {(l : WittVector l k) ^ 1})
  infer_instance

end Witt

section Site

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev QAll : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) :=
  St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}

theorem qAll_all (T : Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) : QAll q ρ T :=
  ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩

def toAll : CH.Mor (Wc.OM l (B.schFn q) ρ 1) (CH.modF (sP (QAll q ρ)).A) (Ideal.Quotient.mk _) where
  G := (QAll q ρ).ι
  τ T := { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toAll_inj (n : ℕ) : Function.Injective ((toAll q ρ).hom.f n) := by
  intro f f' h
  funext s
  exact congrFun h (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ))

theorem toAll_surj (n : ℕ) : Function.Surjective ((toAll q ρ).hom.f n) := by
  intro g
  exact ⟨fun s => g (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ)), rfl⟩

theorem toAll_pull_inj (j : ℕ) : Function.Injective ((toAll q ρ).pull j) :=
  mapH_injective _ (toAll_inj q ρ) (toAll_surj q ρ) j

end Site

theorem finiteLength_level_one : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  intro l _ k _ _ _ O _ X q ρ j hfin
  haveI := wm_artinian l k
  letI : Module (WittVector l k) (HO (QAll q ρ) j) := Module.compHom _ (algebraMap (WittVector l k) (Wc.Wm l k 1))
  haveI : IsScalarTower (WittVector l k) (Wc.Wm l k 1) (HO (QAll q ρ) j) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj : Function.Surjective (algebraMap (WittVector l k) (Wc.Wm l k 1)) := Ideal.Quotient.mk_surjective
  haveI : IsNoetherian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsArtinian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsNoetherian (WittVector l k) (HO (QAll q ρ) j) := isNoetherian_of_surj hsurj
  haveI : IsArtinian (WittVector l k) (HO (QAll q ρ) j) := isArtinian_of_surjective_algebraMap hsurj
  let f : CH.H (Wc.OM l (B.schFn q) ρ 1) j →ₗ[WittVector l k] HO (QAll q ρ) j :=
    { toFun := (toAll q ρ).pull j
      map_add' := map_add _
      map_smul' := fun r x => ((toAll q ρ).pull j).map_smulₛₗ r x }
  have hf : Function.Injective f := toAll_pull_inj q ρ j
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

end GlobalTheory.CompanionTheory.LevelOne
