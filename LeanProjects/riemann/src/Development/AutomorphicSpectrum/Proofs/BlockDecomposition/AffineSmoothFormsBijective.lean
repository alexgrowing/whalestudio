import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupH0NormalCoboundary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMapEqMOm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentativeRestrict
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlue

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

variable {K : Type} [CommRing K] {Z : Scheme.{0}}

theorem inU_mono (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) : inU q V' ≤ inU q V :=
  fun T hT x hx => k (hT hx)

theorem ev_res (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) (T : Thick (smFun Z q))
    (h : inU q V' T) (h' : inU q V T) (g : Γ(Z, V)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T h ((Z.presheaf.map (homOfLE k).op).hom g) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T h' g := by
  simp only [ev, GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem lifts_nonempty (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : Nonempty (Lifts q V) :=
  ⟨⟨fun T g => (Ideal.Quotient.mk_surjective
      (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose,
    fun T g => (Ideal.Quotient.mk_surjective
      (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g)).choose_spec⟩⟩

theorem rep_unique {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  obtain ⟨f', hf', rfl, hz'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst e
  rfl

theorem isForm_unique (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V}
    {c c' : HV q V a a} (h : IsForm q V g₀ g c) (h' : IsForm q V g₀ g c') : c = c' := by
  obtain ⟨Λ⟩ := lifts_nonempty q V
  exact rep_unique (A := (inU q V).ι ⋙ thA (smFun Z q)) ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι)
    ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι) (h Λ) (h' Λ)

theorem isForm_res (q : Z ⟶ Spec (CommRingCat.of K)) {V V' : Z.Opens} (k : V' ≤ V) (φ : Sec q V →ₐ[K] Sec q V')
    (hφ : ∀ g, φ g = (Z.presheaf.map (homOfLE k).op).hom g) {a : ℕ} {g₀ : Sec q V} {g : Fin a → Sec q V}
    {c : HV q V a a} (hc : IsForm q V g₀ g c) :
    IsForm q V' (φ g₀) (fun j => φ (g j)) ((resU (G q a) (inU_mono q k)).pull a c) := by
  classical
  intro Λ'
  obtain ⟨Λ₀⟩ := lifts_nonempty q V
  let Λ : Lifts q V :=
    { v := fun T g => if h : inU q V' T.obj then Λ'.v ⟨T.obj, h⟩ (φ g) else Λ₀.v T g
      hv := fun T g => by
        by_cases h : inU q V' T.obj
        · simp only [dif_pos h]
          refine (Λ'.hv ⟨T.obj, h⟩ (φ g)).trans ?_
          rw [hφ]
          exact ev_res q k T.obj h T.property g
        · simp only [dif_neg h]
          exact Λ₀.hv T g }
  have hv : ∀ (T : (inU q V').FullSubcategory) (g : Sec q V),
      Λ.v ((ObjectProperty.ιOfLE (inU_mono q k)).obj T) g = Λ'.v T (φ g) := fun T g => dif_pos T.property
  have hz := GlobalTheory.CompanionTheory.ConeRep.rep_resB (thA (smFun Z q)) (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))
    (inU_mono q k) (Λ.form g₀ g) c (hc Λ)
  have e : Λ'.form (φ g₀) (fun j => φ (g j)) = resB (thA (smFun Z q)) (inU_mono q k) (Λ.form g₀ g) := by
    funext s
    simp only [Lifts.form, resB]
    refine congrArg₂ (· * ·) (hv _ _).symm (Finset.prod_congr rfl fun k' _ => ?_)
    exact congrArg₂ (· - ·) (congrArg _ (hv _ _).symm) (congrArg _ (hv _ _).symm)
  exact e ▸ hz

theorem fs_hom_heq {C : Type 1} [Category.{0} C] {P : ObjectProperty C} {S₁ S₂ S₁' S₂' : P.FullSubcategory}
    (h : S₁ = S₂) (h' : S₁' = S₂') (f : S₁ ⟶ S₁') (g : S₂ ⟶ S₂') (hh : HEq f.hom g.hom) : HEq f g := by
  subst h h'
  exact heq_of_eq (ObjectProperty.hom_ext _ (eq_of_heq hh))

theorem morV_G (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) :
    (morV (𝟙 Z) (Category.id_comp q) a h).G = (resU (G q a) k).G := by
  refine Functor.hext (fun T => ?_) (fun T T' f => ?_)
  · exact ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj)
  · refine fs_hom_heq (ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj))
      (ObjectProperty.FullSubcategory.ext (GlobalTheory.CompanionTheory.HodgePull.obj_id T'.obj)) _ _ ?_
    exact GlobalTheory.CompanionTheory.HodgePull.hom_heq (GlobalTheory.CompanionTheory.HodgePull.obj_id T.obj) (GlobalTheory.CompanionTheory.HodgePull.obj_id T'.obj) _ _ HEq.rfl

theorem morV_pullC (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a n : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) (z : CH.Cn (P.ι ⋙ G q a) n) :
    (morV (𝟙 Z) (Category.id_comp q) a h).pullC n z = (resU (G q a) k).pullC n z := by
  funext s
  have hs : s ⋙ (morV (𝟙 Z) (Category.id_comp q) a h).G = s ⋙ (resU (G q a) k).G := by
    rw [morV_G q k a h]
  exact (GlobalTheory.CompanionTheory.HodgePull.τ_id a _ _).trans (eq_of_heq (congr_arg_heq z hs))

theorem morV_pull (q : Z ⟶ Spec (CommRingCat.of K)) {P P' : ObjectProperty (Thick (smFun Z q))} (k : P' ≤ P) (a n : ℕ)
    (h : ∀ T, P' T → P ((smS (𝟙 Z) (Category.id_comp q)).G.obj T)) (x : HU (G q a) P n) :
    (morV (𝟙 Z) (Category.id_comp q) a h).pull n x = (resU (G q a) k).pull n x := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (morV_pullC q k a n h z))

theorem isForm_top (q : Z ⟶ Spec (CommRingCat.of K)) {a : ℕ} (g₀ : Γ(Z, ⊤)) (g : Fin a → Γ(Z, ⊤)) (c : Hdg q a a)
    (hc : Om.L2.IsFormT q g₀ g c) :
    IsForm q ⊤ (a := a) g₀ g ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c) := by
  intro Λ
  let Λ' : Om.L2.LiftsT q := ⟨fun T g => Λ.v ⟨T, Om.L2.inTop q T⟩ g, fun T g => Λ.hv ⟨T, Om.L2.inTop q T⟩ g⟩
  obtain ⟨f, hf, hcf, hz⟩ := hc Λ'
  have hf' : CH.d (G q a) a f = 0 := hf
  have hb : CH.d ((inU q ⊤).ι ⋙ G q a) a ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f) = 0 := by
    rw [(CH.Mor.restrict (G q a) (inU q ⊤).ι).d_pullC, hf', map_zero]
  have hcl : (CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c =
      (CH.cx ((inU q ⊤).ι ⋙ G q a)).cls ((CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f) hb := by
    have hc' : c = (CH.cx (G q a)).cls f hf' := hcf
    rw [hc']
    rfl
  exact ⟨(CH.Mor.restrict (G q a) (inU q ⊤).ι).pullC a f, hb, hcl, fun s => hz (s ⋙ (inU q ⊤).ι)⟩

theorem omMap_cross {K A B₁ B₂ C : Type} [CommRing K] [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C] [Algebra K A]
    [Algebra K B₁] [Algebra K B₂] [Algebra K C] (φ₁ : A →ₐ[K] B₁) (φ₂ : A →ₐ[K] B₂) (ψ₁ : B₁ →ₐ[K] C) (ψ₂ : B₂ →ₐ[K] C)
    (h : ∀ g, ψ₁ (φ₁ g) = ψ₂ (φ₂ g)) (a : ℕ) (ω : Om K A a) :
    omMap ψ₁ a (omMap φ₁ a ω) = omMap ψ₂ a (omMap φ₂ a ω) := by
  have hs := (GlobalTheory.CompanionTheory.OntoForms.formLaws K A A a).1
  have e : (omMap ψ₁ a).comp (omMap φ₁ a) = (omMap ψ₂ a).comp (omMap φ₂ a) := by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨g₀, g, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [((GlobalTheory.CompanionTheory.OntoForms.formLaws K A B₁ a).2 φ₁).1, ((GlobalTheory.CompanionTheory.OntoForms.formLaws K A B₂ a).2 φ₂).1,
      ((GlobalTheory.CompanionTheory.OntoForms.formLaws K B₁ C a).2 ψ₁).1, ((GlobalTheory.CompanionTheory.OntoForms.formLaws K B₂ C a).2 ψ₂).1]
    simp only [h]
  exact LinearMap.congr_fun e ω

theorem res_key (hN : OmNat) (K : Type) [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ)
    {V V' : X.Opens} (k : V' ≤ V) :
    ∃ φ : Sec q V →ₐ[K] Sec q V', (∀ g, φ g = (X.presheaf.map (homOfLE k).op).hom g) ∧
      ∀ e e', IsOm q V a e → IsOm q V' a e' → ∀ ω,
        (resU (G q a) (inU_mono q k)).pull a (e ω) = e' (omMap φ a ω) := by
  have h : ∀ T, inU q V' T → inU q V ((smS (𝟙 X) (Category.id_comp q)).G.obj T) := fun T hT => by
    have e : (smS (𝟙 X) (Category.id_comp q)).G.obj T = T := GlobalTheory.CompanionTheory.HodgePull.obj_id T
    rw [e]
    exact inU_mono q k T hT
  obtain ⟨φ, h1, h2⟩ := hN K X X q q (𝟙 X) (Category.id_comp q) V V' k h
  refine ⟨φ, fun g => ?_, fun e e' he he' ω => ?_⟩
  · rw [h1]
    simp [Scheme.Hom.appLE]
  · rw [← morV_pull q (inU_mono q k) a a h]
    exact h2 a e e' he he' ω

theorem om_top : AffOm → OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : Om K (Sec q ⊤) a →ₗ[K] HV q ⊤ a a, IsOm q ⊤ a e ∧ Function.Bijective e := by
  intro hA hN K _ _ X q _ _ a
  classical
  obtain ⟨U⟩ := (Pb.cov_ex q).1 inferInstance
  have hAff2 : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := fun α β => by
    have h := U.inter {α, β} ⟨α, by simp⟩
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hc1 : ∀ α, Nonempty (Coord q (U.U α) (U.d α)) := fun α => ⟨U.c α⟩
  have hc2 : ∀ α β, Nonempty (Coord q (U.U α ⊓ U.U β) (U.d α)) := fun α β =>
    ⟨(Pb.coord_res (U.c α) inf_le_left (hAff2 α β)).choose⟩
  have van : ∀ S : Finset U.ι, S.Nonempty → ∀ j < a, Subsingleton (HV q (⨅ α ∈ S, U.U α) a j) := by
    rintro S hS j hj
    obtain ⟨α₀, h₀⟩ := id hS
    exact (hA K X q _ (U.d α₀) ⟨(Pb.coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hS)).choose⟩ a).1 j (by omega)
  choose E hE hEb using fun α => (hA K X q _ _ (hc1 α) a).2
  choose E₂ hE₂ hE₂b using fun α β => (hA K X q _ _ (hc2 α β) a).2
  choose φ hφ hφn using fun α => res_key hN K q a (le_top : U.U α ≤ ⊤)
  choose ψ₁ hψ₁ hψ₁n using fun α β => res_key hN K q a (inf_le_left : U.U α ⊓ U.U β ≤ U.U α)
  choose ψ₂ hψ₂ hψ₂n using fun α β => res_key hN K q a (inf_le_right : U.U α ⊓ U.U β ≤ U.U β)
  have hk : ∀ α, inU q (U.U α) ≤ inU q ⊤ := fun α => inU_mono q le_top
  have hk₁ : ∀ α β, inU q (U.U α ⊓ U.U β) ≤ inU q (U.U α) := fun α β => inU_mono q inf_le_left
  have hk₂ : ∀ α β, inU q (U.U α ⊓ U.U β) ≤ inU q (U.U β) := fun α β => inU_mono q inf_le_right
  obtain ⟨hinj, hglue⟩ := GlobalTheory.CompanionTheory.CechDeg.om_cech q U.U U.cover a van hk hk₁ hk₂
  obtain ⟨finj, fglue⟩ := GlobalTheory.CompanionTheory.FormsGlue.forms_glue q U.U (fun α => (U.c α).affine) U.cover φ ψ₁ ψ₂ hφ hψ₁ hψ₂ a
  let R : HV q ⊤ a a →ₗ[K] ∀ α, HV q (U.U α) a a := LinearMap.pi fun α => (resU (G q a) (hk α)).pull a
  let Eo : Om K (Sec q ⊤) a →ₗ[K] ∀ α, HV q (U.U α) a a := LinearMap.pi fun α => (E α).comp (omMap (φ α) a)
  have hRinj : Function.Injective R := hinj
  have hcompat : ∀ ω α β, (resU (G q a) (hk₁ α β)).pull a (Eo ω α) = (resU (G q a) (hk₂ α β)).pull a (Eo ω β) := by
    intro ω α β
    have e₁ := hψ₁n α β _ _ (hE α) (hE₂ α β) (omMap (φ α) a ω)
    have e₂ := hψ₂n α β _ _ (hE β) (hE₂ α β) (omMap (φ β) a ω)
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    refine congrArg _ (omMap_cross _ _ _ _ (fun g => ?_) a ω)
    rw [hψ₁, hψ₂, hφ, hφ]
    change ((X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map (homOfLE inf_le_left).op).hom g) =
      ((X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map (homOfLE inf_le_right).op).hom g)
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  have hmem : ∀ ω, Eo ω ∈ LinearMap.range R := fun ω => by
    obtain ⟨x, hx⟩ := hglue (Eo ω) (hcompat ω)
    exact ⟨x, funext hx⟩
  let e : Om K (Sec q ⊤) a →ₗ[K] HV q ⊤ a a :=
    ((LinearEquiv.ofInjective R hRinj).symm : LinearMap.range R →ₗ[K] HV q ⊤ a a).comp (Eo.codRestrict _ hmem)
  have hRe : ∀ ω, R (e ω) = Eo ω := fun ω =>
    congrArg Subtype.val ((LinearEquiv.ofInjective R hRinj).apply_symm_apply (Eo.codRestrict _ hmem ω))
  refine ⟨e, fun g₀ g => ?_, fun ω ω' h => ?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.OmCls.main q (a := a) g₀ g
    have hc' := isForm_top q g₀ g c hc
    have key : e (form K g₀ g) = (CH.Mor.restrict (G q a) (inU q ⊤).ι).pull a c := by
      refine hRinj (funext fun α => ?_)
      rw [hRe]
      have h1 := isForm_res q le_top (φ α) (hφ α) hc'
      have h2 := hE α (φ α g₀) fun j => φ α (g j)
      refine Eq.trans ?_ (isForm_unique q _ h2 h1)
      exact congrArg (E α) (((GlobalTheory.CompanionTheory.OntoForms.formLaws K _ _ a).2 (φ α)).1 g₀ g)
    rw [key]
    exact hc'
  · refine finj (funext fun α => (hEb α).1 ?_)
    have := congrFun ((hRe ω).symm.trans ((congrArg R h).trans (hRe ω'))) α
    exact this
  · choose y hy using fun α => (hEb α).2 (R x α)
    obtain ⟨ω, hω⟩ := fglue y fun α β => (hE₂b α β).1 (by
      rw [← hψ₁n α β _ _ (hE α) (hE₂ α β), ← hψ₂n α β _ _ (hE β) (hE₂ α β), hy, hy]
      change (resU (G q a) (hk₁ α β)).pull a ((resU (G q a) (hk α)).pull a x) =
        (resU (G q a) (hk₂ α β)).pull a ((resU (G q a) (hk β)).pull a x)
      rw [← CrystallineSemistableComparison.Onto.resU_pull_trans (G q a) (hk α) (hk₁ α β) (inU_mono q le_top),
        ← CrystallineSemistableComparison.Onto.resU_pull_trans (G q a) (hk β) (hk₂ α β) (inU_mono q le_top)])
    refine ⟨ω, hRinj (funext fun α => ?_)⟩
    rw [hRe]
    change E α (omMap (φ α) a ω) = R x α
    rw [hω, hy]

end GlobalTheory.CompanionTheory.OmGlue
