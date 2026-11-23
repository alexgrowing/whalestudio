import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValuesStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp.Adapt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ext_frac {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [Module.Finite A B] (f : FractionRing A →+* ℂ) :
    ∃ g : FractionRing B →+* ℂ, ∀ a : A, g (algebraMap B _ (algebraMap A B a)) = f (algebraMap A _ a) := by
  letI : Algebra A ℂ := (f.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B (FractionRing B)
  have hA : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  have hC : Function.Injective (algebraMap A ℂ) :=
    f.injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : Module.IsTorsionFree A (FractionRing B) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hA (h.trans (map_zero _).symm)) id
  haveI : Module.IsTorsionFree A ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hC (h.trans (map_zero _).symm)) id
  let g := IsAlgClosed.lift (M := ℂ) (R := A) (S := FractionRing B)
  refine ⟨g.toRingHom, fun a => ?_⟩
  have h := g.commutes a
  rw [IsScalarTower.algebraMap_apply A B (FractionRing B)] at h
  exact h

variable {D : D7}

theorem charOf_congr {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R]
    (f f' : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (h : ∀ σ, f (ψ σ : Rˣ) = f' (ψ σ : Rˣ)) :
    GlobalTheory.SeriesTie.charOf a f ψ = GlobalTheory.SeriesTie.charOf a f' ψ := by
  have hv : ∀ x, ∃ σ, a.pull ψ x = ψ σ := by
    intro x
    unfold Recip.pull GlobalTheory.SeriesTie.descend
    split_ifs with hc
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ (a.sym x)
      refine ⟨σ, ?_⟩
      rw [MonoidHom.comp_apply, ← hσ]
      rfl
    · exact ⟨1, by simp⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨σ, hσ⟩ := hv x
  simp only [GlobalTheory.SeriesTie.charOf, MonoidHom.comp_apply, hσ]
  rw [show Units.map f.toMonoidHom (ψ σ) = Units.map f'.toMonoidHom (ψ σ) from Units.ext (h σ)]

open Classical in

def withTau (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : Setup D.ntw :=
  { ρ with
    e := fun i b => if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b
    ek := fun i b k => if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k }

open Classical in

theorem withTau_e (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) :
    (withTau ρ t s τ).e i b = if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b := rfl

open Classical in

theorem withTau_ek (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (withTau ρ t s τ).ek i b k = if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k := rfl

theorem withTau_good {ρ : Setup D.ntw} (hρ : ρ.Good) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ)
    (hfix : ∀ y, τ (embLL0 D y) = embLL0 D y)
    (hδ : ∀ σ, τ (ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) =
      ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) :
    (withTau ρ t s τ).Good := by
  refine ⟨hρ.rc, hρ.ch, hρ.bad_ne, hρ.goodSetup_bad_mem_badPlaces, hρ.goodSetup_badPlaces_conj, hρ.goodSetup_placesOverTwo_subset, hρ.goodSetup_count_eq_zero_off_badPlaces, ?_, ?_, hρ.base, hρ.latS, hρ.latT, hρ.Pg,
    ?_, hρ.weil, hρ.classes⟩
  · intro i b x
    rw [withTau_e]
    split_ifs with h
    · show τ (ρ.e i b _) = _
      rw [hρ.e_LL0]
      exact hfix x
    · exact hρ.e_LL0 i b x
  · intro i b k x
    show (withTau ρ t s τ).ek i b k _ = (withTau ρ t s τ).e i b _
    rw [withTau_e, withTau_ek]
    split_ifs with h
    · exact congrArg τ (hρ.ek_e i b k x)
    · exact hρ.ek_e i b k x
  · intro i j b
    show (ρ.B i j b).de = twistOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ρ.ch i)
      (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
    rw [hρ.delta i j b]
    unfold twistOf
    have : GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) =
        GlobalTheory.SeriesTie.charOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
      refine charOf_congr _ _ _ _ fun σ => ?_
      show ρ.e i b _ = (withTau ρ t s τ).e i b _
      rw [withTau_e]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact (hδ σ).symm
      · rfl
    rw [this]

theorem ext_onSmallField {c : NChoice D} (hc : NChTie D c) (w : D.what₂.places.Pl) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (g : FractionRing (c.Oe w) →+* ℂ)
    (hg : ∀ a : D.ntw.Ok (c.twI w) (c.k' w), g (algebraMap (c.Oe w) _ (algebraMap _ (c.Oe w) a)) =
      ρ.ek (c.twI w) (c.sd w) (c.k' w) (algebraMap _ _ a))
    (y : D.LL0) : g (c.embW w (y : D.what₂.LL)) = embLL0 D y := by
  obtain ⟨⟨y', z⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 (c.twI w)))
    ((if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) y)
  have hz0 : (z : D.ntw.O0 (c.twI w)) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  have e1 : ∀ x : D.ntw.O (c.twI w), ρ.ek (c.twI w) (c.sd w) (c.k' w)
      (algebraMap _ (FractionRing _) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) x)) =
      ρ.e (c.twI w) (c.sd w) (algebraMap _ _ x) := hρ.ek_e (c.twI w) (c.sd w) (c.k' w)
  have h1 := congrArg g (hc.embedding_baseField_condition w y y' z hz0 hz)
  rw [map_mul, hg, hg, e1, e1] at h1
  have h2 : sideEmb D.ntw (c.twI w) (c.sd w) y * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) =
      algebraMap _ _ (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y') := by
    have := congrArg (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w))
      (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) hz
    simp only [map_mul, IsFractionRing.map, IsLocalization.map_eq] at this
    exact this
  have h3 := congrArg (ρ.e (c.twI w) (c.sd w)) h2
  rw [map_mul, hρ.e_LL0] at h3
  have hne : ρ.e (c.twI w) (c.sd w) (algebraMap _ (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z)) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((map_ne_zero_iff _ (D.ntw.O_inj (c.twI w))).2 hz0))
  exact mul_right_cancel₀ hne (h1.trans h3.symm)

section Point

theorem realPin_withTau {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ)
    (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : RealPin Rl cG (withTau ρ t s τ) :=
  { psi := h.psi, inf := h.inf, cartT := h.cartT, onbS := h.onbS, onbT := h.onbT, latS := h.latS, latT := h.latT,
    frS := h.frS, frT := h.frT, vac := h.vac, Pg := h.Pg, grp := h.grp, mu0 := h.mu0, eta := h.eta, delta := h.delta,
    deltaPl := h.deltaPl, ap := h.ap, am := h.am }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem adapt_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) (hm : More p) (ρ : Setup D.ntw) (hρ : ρ.Good)
    (hpin : RealPin p.R p.cG ρ) : ∃ ρ' : Setup D.ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ' := by
  haveI : Module.Finite (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w) := ex.nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_ext_frac (ex.nch.Oe_inj w) (ρ.ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w))
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL (g.comp (ex.nch.embW w)) D.what₂.embLL
  have hfix : ∀ y : D.LL0, τ (embLL0 D y) = embLL0 D y := fun y => by
    have h := ext_onSmallField ex.nch_tie w hρ g hg y
    have h2 : τ (g (ex.nch.embW w (y : D.what₂.LL))) = D.what₂.embLL y := hτ _
    rw [h] at h2
    exact h2
  have hχ : (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).ValuesIn 0 (embLL0 D) := by
    have hv := hm.2.2.small.val
    unfold CharFrame.delAt
    split_ifs
    exacts [hv.del', hv.del]
  have hδ := GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ (ex.nch.twI w) j (ex.nch.sd w) _ (hpin.delta _ j _) hχ τ hfix
  refine ⟨withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ, withTau_good hρ _ _ τ hfix hδ, ⟨rfl, rfl, rfl, rfl, rfl⟩, realPin_withTau hpin _ _ τ,
    τ.toRingHom.comp g, fun x => hτ x, fun a => ?_⟩
  show τ (g _) = (withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ).ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) _
  rw [withTau_ek, if_pos ⟨rfl, rfl⟩]
  exact congrArg τ (hg a)

end Point

end GlobalTheory.BigOn.Exp.Adapt

open GlobalTheory.BigOn.Exp.Adapt in

theorem GlobalTheory.BigOn.Exp.adaptEx : AdaptEx := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
