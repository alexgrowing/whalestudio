import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Formalism.LocalToGlobal.UnitaryNorms.CharExHost

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrivOnRead

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infIdele_snd_one {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem fst_prod_apply {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w :=
  map_prod ((Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) f s

theorem snd_prod {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem ideleMap_inf (w : InfinitePlace F) (k : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (infIdele F w (atInf w k)) = CharEx.aFi (L := E) F w k := by
  classical
  refine Units.ext (Prod.ext (funext fun w' => ?_) ?_)
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 w' = _
    rw [CharEx.aFi, Units.coe_prod, fst_prod_apply]
    change LiesOver.completionMap (v := w'.comap (algebraMap F E)) (w := w')
      ((infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 (w'.comap (algebraMap F E))) = _
    by_cases hw : w'.comap (algebraMap F E) = w
    · have hm : w' ∈ aboveInf (L := E) F w := by simp [aboveInf, hw]
      rw [Finset.prod_eq_single_of_mem w' hm (fun w'' _ h => infIdele_fst_ne E w'' w' (Ne.symm h) _),
        infIdele_fst_self]
      subst hw
      rw [infIdele_fst_self]
      exact LiesOver.completionMap_coe (v := w'.comap (algebraMap F E)) (w := w') (WithAbs.toAbs _ (k : F))
    · rw [infIdele_fst_ne F w _ hw, map_one]
      refine (Finset.prod_eq_one fun w'' hw'' => infIdele_fst_ne E w'' w' ?_ _).symm
      rintro rfl
      simp [aboveInf] at hw''
      exact hw hw''
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).2 = _
    rw [CharEx.aFi, Units.coe_prod, snd_prod]
    rw [Finset.prod_eq_one fun w'' _ => infIdele_snd_one w'' _]
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)

end General

open GlobalTheory.CharTransport in
set_option maxHeartbeats 800000 in

theorem exists_hom_tmul (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ a x, Θ (a ⊗ₜ[D.host.F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hΘ, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem trivOn_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  intro D c χ hc ha
  have hχ := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D c χ hc
  obtain ⟨Θ, hΘc, hΘt, hinc, hloc⟩ := exists_hom_tmul D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΘc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have hc' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, hloc P e he]
      rw [hcoe, this]
      rfl
  have hcc : c = c' := GlobalTheory.ChrEqUnique.idc_unique D c c' χ hc hc'
  have key : ∀ a : (AF D.host.F)ˣ, χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a) = 1 := fun a => by
    have h1 : u (idF D a) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a := Units.ext (by
      change Θ ((a : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
      rw [hΘt, map_one, mul_one]
      rfl)
    have h2 := hcoe (idF D a)
    rw [← hcc, ha, h1] at h2
    exact Units.ext (by rw [← h2]; rfl)
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · rw [CharEx.resFin_eq]
    change χ.1 (GlobalTheory.Mem.Chr.locF D.host.F v k) = 1
    rw [← GlobalTheory.ToricDistribution.ideleMap_local]
    exact key _
  · rw [CharEx.resInf_eq, ← ideleMap_inf]
    exact key _

end GlobalTheory.TrivOnRead
