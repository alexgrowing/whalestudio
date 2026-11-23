import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullbackStatement

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.PushLoc

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξg : Spec (CommRingCat.of Ω) ⟶ Y} {e : Y ⟶ X}

theorem dominates_id (h : ξg ≫ e = ξ) : Dominates ξg ξ e (RingHom.id Ω) := by
  have h0 : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
  unfold Dominates
  rw [h0, Category.id_comp, h]

def emb (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) : Cpt ξ := ⟨e p.1, hD.specializes p⟩

theorem genMap_stalkMap (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) (s : X.presheaf.stalk (e p.1)) :
    genMap ξg p ((e.stalkMap p.1).hom s) = genMap ξ (emb hD p) s :=
  PullReg.stalkMap_comp_genMap hD p (hD.specializes p) s

theorem regAt_emb [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) :
    regAt ξg p = regAt ξ (emb hD p) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 s
    exact ⟨s', (genMap_stalkMap hD p s').symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, genMap_stalkMap hD p s⟩

theorem isCptGen_of [IsPreimmersion e] (h : ξg ≫ e = ξ) (hg : IsCptGen ξ) : IsCptGen ξg := by
  subst h
  have hD : Dominates ξg (ξg ≫ e) e (RingHom.id Ω) := dominates_id rfl
  refine ⟨?_, fun p => ?_⟩
  · have hb := hg.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb
    have hs := Scheme.Hom.stalkMap_surjective e (ξg (IsLocalRing.closedPoint Ω))
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      have : a' = b' := hb.1 hab
      rw [this]
    · intro c
      obtain ⟨a, rfl⟩ := hb.2 c
      exact ⟨_, rfl⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 a
    obtain ⟨b', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 b
    have h1 := genMap_stalkMap hD p a'
    have h2 := genMap_stalkMap hD p b'
    have : a' = b' := hg.inj (emb hD p) (h1.symm.trans (Eq.trans hab h2))
    rw [this]

theorem isIntegral_congr {R S : Subring Ω} (h : R = S) {a : Ω} (ha : IsIntegral R a) : IsIntegral S a := by
  subst h
  exact ha

theorem normalCpt_of [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (hn : NormalCpt ξ) :
    NormalCpt ξg := by
  intro p a ha
  rw [regAt_emb hD p]
  exact hn (emb hD p) a (isIntegral_congr (regAt_emb hD p) ha)

theorem coe_span_eq {R S : Subring Ω} (h : R = S) (M : Submodule S Ω) :
    ((Submodule.span R (M : Set Ω) : Submodule R Ω) : Set Ω) = M := by
  subst h
  rw [Submodule.span_eq]

theorem eq_span_of_coe {R S : Subring Ω} (h : R = S) {N : Submodule R Ω} {M : Submodule S Ω}
    (hNM : (N : Set Ω) = M) {A : Set Ω} (hM : M = Submodule.span S A) : N = Submodule.span R A := by
  subst h
  exact (SetLike.coe_injective hNM).trans hM

theorem coe_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) (p : Cpt ξg) :
    ((L.pull ξg e (AddMonoidHom.id Ω) p : Submodule (regAt ξg p) Ω) : Set Ω) = L (emb hD p) := by
  rw [Lat.pull_apply L hD]
  have h0 : (AddMonoidHom.id Ω) '' (L (emb hD p) : Set Ω) = (L (emb hD p) : Set Ω) := Set.image_id _
  exact (congrArg (fun A : Set Ω => ((Submodule.span (regAt ξg p) A : Submodule _ Ω) : Set Ω)) h0).trans
    (coe_span_eq (regAt_emb hD p) _)

theorem isVBOn_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) {T : Set (Cpt ξ)}
    (hT : ∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) (h : L.IsVBOn T 1 ⊤) :
    (L.pull ξg e (AddMonoidHom.id Ω)).IsVBOn Set.univ 1 ⊤ := by
  have hmem : ∀ p : Cpt ξg, emb hD p ∈ T := fun p => (hT _).2 ⟨p.1, rfl⟩
  intro p _
  obtain ⟨U, hU, b, hb, hq⟩ := h (emb hD p) (hmem p)
  refine ⟨e ⁻¹ᵁ U, hU, b, hb, fun q _ hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hq (emb hD q) (hmem q) hqU
  exact ⟨h1, eq_span_of_coe (regAt_emb hD q) (coe_pull hD L q) h2⟩

theorem pull_pull_eq [IsPreimmersion e] {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ Y}
    (hD : Dominates ξg ξ e (RingHom.id Ω)) (hD' : Dominates ξ' ξg f (RingHom.id Ω))
    (hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω)) (L : Lat ξ Ω) (p' : Cpt ξ') :
    (L.pull ξg e (AddMonoidHom.id Ω)).pull ξ' f (RingHom.id Ω).toAddMonoidHom p' =
      L.pull ξ' (f ≫ e) (AddMonoidHom.id Ω) p' := by
  rw [Lat.pull_apply _ hD', Lat.pull_apply _ hD'']
  congr 1
  have h1 := coe_pull hD L ⟨f p'.1, hD'.specializes p'⟩
  have h2 : emb hD ⟨f p'.1, hD'.specializes p'⟩ = ⟨(f ≫ e) p'.1, hD''.specializes p'⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply f e p'.1).symm
  rw [h1, h2]
  rfl

theorem gen_descends : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  intro X₀ Xg X' Ω _ ξ ξg ξ' e f L T t hpre hprop hloc h1 h2 hgen hnorm hT hVB hG x hx
  haveI := hpre
  haveI := hprop
  haveI := hloc
  have hD : Dominates ξg ξ e (RingHom.id Ω) := dominates_id h1
  have hD' : Dominates ξ' ξg f (RingHom.id Ω) := dominates_id h2
  have hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω) := dominates_id (by rw [← Category.assoc, h2, h1])
  obtain ⟨z, hz⟩ := (hT x).1 hx
  have hs : genPt ξg ⤳ z := by
    have h3 : e (genPt ξg) ⤳ e z := by
      rw [hD.map_genPt, hz]
      exact x.2
    exact (e.isEmbedding.isInducing.specializes_iff).1 h3
  have hp : (L.pull ξg e (AddMonoidHom.id Ω)).IsGenAt ⟨z, hs⟩ t :=
    GlobalTheory.T.line_bundle_normal_proper_pullback Xg Ω ξg X' Ω ξ' f (RingHom.id Ω) hD' Function.bijective_id (isCptGen_of h1 hgen)
      (normalCpt_of hD hnorm) (L.pull ξg e (AddMonoidHom.id Ω)) Set.univ ⟨z, hs⟩ t (isVBOn_pull hD L hT hVB)
      (fun _ _ => trivial) (fun p' _ => by
        have h4 := hG p'
        refine ⟨h4.1, ?_⟩
        rw [pull_pull_eq hD hD' hD'' L p']
        exact h4.2)
  have hx' : x = emb hD ⟨z, hs⟩ := Subtype.ext hz.symm
  rw [hx']
  exact ⟨hp.1, eq_span_of_coe (regAt_emb hD _).symm (coe_pull hD L _).symm hp.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PushLoc
