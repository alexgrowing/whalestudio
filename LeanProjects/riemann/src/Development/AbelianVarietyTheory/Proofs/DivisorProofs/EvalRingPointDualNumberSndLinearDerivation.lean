import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.DualEval

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem evalPt_of_eq {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (φ : R →+* R')
    (G' : Sp R ⟶ X) (x : Sp R' ⟶ X) (O : X.Opens) (h0 : ⊤ ≤ G' ⁻¹ᵁ O) (hx : ⊤ ≤ x ⁻¹ᵁ O)
    (e : x = spMap φ ≫ G') (f : Γ(X, O)) : evalPt x O hx f = φ (evalPt G' O h0 f) := by
  subst e
  exact evalPt_spMap_comp φ G' O h0 hx f

theorem snd_of_mul_eq {K : Type} [Field K] (u t s : DualNumber K) (ht : t.fst ≠ 0)
    (e : u * t = s) : u.snd = (s.snd - s.fst / t.fst * t.snd) / t.fst := by
  have e1 : u.fst * t.fst = s.fst := by rw [← e]; rfl
  have e2 : u.fst * t.snd + u.snd * t.fst = s.snd := by rw [← e, DualNumber.snd_mul]
  have hu : u.fst = s.fst / t.fst := by rw [eq_div_iff ht, e1]
  rw [eq_div_iff ht, ← e2, hu]
  ring

end GlobalTheory.DualEval

namespace GlobalTheory.DualEval

attribute [local instance] RingHom.ker_isPrime

section Lift

variable {S K : Type} [CommRing S] [Field K] (ψ : S →+* K)

theorem isUnit_of_lifts (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
    (y : (RingHom.ker ψ).primeCompl) : IsUnit (φ y) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
  rw [hφ]
  exact Ne.isUnit fun h0 => y.2 (by simpa [RingHom.mem_ker] using h0)

def liftAt (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    Localization.AtPrime (RingHom.ker ψ) →+* DualNumber K :=
  IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (isUnit_of_lifts ψ φ hφ)

theorem liftAt_comp (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    (liftAt ψ φ hφ).comp (algebraMap S (Localization.AtPrime (RingHom.ker ψ))) = φ :=
  IsLocalization.lift_comp _

theorem liftAt_mk'_mul (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t) * φ t = φ s := by
  have := congrArg (liftAt ψ φ hφ)
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker ψ)) s t)
  rw [map_mul] at this
  unfold liftAt at this ⊢
  rw [IsLocalization.lift_eq, IsLocalization.lift_eq] at this
  exact this

theorem psi_ne_zero (t : (RingHom.ker ψ).primeCompl) : ψ t ≠ 0 := fun h0 =>
  t.2 (by simpa [RingHom.mem_ker] using h0)

theorem liftAt_mk'_snd (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).snd =
      ((φ s).snd - ψ s / ψ t * (φ t).snd) / ψ t := by
  have := snd_of_mul_eq _ _ _ (by rw [hφ]; exact psi_ne_zero ψ t) (liftAt_mk'_mul ψ φ hφ s t)
  rw [hφ, hφ] at this
  exact this

theorem liftAt_isLocalHom (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    IsLocalHom ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftAt ψ φ hφ)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hs
  have e1 : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst *
      ψ t = ψ s := by
    rw [← hφ, ← hφ, ← liftAt_mk'_mul ψ φ hφ s t]
    rfl
  have hs0 : ψ s = 0 := by simpa [RingHom.mem_ker] using hs
  rw [hs0] at e1
  have hne : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst
      ≠ 0 := hx.ne_zero
  exact hne ((mul_eq_zero.1 e1).resolve_right (psi_ne_zero ψ t))

end Lift

theorem evalPt_snd_sum {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X)
    (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K)
    (m : ι → K) (h1 : ∀ a s, (θc a s).fst = ψ s) (h2 : ∀ s, (θ s).fst = ψ s)
    (h3 : ∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) (O : X.Opens) (f : Γ(X, O))
    (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O) :
    (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  classical
  let L := Localization.AtPrime (RingHom.ker ψ)
  let alg : S →+* L := algebraMap S L
  let fstR : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  let G' : Sp L ⟶ X := spMap alg ≫ G
  haveI := liftAt_isLocalHom ψ θ h2
  have hm : IsLocalRing.closedPoint L ∈ G' ⁻¹ᵁ O := by
    rw [← IsLocalRing.comap_closedPoint (fstR.comp (liftAt ψ θ h2))]
    have hmor : spMap (fstR.comp (liftAt ψ θ h2)) ≫ G' = spMap fstR ≫ spMap θ ≫ G := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp_ring, ← spMap_comp_ring,
        RingHom.comp_assoc, liftAt_comp]
    let pt : Sp K := IsLocalRing.closedPoint K
    have key : (spMap (fstR.comp (liftAt ψ θ h2)) ≫ G') pt ∈ O := by
      rw [hmor]
      exact h (Set.mem_univ ((spMap fstR) pt))
    exact key
  have h0 : ⊤ ≤ G' ⁻¹ᵁ O := ((IsLocalRing.closed_point_mem_iff (U := G' ⁻¹ᵁ O)).1 hm).ge
  have hval : ∀ (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
      (hx : ⊤ ≤ (spMap φ ≫ G) ⁻¹ᵁ O),
      evalPt (spMap φ ≫ G) O hx f = liftAt ψ φ hφ (evalPt G' O h0 f) := by
    intro φ hφ hx
    refine evalPt_of_eq _ G' _ O h0 hx ?_ f
    rw [← Category.assoc, ← spMap_comp_ring, liftAt_comp]
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl (evalPt G' O h0 f)
  have hA : ∀ a, (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd =
      (((θc a) s).snd - ψ s / ψ t * ((θc a) t).snd) / ψ t := fun a => by
    rw [hval (θc a) (h1 a) (h' a), ← hst, liftAt_mk'_snd]
  rw [hval θ h2 h, ← hst, liftAt_mk'_snd]
  simp_rw [hA, h3, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end GlobalTheory.DualEval
