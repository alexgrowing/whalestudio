import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AlgExtPf

variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : _ → _) = (pull R f F n) ∘ (pull R g F n) := funext (pull_comp R f g F n)
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_cancel {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (h : Eqv R (f ≫ g) F) (hf : Eqv R f F) :
    Eqv R g F := fun n => by
  have hc : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun a b hab => (h n).1 (by rw [hc, hc, hab]), fun y => ?_⟩
  obtain ⟨z, hz⟩ := (h n).2 (pull R f F n y)
  exact ⟨z, (hf n).1 (by rw [← hc, hz])⟩

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_sch_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := eqv_iso F _

theorem eqv_fst_comp {W X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h1 : Eqv R (sch.map (pullback.fst (pullback.snd f g) g')) F) (h2 : Eqv R (sch.map (pullback.fst f g)) F) :
    Eqv R (sch.map (pullback.fst f (g' ≫ g))) F := by
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp]
  exact eqv_comp F (eqv_sch_iso F _) (eqv_comp F h1 h2)

theorem eqv_fst_congr {X Z W : Scheme.{0}} (f : X ⟶ Z) {h h' : W ⟶ Z} (e : h = h') :
    Eqv R (sch.map (pullback.fst f h)) F → Eqv R (sch.map (pullback.fst f h')) F := by
  subst e; exact id

end LateralTheory.KummerTheory.AlgExtPf

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.AlgExtPf

theorem AlgExt_of (hP : Place) : AlgExt := by
  intro hE2 hE3 q _ k K _ _ _ _ f hq X p _ _ i
  let _ := f.toAlgebra
  obtain ⟨T, σ, hσ, hres, hAIC, hSH⟩ := hP k K
  have hqT : IsUnit ((q : ℕ) : T) := by simpa using hq.map σ
  set gσ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom σ) with hgσ
  set gr : Spec (CommRingCat.of (IsLocalRing.ResidueField T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue T)) with hgr
  have e2 := hE2 q T hSH hqT (pullback.snd p gσ) i

  have hiso : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) :=
    (RingEquiv.ofBijective _ hres).toCommRingCatIso.isIso_hom
  have hcomp : gr ≫ gσ = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) := by
    rw [hgr, hgσ, ← Spec.map_comp]; rfl
  have hs : Eqv (ZMod q) (sch.map (pullback.fst p (gr ≫ gσ))) (tw q i) := by
    rw [hcomp]; exact eqv_sch_iso _ _
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp] at hs
  have hT : Eqv (ZMod q) (sch.map (pullback.fst p gσ)) (tw q i) :=
    eqv_cancel _ (eqv_cancel _ hs (eqv_sch_iso _ _)) e2

  have e3 := hE3 q T hAIC hqT (pullback.snd p gσ) i
  let eK : FractionRing T ≃+* K := (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv
  set gj : Spec (CommRingCat.of (FractionRing T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))) with hgj
  set ge : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (FractionRing T)) :=
    Spec.map (CommRingCat.ofHom eK.toRingHom) with hge
  have hge_iso : IsIso ge := by
    have : IsIso (CommRingCat.ofHom eK.toRingHom) := eK.toCommRingCatIso.isIso_hom
    rw [hge]; infer_instance
  have hfac : (ge ≫ gj) ≫ gσ = Spec.map (CommRingCat.ofHom f) := by
    rw [hge, hgj, hgσ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1; ext x
    have h1 := hσ x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change eK (algebraMap T (FractionRing T) (σ x)) = f x
    rw [show f x = algebraMap k K x from rfl, ← h1]
    exact (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).commutes (σ x)
  refine eqv_fst_congr _ p hfac (eqv_fst_comp _ p gσ (ge ≫ gj) ?_ hT)
  refine eqv_fst_comp _ _ gj ge ?_ e3
  exact eqv_sch_iso _ _

end LateralTheory.KummerTheory
