import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTanShift

theorem spMap_comp_spMap' {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem isLocalRing_sq (K : Type) [Field K] : IsLocalRing (TrivSqZeroExt K (K × K)) :=
  haveI : Nontrivial (TrivSqZeroExt K (K × K)) := TrivSqZeroExt.inl_injective.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_sq (K : Type) [Field K] : IsArtinianRing (TrivSqZeroExt K (K × K)) := by
  haveI : Module.Finite K (TrivSqZeroExt K (K × K)) := inferInstanceAs (Module.Finite K (K × (K × K)))
  exact IsArtinianRing.of_finite K _

theorem pbEq {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h k ζ' s'} {c : SiegPre h k ζ s} {f f' : S' ⟶ S}
    (hc : SiegPB c' c f) (e : f = f') : SiegPB c' c f' := e ▸ hc

theorem shift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  intro g n h3 hodd K _ r β G hG lam κ κ' t c₃ c₁ hκ h₁ h₂ h₃
  subst hκ
  have pull : ∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (s' : S' ⟶ Sp (cycAway n)) (f : S' ⟶ S), f ≫ s = s' →
      ∀ c : SiegPre g n (zetaAway n) s, c.Principal →
        ∃ c' : SiegPre g n (zetaAway n) s', SiegPB c' c f ∧ c'.Principal := by
    intro S S' s s' f hf c hc
    have hf' : f ≫ s = s' ≫ spMap (RingHom.id (cycAway n)) := by rw [spMap_id', Category.comp_id]; exact hf
    have pr := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S S' s s' f rfl hf'
    obtain ⟨c', hcc⟩ := pr.1 c
    exact ⟨c', hcc, pr.2.1 c c' hcc hc⟩
  have base : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] (f : R →ₐ[K] R'),
      spMap f.toRingHom ≫ spMap ((algebraMap K R).comp β) = spMap ((algebraMap K R').comp β) := by
    intro R R' _ _ _ _ f
    rw [spMap_comp_spMap', ← RingHom.comp_assoc]
    congr 2
    ext x
    simp
  let Φ := TrivSqZeroExt.map (LinearMap.prod κ' (t • lam))
  let p₁ := TrivSqZeroExt.map (LinearMap.fst K K K)
  let p₂ := TrivSqZeroExt.map (LinearMap.snd K K K)
  let ι₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let sm := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)
  let mt := TrivSqZeroExt.map (t • LinearMap.id : K →ₗ[K] K)
  let cst : TrivSqZeroExt K (Fin r → K) →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let cD : DualNumber K →+* DualNumber K := (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have e1 : p₁.toRingHom.comp Φ.toRingHom = dirMap κ' := by
    ext x <;> simp [p₁, Φ, dirMap]
  have e2 : p₂.toRingHom.comp Φ.toRingHom = dirMap (t • lam) := by
    ext x <;> simp [p₂, Φ, dirMap]
  have e3 : mt.toRingHom.comp (dirMap lam) = dirMap (t • lam) := by
    ext x <;> simp [mt, dirMap]
  have e4 : mt.toRingHom.comp cst = cst := by
    ext x <;> simp [mt, cst]
  have e6 : p₁.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [p₁, ι₁]
  have e7 : p₂.toRingHom.comp ι₁.toRingHom = cD := by
    ext x <;> simp [p₂, ι₁, cD]
  have e8 : sm.toRingHom.comp Φ.toRingHom = dirMap (κ' + t • lam) := by
    ext x <;> simp [sm, Φ, dirMap]
  have e9 : sm.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [sm, ι₁]
  have e10 : cD.comp (dirMap κ') = cst := by
    ext x <;> simp [cD, cst, dirMap]
  have hconst : constPt (spMap (dirMap lam)) = spMap cst := by
    simp only [constPt, spMap_comp_spMap']
    congr 1
  obtain ⟨c', hc', hc'p⟩ := pull _ _ (spMap (dirMap κ')) (base (TrivSqZeroExt.map κ')) G hG
  obtain ⟨H, hH, hHp⟩ := pull _ _ (spMap Φ.toRingHom) (base Φ) G hG
  obtain ⟨H'', hH'', hH''p⟩ := pull _ _ (spMap ι₁.toRingHom) (base ι₁) c' hc'p
  obtain ⟨C1, hC1, -⟩ := pull _ (spMap p₁.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₁.toRingHom) rfl H hHp
  obtain ⟨C2, hC2, -⟩ := pull _ (spMap p₂.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₂.toRingHom) rfl H hHp
  have hC1G : SiegPB C1 G (spMap (dirMap κ')) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC1) (by rw [spMap_comp_spMap', e1])
  have hC1c' : SiegPB C1 c' (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq hC1G (by rw [Category.id_comp]))
  have hC1H'' : SiegPB C1 H'' (spMap p₁.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC1c' (by rw [spMap_comp_spMap', e6, spMap_id']))
  have hC2G : SiegPB C2 G (spMap (dirMap (t • lam))) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC2) (by rw [spMap_comp_spMap', e2])
  have h₂' : SiegPB c₃ G (spMap cst) := pbEq h₂ hconst
  have hC2m : SiegPB C2 c₃ (spMap mt.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel h₁ (pbEq hC2G (by rw [spMap_comp_spMap', e3]))
  have hC2Gc : SiegPB C2 G (spMap cst) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp h₂' hC2m) (by rw [spMap_comp_spMap', e4])
  have hC2c₃ : SiegPB C2 c₃ (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel h₂' (pbEq hC2Gc (by rw [Category.id_comp]))
  have hc₃c' : SiegPB c₃ c' (spMap cD) :=
    GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq h₂' (by rw [spMap_comp_spMap', e10]))
  have hC2c' : SiegPB C2 c' (spMap cD) := pbEq (GlobalTheory.SiegelPullComp.pb_comp hc₃c' hC2c₃) (by rw [Category.id_comp])
  have hC2H'' : SiegPB C2 H'' (spMap p₂.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC2c' (by rw [spMap_comp_spMap', e7]))
  have hpb := GlobalTheory.T.trivial_square_zero_extension_pullback K (K × K) K K (LinearMap.fst K K K) (LinearMap.snd K K K)
    ⟨fun a b hab => by simpa using hab, fun y => ⟨y, by simp⟩⟩
  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hHH : SiegPB H'' H (𝟙 _) :=
    GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n h3 hodd (CommRingCat.of (TrivSqZeroExt K (K × K))) (CommRingCat.of (DualNumber K))
      (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _ hpb (isLocalRing_sq K) (isArtinianRing_sq K)
      hsurj hsurj (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (K × K))).comp β)) H H'' C1 C2 hHp hH''p
      hC1 hC1H'' hC2 hC2H''
  have hc₁H : SiegPB c₁ H (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH (pbEq h₃ (by rw [spMap_comp_spMap', e8]))
  have hc₁H'' : SiegPB c₁ H'' (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hHH (pbEq hc₁H (by rw [Category.comp_id]))
  have hc₁c' : SiegPB c₁ c' (𝟙 _) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH'' hc₁H'') (by rw [spMap_comp_spMap', e9, spMap_id'])
  exact pbEq (GlobalTheory.SiegelPullComp.pb_comp hc' hc₁c') (by rw [Category.id_comp])

end GlobalTheory.SiegTanShift
