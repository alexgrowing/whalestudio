import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ObjDesc

open GlobalTheory.ObjPull

theorem exists_geomPt_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [LocallyOfFiniteType π] [Surjective π]
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) : ∃ y : Sp k ⟶ X, y ≫ π = x := by

  have hJ := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (IsLocalRing.closedPoint k)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem (Set.mem_univ p))
    isOpen_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  have hpt := pointOfClosedPoint_comp (pullback.snd π x) c hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc' ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hpt, Category.id_comp]

section Sections

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem secPull_injective [Epi f] (h : IsGrpPullback G' G f φ) : Function.Injective (secPull h) := by
  intro e₁ e₂ he
  have key : f ≫ e₁.left = f ≫ e₂.left := by
    rw [← secPull_left h e₁, ← secPull_left h e₂, he]
  exact Over.OverMorphism.ext ((cancel_epi f).1 key)

theorem secPull_eq (h : IsGrpPullback G' G f φ) {e : 𝟙_ (Over S) ⟶ G} {e' : 𝟙_ (Over S') ⟶ G'}
    (he : e'.left ≫ φ = f ≫ e.left) : secPull h e = e' := by

  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [secPull_left, he]
  · exact (Over.w _).trans (Over.w e').symm

theorem exists_sec [Epi f] (h : IsGrpPullback G' G f φ) (e' : 𝟙_ (Over S') ⟶ G') (g : S ⟶ G.left)
    (hg : f ≫ g = e'.left ≫ φ) : ∃ e : 𝟙_ (Over S) ⟶ G, e'.left ≫ φ = f ≫ e.left := by

  have hsec : g ≫ G.hom = (𝟙_ (Over S)).hom := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hg, Category.assoc, h.1.w, ← Category.assoc, Over.w e']
    simp
  exact ⟨Over.homMk g hsec, hg.symm⟩

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X Y : Scheme.{0}}
  {s : Y ⟶ Sp B} {s' : X ⟶ Sp B'} {π : X ⟶ Y}

def descend [Epi π] [LocallyOfFiniteType π] [Surjective π] (j : B →+* B') (hρ : j b.ρ = b'.ρ) (hζ : j b.ζ = b'.ζ)
    (hs : π ≫ s = s' ≫ spMap j) (o : Obj D l b' s') (t : SAB H Y) (m : SABMap o.t t π)
    (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (e eA : D.La → (𝟙_ (Over Y) ⟶ t.G)) (he : ∀ a, secPull m.cart (e a) = o.eta a)
    (heA : ∀ a, secPull m.cart (eA a) = o.etaA a) : Obj D l b s where
  t := t
  proper := hp
  ample := ha
  ktriv := hk
  eta := e
  eta_add a c := secPull_injective m.cart (by rw [map_mul, he, he, he, o.eta_add])
  eta_ker a h := secPull_injective m.cart (by rw [map_one, he, o.eta_ker a h])
  etaA := eA
  etaA_add a c := secPull_injective m.cart (by rw [map_mul, heA, heA, heA, o.etaA_add])
  etaA_ker a := secPull_injective m.cart (by rw [map_one, heA, o.etaA_ker a])
  geom k _ _ x β hx := by
    obtain ⟨y, rfl⟩ := exists_geomPt_lift π k x
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, y ≫ s' = spMap β' :=
      ⟨(Spec.preimage (y ≫ s')).hom, (Spec.map_preimage _).symm⟩
    obtain rfl : β = β'.comp j := by
      have : spMap β = spMap (β'.comp j) := by
        rw [← hx, Category.assoc, hs, ← Category.assoc, hβ', spMap_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have hL : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := by
      obtain ⟨w, hw, -⟩ := m.lin
      exact ⟨w, hw⟩
    obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k y β' hβ'
    rw [RingHom.comp_apply, RingHom.comp_apply, hρ, hζ]
    refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk y)).symm (fun c g => ?_) (fun n g g' c hc => ?_) I,
      hI, fun a => ?_, fun a ha => ?_⟩
    · rw [← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ,
        ← GlobalTheory.LiePull.lieMult_pull _ Y X t.G o.t.G π m.cm.F t.act o.t.act m.cart m.act k y τ]
      exact hdet τ
    · obtain ⟨g, rfl⟩ := (pushEquiv m.cart (Over.mk y)).surjective g
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, ← m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X t.G o.t.G π m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB m.cart hL
        (Over.mk y) n _ _ g g' _ (pushEquiv_symm_left m.cart (Over.mk y) g).symm
        (pushEquiv_symm_left m.cart (Over.mk y) g').symm).1 hc
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [heA, hA]
      rfl
    · refine (pushEquiv_secPull m.cart (Over.mk y) _).symm.trans ?_
      rw [he, hM a ha]
      rfl

def lowerBase {l₂ : Level H} (h : l.Dvd l₂) (b₂ : Base l₂ B') : Base l B' where
  unit := b₂.unit
  ρ := b₂.ρ
  ρ_sq := b₂.ρ_sq
  ζ := b₂.ζ ^ (l₂.A / l.A)
  ζ_prim := b₂.ζ_prim.pow l₂.A_pos (Nat.div_mul_cancel h.2.2).symm

end GlobalTheory.ObjDesc

theorem GlobalTheory.obj_descend_lower_level : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B B₂ : Type) [CommRing B] [CommRing B₂] (b : Base l B) (b₂ : Base l₂ B₂) (j : B →+* B₂) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp B) (s₂ : X ⟶ Sp B₂) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ob₂ : Obj D l₂ b₂ s₂) (ν : Ga → (ob₂.t.G.left ⟶ ob₂.t.G.left)) (t' : SAB H Y) (m : SABMap ob₂.t t' π), l.Dvd l₂ → j b.ρ = b₂.ρ → j b.ζ = b₂.ζ ^ (l₂.A / l.A) → π ≫ s = s₂ ≫ spMap j → IsGaloisCover Ga ρ π → (∀ a, ν a ≫ m.φ = m.φ) → (∀ a, Lowers l ob₂ (fun x => ob₂.eta x ^ (l₂.M / l.M)) (fun x => ob₂.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∃ (ob : Obj D l b s) (m' : SABMap ob₂.t ob.t π), (∀ a, (ob₂.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = π ≫ (ob.eta a).left) ∧ ∀ a, (ob₂.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = π ≫ (ob.etaA a).left := by
  intro _ _ E _ _ _ H D l l₂ B B₂ _ _ b b₂ j X Y π s s₂ Ga _ ρ ob₂ ν t' m hdvd hρ hζ hs hG hν hlow hp ha hk

  have : Epi π := ⟨fun g₁ g₂ hg => (hG.existsUnique_desc (π ≫ g₁)
    (fun a => by rw [← Category.assoc, hG.inv])).unique rfl hg.symm⟩
  have : IsFinite π := hG.fin
  have : Surjective π := hG.onto

  let o := GlobalTheory.ObjLower.lower (b := GlobalTheory.ObjDesc.lowerBase hdvd b₂) ob₂ hdvd rfl rfl

  have desc : ∀ u : D.La → (𝟙_ (Over X) ⟶ ob₂.t.G), (∀ c a, ρ c ≫ (u a).left = (u a).left ≫ ν c) →
      ∃ w : D.La → (𝟙_ (Over Y) ⟶ t'.G), ∀ a, (u a).left ≫ m.φ = π ≫ (w a).left := by
    intro u hu
    have hex : ∀ a, ∃ w : 𝟙_ (Over Y) ⟶ t'.G, (u a).left ≫ m.φ = π ≫ w.left := by
      intro a
      obtain ⟨g, hg, -⟩ := hG.existsUnique_desc ((u a).left ≫ m.φ)
        (fun c => by rw [← Category.assoc, hu c a, Category.assoc, hν c])
      exact GlobalTheory.ObjDesc.exists_sec m.cart (u a) g hg
    exact ⟨fun a => (hex a).choose, fun a => (hex a).choose_spec⟩
  obtain ⟨e, he⟩ := desc (fun a => ob₂.eta a ^ (l₂.M / l.M)) (fun c a => ((hlow c).1 a).symm)
  obtain ⟨eA, heA⟩ := desc (fun a => ob₂.etaA a ^ (l₂.A / l.A)) (fun c a => ((hlow c).2 a).symm)
  exact ⟨GlobalTheory.ObjDesc.descend (b' := GlobalTheory.ObjDesc.lowerBase hdvd b₂) j hρ hζ hs o t' m hp ha hk e eA
    (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (he a)) (fun a => GlobalTheory.ObjDesc.secPull_eq m.cart (heA a)),
    m, he, heA⟩

end
