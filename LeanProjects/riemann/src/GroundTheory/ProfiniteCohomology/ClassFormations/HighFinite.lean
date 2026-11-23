import Mathlib
import GroundTheory.TateCohomology.TateCup
import GroundTheory.TateCohomology.CupTateShift
import GroundTheory.TateCohomology.CupTateNatural
import GroundTheory.TateCohomology.CupFunctorial
import GroundTheory.TateCohomology.Annihilation
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.GroupCoh

open CategoryTheory MonoidalCategory groupCohomology Rep

section Top

variable {k : Type} [CommRing k] {Γ : Type} [Group Γ]

abbrev topHom (Γ : Type) [Group Γ] : Γ →* (⊤ : Subgroup Γ) :=
  (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom

def topBackHom (A : Rep k Γ) : res (topHom Γ) (res (⊤ : Subgroup Γ).subtype A) ⟶ A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def topBackTrivialHom : res (topHom Γ) (Rep.trivial k (⊤ : Subgroup Γ) k) ⟶ Rep.trivial k Γ k :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem map_topBackHom_map_subtype (A : Rep k Γ) (n : ℕ) (x : groupCohomology A n) :
    map (topHom Γ) (topBackHom A) n (map (⊤ : Subgroup Γ).subtype (𝟙 _) n x) = x := by
  have h := map_comp (⊤ : Subgroup Γ).subtype (topHom Γ) (𝟙 (res (⊤ : Subgroup Γ).subtype A))
    (topBackHom A) n
  have h' : map ((⊤ : Subgroup Γ).subtype.comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (𝟙 (res (⊤ : Subgroup Γ).subtype A)) ≫ topBackHom A) n =
      map (MonoidHom.id Γ) (𝟙 A) n :=
    map_congr (MonoidHom.ext fun _ => rfl) rfl n
  rw [h', map_id] at h
  exact (congrArg (fun f => f.hom x) h).symm

theorem topBack_rightUnitor (A : Rep k Γ) :
    ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype A)).hom ≫
        topBackHom A).hom.toLinearMap =
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom A) topBackTrivialHom) ≫
        (ρ_ A).hom).hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end Top

section Tate

variable {Γ : Type} [Group Γ] [Fintype Γ] (M : Rep ℤ Γ) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup Γ, Limits.IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup Γ,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

omit [Fintype Γ] in

theorem tateIsoH_map_apply' {X Y : Rep ℤ Γ} [Fintype Γ] (φ : X ⟶ Y) {p : ℤ} (n : ℕ) [NeZero n]
    (hp : p = n) (x : tateCohomology X p) :
    (tateIsoH Y p n hp).hom.hom (((tateCohomologyFunctor p).map φ).hom x) =
      groupCohomology.map (MonoidHom.id Γ) φ n ((tateIsoH X p n hp).hom.hom x) := by
  subst hp
  exact tateIsoH_map_apply φ n x

include h1 h2 h3

theorem exists_cupH_top (n : ℕ) [NeZero n] [Fintype (⊤ : Subgroup Γ)]
    (x : groupCohomology (res (⊤ : Subgroup Γ).subtype M) (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id _) (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)
        (cupH (add_comm 2 n) (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u)
          y) := by
  have hp : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  let T := tateTheoremIso M u h1 h2 h3 ⊤ (n : ℤ)
  let s : tateCohomology (res (⊤ : Subgroup Γ).subtype M) ((n : ℤ) + 2) :=
    (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv.hom x
  let y0 := T.inv.hom s
  refine ⟨(tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0,
    ⟨Fintype.card (⊤ : Subgroup Γ), Fintype.card_ne_zero, ?_⟩, ?_⟩
  · rw [← map_nsmul, card_smul_tateCohomology, map_zero]
  · have hs : T.hom.hom y0 = s := T.inv_hom_id_apply s
    have hx : x = (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).hom.hom s :=
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv_hom_id_apply x).symm
    rw [hx, ← hs, tateTheoremIso_hom_apply M u ⊤ h1 h2 h3 (n : ℤ) y0, tateIsoH_map_apply' _ _ hp]
    erw [tateIsoH_tateCup (show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num) rfl hp (add_comm 2 (n : ℤ))
        (add_comm 2 n)]
    exact congrArg (fun t => (groupCohomology.map (MonoidHom.id _)
      (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)) (cupH (add_comm 2 n) t
        ((tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0)))
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) 2 2 (by norm_num)).inv_hom_id_apply
        (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u))

theorem exists_cupH_of_tate (n : ℕ) [NeZero n] (x : groupCohomology M (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ Γ ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id Γ) (ρ_ M).hom (n + 2) (cupH (add_comm 2 n) u y) := by
  classical
  obtain ⟨y, ⟨m, hm, hmy⟩, hx⟩ := exists_cupH_top M u h1 h2 h3 n
    (map (⊤ : Subgroup Γ).subtype (𝟙 _) (n + 2) x)
  refine ⟨map (topHom Γ) topBackTrivialHom n y, ⟨m, hm, by rw [← map_nsmul, hmy, map_zero]⟩, ?_⟩
  have hback := map_topBackHom_map_subtype M (n + 2) x
  rw [hx] at hback
  rw [← hback]
  have e1 := map_comp (MonoidHom.id (⊤ : Subgroup Γ)) (topHom Γ)
    (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (topBackHom M) (n + 2)
  have e2 := map_comp (topHom Γ) (MonoidHom.id Γ)
    (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) (ρ_ M).hom (n + 2)
  have e3 : map ((MonoidHom.id (⊤ : Subgroup Γ)).comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom ≫ topBackHom M) (n + 2) =
      map ((topHom Γ).comp (MonoidHom.id Γ))
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) ≫
        (ρ_ M).hom) (n + 2) := by
    exact map_congr (MonoidHom.ext fun _ => rfl) (topBack_rightUnitor M) (n + 2)
  have e4 := congrArg (fun f => f.hom (cupH (add_comm 2 n)
    (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u) y)) (e1.symm.trans (e3.trans e2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e4
  rw [e4, map_resTensorHom_cupH, map_topBackHom_map_subtype]

end Tate

end GroundTheory.GroupCoh
