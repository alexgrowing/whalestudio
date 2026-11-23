import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzEtDualOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPartStatement
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Glue

variable {p : ℕ}

def semiThrough {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) : SemiHom σ A' A :=
  (SemiHom.ofHom i).comp (s.comp (SemiHom.ofHom q))

@[simp] theorem semiThrough_app {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'}
    {G A : PDivGroup p k} (i : A' ⟶ G') (s : SemiHom σ G' G) (q : G ⟶ A) (n : ℕ) (a : A.A n) :
    (semiThrough i s q).app n a = i.app n (s.app n (q.app n a)) := rfl

theorem semiThrough_ofHom {k : Type} [CommRing k] {A' G' G A : PDivGroup p k} (i : A' ⟶ G') (f : G' ⟶ G)
    (q : G ⟶ A) : semiThrough i (SemiHom.ofHom f) q = SemiHom.ofHom (i ≫ f ≫ q) :=
  SemiHom.ext_apply fun _ _ => rfl

section Base

variable [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H)
    (g : H ⟶ K) (m : B.M K hK) : B.map hG hK (f ≫ g) m = B.map hG hH f (B.map hH hK g m) :=
  B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g)) (fun _ _ => rfl) m

theorem eq_zero_of_id_eq_zero {G : PDivGroup p k} (hG : P k G) (h0 : 𝟙 G = 0) (m : B.M G hG) : m = 0 := by
  have h := B.smap_add hG hG 0 0 m
  rw [add_zero] at h
  have h2 : B.smap hG hG (SemiHom.ofHom 0) m = 0 := by simpa using h
  rw [← B.smap_id G hG m, h0]
  exact h2

theorem rigExtMap_rigExtMap {k : Type} [CommRing k] {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Z.RigExt) : rigExtMap f (rigExtMap g x) = rigExtMap (f ≫ g) x := by
  rw [rigExtMap_comp]; rfl

theorem rigExtMap_zero' {X Y : PDivGroup p k} : rigExtMap (0 : X ⟶ Y) = 0 := by
  have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
  rw [add_zero] at h
  simpa using h

theorem rig_split₀ {G G₀ G₁ : PDivGroup p k} (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₀ : i₀ ≫ q₀ = 𝟙 G₀) (z : i₀ ≫ q₁ = 0) (r₀ : G₀.RigExt) (r₁ : G₁.RigExt) :
    rigExtMap i₀ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₀ := by
  rw [LinearMap.map_add, rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₀, z, rigExtMap_zero', rigExtMap_id]
  simp

theorem rig_split₁ {G G₀ G₁ : PDivGroup p k} (i₁ : G₁ ⟶ G) (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (h₁ : i₁ ≫ q₁ = 𝟙 G₁) (z : i₁ ≫ q₀ = 0) (r₀ : G₀.RigExt) (r₁ : G₁.RigExt) :
    rigExtMap i₁ (rigExtMap q₀ r₀ + rigExtMap q₁ r₁) = r₁ := by
  rw [LinearMap.map_add, rigExtMap_rigExtMap, rigExtMap_rigExtMap, h₁, z, rigExtMap_zero', rigExtMap_id]
  simp

def redSum {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] G₀.RigExt) (r₁ : M₁ →ₛₗ[τ] G₁.RigExt) : M₀ × M₁ →ₛₗ[τ] G.RigExt :=
  ((rigExtMap q₀).comp r₀).comp (LinearMap.fst W M₀ M₁) + ((rigExtMap q₁).comp r₁).comp (LinearMap.snd W M₀ M₁)

theorem redSum_apply {W : Type} [CommRing W] (τ : W →+* k) {M₀ M₁ : Type} [AddCommGroup M₀] [Module W M₀]
    [AddCommGroup M₁] [Module W M₁] {G G₀ G₁ : PDivGroup p k} (q₀ : G ⟶ G₀) (q₁ : G ⟶ G₁)
    (r₀ : M₀ →ₛₗ[τ] G₀.RigExt) (r₁ : M₁ →ₛₗ[τ] G₁.RigExt) (m : M₀ × M₁) :
    redSum τ q₀ q₁ r₀ r₁ m = rigExtMap q₀ (r₀ m.1) + rigExtMap q₁ (r₁ m.2) := rfl

theorem rig_semiThrough {k' : Type} [CommRing k'] {σ : k →+* k'} {G' A' : PDivGroup p k'} {G A : PDivGroup p k}
    (i : A' ⟶ G') (q' : G' ⟶ A') (s : SemiHom σ G' G) (q : G ⟶ A)
    (h : ∀ n a, q'.app n (i.app n (s.app n (q.app n a))) = s.app n (q.app n a)) (r : A.RigExt) :
    rigExtMap q' ((semiThrough i s q).rig r) = s.rig (rigExtMap q r) := by
  rw [← SemiHom.ofHom_rig, ← SemiHom.ofHom_rig, SemiHom.rig_rig (semiThrough i s q) (SemiHom.ofHom q') (s.comp (SemiHom.ofHom q))
    (fun n a => (h n a).symm)]
  exact SemiHom.comp_rig _ _ _

end Base

theorem exists_katz_etDual : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn))
    (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc →
    ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  intro p _ Bc Be hK hE
  choose G₀ G₁ i₀ q₀ i₁ q₁ hc he h₀ h₁ hs using
    fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) =>
      GlobalTheory.PDivGroup.exists_isConn_isEt_splitting p k G
  have rz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (X Y : PDivGroup p k),
      rigExtMap (0 : X ⟶ Y) = 0 := by
    intro k _ _ _ X Y
    have h := (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) X Y).1 0 0
    rw [add_zero] at h
    simpa using h
  let D : Base p (fun _ _ _ => True) :=
  { M := fun {k} _ _ _ G _ =>
      ModuleCat.of (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G))
    smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s =>
      (Bc.smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))).prodMap
        (Be.smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)))
    red := fun {k} _ _ _ G _ =>
      redSum _ (q₀ k G) (q₁ k G) (Bc.red (G₀ k G) (hc k G)) (Be.red (G₁ k G) (he k G))
    free := fun {k} _ _ _ G _ => by
      haveI := Bc.free (G₀ k G) (hc k G)
      haveI := Be.free (G₁ k G) (he k G)
      exact (inferInstance : Module.Free (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    finite := fun {k} _ _ _ G _ => by
      haveI := Bc.finite (G₀ k G) (hc k G)
      haveI := Be.finite (G₁ k G) (he k G)
      exact (inferInstance : Module.Finite (WittVector p k) (Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)))
    red_surjective := fun {k} _ _ _ G _ x => by
      obtain ⟨m₀, e₀⟩ := Bc.red_surjective (G₀ k G) (hc k G) (rigExtMap (i₀ k G) x)
      obtain ⟨m₁, e₁⟩ := Be.red_surjective (G₁ k G) (he k G) (rigExtMap (i₁ k G) x)
      refine ⟨(m₀, m₁), ?_⟩
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = x
      rw [e₀, e₁, rigExtMap_rigExtMap, rigExtMap_rigExtMap, ← LinearMap.add_apply, ← (rigExtMap_add_and_natCast_smul_id p k (CharP.cast_eq_zero k p) G G).1,
        hs, rigExtMap_id, LinearMap.id_apply]
    red_eq_zero := fun {k} _ _ _ G _ m => by
      obtain ⟨m₀, m₁⟩ := m
      have ke₀ := Bc.red_eq_zero (G₀ k G) (hc k G) m₀
      have ke₁ := Be.red_eq_zero (G₁ k G) (he k G) m₁
      have z01 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).1 (i₀ k G ≫ q₁ k G)
      have z10 := (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) (G₁ k G) (hc k G) (he k G)).2 (i₁ k G ≫ q₀ k G)
      change rigExtMap (q₀ k G) (Bc.red _ _ m₀) + rigExtMap (q₁ k G) (Be.red _ _ m₁) = 0 ↔ _
      constructor
      · intro h
        have a₀ := (rig_split₀ (i₀ k G) (q₀ k G) (q₁ k G) (h₀ k G) z01 _ _).symm.trans
          ((congrArg (rigExtMap (i₀ k G)) h).trans (map_zero _))
        have a₁ := (rig_split₁ (i₁ k G) (q₀ k G) (q₁ k G) (h₁ k G) z10 _ _).symm.trans
          ((congrArg (rigExtMap (i₁ k G)) h).trans (map_zero _))
        obtain ⟨n₀, e₀⟩ := ke₀.1 a₀
        obtain ⟨n₁, e₁⟩ := ke₁.1 a₁
        exact ⟨(n₀, n₁), Prod.ext e₀ e₁⟩
      · rintro ⟨n, h⟩
        have h' : ((m₀, m₁) : Bc.M (G₀ k G) (hc k G) × Be.M (G₁ k G) (he k G)) = (p • n.1, p • n.2) := h
        obtain ⟨e₀, e₁⟩ := Prod.ext_iff.1 h'
        exact (congrArg₂ (fun a b => rigExtMap (q₀ k G) a + rigExtMap (q₁ k G) b) (ke₀.2 ⟨n.1, e₀⟩)
          (ke₁.2 ⟨n.2, e₁⟩)).trans (by simp)
    smap_smul := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s a m =>
      Prod.ext (Bc.smap_smul (hc k' G') (hc k G) _ a m.1) (Be.smap_smul (he k' G') (he k G) _ a m.2)
    smap_id := fun {k} _ _ _ G _ m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (𝟙 G)) (q₀ k G)) m.1 = m.1
        rw [semiThrough_ofHom, Category.id_comp, h₀]
        exact Bc.smap_id _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (𝟙 G)) (q₁ k G)) m.2 = m.2
        rw [semiThrough_ofHom, Category.id_comp, h₁]
        exact Be.smap_id _ _ _
    smap_add := fun {k} _ _ _ G H _ _ f g m => by
      refine Prod.ext ?_ ?_
      · change Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom (f + g)) (q₀ k H)) m.1 =
          Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom f) (q₀ k H)) m.1 +
            Bc.smap _ _ (semiThrough (i₀ k G) (SemiHom.ofHom g) (q₀ k H)) m.1
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Bc.smap_add _ _ _ _ _
      · change Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom (f + g)) (q₁ k H)) m.2 =
          Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom f) (q₁ k H)) m.2 +
            Be.smap _ _ (semiThrough (i₁ k G) (SemiHom.ofHom g) (q₁ k H)) m.2
        rw [semiThrough_ofHom, semiThrough_ofHom, semiThrough_ofHom, Preadditive.add_comp, Preadditive.comp_add]
        exact Be.smap_add _ _ _ _ _
    smap_comp := fun {k k' k''} _ _ _ _ _ _ _ _ _ {σ τ υ G'' G' G} _ _ _ s t u hu m => by
      refine Prod.ext ?_ ?_
      · refine Bc.smap_comp (hc k'' G'') (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G))
          (semiThrough (i₀ k'' G'') t (q₀ k' G')) (semiThrough (i₀ k'' G'') u (q₀ k G)) (fun n a => ?_) m.1
        have e := GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
      · refine Be.smap_comp (he k'' G'') (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G))
          (semiThrough (i₁ k'' G'') t (q₁ k' G')) (semiThrough (i₁ k'' G'') u (q₁ k G)) (fun n a => ?_) m.2
        have e := GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
          (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a
        simp only [SemiHom.comp_app, SemiHom.ofHom_app] at e
        simp only [semiThrough_app, hu, e]
    red_smap := fun {k k'} _ _ _ _ _ _ {σ G' G} _ _ s m => by
      have c₀ := rig_semiThrough (i₀ k' G') (q₀ k' G') s (q₀ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₀ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G') (s.comp (SemiHom.ofHom (q₀ k G))) n a)
      have c₁ := rig_semiThrough (i₁ k' G') (q₁ k' G') s (q₁ k G) (fun n a =>
        GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G') (G₁ k G) (i₀ k' G') (q₀ k' G')
                     (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G') (s.comp (SemiHom.ofHom (q₁ k G))) n a)
      obtain ⟨m₀, m₁⟩ := m
      have a := Bc.red_smap (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) m₀
      have b := Be.red_smap (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) m₁
      refine (redSum_apply _ _ _ _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg s.rig (redSum_apply _ _ _ _ _ _)).symm
      refine Eq.trans ?_ (map_add s.rig _ _).symm
      exact congrArg₂ (· + ·) ((congrArg (rigExtMap (q₀ k' G')) a).trans (c₀ _))
        ((congrArg (rigExtMap (q₁ k' G')) b).trans (c₁ _)) }
  have qz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₁ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k G (G₁ k G) hG (he k G)).1 _
  have id1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      𝟙 (G₁ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₁ k G, qz k G hG, Limits.comp_zero]
  have qi0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      q₀ k G ≫ i₀ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [qz k G hG, Limits.zero_comp, add_zero] at this
  have iz : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₀ k G = 0 := fun k _ _ _ G hG => (hom_eq_zero_of_isConn_of_isEt p k (G₀ k G) G (hc k G) hG).2 _
  have id0 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      𝟙 (G₀ k G) = 0 := by
    intro k _ _ _ G hG
    rw [← h₀ k G, iz k G hG, Limits.comp_zero]
  have qi1 : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt →
      q₁ k G ≫ i₁ k G = 𝟙 G := by
    intro k _ _ _ G hG
    have := hs k G
    rwa [iz k G hG, Limits.zero_comp, zero_add] at this
  refine ⟨D, katz_etDual_of_iso p Bc Be D hK hE ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Bc.map h (hc k G) (q₀ k G)).comp (LinearMap.fst _ _ _))
      ((LinearMap.inl _ _ _).comp (Bc.map (hc k G) h (i₀ k G)))
      (LinearMap.ext fun m => (map_comp Bc h (hc k G) h (q₀ k G) (i₀ k G) m).symm.trans (by
        rw [qi0 k G h]; exact Bc.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        ((map_comp Bc (hc k G) h (hc k G) (i₀ k G) (q₀ k G) m.1).symm.trans (by
          rw [h₀ k G]; exact Bc.smap_id _ _ m.1))
        (eq_zero_of_id_eq_zero Be (he k G) (id1 k G h) m.2).symm), ?_⟩
    ⟨fun {k} _ _ _ G h => LinearEquiv.ofLinearMap
      ((Be.map h (he k G) (q₁ k G)).comp (LinearMap.snd _ _ _))
      ((LinearMap.inr _ _ _).comp (Be.map (he k G) h (i₁ k G)))
      (LinearMap.ext fun m => (map_comp Be h (he k G) h (q₁ k G) (i₁ k G) m).symm.trans (by
        rw [qi1 k G h]; exact Be.smap_id G h m))
      (LinearMap.ext fun m => Prod.ext
        (eq_zero_of_id_eq_zero Bc (hc k G) (id0 k G h) m.1).symm
        ((map_comp Be (he k G) h (he k G) (i₁ k G) (q₁ k G) m.2).symm.trans (by
          rw [h₁ k G]; exact Be.smap_id _ _ m.2))), ?_⟩⟩
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Bc.smap_comp h' (hc k' G') (hc k G) (semiThrough (i₀ k' G') s (q₀ k G)) (SemiHom.ofHom (q₀ k' G'))
      (s.comp (SemiHom.ofHom (q₀ k G))) (fun n a => (GlobalTheory.T.semilinearHom_connected_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₀ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (he k' G') (hc k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₀ k G))) n a).symm) m.1).symm.trans
      (Bc.smap_comp h' h (hc k G) (SemiHom.ofHom (q₀ k G)) s (s.comp (SemiHom.ofHom (q₀ k G)))
        (fun _ _ => rfl) m.1)
  · intro k k' _ _ _ _ _ _ σ G' G h' h s m
    exact (Be.smap_comp h' (he k' G') (he k G) (semiThrough (i₁ k' G') s (q₁ k G)) (SemiHom.ofHom (q₁ k' G'))
      (s.comp (SemiHom.ofHom (q₁ k G))) (fun n a => (GlobalTheory.T.semilinearHom_etale_factor_through_part p k k' _ G' (G₀ k' G') (G₁ k' G')
        (G₁ k G) (i₀ k' G') (q₀ k' G') (i₁ k' G') (q₁ k' G') (hc k' G') (he k G) (hs k' G')
        (s.comp (SemiHom.ofHom (q₁ k G))) n a).symm) m.2).symm.trans
      (Be.smap_comp h' h (he k G) (SemiHom.ofHom (q₁ k G)) s (s.comp (SemiHom.ofHom (q₁ k G)))
        (fun _ _ => rfl) m.2)

end GlobalTheory.Dieu.Glue
