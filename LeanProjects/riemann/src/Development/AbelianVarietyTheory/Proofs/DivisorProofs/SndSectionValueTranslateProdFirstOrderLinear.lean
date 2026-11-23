import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSLin

theorem valR_eq_evAt {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR x U f = GlobalTheory.TanDeriv.evAt x U h f := dif_pos h

theorem valR_spMap_comp {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) {Y : Scheme.{0}} (x : Sp R ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Y, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  rw [valR_eq_evAt x U h, valR_eq_evAt _ U (GlobalTheory.TanDeriv.comp_top_le φ x U h)]
  exact GlobalTheory.TanDeriv.evAt_comp φ x U h _ f

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]

theorem top_le_of_fst (z : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left) ⁻¹ᵁ O) :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine GlobalTheory.TanDeriv.top_le_of_comp (TrivSqZeroExt.fstHom S S S).toRingHom ?_ ?_ _ O h
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]

theorem fst_comp_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (z : overAt x0 (DualNumber S) ⟶ G)
    (hz : smT x0 0 z = g') : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ z.left = g₀ := by
  have h1 : (smT x0 0 z).left = spMap (epsMul 0) ≫ z.left := rfl
  have h2 := congrArg (fun φ => spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ φ) (hz ▸ h1)
  rw [hg, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap] at h2
  have e1 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext; simp
  have e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul (0 : S)) =
      (TrivSqZeroExt.fstHom S S S).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  rw [e1, e2] at h2
  rw [← h2]
  simp [spMap]

theorem smT_const (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (a : S) : smT x0 a g' = g' := by
  apply Over.OverMorphism.ext
  have h1 : (smT x0 a g').left = spMap (epsMul a) ≫ g'.left := rfl
  rw [h1, hg, ← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun x => by simp [epsMul]

theorem valR_smT (a : S) (w : overAt x0 (DualNumber S) ⟶ G) (O : G.left.Opens)
    (hw : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from w.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (smT x0 a w).left O f).snd = a * (valR w.left O f).snd := by
  have h1 : (smT x0 a w).left = spMap (epsMul a) ≫ w.left := rfl
  rw [h1, valR_spMap_comp _ _ O hw f]
  simp [epsMul]

theorem valR_const_snd (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : (valR g'.left O f).snd = 0 := by
  rw [hg, valR_spMap_comp _ _ O hO f]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_valR_mul (u v : overAt x0 (DualNumber S) ⟶ G) (hv0 : smT x0 0 v = 1) (O : G.left.Opens)
    (hu : ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from u.left) ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (u * v).left O f).snd = (valR u.left O f).snd + (valR (smT x0 0 u * v).left O f).snd := by
  have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
  let P : overAt x0 (TrivSqZeroExt S (S × S)) ⟶ G :=
    (homAt x0 (tm (LinearMap.inl S S S)) ≫ u) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)
  have e1 : homAt x0 (tm (LinearMap.fst S S S)) ≫ P = u := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    change _ * smT x0 0 v = _
    rw [hv0, _root_.mul_one]
  have e2 : homAt x0 (tm (LinearMap.snd S S S)) ≫ P = smT x0 0 u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz, TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
    rfl
  have e3 : homAt x0 (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S)) ≫ P = u * v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
      LinearMap.coprod_inl, LinearMap.coprod_inr, TrivSqZeroExt.map_id, homAt_id, Category.id_comp,
      Category.id_comp]
  have f1 : spMap (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = u.left :=
    congrArg (fun φ => φ.left) e1
  have f2 : spMap (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left =
      (smT x0 0 u * v).left :=
    congrArg (fun φ => φ.left) e2
  have f3 : spMap (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) ≫ P.left = (u * v).left :=
    congrArg (fun φ => φ.left) e3
  have hP : ⊤ ≤ (show Sp (TrivSqZeroExt S (S × S)) ⟶ G.left from P.left) ⁻¹ᵁ O := by
    refine GlobalTheory.TanDeriv.top_le_of_comp
      (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) ?_ ?_ _ O ?_
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · exact f1 ▸ hu
  have k1 := valR_spMap_comp (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k2 := valR_spMap_comp (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  have k3 := valR_spMap_comp (tm (LinearMap.coprod LinearMap.id LinearMap.id : S × S →ₗ[S] S) :
      TrivSqZeroExt S (S × S) →+* DualNumber S) P.left O hP f
  rw [f1] at k1
  rw [f2] at k2
  rw [f3] at k3
  rw [k1, k2, k3]
  simp

theorem top_le_of_smT_zero (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (z : overAt x0 (DualNumber S) ⟶ G) (hz : smT x0 0 z = g') :
    ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from z.left) ⁻¹ᵁ O := by
  refine top_le_of_fst z O ?_
  rw [fst_comp_of_smT_zero g₀ g' hg z hz]
  exact hO

theorem snd_sectionValue_translate_list_prod_induction (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G)
    (hg : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀) (O : G.left.Opens) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (f : Γ(G.left, O)) : ∀ (m : ℕ) (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S),
    (∀ c, smT x0 0 (y c) = 1) →
    smT x0 0 (List.ofFn fun c => smT x0 (r c) (y c)).prod = 1 ∧
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  have hg0 : smT x0 0 g' = g' := smT_const g₀ g' hg 0
  intro m
  induction m with
  | zero =>
    intro y r _
    rw [List.ofFn_zero, List.prod_nil, smT_one', _root_.mul_one, valR_const_snd g₀ g' hg O hO f]
    simp
  | succ n ih =>
    intro y r hy
    obtain ⟨h0, hs⟩ := ih (fun c => y c.succ) (fun c => r c.succ) (fun c => hy c.succ)
    have ha : smT x0 0 (smT x0 (r 0) (y 0)) = 1 := by rw [smT_smT, zero_mul, hy 0]
    rw [List.ofFn_succ, List.prod_cons]
    refine ⟨by rw [smT_mul, ha, h0, _root_.mul_one], ?_⟩
    have hu : smT x0 0 (g' * smT x0 (r 0) (y 0)) = g' := by rw [smT_mul, hg0, ha, _root_.mul_one]
    have hy0 : smT x0 0 (g' * y 0) = g' := by rw [smT_mul, hg0, hy 0, _root_.mul_one]
    have hgy : g' * smT x0 (r 0) (y 0) = smT x0 (r 0) (g' * y 0) := by
      rw [smT_mul, smT_const g₀ g' hg]
    rw [← _root_.mul_assoc, snd_valR_mul _ _ h0 O (top_le_of_smT_zero g₀ g' hg O hO _ hu) f, hu, hs, hgy,
      valR_smT _ _ O (top_le_of_smT_zero g₀ g' hg O hO _ hy0) f, Fin.sum_univ_succ]

theorem snd_valR_translate_prod : ∀ {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G]
    (g₀ : Sp S ⟶ G.left) (g' : overAt x0 (DualNumber S) ⟶ G),
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ →
    ∀ {m : ℕ} (y : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (r : Fin m → S), (∀ c, smT x0 0 (y c) = 1) →
    ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O →
    (valR (g' * (List.ofFn fun c => smT x0 (r c) (y c)).prod).left O f).snd =
      ∑ c, r c * (valR (g' * y c).left O f).snd := by
  intro X0 S _ x0 G _ g₀ g' hg m y r hy O f hO
  exact (snd_sectionValue_translate_list_prod_induction g₀ g' hg O hO f m y r hy).2

end GlobalTheory.KSLin
