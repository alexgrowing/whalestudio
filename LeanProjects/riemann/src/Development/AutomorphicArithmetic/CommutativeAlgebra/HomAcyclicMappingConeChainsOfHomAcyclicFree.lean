import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicOfIsoOfIsZeroOfBiproduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

section Cone

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
  (comm : φ₁ ≫ b = a ≫ φ₂)

private theorem inl_map (n m : ℤ) (h : m + (-1) = n) :
    (mappingCone.inl φ₁).v m n h ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      a.f m ≫ (mappingCone.inl φ₂).v m n h := by
  simp [mappingCone.map, Cochain.zero_cochain_comp_v]

private theorem inr_map (n : ℤ) :
    (mappingCone.inr φ₁).f n ≫ (mappingCone.map φ₁ φ₂ a b comm).f n =
      b.f n ≫ (mappingCone.inr φ₂).f n := by
  simp [mappingCone.map]

private theorem map_fst (n m : ℤ) (h : n + 1 = m) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.fst φ₂).1.v n m h =
      (mappingCone.fst φ₁).1.v n m h ≫ a.f m := by
  rw [mappingCone.ext_from_iff φ₁ m n h]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n m (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

private theorem map_snd (n : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.snd φ₂).v n n (add_zero n) =
      (mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  rw [mappingCone.ext_from_iff φ₁ (n + 1) n rfl]
  constructor
  · rw [reassoc_of% (inl_map φ₁ φ₂ a b comm n (n + 1) (by omega))]
    simp
  · rw [reassoc_of% (inr_map φ₁ φ₂ a b comm n)]
    simp

end Cone

variable {B : Scheme.{0}}

private def famCh (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) : B.Etale ⥤ Cx (ZMod q) := G ⋙ sch ⋙ chains (ZMod q)

private def termIso (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (p : ℕ) :
    G ⋙ yoneda ⋙ free (ZMod q) ≅ famCh q G ⋙ HomologicalComplex.eval _ _ (-(p : ℤ)) :=
  NatIso.ofComponents (fun U => (chainsXIso (ZMod q) (sch.obj (G.obj U)) p).symm) (by
    intro U V a
    exact (GlobalTheory.EtC.HCTerms.chainsXIso_inv_map (ZMod q) (sch.map (G.map a)) p).symm)

private theorem famCh_good (q : ℕ) (G : B.Etale ⥤ Scheme.{0}) (h : Good (G ⋙ yoneda ⋙ free (ZMod q))) (n : ℤ) :
    Good (famCh q G ⋙ HomologicalComplex.eval _ _ n) := by
  obtain ⟨hiso, hzero, -⟩ := UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B
  rcases lt_or_ge 0 n with hn | hn
  · exact hzero _ fun U => GlobalTheory.EtC.HCTerms.isZero_chains_X (ZMod q) _ n hn
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact hiso _ _ ⟨termIso q G p⟩ h

private theorem cone_comm {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) {U V : B.Etale} (a : U ⟶ V) :
    (chains (ZMod q)).map (sch.map (F.app U)) ≫ (chains (ZMod q)).map (sch.map (G₂.map a)) =
      (chains (ZMod q)).map (sch.map (G₁.map a)) ≫ (chains (ZMod q)).map (sch.map (F.app V)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, F.naturality]

private def coneI₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inl ((chains (ZMod q)).map (sch.map (F.app U)))).v (n + 1) n (by omega)
  naturality U V a := (inl_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) (by omega)).symm

private def coneR₁ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₁ ⋙ HomologicalComplex.eval _ _ (n + 1) where
  app U := (mappingCone.fst ((chains (ZMod q)).map (sch.map (F.app U)))).1.v n (n + 1) rfl
  naturality U V a := map_fst ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n (n + 1) rfl

private def coneI₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    famCh q G₂ ⋙ HomologicalComplex.eval _ _ n ⟶ coneF F q ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.inr ((chains (ZMod q)).map (sch.map (F.app U)))).f n
  naturality U V a := (inr_map ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n).symm

private def coneR₂ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂) (q : ℕ) (n : ℤ) :
    coneF F q ⋙ HomologicalComplex.eval _ _ n ⟶ famCh q G₂ ⋙ HomologicalComplex.eval _ _ n where
  app U := (mappingCone.snd ((chains (ZMod q)).map (sch.map (F.app U)))).v n n (add_zero n)
  naturality U V a := map_snd ((chains (ZMod q)).map (sch.map (F.app U))) ((chains (ZMod q)).map (sch.map (F.app V)))
    ((chains (ZMod q)).map (sch.map (G₁.map a))) ((chains (ZMod q)).map (sch.map (G₂.map a))) (cone_comm F q a) n

theorem UpperTheory.homAcyclic_mappingCone_chains_of_homAcyclic_free :
    ∀ (q : ℕ) {B : Scheme.{0}} {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂), Good (G₁ ⋙ yoneda ⋙ free (ZMod q)) → Good (G₂ ⋙ yoneda ⋙ free (ZMod q)) → (∀ n : ℤ, Good (coneF F q ⋙ HomologicalComplex.eval _ _ n)) ∧ ∀ (U : B.Etale) (n : ℤ), 0 < n → IsZero (((coneF F q).obj U).X n) := by
  intro q B G₁ G₂ F h₁ h₂
  refine ⟨fun n => ?_, fun U n hn => ?_⟩
  · refine (UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B).2.2 _ _ _ (coneI₁ F q n) (coneR₁ F q n) (coneI₂ F q n) (coneR₂ F q n)
      ?_ ?_ ?_ ?_ ?_ (famCh_good q G₁ h₁ (n + 1)) (famCh_good q G₂ h₂ n)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inl_v_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n rfl
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.inr_f_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) n
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inl_v_snd_v ((chains (ZMod q)).map (sch.map (F.app U))) (n + 1) n (by omega)
    · ext U : 2
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact mappingCone.inr_f_fst_v ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
    · ext U : 2
      rw [NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app]
      exact mappingCone.id_X ((chains (ZMod q)).map (sch.map (F.app U))) n (n + 1) rfl
  · exact (mappingCone.isZero_X_iff ((chains (ZMod q)).map (sch.map (F.app U))) n).2
      ⟨GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ (by omega), GlobalTheory.EtC.HCTerms.isZero_chains_X _ _ _ hn⟩

end
