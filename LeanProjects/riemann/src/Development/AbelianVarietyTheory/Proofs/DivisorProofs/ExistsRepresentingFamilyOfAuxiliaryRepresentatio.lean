import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfLocalEqPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOActNDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendsFiniteEtaleGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCoverStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.HTQuot

theorem objMap_comp_φ_of_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem obj_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (G : Type)
    [Group G] (ρ : G → (X ⟶ X)) (o : Obj b N (π ≫ sY)), GlobalTheory.ZM.IsGaloisCover G ρ π → IsQProjOver (π ≫ sY) →
    IsQProjOver sY → (∀ a, Nonempty (ObjMap o o (ρ a))) → ∃ oY : Obj b N sY, Nonempty (ObjMap o oY π) := by
  intro p _ D R _ _ b N hN hNp X Y π sY G _ ρ o hG hq hqY hmaps
  have : IsLocallyNoetherian Y := by
    obtain ⟨M, i, hi, -, hi'⟩ := hqY
    have := isProper_str R M
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str R M)
  have m : ∀ a, ObjMap o o (ρ a) := fun a => (hmaps a).some
  let ν : G → (o.A.left ⟶ o.A.left) := fun a => (m a).φ
  have uniq : ∀ {f f' : X ⟶ X} (_ : f = f') (m₁ : ObjMap o o f) (m₂ : ObjMap o o f'), m₁.φ = m₂.φ := by
    rintro f f' rfl m₁ m₂
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp X X _ _ o o f m₁ m₂
  have ν1 : ν 1 = 𝟙 _ := by
    have key : ∀ {f : X ⟶ X} (_ : f = 𝟙 X) (m₁ : ObjMap o o f), m₁.φ = 𝟙 _ := by
      rintro f rfl m₁
      exact GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp X _ o m₁
    exact key hG.one (m 1)
  have νmul : ∀ a c, ν (a * c) = ν a ≫ ν c := by
    intro a c
    obtain ⟨m', hm'⟩ := objMap_comp_φ_of_comp (m a) (m c)
    exact (uniq (hG.mul a c) (m (a * c)) m').trans hm'
  have hcart : ∀ a, IsGrpPullback o.A o.A (ρ a) (ν a) := fun a => (m a).cart
  have hqA : IsQProjOver (o.A.hom ≫ π ≫ sY) :=
    GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth R X (π ≫ sY) o.A _ hq (pull_isLB o.isLB _) o.ample
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ :=
    GlobalTheory.abelianScheme_descends_galoisCover_noetherian R X Y π sY G ρ o.A ν hG hqA o.ab hcart ν1 νmul
  have := hA₀.comm
  obtain ⟨act₀, hact⟩ := GlobalTheory.GaloisActDesc.exists_oActN_descend D.O X Y π G ρ o.A A₀ φ ν o.act hG o.ab hA₀ gp hφ
    hcart (fun a c => (m a).act c)
  obtain ⟨P₀, φ₂, hP₀, hsq, iso, rig0⟩ := GlobalTheory.SquareDescent.exists_bundle_descent X Y π G ρ o.A A₀ φ ν o.P hG o.ab
    hA₀ gp hφ hcart ν1 νmul o.isLB o.rig₁ (fun a => ⟨(m a).φ₂, (m a).sq, (m a).pol⟩)
  obtain ⟨rig₁, rig₂⟩ := GlobalTheory.T.descended_birigidified_bundle_trivial_on_axes X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.rig₁ o.rig₂
  have symm := GlobalTheory.T.descended_birigidified_bundle_swap_symmetric X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.symm
  have ample := GlobalTheory.T.relAmple_diagonal_descends_finiteEtaleGalois X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso o.ample
  have kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ A₀),
      (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.descended_polarisation_kernel_killed_same_integer X Y π G ρ o.A A₀ φ φ₂ o.P P₀ e hG o.ab hA₀ gp hsq o.isLB hP₀ iso hk⟩
  have rosati := GlobalTheory.T.rosati_condition_descends_galois_cover D.O (fun c => (D.star c).unop) X Y π G ρ o.A A₀ φ φ₂ o.P P₀ o.act act₀ hG o.ab hA₀ gp
    hsq o.isLB hP₀ iso rig0 hact o.rosati
  obtain ⟨eta₀, eta_add, eta_lin, eta_ker, heta⟩ := GlobalTheory.LevelSecDesc.levelSections_descend D.O D.La N X Y π G ρ o.A A₀ φ
    ν o.act act₀ o.eta hG gp hφ hact (fun a y => (m a).eta y) o.eta_add o.eta_lin o.eta_ker
  have lie := GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lie
  have lieRank := GlobalTheory.T.lie_multiplicities_geometric_points_descend p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lieRank
  have geom := GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ N φ₂ o.P P₀ o.eta eta₀ hG o.ab hA₀ gp hact hsq
    o.isLB hP₀ iso heta o.geom
  let oY : Obj b N sY :=
    { A := A₀, ab := hA₀, act := act₀, P := P₀, isLB := hP₀, rig₁ := rig₁, rig₂ := rig₂, symm := symm
      ample := ample, kerP := kerP, rosati := rosati, lie := lie, lieRank := lieRank, eta := eta₀,
      eta_add := eta_add, eta_lin := eta_lin, eta_ker := eta_ker, geom := geom }
  exact ⟨oY, ⟨⟨φ, φ₂, gp, hsq, hact, iso, heta⟩⟩⟩

theorem exists_repFam_of_levelCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (u : Obj b N s) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)),
    IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) →
    (∀ a, Nonempty (ObjMap u u (ρ a))) →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) →
    (∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : Ga → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧ y ≫ s = π₁ ≫ t ∧
        Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : Ga), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') →
    ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp X s u Ga _ _ ρ hq h1 hmul hbase hmaps hfree hcov huniq
  obtain ⟨Y, π, sY, hπs, hgal, hsep, hlft, -⟩ :=
    GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian R X s Ga ρ hq h1 hmul hbase hfree
  have hqY : IsQProjOver sY := GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover R X Y π sY Ga ρ
    hgal hsep hlft (by rw [hπs]; exact hq)
  subst hπs
  obtain ⟨uY, ⟨mu⟩⟩ := obj_descends_galoisCover p D R b N hN hNp X Y π sY Ga ρ u hgal hq hqY hmaps
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'),
      ∃! f : S ⟶ Y, f ≫ sY = s' ∧ Nonempty (ObjMap o uY f) := by
    intro S s' o
    obtain ⟨S₁, π₁, ρ₁, y, o', hgal₁, hequi, hys, ⟨m₁⟩, ⟨m₂⟩⟩ := hcov S s' o
    have hinv : ∀ a, ρ₁ a ≫ (y ≫ π) = y ≫ π := by
      intro a; rw [← Category.assoc, hequi a, Category.assoc, hgal.inv a]
    obtain ⟨f, hf, hfu⟩ := hgal₁.existsUnique_desc (y ≫ π) hinv
    have canc : ∀ {Z : Scheme.{0}} (h₁ h₂ : S ⟶ Z), π₁ ≫ h₁ = π₁ ≫ h₂ → h₁ = h₂ := by
      intro Z h₁ h₂ e
      obtain ⟨w, -, hwu⟩ := hgal₁.existsUnique_desc (π₁ ≫ h₁) (fun a => by rw [← Category.assoc, hgal₁.inv a])
      exact (hwu h₁ rfl).trans (hwu h₂ e.symm).symm
    have hfs : f ≫ sY = s' := canc _ _ (by rw [← Category.assoc, hf, Category.assoc, hys])
    have hmf : Nonempty (ObjMap o uY f) := by
      obtain ⟨m₃⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' u uY y π m₂ mu
      rw [← hf] at m₃
      exact GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover p D R b N S S₁ Y s' sY π₁ Ga ρ₁ f o o' uY hN hNp hgal₁ m₁ m₃
    refine ⟨f, ⟨hfs, hmf⟩, ?_⟩
    rintro f' ⟨hf's, ⟨m'⟩⟩
    obtain ⟨m₄⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' o uY π₁ f' m₁ m'
    obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ (pullback (π₁ ≫ f') π) (π₁ ≫ s')
      (pullback.fst (π₁ ≫ f') π) o'
    obtain ⟨mT1⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' u _ y mT m₂
    obtain ⟨mT2⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' uY _ _ mT m₄
    rw [pullback.condition] at mT2
    obtain ⟨mT3⟩ := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ oT u uY
      (pullback.snd (π₁ ≫ f') π) π).2 ⟨mT2⟩ ⟨mu⟩
    have key : y ≫ π = π₁ ≫ f' := by
      apply GlobalTheory.ZM.IsGaloisCover.eq_of_local_eq_pullback X Y S₁ Y π Ga ρ (π₁ ≫ f') (y ≫ π) (π₁ ≫ f') hgal
      intro q
      obtain ⟨V, a, hqV, hV⟩ := huniq _ _ oT (pullback.fst (π₁ ≫ f') π ≫ y) (pullback.snd (π₁ ≫ f') π)
        (by rw [Category.assoc, hys])
        (by rw [← Category.assoc, ← pullback.condition]; simp [hf's]) ⟨mT1⟩ ⟨mT3⟩ q
      refine ⟨V, hqV, ?_⟩
      calc V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ y ≫ π
          = (V.ι ≫ (pullback.fst (π₁ ≫ f') π ≫ y) ≫ ρ a) ≫ π := by simp [hgal.inv]
        _ = (V.ι ≫ pullback.snd (π₁ ≫ f') π) ≫ π := by rw [hV]
        _ = V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ π₁ ≫ f' := by rw [Category.assoc, ← pullback.condition]
    exact hfu f' key.symm
  exact ⟨⟨Y, sY, uY, hrep⟩, hqY⟩

theorem exists_representing_family_of_level_structure : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N M e hN hNp hM hodd hMp hep hMe hperf hrep
  obtain ⟨X, s, s₁, u, lev, hlev, hq, huniv⟩ := hrep
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨ρ, h1, hmul, hact⟩ := GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily p D R b N _ M (by omega) X s s₁ u lev hlev huniv
  exact exists_repFam_of_levelCover p D R b N hN hNp X s u _ ρ hq h1 hmul (fun a => (hact a).1)
    (fun a => let ⟨m, _⟩ := (hact a).2.2; ⟨m⟩)
    (GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one p D R b N _ M hN hNp (by omega) X s s₁ u lev hlev ρ hact)
    (GlobalTheory.T.symplectic_level_over_cyclotomic p D R b N M e hN hNp hM hodd hMp hep hMe hperf X s s₁ u lev hlev huniv ρ hact)
    (GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps p D R b N _ M hN hNp hM hodd hMp X s s₁ u lev hlev huniv ρ hact)

end GlobalTheory.HTQuot
