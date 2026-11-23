import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObjectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariantStatement

noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_galoisCover_of_geom {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    (N h M : ℕ) (h1 : 1 ≤ h) (hM0 : 0 < M) (hodd : Odd M) (hMp : M.Coprime p)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (huniv : HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev)
    (ρ : sympSimGrp h M → (X ⟶ X)) (hρ : SympActs s s₁ u lev ρ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t)
    (geo : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)), SympCond o h M (Over.mk x) t₁ lv) :
    ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp h M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
      GlobalTheory.ZM.IsGaloisCover (sympSimGrp h M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
      y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Y, t₁, lu, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme p D R b N h M hM0 hMp S t o
  have hAu : SympCond o h M Y t₁ lu := (hY Y t₁ lu).2 ⟨𝟙 Y, by simp, fun a => Category.id_comp _⟩
  have uniqY : ∀ {T : Over S} (f g : T ⟶ Y), f.left ≫ t₁ = g.left ≫ t₁ → (∀ c, f ≫ lu c = g ≫ lu c) → f = g :=
    fun {T} f g e1 e2 => ((hY T (g.left ≫ t₁) (fun c => g ≫ lu c)).1 ((hY T _ _).2 ⟨g, rfl, fun _ => rfl⟩)).unique
      ⟨e1, e2⟩ ⟨rfl, fun _ => rfl⟩
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y.left t Y.hom o
  have hlift : ∀ c, ∃ g : 𝟙_ (Over Y.left) ⟶ o'.A, g.left ≫ m.φ = (lu c).left := fun c => by
    have w : (lu c).left ≫ o.A.hom = 𝟙 Y.left ≫ Y.hom := by rw [Over.w (lu c), Category.id_comp]
    exact ⟨Over.homMk (m.cart.1.lift (lu c).left (𝟙 Y.left) w) (m.cart.1.lift_snd _ _ _),
      m.cart.1.lift_fst _ _ _⟩
  choose lv' hlv' using hlift
  choose n σ hn hσζ hσs using fun a => (hρ a).2.1
  have hTw : ∀ a, SympCond o h M Y (t₁ ≫ spMap (σ a)) (sympTwist a lu) := fun a =>
    GlobalTheory.T.symplecticLevel_twist_by_similitude p D R b N h M hM0 S t o Y t₁ lu hAu a (n a) (σ a) (hn a) (hσζ a)
  choose r hr using fun a => ((hY Y _ _).1 (hTw a)).exists
  have hlev' : IsSympLev o'.P h M (zetaAway M) t₁ lv' := GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y t₁ o' m lv' lu hlv' hAu
  have hlevT : ∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv') := fun a =>
    GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y (t₁ ≫ spMap (σ a)) o' m (sympTwist a lv') (sympTwist a lu) (fun c => hlv' _) (hTw a)
  obtain ⟨y, ⟨hys, hys₁, my, hmy⟩, -⟩ := huniv Y.left (Y.hom ≫ t) t₁ o' lv' hlev'
  have hdet := (GlobalTheory.SiegelTor.cycAway_galois M (by omega)).2.1
  have hσ1 : σ 1 = RingHom.id _ := hdet _ (σ 1) (RingHom.id _) (by
    rw [hσζ, RingHom.id_apply]
    conv_rhs => rw [← pow_one (zetaAway M)]
    apply zetaAway_pow_eq M (by omega)
    have hm1 : IsMultOf (1 : sympSimGrp h M) 1 := fun x y => by simp
    exact_mod_cast isMultOf_unique h1 (hn 1) hm1)
  have hσmul : ∀ a c, (σ a).comp (σ c) = σ (a * c) := fun a c => hdet _ _ _ (by
    rw [RingHom.comp_apply, hσζ, map_pow, hσζ, hσζ, ← pow_mul]
    apply zetaAway_pow_eq M (by omega)
    have hm : IsMultOf (a * c) (n a * n c) := fun x y => by
      show omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
      rw [hn a, hn c]
      push_cast
      ring
    exact isMultOf_unique h1 hm (hn (a * c)))
  have hsm : ∀ (k : ℕ) w, lu (k • w) = lu w ^ k := by
    have h0 : lu 0 = 1 := by
      have e0 := hAu.1 0 0
      rw [add_zero] at e0
      exact (by simpa using congrArg (· * (lu 0)⁻¹) e0 : (1 : Y ⟶ o.A) = lu 0).symm
    intro k w
    induction k with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ k ih => rw [succ_nsmul, hAu.1, ih, pow_succ]
  have hper : ∀ c, lu (liftMod (reduceMod M c)) = lu c := by
    intro c
    have hw : liftMod (reduceMod M c) = c + M • (fun i => -(c i / M)) := by
      funext i
      simp only [liftMod, reduceMod, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply]
      rw [Int.emod_def]
      ring
    rw [hw, hAu.1, hsm, hAu.2.1, _root_.mul_one]
  have hsp1 : spMap (RingHom.id (cycAway M)) = 𝟙 _ := Spec.map_id _
  have hr1 : r 1 = 𝟙 Y := uniqY _ _ (by rw [(hr 1).1, hσ1, hsp1]; simp) (fun c => by
    rw [(hr 1).2, Category.id_comp]
    exact hper c)
  have hrmul : ∀ a c, r (a * c) = r a ≫ r c := fun a c => uniqY _ _ (by
      rw [(hr _).1, Over.comp_left, Category.assoc, (hr c).1, ← Category.assoc, (hr a).1, Category.assoc,
        ← spMap_comp, hσmul])
    (fun d => by
      rw [(hr _).2, Category.assoc, (hr c).2]
      change sympTwist (a * c) lu d = r a ≫ lu (liftMod
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M d)))
      rw [(hr a).2]
      change lu (liftMod (((a * c : sympSimGrp h M) : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M d))) = lu (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
            (reduceMod M d))))))
      rw [reduceMod_liftMod]
      rfl)
  refine ⟨Y.left, Y.hom, fun a => (r a).left, y, o', ⟨sympSimGrp_finite h M, ?_, ?_, ?_, hYf, hYe, ?_, ?_⟩,
    ?_, hys, ⟨m⟩, ⟨my⟩⟩
  · show (r 1).left = _
    rw [hr1]
    rfl
  · intro a c
    show (r (a * c)).left = _
    rw [hrmul]
    rfl
  · intro a
    exact Over.w (r a)
  · refine ⟨fun pt => ?_⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨t₀, lv, hlv⟩ := geo k x
    obtain ⟨f, -, -⟩ := (hY (Over.mk x) t₀ lv).1 hlv
    obtain ⟨q, hq⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨f.left q, by rw [← Scheme.Hom.comp_apply, Over.w f]; exact hq⟩
  · intro K _ _ y₁ y₂ h12
    let P1 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₁ rfl
    let P2 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₂ h12.symm
    have c1 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₁ ≫ t₁) (fun c => P1 ≫ lu c) :=
      (hY _ _ _).2 ⟨P1, rfl, fun _ => rfl⟩
    have c2 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₂ ≫ t₁) (fun c => P2 ≫ lu c) :=
      (hY _ _ _).2 ⟨P2, rfl, fun _ => rfl⟩
    obtain ⟨a, ⟨ha1, ha2⟩, hu⟩ := GlobalTheory.T.existsUnique_similitude_between_symplecticLevels p D R b N h M hM0 hodd h1 σ (fun a => ⟨n a, hn a, hσζ a⟩) S t o K
      (y₁ ≫ Y.hom) _ _ _ _ c1 c2
    refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
    · have : P1 ≫ r a = P2 := uniqY _ _ (by
          show y₁ ≫ (r a).left ≫ t₁ = y₂ ≫ t₁
          rw [(hr a).1, ← Category.assoc]
          exact ha1)
        (fun c => by rw [Category.assoc, (hr a).2]; exact ha2 c)
      exact congrArg (fun q => q.left) this
    · have e' : P1 ≫ r a' = P2 := Over.OverMorphism.ext ha'
      refine ⟨?_, fun c => ?_⟩
      · rw [Category.assoc, ← (hr a').1, ← Category.assoc]
        exact congrArg (· ≫ t₁) ha'
      · show P1 ≫ lu _ = P2 ≫ lu c
        rw [← e', Category.assoc, (hr a').2]
        rfl
  · exact fun a => GlobalTheory.T.classifyingMap_symplecticLevel_equivariant p D R b N h M X s s₁ u lev huniv ρ hρ σ hσs S t o Y t₁ lu o' m lv' hlv' hlevT y my hmy
      hys hys₁ r (fun a => (hr a).1) (fun a => (hr a).2) a

theorem exists_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
  (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  intro p _ D R _ b N M e _ _ hM hodd hMp _ hMe hperf X s s₁ u lev _ huniv ρ hρ S t o
  have h1 : 1 ≤ Module.finrank ℤ D.La / 2 := by have := D.two_le_finrank_La; omega
  exact exists_galoisCover_of_geom b N _ M h1 (by omega) hodd hMp X s s₁ u lev huniv ρ hρ S t o
    (fun K _ _ x => GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor p D R b N M e hM hodd hMp hMe hperf S t o K x)

end GlobalTheory.HTSympCover
