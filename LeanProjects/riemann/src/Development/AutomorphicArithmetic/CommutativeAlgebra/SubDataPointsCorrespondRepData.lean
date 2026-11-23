import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyKernelPointsIffOfIsPIsog
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsoOfPIsogenyKernelEq
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.KernelTorsionPullback

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_equiv_points_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  let Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G) :=
    { toFun := fun x => Over.homMk (x.left ≫ φ) (by
        show _ = T.hom ≫ f
        rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
      invFun := fun y => Over.homMk (hp.1.lift y.left T.hom (Over.w y)) (by simp)
      left_inv := fun x => by
        apply Over.OverMorphism.ext
        apply hp.1.hom_ext
        · simp
        · simp
      right_inv := fun y => by
        apply Over.OverMorphism.ext
        simp }
  have hl : ∀ x, (Φ x).left = x.left ≫ φ := fun x => rfl
  have h1 : Φ 1 = 1 := by
    have hm := hp.2 T 1 1 (Φ 1) (Φ 1) (hl 1) (hl 1)
    have hsq : Φ 1 * Φ 1 = Φ 1 := by
      apply Over.OverMorphism.ext
      rw [hm, _root_.mul_one]
      rfl
    exact mul_left_cancel (a := Φ 1) (by rw [hsq, _root_.mul_one])
  refine ⟨Φ, hl, fun x => ⟨fun hx => Φ.injective (by rw [hx, h1]), fun hx => by rw [hx, h1]⟩⟩

private theorem isTj_of_pull {Y S : Scheme.{0}} {σ : Y ⟶ Sp R} {σ₁ : S ⟶ Sp R} {f : S ⟶ Y} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j : ℕ} {o o' : Obj b N σ} {o₁ o₁' : Obj b N σ₁}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) {ψ : o.A ⟶ o'.A} {ψ₁ : o₁.A ⟶ o₁'.A}
    (e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (h : IsTj r w j o o' ψ) : IsTj r w j o₁ o₁' ψ₁ := by
  intro k _ _ _ x
  obtain ⟨h1, h2⟩ := h k (x ≫ f)
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_of_isGrpPullback m.cart (Over.mk x)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_of_isGrpPullback m'.cart (Over.mk x)
  have hψ : ∀ g, Φ' (g ≫ ψ₁) = Φ g ≫ ψ := by
    intro g
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, e]
  have hk1 : ∀ g, g ≫ ψ₁ = 1 ↔ Φ g ≫ ψ = 1 := by
    intro g
    rw [← hψ, hΦ'1]
  have hkill : ∀ v g, KilledBy o₁ v g ↔ KilledBy o v (Φ g) := by
    intro v g
    apply forall₂_congr
    intro a _
    have hc : Φ (g ≫ o₁.act.act ((algebraMap (𝓞 D.F) D.O) a))
        = Φ g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) a) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act]
    rw [← hc, hΦ1]
  constructor
  · intro g hg hex
    rw [hkill]
    obtain ⟨e0, he⟩ := hex
    exact h1 (Φ g) ((hk1 g).mp hg) ⟨e0, (hkill _ g).mp he⟩
  · rw [← h2]
    exact Nat.card_congr (Φ.subtypeEquiv (fun g => by rw [hk1, hkill]))

private theorem exists_equiv_points_mk_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk g ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  subst hg
  exact exists_equiv_points_of_isGrpPullback hp T

private theorem ker_iff {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s}
    (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {k : Type} [Field k] (y : Sp k ⟶ Rd.Y.left) {x : Sp k ⟶ S}
    (e : y ≫ Rd.Y.hom = x) {t : Sp k ⟶ Sp R} {ox o₁ : Obj b N t} (m : ObjMap ox o x) (my : ObjMap ox Rd.o₀ y)
    (hm : my.φ ≫ Rd.m₀.φ = m.φ) (n : ObjMap o₁ Rd.o' y) (ψ₁ : ox.A ⟶ o₁.A)
    (hψ : my.φ ≫ Rd.ψ.left = ψ₁.left ≫ n.φ) (hK : KerGeo Rd Sd y) (h : Over.mk (𝟙 (Sp k)) ⟶ ox.A)
    (a : Over.mk x ⟶ o.A) (ha : a.left = h.left ≫ m.φ) :
    (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy ox (uIdeal D r ^ e) h) ↔ InSub Sd.i a := by
  subst e
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_mk_of_isGrpPullback my.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_mk_of_isGrpPullback n.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  have key := hK (Φ h) a (by rw [hΦl, Category.assoc, hm, ha])
  rw [← key]
  have hψ' : Φ' (h ≫ ψ₁) = Φ h ≫ Rd.ψ := by
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, hψ]
  have hk : ∀ v, KilledBy ox v h ↔ KilledBy Rd.o₀ v (Φ h) := by
    intro v
    apply forall₂_congr
    intro c _
    have hc : Φ (h ≫ ox.act.act ((algebraMap (𝓞 D.F) D.O) c))
        = Φ h ≫ Rd.o₀.act.act ((algebraMap (𝓞 D.F) D.O) c) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, my.act]
    rw [← hc, hΦ1]
  rw [← hψ', hΦ'1]
  exact and_congr Iff.rfl (exists_congr fun _ => hk _)

end UpperTheory.KernelTorsionPullback

private theorem exists_objMap_same_phi_of_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f f' : S' ⟶ S}
    (hf : f = f') (n : ObjMap o' o f) : ∃ n' : ObjMap o' o f', n'.φ = n.φ := by
  subst hf
  exact ⟨n, rfl⟩

open UpperTheory.KernelTorsionPullback in
theorem UpperTheory.subData_points_correspond_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left), y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → KerGeo Rd Sd y₁ → KerGeo Rd Sd y₂ → y₁ = y₂ := by
  intro p _ D R _ _ b N hN hcop hp hm1 r w j c hw hu hc S _ s o Rd Sd k _ _ y₁ y₂ hy hK₁ hK₂
  obtain ⟨x, hx⟩ : ∃ x, y₁ ≫ Rd.Y.hom = x := ⟨_, rfl⟩
  have hx2 : y₂ ≫ Rd.Y.hom = x := hy ▸ hx
  obtain ⟨ox, ⟨my₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o₀ (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨o₁, ⟨n₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o' (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨ψ₁, hiso₁, hsq₁⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₁ Rd.o₀ Rd.o' ox o₁ my₁ n₁ Rd.ψ Rd.isog
  have htj₁ : IsTj r w j ox o₁ ψ₁ := isTj_of_pull my₁ n₁ hsq₁ Rd.tj
  obtain ⟨mc, hmc⟩ := IsogRep.exists_comp my₁ Rd.m₀
  obtain ⟨m, hmφ⟩ := exists_objMap_same_phi_of_eq hx mc
  obtain ⟨my₂, hmy₂⟩ := IsogRep.exists_factor hN hcop hx2 Rd.m₀ m
  obtain ⟨o₂, ⟨n'⟩⟩ := IsogRep.exists_pull y₂ Rd.o' (s' := x ≫ s) (by rw [← hx2, Category.assoc])
  obtain ⟨ψ₂, hiso₂, hsq₂⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₂ Rd.o₀ Rd.o' ox o₂ my₂ n' Rd.ψ Rd.isog
  have hker : ∀ h : 𝟙_ (Over (Sp k)) ⟶ ox.A,
      (h ≫ ψ₁ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) ↔
        (h ≫ ψ₂ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) := by
    intro h
    let a : Over.mk x ⟶ o.A := Over.homMk (h.left ≫ m.φ) (by
      show _ = x
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w h]
      exact Category.id_comp x)
    rw [ker_iff Rd Sd y₁ hx m my₁ (by rw [hmφ, hmc]) n₁ ψ₁ hsq₁ hK₁ h a rfl,
      ker_iff Rd Sd y₂ hx2 m my₂ hmy₂ n' ψ₂ hsq₂ hK₂ h a rfl]
  have hgeo := isogeny_kernel_points_iff_of_isPIsog p D R b N hp r w c hw hu k (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hker
  obtain ⟨mm, hmm⟩ := exists_iso_of_pIsogeny_kernel_eq p D R b N hN hcop hp c (Sp k) (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hgeo
  obtain ⟨nc, hnc⟩ := IsogRep.exists_comp mm n'
  obtain ⟨n₂, hn₂⟩ := exists_objMap_same_phi_of_eq (Category.id_comp y₂) nc
  exact (Rd.univ (Sp k) x ox o₁ m ψ₁ hiso₁ htj₁).unique ⟨hx, my₁, n₁, hsq₁⟩
    ⟨hx2, my₂, n₂, by rw [hn₂, hnc, ← Category.assoc, hmm, hsq₂]⟩
