import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFinitePartMulConstant
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfDiv
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twhopf

noncomputable def liftHom {V : Type} [CommRing V] [IsDomain V] {T : Type} [CommGroup T] {Γ : QFGroup V T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of V) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (ht : Γ.IsTorsionAlong G x N i) (Y : Over (Spec (CommRingCat.of V))) :
    (Y ⟶ Γ.G) →* (Over.mk (Y.hom ≫ x) ⟶ G) :=
  let l : (Y ⟶ Γ.G) → (Over.mk (Y.hom ≫ x) ⟶ G) := fun σ => Over.homMk (σ.left ≫ i) (by
    simp only [Over.mk_hom, Category.assoc, ht.isOver]
    rw [← Category.assoc, Over.w σ])
  MonoidHom.mk' l fun a b => Over.OverMorphism.ext (ht.mul Y a b (l a) (l b) rfl rfl).symm

theorem liftHom_left {V : Type} [CommRing V] [IsDomain V] {T : Type} [CommGroup T] {Γ : QFGroup V T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of V) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (ht : Γ.IsTorsionAlong G x N i) (Y : Over (Spec (CommRingCat.of V))) (σ : Y ⟶ Γ.G) :
    (liftHom ht Y σ).left = σ.left ≫ i := rfl

theorem finite_levGrp (p : ℕ) [hp : Fact p.Prime] (La : Type) [AddCommGroup La] [Module.Finite ℤ La] (n : ℕ) :
    Finite (LevGrp La p n) := by
  refine Module.finite_of_fg_torsion (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) fun z => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast pow_ne_zero n hp.out.ne_zero)⟩, ?_⟩
  change ((p ^ n : ℕ) : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, by simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩

theorem lev_nsmul {La : Type} [AddCommGroup La] (p n k : ℕ) (a : La) : lev p n (k • a) = lev p n a ^ k := by
  unfold lev
  rw [← ofAdd_nsmul]
  exact congrArg _ (map_nsmul (Submodule.mkQ _) k a)

theorem lev_pow_self {La : Type} [AddCommGroup La] (p n : ℕ) (a : La) : lev p n a ^ p ^ n = 1 := by
  rw [← lev_nsmul]
  exact congrArg Multiplicative.ofAdd ((Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)

theorem lev_surj {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t :=
  Submodule.Quotient.mk_surjective _ t.toAdd

theorem btOrder_eq_top {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) {T : Type} [CommGroup T] [Finite T]
    (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [mem_order, mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  rcases hR _ (Γ.G.hom g).isPrime with h | h
  · exact regularAt_generic R T Γ _ g h
  · exact hf t g (hU g (PrimeSpectrum.ext h))

theorem level {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [HenselianLocalRing R]
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) {T : Type} [CommGroup T] [Finite T]
    (Γ : QFGroup R T) : ∃ (U : Γ.G.left.Opens) (H : Subgroup T), Γ.IsFinOpenSub U ∧
      (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) ∧ (∀ t, t ∈ H ↔ ∀ z, (Γ.pt t).left z ∈ U) ∧
      IsHopfOrder (Γ.btOrder ⊤) ∧ IsHopfOrder (resOrder H.subtype (Γ.btOrder ⊤)) ∧
      Γ.btOrder ⊤ = indOrder H.subtype (resOrder H.subtype (Γ.btOrder ⊤)) ∧
      ∀ t, t ∈ H ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t := by
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.quasiCompact
  have := Γ.finPres
  obtain ⟨U, hUf, hUc⟩ := finite_part R Γ.G.left Γ.G.hom
  have hsub := finite_sub R T Γ U hUf hUc
  have htop := btOrder_eq_top hR Γ U hUc
  obtain ⟨H, A, hH, hA, hAf⟩ := sub_order R T Γ U hsub
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  have hres := res_ind H A hA
  refine ⟨U, H, hsub, hUc, fun t => (hH t).trans ⟨fun h z => h (Set.mem_univ z), fun h z _ => h z⟩, ?_, ?_, ?_,
    fun t => (hH t).trans (mem_iff_section R T Γ U hUf hUc t)⟩
  · rw [← htop, key]
    exact ind_hopf R T H H.subtype H.subtype_injective A hA
  · rw [← htop, key, hres]
    exact hA
  · rw [← htop, key, hres]

theorem tw_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La), ∃ (U : ∀ n, (X.Γ n).G.left.Opens) (H : ∀ n, Subgroup (LevGrp La p n)), (∀ n, (X.Γ n).IsFinOpenSub (U n)) ∧ (∀ n (g : (X.Γ n).G.left), (X.Γ n).G.hom g = IsLocalRing.closedPoint O → g ∈ U n) ∧ (∀ n t, t ∈ H n ↔ ∀ z, ((X.Γ n).pt t).left z ∈ U n) ∧ (∀ n, IsHopfOrder ((X.Γ n).btOrder ⊤)) ∧ (∀ n, IsHopfOrder (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n, (X.Γ n).btOrder ⊤ = indOrder (H n).subtype (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n (a : La), lev p n a ∈ H n ↔ lev p (n + 1) (p • a) ∈ H (n + 1)) ∧ ∀ n (a : La), lev p n a ∈ H n → ∃ b : La, lev p (n + 1) b ∈ H (n + 1) ∧ lev p n b = lev p n a := by
  intro p hpp C _ _ _ v O _ _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X
  obtain ⟨-, hH, hN, hV, hA, -⟩ := padic_alg p C v O hv hp hO
  have hR := prime_eq_bot_or_max C v O hv
  have hfin := finite_levGrp p La
  choose U H h1 h2 h3 h4 h5 h6 h7 using fun n => level hR (X.Γ n)
  let Y := 𝟙_ (Over (Spec (CommRingCat.of O)))
  have pow : ∀ n (σ : Y ⟶ (X.Γ n).G) (t : LevGrp La p n) (k : ℕ), toUnit (genPt O) ≫ σ = (X.Γ n).pt t →
      toUnit (genPt O) ≫ σ ^ k = (X.Γ n).pt (t ^ k) := fun n σ t k h => by
    rw [MonObj.comp_pow, h, map_pow]
  refine ⟨U, H, h1, h2, h3, h4, h5, h6, fun n a => ?_, fun n a ha => ?_⟩
  · rw [h7, h7]
    constructor
    · rintro ⟨σ, hσ⟩
      have e1 : liftHom (X.tors n) Y σ ^ p ^ n = 1 := ((X.tors n).kernel Y _).2 ⟨σ, rfl⟩
      obtain ⟨τ, hτ⟩ := ((X.tors (n + 1)).kernel Y (liftHom (X.tors n) Y σ)).1 (by rw [pow_succ, pow_mul, e1, one_pow])
      refine ⟨τ, (X.tors (n + 1)).inj _ _ _ ?_⟩
      rw [← X.compat, ← hσ, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hτ, liftHom_left]
    · rintro ⟨τ, hτ⟩
      have e0 : τ ^ p ^ n = 1 := by
        apply LateralTheory.section_ext
        rw [pow _ _ _ _ hτ, lev_nsmul, ← pow_mul, ← pow_succ', lev_pow_self, map_one, MonObj.comp_one]
      have e1 : liftHom (X.tors (n + 1)) Y τ ^ p ^ n = 1 := by rw [← map_pow, e0, map_one]
      obtain ⟨σ, hσ⟩ := ((X.tors n).kernel Y _).1 e1
      refine ⟨σ, (X.tors n).inj _ _ _ ?_⟩
      rw [X.compat, ← hτ, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, liftHom_left]
  · obtain ⟨σ, hσ⟩ := (h7 _ _).1 ha
    have e1 : liftHom (X.tors n) Y σ ^ p ^ n = 1 := ((X.tors n).kernel Y _).2 ⟨σ, rfl⟩
    obtain ⟨c, hc⟩ := points_div O S G hG (Y.hom ≫ y) p hpp.out.one_le (liftHom (X.tors n) Y σ)
    obtain ⟨τ, hτ⟩ := ((X.tors (n + 1)).kernel Y c).1 (by rw [pow_succ', pow_mul, hc, e1])
    obtain ⟨t, ht⟩ := LateralTheory.exists_pt_of_section _ τ
    obtain ⟨b, rfl⟩ := lev_surj p (n + 1) t
    refine ⟨b, (h7 _ _).2 ⟨τ, ht⟩, ?_⟩
    have e2 : liftHom (X.tors (n + 1)) Y τ = c := Over.OverMorphism.ext hτ
    have e3 : (τ ^ p).left ≫ X.i (n + 1) = σ.left ≫ X.i n := by
      rw [← liftHom_left (X.tors (n + 1)), map_pow, e2, hc, liftHom_left]
    have e4 : (X.Γ n).pt (lev p n b) = (X.Γ n).pt (lev p n a) := by
      refine (X.tors n).inj _ _ _ ?_
      rw [X.compat, lev_nsmul, ← pow _ _ _ p ht, ← hσ, Over.comp_left, Over.comp_left, Category.assoc,
        Category.assoc, e3]
    exact (X.Γ n).pt_inj _ _ default default (by rw [e4])

end PositivityTheory.HtPt.Twhopf
