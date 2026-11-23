import Development.WeilBound.CoreStatements.HodgeTatePoints.GiResGeo
import Development.WeilBound.CoreStatements.HodgeTatePoints.GiResAlg
import Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.BT.SubOrder PositivityTheory.HtPt.Twhopf

namespace PositivityTheory.HtPt.Gi

section Sec

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
  (U : Γ.G.left.Opens)

theorem exists_sec {f : T → R} (hf : f ∈ Γ.btOrder ⊤) :
    ∃ s : Γ(Γ.G.left, U), ∀ t h, valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  obtain ⟨s, hs⟩ := (reg_iff R T Γ U _).1 fun g _ => (mem_order R T Γ ⊤ f).1 hf 1 g trivial
  exact ⟨s, fun t h => by rw [hs t h, _root_.one_mul]⟩

theorem exists_fun [IsIntegrallyClosed R] [IsLocalRing R]
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) (hF : Γ.IsFinOpenSub U)
    (hU : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) (s : Γ(Γ.G.left, U)) :
    ∃ f ∈ Γ.btOrder ⊤, ∀ t h, valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  obtain ⟨H, A, hH, hA, hAf⟩ := sub_order R T Γ U hF
  have hV := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hV).toAlgebra
  have hρ : hV.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hV
  have hfin := sec_finite hρ hF
  have hval : ∀ t : H, ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t ((hH t).1 t.2) s := fun t =>
    IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := R) s).map (valAlg hρ t ((hH t).1 t.2)))
  choose a ha using hval
  have h1 : a ∈ A := (hAf a).2 ⟨s, fun t _ => (ha t).symm⟩
  rw [← res_ind H A hA] at h1
  obtain ⟨f, hf, e⟩ := h1
  refine ⟨f, ?_, fun t h => ?_⟩
  · rw [← btOrder_eq_top hR Γ U hU, mem_order R T Γ U f]
    intro t
    refine (reg_iff R T Γ U _).2 ?_
    obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
    exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  · exact (ha ⟨t, (hH t).2 h⟩).symm.trans (congrArg _ (congrFun e ⟨t, (hH t).2 h⟩).symm)

end Sec

theorem exists_incl {R : Type} [CommRing R] [IsDomain R] {T T' : Type} [CommGroup T] [CommGroup T']
    {Γ : QFGroup R T} {Γ' : QFGroup R T'} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N m : ℕ} {i : Γ.G.left ⟶ G.left} {i' : Γ'.G.left ⟶ G.left}
    (ht : Γ.IsTorsionAlong G x N i) (ht' : Γ'.IsTorsionAlong G x (N * m) i') :
    ∃ j : Γ.G ⟶ Γ'.G, j.left ≫ i' = i ∧ (∀ (Y) (y y' : Y ⟶ Γ.G), y ≫ j = y' ≫ j → y = y') ∧
      ∀ (Y) (z : Y ⟶ Γ'.G), z ^ N = 1 ↔ ∃ y, y ≫ j = z := by
  have e1 : ∀ Y (y : Y ⟶ Γ.G), liftHom ht Y y ^ N = 1 := fun Y y => (ht.kernel Y _).2 ⟨y, rfl⟩
  obtain ⟨j, hj⟩ := (ht'.kernel Γ.G (liftHom ht _ (𝟙 _))).1 (by rw [pow_mul, e1, one_pow])
  replace hj : j.left ≫ i' = i := hj.trans (Category.id_comp _)
  have hc : ∀ Y (y : Y ⟶ Γ.G), (y ≫ j).left ≫ i' = y.left ≫ i := fun Y y => by
    rw [Over.comp_left, Category.assoc, hj]
  refine ⟨j, hj, fun Y y y' h => ht.inj _ _ _ (by rw [← hc, ← hc, h]), fun Y z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨y, hy⟩ := (ht.kernel Y (liftHom ht' Y z)).1 (by rw [← map_pow, h, map_one])
    exact ⟨y, ht'.inj _ _ _ ((hc Y y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    have e2 : liftHom ht' Y (y ≫ j) = liftHom ht Y y := Over.OverMorphism.ext (hc Y y)
    refine ht'.inj _ _ _ ?_
    rw [← liftHom_left ht', ← liftHom_left ht', map_pow, e2, e1, map_one]

theorem fin_compare {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) {T T' : Type} [CommGroup T]
    [CommGroup T'] [Finite T] [Finite T'] {Γ : QFGroup R T} {Γ' : QFGroup R T'} {N : ℕ} (j : Γ.G ⟶ Γ'.G)
    (hinj : ∀ (Y) (y y' : Y ⟶ Γ.G), y ≫ j = y' ≫ j → y = y') (hker : ∀ (Y) (z : Y ⟶ Γ'.G), z ^ N = 1 ↔ ∃ y, y ≫ j = z)
    (κ : T →* T') (hk : ∀ t, Γ.pt t ≫ j = Γ'.pt (κ t)) {U : Γ.G.left.Opens} {U' : Γ'.G.left.Opens}
    (hF : Γ.IsFinOpenSub U) (hF' : Γ'.IsFinOpenSub U')
    (hU : ∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U)
    (hU' : ∀ g : Γ'.G.left, Γ'.G.hom g = IsLocalRing.closedPoint R → g ∈ U') {H : Subgroup T} {H' : Subgroup T'}
    (hH : ∀ t, t ∈ H ↔ ∀ z, (Γ.pt t).left z ∈ U) (hH' : ∀ t, t ∈ H' ↔ ∀ z, (Γ'.pt t).left z ∈ U')
    (hB' : IsHopfOrder (Γ'.btOrder ⊤)) :
    (∀ f ∈ Γ'.btOrder ⊤, ∃ g ∈ Γ.btOrder ⊤, ∀ h ∈ H, g h = f (κ h)) ∧
    (∀ g ∈ Γ.btOrder ⊤, ∃ f ∈ Γ'.btOrder ⊤, ∀ h ∈ H, g h = f (κ h)) ∧
    ∀ f ∈ Γ'.btOrder ⊤, (∀ t, f (κ t) = 0) → ∃ g ∈ torsJ (Γ'.btOrder ⊤) N, ∀ h ∈ H', g.1 h = f h := by
  obtain ⟨r, hr, hv, hI⟩ := core j hinj hker U U' hF.finite hF'.finite hU hU'
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have mH : ∀ t ∈ H, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun t ht => (top_le_iff_mem _ _).2 ((hH t).1 ht)
  have mH' : ∀ t ∈ H', ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun t ht => (top_le_iff_mem _ _).2 ((hH' t).1 ht)
  have hv' : ∀ t h, ∃ h', ∀ s, valAt (Γ.pt t).left U h (r s) = valAt (Γ'.pt (κ t)).left U' h' s := fun t h => by
    have := hv (Γ.pt t) h
    rwa [hk] at this
  refine ⟨fun f hf => ?_, fun g hg => ?_, fun f hf h0 => ?_⟩
  · obtain ⟨s, hs⟩ := exists_sec Γ' U' hf
    obtain ⟨g, hg, e⟩ := exists_fun Γ U hR hF hU (r s)
    refine ⟨g, hg, fun t ht => inj ?_⟩
    obtain ⟨h', e'⟩ := hv' t (mH t ht)
    rw [← e t (mH t ht), e', hs]
  · obtain ⟨s, hs⟩ := exists_sec Γ U hg
    obtain ⟨s, rfl⟩ := hr s
    obtain ⟨f, hf, e⟩ := exists_fun Γ' U' hR hF' hU' s
    refine ⟨f, hf, fun t ht => inj ?_⟩
    obtain ⟨h', e'⟩ := hv' t (mH t ht)
    rw [← hs t (mH t ht), e', e]
  · obtain ⟨s, hs⟩ := exists_sec Γ' U' hf
    have h1 : r s = 0 := sec_inj R T Γ U _ fun t h => by
      obtain ⟨h', e'⟩ := hv' t h
      rw [e', hs, h0, map_zero]
    let I : Ideal Γ(Γ'.G.left, U') :=
      { carrier := {c | ∃ g ∈ torsJ (Γ'.btOrder ⊤) N, ∀ t h, valHom (Γ'.pt t).left U' h c = algebraMap R _ (g.1 t)}
        zero_mem' := ⟨0, Ideal.zero_mem _, fun t h => by simp⟩
        add_mem' := by
          rintro a b ⟨g, hg, e⟩ ⟨g', hg', e'⟩
          exact ⟨g + g', Ideal.add_mem _ hg hg', fun t h => by simp [e, e']⟩
        smul_mem' := by
          rintro a b ⟨g, hg, e⟩
          obtain ⟨u, hu, eu⟩ := exists_fun Γ' U' hR hF' hU' a
          refine ⟨⟨u, hu⟩ * g, Ideal.mul_mem_left _ _ hg, fun t h => ?_⟩
          rw [smul_eq_mul, map_mul, e, valHom_apply, eu, ← map_mul]
          rfl }
    obtain ⟨g, hg, e⟩ := hI I (fun a c hc => by
      obtain ⟨u, hu, eu⟩ := exists_fun Γ' U' hR hF' hU' a
      refine ⟨⟨_, pow_pull hB' hu N⟩ - algebraMap R _ (u 1), Ideal.subset_span ⟨u, hu, fun t => rfl⟩, fun t h => ?_⟩
      have := hc (Γ'.pt t) h
      rw [← map_pow, ← map_one Γ'.pt] at this
      obtain ⟨hN, h1, e⟩ := this
      rw [valHom_apply, e, eu, eu, ← map_sub]
      rfl) h1
    refine ⟨g, hg, fun t ht => inj ?_⟩
    rw [← e t (mH' t ht), valHom_apply, hs]

theorem tw_res : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (n : ℕ), (∀ g : LevGrp La p n → O, g ∈ (X.Γ n).btOrder ⊤ ↔ ∃ f ∈ (X.Γ (n + 1)).btOrder ⊤, ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) ∧ ∀ f : (X.Γ (n + 1)).btOrder ⊤, (∀ a : La, f.1 (lev p (n + 1) (p • a)) = 0) → f ∈ Ideal.span {g : (X.Γ (n + 1)).btOrder ⊤ | ∃ h ∈ (X.Γ (n + 1)).btOrder ⊤, ∀ t, g.1 t = h (t ^ p ^ n) - h 1} := by
  intro p hpp C _ _ _ v O _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X n
  obtain ⟨-, hH, hN, -, -, -⟩ := padic_alg p C v O hv hp hO
  have hR := prime_eq_bot_or_max C v O hv
  obtain ⟨U, H, h1, h2, h3, h4, -, h6, h7, h8⟩ := tw_hopf p C v O hv hp hO S G hG y La X
  obtain ⟨j, hj, hinj, hker⟩ := exists_incl (m := p) (X.tors n) (X.tors (n + 1))
  have hk : ∀ t, (X.Γ n).pt t ≫ j = (X.Γ (n + 1)).pt (Twpdiv.incl p n t) := fun t => by
    obtain ⟨a, rfl⟩ := lev_surj p n t
    refine (X.tors (n + 1)).inj _ _ _ ?_
    rw [Over.comp_left, Category.assoc, hj, X.compat, Twpdiv.incl_lev]
  obtain ⟨ha, hb, hc⟩ := fin_compare hR j hinj hker _ hk (h1 n) (h1 (n + 1)) (h2 n) (h2 (n + 1)) (h3 n) (h3 (n + 1))
    (h4 (n + 1))
  have down : ∀ k (a : La), lev p (k + 1) (p ^ k • a) ∈ H (k + 1) → lev p 1 a ∈ H 1 := by
    intro k a
    induction k with
    | zero => simp
    | succ k ih => exact fun h => ih ((h7 _ _).2 (by rwa [← mul_smul, ← pow_succ']))
  have up : ∀ k (a : La), lev p 1 a ∈ H 1 → ∃ b c : La, lev p (k + 1) b ∈ H (k + 1) ∧ a = b + p • c := by
    intro k a h
    induction k with
    | zero => exact ⟨a, 0, h, by simp⟩
    | succ k ih =>
      obtain ⟨b, c, hb, rfl⟩ := ih
      obtain ⟨b', hb', e⟩ := h8 _ b hb
      obtain ⟨d, hd⟩ := (Twpdiv.lev_eq_iff p _ _ _).1 e.symm
      exact ⟨b', c + p ^ k • d, hb', by
        rw [smul_add, ← mul_smul, ← pow_succ', ← hd]; abel⟩
  refine ⟨fun g => ?_, fun f hf => ?_⟩
  · rw [res_iff_abs (Twpdiv.incl p n) (h4 n) (h4 (n + 1)) (isLoc_of_ind (h6 n)) (isLoc_of_ind (h6 (n + 1)))
      (fun t ht => by
        obtain ⟨a, rfl⟩ := lev_surj p n t
        exact (h7 n a).2 ht) ha hb g]
    refine exists_congr fun f => and_congr_right fun _ => ⟨fun h a => h _, fun h t => ?_⟩
    obtain ⟨a, rfl⟩ := lev_surj p n t
    exact h a
  · refine ker_abs (Twpdiv.incl p n) (h4 (n + 1)) (isLoc_of_ind (h6 (n + 1)))
      (fun t => by rw [← map_pow, Twpdiv.lev_pow, map_one]) (fun s hs => ?_) hc f fun t => ?_
    · obtain ⟨a, rfl⟩ := lev_surj p (n + 1) s
      rw [← lev_nsmul] at hs
      obtain ⟨b, c, hb, rfl⟩ := up n a (down n a hs)
      refine ⟨lev p n c, ?_⟩
      rw [Twpdiv.incl_lev, add_comm b, Twpdiv.lev_add, QuotientGroup.mk_mul_of_mem _ hb]
    · obtain ⟨a, rfl⟩ := lev_surj p n t
      exact hf a

end PositivityTheory.HtPt.Gi
