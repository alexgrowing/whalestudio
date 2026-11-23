import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpreadPt

theorem isOpen_compl_basicOpen_sub {X : Scheme.{0}} (a b : Γ(X, ⊤)) {k : ℕ} (hk0 : 0 < k) (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hk : IsUnit (k : Γ(X, ⊤))) : IsOpen ((X.basicOpen (a - b) : Set X)ᶜ) := by
  let bu : Γ(X, ⊤)ˣ := Units.ofPowEqOne b k hb hk0.ne'
  have hbu : (bu : Γ(X, ⊤)) = b := rfl
  set u : Γ(X, ⊤) := a * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) with hu_def
  have hab : a - b = b * (u - 1) := by
    have : b * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = 1 := by rw [← hbu]; exact bu.mul_inv
    rw [hu_def, mul_sub, _root_.mul_one, mul_left_comm, this, _root_.mul_one]
  have hu : u ^ k = 1 := by
    have : bu ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hbu, hb, Units.val_one])
    rw [hu_def, mul_pow, ha, _root_.one_mul, ← Units.val_pow_eq_pow_val, inv_pow, this, inv_one, Units.val_one]
  have hbo : X.basicOpen (a - b) = X.basicOpen (u - 1) := by
    rw [hab, Scheme.basicOpen_mul, ← hbu, Scheme.basicOpen_of_isUnit _ bu.isUnit, top_inf_eq]
  set g : Γ(X, ⊤) := ∑ i ∈ Finset.range k, u ^ i with hg
  have h1 : (u - 1) * g = 0 := by rw [hg, mul_comm, geom_sum_mul, hu, sub_self]
  obtain ⟨q, hq⟩ : (u - 1) ∣ g - k := by
    have : g - k = ∑ i ∈ Finset.range k, (u ^ i - 1) := by
      rw [hg, Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow u 1 i
  have hdis : X.basicOpen (u - 1) ⊓ X.basicOpen g = ⊥ := by
    rw [← Scheme.basicOpen_mul, h1, Scheme.basicOpen_zero]
  have e : (k : Γ(X, ⊤)) = g + (u - 1) * (-q) := by rw [mul_neg, ← hq]; ring
  have hcov : ⊤ ≤ X.basicOpen g ⊔ X.basicOpen (u - 1) := by
    calc (⊤ : X.Opens) = X.basicOpen (k : Γ(X, ⊤)) := (Scheme.basicOpen_of_isUnit _ hk).symm
      _ = X.basicOpen (g + (u - 1) * (-q)) := by rw [← e]
      _ ≤ X.basicOpen g ⊔ X.basicOpen ((u - 1) * (-q)) := Scheme.basicOpen_add_le _ _ _
      _ ≤ _ := sup_le_sup_left (by rw [Scheme.basicOpen_mul]; exact inf_le_left) _
  have hd : ∀ x, x ∈ X.basicOpen (u - 1) → x ∈ X.basicOpen g → False := fun x h h' => by
    have : x ∈ ((X.basicOpen (u - 1) ⊓ X.basicOpen g : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_inf]; exact ⟨h, h'⟩
    rw [hdis] at this; exact this
  have hc : ∀ x, x ∈ X.basicOpen g ∨ x ∈ X.basicOpen (u - 1) := fun x => by
    have : x ∈ ((X.basicOpen g ⊔ X.basicOpen (u - 1) : X.Opens) : Set X) := hcov trivial
    rwa [TopologicalSpace.Opens.coe_sup, Set.mem_union] at this
  have hs : ((X.basicOpen (u - 1) : Set X)ᶜ) = X.basicOpen g := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => (hc x).resolve_right h, fun h h' => hd x h' h⟩
  rw [hbo, hs]
  exact (X.basicOpen g).isOpen

end GlobalTheory.LevelSpreadPt

namespace GlobalTheory

open LevelSpread LevelSpreadPt TorsRootParam

theorem exists_levelIsometry_of_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (A : Type) [CommRing A] [IsDomain A] (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (z : A) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver (Sp A) ⟶ P.A)) (n m N : ℕ), 0 < n → 0 < N → Nonempty (ℚ →+* A) → z ^ N = 1 → (∀ i, pt i ^ N = 1) → (∀ a, IsMonHom (act a)) → (∃ (K : Type) (_ : Field K) (β : A →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : A →+* K), ∃ (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i := by
  intro E _ _ _ H D A _ _ P act z κ lam pt n m N hn hN hQ hz hpt hact hex K _ _ β
  obtain ⟨K₀, _, β₀, ζ₀, ev₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hex
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  obtain ⟨q₀⟩ := hQ
  have hnat : ∀ k : ℕ, 0 < k → IsUnit (k : Γ(Sp A, ⊤)) := fun k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp q₀)
    rwa [map_natCast] at h
  have hK : ∀ {L : Type} [Field L] (ρ : A →+* L) (k : ℕ), 0 < k → (k : L) ≠ 0 := fun ρ k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map (ρ.comp q₀)
    rw [map_natCast] at h
    exact h.ne_zero
  have hn' := hnat n hn
  refine GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp A) P act A (𝟙 _) z κ lam pt n m hn ?_ K (spMap β) β
    (hK β n hn) (Category.comp_id _)
  let gp : Sp A := (⊥ : PrimeSpectrum A)
  refine Dense.mono ((Set.singleton_subset_iff (a := gp)).2 ?_) ?_
  rotate_left
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun p => ?_)
    exact specializes_iff_mem_closure.1 ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum A) p).1 bot_le)

  obtain ⟨Z₀, e₀, -, hZet, hadd, hpow, hrep⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom (Sp A) P.A n D.La P.isAb hn'
  let s₀ : Z₀.left ⟶ Sp ℤ := specZIsTerminal.from _
  let p := pullback.fst s₀ (spMap (algebraMap ℤ (CycRing n)))
  let g := pullback.snd s₀ (spMap (algebraMap ℤ (CycRing n)))
  let Y : Over (Sp A) := Over.mk (p ≫ Z₀.hom)
  let π : Y ⟶ Z₀ := Over.homMk p rfl
  let et : D.La → (Y ⟶ P.A) := fun a => π ≫ e₀ a
  let c : Γ(Y.left, ⊤)ˣ := Units.map (LevCover.fnOn g).toMonoidHom (cycUnit hn)
  have hu : IsUnit (n : Γ(Y.left, ⊤)) := isUnit_natCast_of_hom Y.hom hn'
  have hadd' : ∀ a a', et (a + a') = et a * et a' := fun a a' => by
    simp only [et]; rw [hadd, MonObj.comp_mul]
  have hpow' : ∀ a, et a ^ n = 1 := fun a => by
    simp only [et]; rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  have hc : c ^ n = 1 := by rw [← map_pow, cycUnit_pow, map_one]
  have hflat : Flat Y.hom := by
    have : Module.Free ℤ (CycRing n) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic n ℤ)).basis
    have : Flat (spMap (algebraMap ℤ (CycRing n))) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    have : Flat Z₀.hom := inferInstance
    show Flat (p ≫ Z₀.hom)
    infer_instance

  have hq1 : ∀ {T : Over (Sp A)} (h : T ⟶ Y) (x y : Y ⟶ P.A), h ≫ (x * y⁻¹) = 1 ↔ h ≫ x = h ≫ y :=
    fun h x y => by rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hn' (et (b • a) * (et a ≫ act b)⁻¹) (by
      haveI := hact b
      rw [mul_pow, inv_pow, hpow', ← MonObj.pow_comp, hpow', MonObj.one_comp, inv_one, _root_.mul_one])
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL (Sp A) P n Y (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow' _) (hpow' _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let qY : Y ⟶ Out.baseOver (Sp A) := Over.homMk Y.hom (by simp)
  have hnN : IsUnit ((n * N : ℕ) : Γ(Sp A, ⊤)) := hnat _ (Nat.mul_pos hn hN)
  choose C4 hC4 HC4 using fun i : κ =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hnN (et (lam i) ^ m * (qY ≫ pt i)⁻¹) (by
      have e1 : (et (lam i) ^ m) ^ (n * N) = 1 := by
        rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, hpow', one_pow]
      have e2 : (qY ≫ pt i) ^ (n * N) = 1 := by
        rw [← MonObj.comp_pow, show n * N = N * n by ring, pow_mul, hpt, one_pow, MonObj.comp_one]
      rw [mul_pow, inv_pow, e1, e2, inv_one, _root_.mul_one])
  let w : Γ(Y.left, ⊤) := LevCover.fnOn Y.hom z
  let C3 : Set Y.left := (Y.left.basicOpen ((c : Γ(Y.left, ⊤)) ^ m - w) : Set Y.left)ᶜ
  have hC3 : IsOpen C3 := by
    refine isOpen_compl_basicOpen_sub _ _ (Nat.mul_pos hn hN) ?_ ?_ (isUnit_natCast_of_hom Y.hom hnN)
    · rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, ← Units.val_pow_eq_pow_val, hc, Units.val_one,
        one_pow]
    · simp only [w]
      rw [← map_pow, show n * N = N * n by ring, pow_mul, hz, one_pow, map_one]
  let C : Set Y.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Y.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hgen : ∀ {y y' : Y.left}, y ⤳ y' → y' ∈ C → y ∈ C := by
    intro y y' hyy hy'
    simp only [C, Set.mem_inter_iff, Set.mem_iInter] at hy' ⊢
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hy'
    exact ⟨⟨⟨fun b a => hyy.mem_open (hC1 b a).isOpen (k1 b a),
      fun a a' => hyy.mem_open (C2 a a').isOpen (k2 a a')⟩, hyy.mem_open hC3 k3⟩,
      fun i => hyy.mem_open (hC4 i).isOpen (k4 i)⟩
  have key : ∀ (F : Type) [Field F] (x : Sp F ⟶ Sp A) (ρ : A →+* F) (ζ : Fˣ) (h : Over.mk x ⟶ Y), x = spMap ρ →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : F) ^ m = ρ z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro F _ x ρ ζ h hx hζ
    have hw : h.left ≫ Y.hom = x := Over.w h
    have hq : h ≫ qY = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff Y.hom h.left ρ (by rw [hw, hx]) z c ζ m hζ
    have hzk : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a _ h, hq1, Category.assoc]
    · rw [← HC2 a a' _ h, hzk]
    · rw [← HC4 i _ h, hq1, ← hq, Category.assoc, MonObj.comp_pow]

  obtain ⟨ρ₀, hρ₀⟩ := exists_map_eq hn h₁
  obtain ⟨h₀, hh₀, -⟩ := hrep (Over.mk (spMap β₀)) ev₀ h₂ h₃
  let w₀ : Sp K₀ ⟶ Y.left := pullback.lift h₀.left (spMap ρ₀) (specZIsTerminal.hom_ext _ _)
  have hw₀ : w₀ ≫ p = h₀.left := pullback.lift_fst _ _ _
  have hw₀' : w₀ ≫ g = spMap ρ₀ := pullback.lift_snd _ _ _
  let y₀ : Over.mk (spMap β₀) ⟶ Y := Over.homMk w₀ (by
    show w₀ ≫ p ≫ Z₀.hom = spMap β₀
    rw [← Category.assoc, hw₀]
    exact Over.w h₀)
  have hy₀c : Units.map y₀.left.appTop.hom.toMonoidHom c = unitOn ζ₀ := by
    rw [← hρ₀]
    exact LevCover.map_fnOn g w₀ ρ₀ hw₀' (cycUnit hn)
  obtain rfl : (fun a => y₀ ≫ et a) = ev₀ := funext fun a => by
    apply Over.OverMorphism.ext
    show w₀ ≫ p ≫ (e₀ a).left = (ev₀ a).left
    rw [← Category.assoc, hw₀]
    exact congrArg (fun t => t.left) (hh₀ a)
  have hC₀ := (key K₀ (spMap β₀) β₀ ζ₀ y₀ rfl hy₀c).1 ⟨h₄, h₅, h₆, h₇⟩
  obtain ⟨v₀⟩ : Nonempty (Sp K₀) := inferInstance

  have hs : (⊥ : PrimeSpectrum A) ⤳ Y.hom (w₀ v₀) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨y, hy, ey⟩ := Flat.generalizingMap Y.hom hs
  have hyC : y ∈ C := hgen hy (hC₀ ⟨v₀, rfl⟩)
  let k := AlgebraicClosure (Y.left.residueField y)
  let u : Sp k ⟶ Y.left := spMap (algebraMap (Y.left.residueField y) k) ≫ Y.left.fromSpecResidueField y
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have huy : ∀ v', u v' = y := fun v' => by
    have : u v' ∈ Set.range (Y.left.fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨ρ, hρ⟩ := LevCover.exists_spMap (A := k) (u ≫ Y.hom)
  let yk : Over.mk (u ≫ Y.hom) ⟶ Y := Over.homMk u rfl
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := k) (Units.map yk.left.appTop.hom.toMonoidHom c)
  have hprim : IsPrimitiveRoot ζ n := by
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (A := k) (u ≫ g)
    have e1 := (LevCover.map_fnOn g u β' hβ' (cycUnit hn)).symm.trans hζ
    rw [← unitOn_inj e1]
    exact isPrimitiveRoot_map hn (hK ρ n hn) β'
  refine ⟨k, inferInstance, u ≫ Y.hom, ρ, ζ, fun a => yk ≫ et a, hK ρ n hn, ⟨v, ?_⟩, by rw [Category.comp_id, hρ],
    hprim, fun a a' => by beta_reduce; rw [hadd', MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow', MonObj.comp_one],
    (key k (u ≫ Y.hom) ρ ζ yk hρ hζ).2 ?_⟩
  · show Y.hom (u v) = _
    rw [huy v, ey]
  · rintro _ ⟨v', rfl⟩
    show u v' ∈ C
    rw [huy v']
    exact hyC

end GlobalTheory
