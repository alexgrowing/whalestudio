import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem card_eq_relIndex {G Γ : Type} [Group G] (H L : Subgroup G) (r : Γ → G) (hr : ∀ x, r x ∈ L)
    (hu : ∀ k ∈ L, ∃! x, k * (r x)⁻¹ ∈ H) : Nat.card Γ = H.relIndex L := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (QuotientGroup.mk ⟨(r x)⁻¹, L.inv_mem (hr x)⟩ : L ⧸ H.subgroupOf L)) ⟨?_, ?_⟩)
  · intro x y e
    have e' := QuotientGroup.eq.mp e
    have h2 : r x * (r y)⁻¹ ∈ H := by simpa [Subgroup.mem_subgroupOf] using e'
    have h1 : r x * (r x)⁻¹ ∈ H := by simp [H.one_mem]
    exact (hu (r x) (hr x)).unique h1 h2
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, -⟩ := hu (g : G)⁻¹ (L.inv_mem g.2)
      refine ⟨x, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      have h3 := H.inv_mem hx
      simpa using h3

private theorem fEt_normal (hb : FEtBasic) (hg : TwGal) {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)
    (m j : X.ι) (b : X.admitted m j 1) (hn : ∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) :
    FEt (X.tr m j 1 b.1 b.2) ((X.K m).relIndex (X.K j)) := by
  obtain ⟨Γ, _, _, r, c, hr, hu, hG⟩ := hg X m j b hn
  rw [← card_eq_relIndex _ _ r hr hu]
  exact hb.2.2 _ Γ _ hG

theorem UpperTheory.Gal.G3.pTwFEt :
    FEtBasic → TwGal → TwFEt := by
  intro hb hg B G _ X i j a
  obtain ⟨m, hmj, hn, hS⟩ := X.deep j {(i, 1)}
  have hmi : X.K m ≤ X.K i := fun u hu => by simpa using hS (i, 1) (by simp) u hu
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have b : X.admitted m j 1 := ⟨a.1, fun u hu => by simpa using hmj hu⟩
  have b' : X.admitted m i 1 := ⟨a.1, fun u hu => by simpa using hmi hu⟩
  have h1 := fEt_normal hb hg X m j b hn
  have h2 := fEt_normal hb hg X m i b' (fun k hk u hu => hn k (hij hk) u hu)
  have hc : X.tr m i 1 b'.1 b'.2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    have e : ∀ (h : G) (_ : h = 1) p q, X.tr m j h p q = X.tr m j 1 b.1 b.2 := by
      rintro _ rfl _ _; rfl
    rw [X.tr_mul m i j 1 1 b'.1 b'.2 a.1 a.2 (by simpa using a.1) (by simpa using b.2)]
    exact e _ (mul_one 1) _ _
  refine ⟨X.fin i j a.1 a.2, X.etale i j a.1 a.2, fun K _ _ x => ?_⟩
  set s := X.tr i j 1 a.1 a.2 with hs
  set r := X.tr m i 1 b'.1 b'.2 with hr
  have fs : Finite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} :=
    have := X.fin i j a.1 a.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds s K x).to_subtype
  have fr : ∀ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} := fun y =>
    have := X.fin m i b'.1 b'.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds r K y.1).to_subtype
  have := Fintype.ofFinite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x}
  have e1 : {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ X.tr m j 1 b.1 b.2 = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc, hc, w.2]⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← hc, ← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        change w ≫ r = y at hw
        subst hw
        rfl }
  have hcount : Nat.card {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} * (X.K m).relIndex (X.K i) =
      (X.K m).relIndex (X.K j) := by
    rw [← h1.2.2 K x, Nat.card_congr e1, Nat.card_sigma]
    simp only [h2.2.2 K, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hmul := Subgroup.relIndex_mul_relIndex (X.K m) (X.K i) (X.K j) hmi hij
  have hpos : 0 < (X.K m).relIndex (X.K i) := Nat.pos_of_ne_zero (X.idx m i)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, ← hcount, mul_comm]
