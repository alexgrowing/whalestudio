import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dif_pos a, dif_pos hh]
  simp only [e]

theorem UpperTheory.Gal.G3.pSumFn :
    SumFn.{u} := by
  classical
  intro B G _ X F _ T m j A _ e he f hf
  have hmem : ∀ (a : A) (y : G), e a * y ∈ X.K j ↔ (y : G ⧸ X.K j) = (((e a)⁻¹ : G) : G ⧸ X.K j) := by
    intro a y
    rw [eq_comm, QuotientGroup.eq, inv_inv]
  have hex : ∀ g, f g ≠ 0 → ∃ a, e a * g ∈ X.K j := by
    intro g hg
    by_contra hn
    have : IsEmpty {a : A // e a * g ∈ X.K j} := ⟨fun a => hn ⟨a.1, a.2⟩⟩
    exact hg (by rw [hf, Nat.card_of_isEmpty, Nat.cast_zero])
  have h1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := by
    intro g hg
    obtain ⟨a, ha⟩ := hex g hg
    have hk : g⁻¹ = (e a * g)⁻¹ * e a := by group
    rw [hk]
    exact isAdmissible_flagPair_of_unitriangular_left_automorphism X ((X.K j).inv_mem ha) (he a)
  set Fq : A → G ⧸ X.K j := fun a => (((e a)⁻¹ : G) : G ⧸ X.K j) with hFq
  refine ⟨h1, fun hl => ⟨fun k hk g => ⟨hl k hk g, ?_⟩, fun g hg => (h1 g hg).1, ?_⟩, ?_⟩
  · rw [hf, hf]
    have h2 : ∀ a, e a * (g * k) ∈ X.K j ↔ e a * g ∈ X.K j := fun a => by
      rw [← _root_.mul_assoc]
      exact Subgroup.mul_mem_cancel_right _ hk
    simp only [h2]
  · refine (Set.finite_range Fq).subset fun y hy => ?_
    obtain ⟨a, ha⟩ := hex _ hy
    refine ⟨a, ?_⟩
    have := (hmem a y.out).1 ha
    rw [QuotientGroup.out_eq'] at this
    exact this.symm
  · intro x
    have hpl : ∀ a, X.pl T m j (e a) x = X.pl T m j (Fq a).out⁻¹ x := by
      intro a
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (X.K j) (e a)⁻¹
      have h2 : (Fq a).out⁻¹ = (k : G)⁻¹ * e a := by
        simp only [hFq, hk, mul_inv_rev, inv_inv]
      rw [h2, pl_left X T ((X.K j).inv_mem k.2) (he a)]
    have hfy : ∀ y : G ⧸ X.K j, f y.out = ((Finset.univ.filter (fun a => Fq a = y)).card : F) := by
      intro y
      have h2 : Nat.card {a : A // e a * y.out ∈ X.K j} = (Finset.univ.filter (fun a => Fq a = y)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hmem, QuotientGroup.out_eq', eq_comm]
      rw [hf, h2]
    have hsupp : Function.support (fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x) ⊆
        ↑(Finset.univ.image Fq) := by
      intro y hy
      by_contra hn
      apply hy
      have h0 : Finset.univ.filter (fun a => Fq a = y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a _ ha
        exact hn (by simpa using ⟨a, ha⟩)
      simp only [hfy, h0, Finset.card_empty, Nat.cast_zero, zero_smul]
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image Fq) (g := Fq)
        (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hfy, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hpl a, (Finset.mem_filter.1 ha).2]
