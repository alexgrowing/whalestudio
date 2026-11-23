import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LiftIntegral
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnSpec
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

section Act

variable {l : ℕ} {Y : Scheme.{0}} {J : Type} {T : J → Corr l Y} (D : WDat l T)

private lemma unit_away (U : Type) [CommRing U] :
    IsUnit ((l : ℕ) : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := by
  have hunit : IsUnit ((l : ℕ) : Localization.Away (l : U)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : U)) (l : U)
    simpa using this
  have := hunit.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : U)))).inv.hom
  rwa [map_natCast] at this

private lemma split_point_generic {U : Type} [CommRing U] (w : Spec (CommRingCat.of U) ⟶ D.W) (j : J) :
    SplitOn (T j).p (awayPt l U ≫ w ≫ D.π) fun i => awayPt l U ≫ w ≫ D.s j i := by
  have h := D.gen _ (awayPt l U ≫ w) (unit_away U) j
  simp only [Category.assoc] at h
  exact h

private lemma split_pt {U : Type} [CommRing U] (w : Spec (CommRingCat.of U) ⟶ D.W)
    (σ : ∀ j, Equiv.Perm (Fin (T j).d)) (j : J) :
    SplitOn (T j).p (awayPt l U ≫ w ≫ D.π) fun i => awayPt l U ≫ w ≫ D.s j (σ j i) :=
  (splitRules.1 _ _ (𝟙 _) _ (split_point_generic D w j)).2 (σ j)

private lemma act_ex {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    ∃! w₁ : Spec (CommRingCat.of U) ⟶ D.W, w₁ ≫ D.π = w ≫ D.π ∧ ∀ j i, w₁ ≫ D.s j i = w ≫ D.s j (σ j i) :=
  D.univ U hl (w ≫ D.π) (fun j i => w ≫ D.s j (σ j i)) (fun j i => by rw [Category.assoc, D.hs])
    (fun j => split_pt D w σ j)

private def act {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    Spec (CommRingCat.of U) ⟶ D.W := (act_ex D hl w σ).exists.choose

private lemma act_spec {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    act D hl w σ ≫ D.π = w ≫ D.π ∧ ∀ j i, act D hl w σ ≫ D.s j i = w ≫ D.s j (σ j i) :=
  (act_ex D hl w σ).exists.choose_spec

private lemma act_eq {U : Type} [CommRing U] (hl : (l : U) ∈ nonZeroDivisors U)
    (w w₁ : Spec (CommRingCat.of U) ⟶ D.W) (σ : ∀ j, Equiv.Perm (Fin (T j).d))
    (h₁ : w₁ ≫ D.π = w ≫ D.π) (h₂ : ∀ j i, w₁ ≫ D.s j i = w ≫ D.s j (σ j i)) :
    act D hl w σ = w₁ :=
  (act_ex D hl w σ).unique (act_spec D hl w σ) ⟨h₁, h₂⟩

end Act

section Idem

variable {R : Type} [CommRing R]

private lemma coi_pi {J : Type} [Fintype J] [DecidableEq J] {I : J → Type} [∀ j, Fintype (I j)]
    (e : ∀ j, I j → R) (he : ∀ j, CompleteOrthogonalIdempotents (e j)) :
    CompleteOrthogonalIdempotents fun τ : (∀ j, I j) => ∏ j, e j (τ j) := by
  refine ⟨⟨fun τ => ?_, fun τ τ' h => ?_⟩, ?_⟩
  · change (∏ j, e j (τ j)) * (∏ j, e j (τ j)) = ∏ j, e j (τ j)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (he j).toOrthogonalIdempotents.idem (τ j)
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    change (∏ j, e j (τ j)) * (∏ j, e j (τ' j)) = 0
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ j) ((he j).toOrthogonalIdempotents.ortho hj)
  · have h : ∏ j, ∑ i, e j i = 1 := by simp [fun j => (he j).complete]
    rw [Finset.prod_univ_sum] at h
    simpa [Fintype.piFinset_univ] using h

end Idem

variable {l : ℕ} [Fact l.Prime]

private lemma lift_coi (A : PAlg l) {I : Type} [Fintype I] (e : I → A.U)
    (he : CompleteOrthogonalIdempotents e) :
    ∃ e₀ : I → A.A, CompleteOrthogonalIdempotents e₀ ∧ ∀ i, A.sharp (e₀ i) = e i := by
  classical
  have s1 : A.sharp 1 = 1 := map_one _
  have s0 : A.sharp 0 = 0 := by
    have := (RL.sharp_cong A).2.2 1 IsIdempotentElem.one
    simpa [s1] using this
  have hsub : ∀ a : A.A, IsIdempotentElem a → A.sharp (1 - a) = 1 - A.sharp a := (RL.sharp_cong A).2.2
  have h := fun i => (RL.idem_au A (e i) (he.toOrthogonalIdempotents.idem i)).exists
  choose e₀ h1 h2 using h
  have hz : ∀ a : A.A, IsIdempotentElem a → A.sharp a = 0 → a = 0 := fun a ha hs =>
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, s0⟩
  have ho : ∀ a : A.A, IsIdempotentElem a → A.sharp a = 1 → a = 1 := fun a ha hs =>
    (RL.idem_au A 1 IsIdempotentElem.one).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.one, s1⟩
  have hort : ∀ i j, i ≠ j → e₀ i * e₀ j = 0 := fun i j hij =>
    hz _ ((h1 i).mul (h1 j)) (by
      rw [map_mul, h2, h2]
      exact he.toOrthogonalIdempotents.ortho hij)
  have hsum : ∀ s : Finset I, IsIdempotentElem (∑ i ∈ s, e₀ i) ∧ A.sharp (∑ i ∈ s, e₀ i) = ∑ i ∈ s, e i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using IsIdempotentElem.zero, by simpa using s0⟩
    | insert a s ha ih =>
      obtain ⟨i1, i2⟩ := ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hbc : e₀ a * ∑ i ∈ s, e₀ i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hort a i fun h => ha (h ▸ hi)
      have hid : IsIdempotentElem (e₀ a + ∑ i ∈ s, e₀ i) := by
        have e1 : e₀ a * e₀ a = e₀ a := h1 a
        have e2 : (∑ i ∈ s, e₀ i) * (∑ i ∈ s, e₀ i) = ∑ i ∈ s, e₀ i := i1
        change (e₀ a + ∑ i ∈ s, e₀ i) * (e₀ a + ∑ i ∈ s, e₀ i) = _
        rw [add_mul, mul_add, mul_add, e1, e2, hbc, mul_comm, hbc]
        simp
      refine ⟨hid, ?_⟩
      have hx : e₀ a + ∑ i ∈ s, e₀ i = 1 - (1 - e₀ a) * (1 - ∑ i ∈ s, e₀ i) := by
        linear_combination hbc
      have hm : A.sharp (e₀ a) * A.sharp (∑ i ∈ s, e₀ i) = 0 := by
        rw [← map_mul, hbc, s0]
      rw [hx, hsub _ ((h1 a).one_sub.mul i1.one_sub), map_mul, hsub _ (h1 a), hsub _ i1, h2, ← i2]
      rw [h2] at hm
      linear_combination -hm
  refine ⟨e₀, ⟨⟨h1, fun i j hij => hort i j hij⟩, ?_⟩, h2⟩
  obtain ⟨i1, i2⟩ := hsum Finset.univ
  exact ho _ i1 (by rw [i2, he.complete])

variable {O : Type} [CommRing O] {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {J : Type}
  {T : J → Corr l Y}

private def gAct (κ : O →+* OC l) (D : WDat l T) (σ : ∀ j, Equiv.Perm (Fin (T j).d)) :
    PX (D.π ≫ q) κ ⟶ PX (D.π ≫ q) κ where
  app A := TypeCat.ofHom fun w => ⟨act D (RL.u_tf A).1 w.1 σ, by
    rw [← Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).1, Category.assoc]
    exact w.2⟩
  naturality A B f := by
    ext w
    refine Subtype.ext ?_
    change act D (RL.u_tf B).1 (Spec.map (CommRingCat.ofHom (PAlg.mapU f)) ≫ w.1) σ =
      Spec.map (CommRingCat.ofHom (PAlg.mapU f)) ≫ act D (RL.u_tf A).1 w.1 σ
    refine act_eq D _ _ _ σ ?_ fun j i => ?_
    · rw [Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).1, Category.assoc]
    · rw [Category.assoc, (act_spec D (RL.u_tf A).1 w.1 σ).2, Category.assoc]

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.wTrans :
    UpperTheory.Ru.crystallineComparison.WTrans := by
  intro l _ O _ Y q κ J _ _ T D
  refine ⟨fun σ => gAct κ D σ, ?_, ?_, ?_⟩
  · intro σ
    ext A w
    refine Subtype.ext ?_
    exact (act_spec D (RL.u_tf A).1 w.1 σ).1
  · intro A y
    have hT := testFacts l A.obj A.property
    have hz : ∀ j, ∃ z : Fin (T j).d → (Spec (CommRingCat.of A.obj.U) ⟶ (T j).Z), (∀ i, z i ≫ (T j).p = y.1) ∧
        SplitOn (T j).p (awayPt l A.obj.U ≫ y.1) fun i => awayPt l A.obj.U ≫ z i := fun j =>
      splitEx l Fact.out Y (T j) A.obj.U hT.1 hT.2.1 hT.2.2.1 y.1
    choose z hz hs using hz
    obtain ⟨w, ⟨hw, -⟩, -⟩ := D.univ A.obj.U hT.1 y.1 z hz hs
    exact ⟨⟨w, by rw [← Category.assoc, hw]; exact y.2⟩, Subtype.ext hw⟩
  · intro A w w' hp
    have hT := testFacts l A.obj A.property
    have hww : w.1 ≫ D.π = w'.1 ≫ D.π := congrArg Subtype.val hp
    have hperm : ∀ j, ∃ e : Equiv.Perm (Fin (T j).d) → A.obj.U, CompleteOrthogonalIdempotents e ∧
        ∀ (σ : Equiv.Perm (Fin (T j).d)) (V : Type) [CommRing V] (ρ : A.obj.U →+* V), ρ (e σ) = 1 → ∀ i,
          Spec.map (CommRingCat.ofHom ρ) ≫ w'.1 ≫ D.s j i = Spec.map (CommRingCat.ofHom ρ) ≫ w.1 ≫ D.s j (σ i) := fun j =>
      splitPerm l Y (T j) A.obj.U hT.1 hT.2.1 (w.1 ≫ D.π) (fun i => w.1 ≫ D.s j i) (fun i => w'.1 ≫ D.s j i)
        (fun i => by rw [Category.assoc, D.hs]) (fun i => by rw [Category.assoc, D.hs, hww])
        (split_point_generic D w.1 j) (by rw [hww]; exact split_point_generic D w'.1 j)
    choose e he hE using hperm
    obtain ⟨e₀, he₀, hs⟩ := lift_coi A.obj _ (coi_pi e he)
    obtain ⟨B, f, hdec, hf⟩ := decEx l A (∀ j, Equiv.Perm (Fin (T j).d)) e₀ he₀
    refine ⟨(⟨_, B, f⟩ : Fam A), hdec, fun τ => ?_⟩
    let ρ : A.obj.U →+* (B τ).obj.U := PAlg.mapU (f τ).hom
    have hρ : ρ (∏ j, e j (τ j)) = 1 := by
      rw [← hs τ]
      refine ((RL.expand_nat A.obj (B τ).obj (f τ).hom).2.2.1 (e₀ τ)).trans ?_
      rw [hf τ, map_one]
    have hρj : ∀ j, ρ (e j (τ j)) = 1 := by
      intro j
      have h1 := hρ
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), map_mul] at h1
      have h2 : ρ (e j (τ j)) * ρ (e j (τ j)) = ρ (e j (τ j)) := by
        rw [← map_mul, (he j).toOrthogonalIdempotents.idem (τ j)]
      calc ρ (e j (τ j)) = ρ (e j (τ j)) * (ρ (e j (τ j)) * _) := by rw [h1, mul_one]
        _ = _ := by rw [← mul_assoc, h2, h1]
    have key : ∀ j i, Spec.map (CommRingCat.ofHom ρ) ≫ w'.1 ≫ D.s j i =
        Spec.map (CommRingCat.ofHom ρ) ≫ w.1 ≫ D.s j (τ j i) := fun j i => hE j (τ j) _ ρ (hρj j) i
    have hstep : ∀ σ, (gAct κ D σ).app _ ((PX (D.π ≫ q) κ).map (f τ).hom w') =
        (gAct κ D (τ * σ)).app _ ((PX (D.π ≫ q) κ).map (f τ).hom w) := by
      intro σ
      refine Subtype.ext ?_
      change act D (RL.u_tf _).1 (Spec.map (CommRingCat.ofHom ρ) ≫ w'.1) σ =
        act D (RL.u_tf _).1 (Spec.map (CommRingCat.ofHom ρ) ≫ w.1) (τ * σ)
      refine act_eq D _ _ _ σ ?_ fun j i => ?_
      · rw [(act_spec D _ _ _).1, Category.assoc, Category.assoc, hww]
      · rw [(act_spec D _ _ _).2]
        simp only [Category.assoc]
        rw [key]
        rfl
    simp only [hstep]
    have hm := Multiset.map_univ_val_equiv (Equiv.mulLeft τ)
    conv_lhs => rw [← hm]
    rw [Multiset.map_map]
    rfl
