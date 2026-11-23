import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqMass
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbProd

open MulAction

namespace UpperTheory.V.Z.Sym.Glob

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

theorem rpg_ext (P : RPG G Gv K) {a b : G} (h : ∀ v, P.p v a = P.p v b) : a = b := by
  have hab := P.inj (a * b⁻¹) fun v => by rw [map_mul, map_inv, h v, mul_inv_cancel]
  exact mul_inv_eq_one.mp hab

theorem mem_box (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

theorem smul_mk_iff {A : Type} [Group A] (U : Subgroup A) (x g : A) : x • (g : A ⧸ U) = g ↔ g⁻¹ * x * g ∈ U := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, ← U.inv_mem_iff]
  simp [mul_assoc]

theorem rpg_hom {T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)] {C₀ : ∀ v, Subgroup (Tv v)} (P : RPG G Gv K)
    (Q : RPG T Tv C₀) (ιv : ∀ v, Tv v →* Gv v) (h : ∀ᶠ v in Filter.cofinite, (C₀ v).map (ιv v) ≤ K v) :
    ∃ ι : T →* G, ∀ v t, P.p v (ι t) = ιv v (Q.p v t) := by
  have hx : ∀ t : T, ∀ᶠ v in Filter.cofinite, ιv v (Q.p v t) ∈ K v := fun t =>
    ((Q.ae t).and h).mono fun v hv => hv.2 ⟨_, hv.1, rfl⟩
  choose g hg using fun t => P.surj _ (hx t)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_ }, fun v t => hg t v⟩
  · exact rpg_ext P fun v => by simp only [hg, map_one]
  · intro a b
    exact rpg_ext P fun v => by simp only [hg, map_mul]

private theorem box_relIndex_ne_zero_of_local {T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)]
    {C₀ : ∀ v, Subgroup (Tv v)} (Q : RPG T Tv C₀) (A B : ∀ v, Subgroup (Tv v))
    (hA : ∀ v, (A v).relIndex (B v) ≠ 0) (hfin : ∀ᶠ v in Filter.cofinite, B v ≤ A v) :
    (Q.box A).relIndex (Q.box B) ≠ 0 := by
  classical
  have key : ∀ F : Finset I, ∃ D : Subgroup T, D.relIndex (Q.box B) ≠ 0 ∧
      ∀ t ∈ D, ∀ v ∈ F, Q.p v t ∈ A v := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨⊤, by simp, fun _ _ v hv => by simp at hv⟩
    | @insert a F _ ih =>
      obtain ⟨D, hD, hDF⟩ := ih
      refine ⟨D ⊓ (A a).comap (Q.p a), Subgroup.relIndex_inf_ne_zero hD ?_, ?_⟩
      · rw [Subgroup.relIndex_comap]
        refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) (hA a)
        rw [Subgroup.map_le_iff_le_comap]
        intro t ht
        exact (mem_box Q B t).1 ht a
      · intro t ht v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact ht.2
        · exact hDF t ht.1 v hv
  obtain ⟨D, hD, hDF⟩ := key (Filter.eventually_cofinite.1 hfin).toFinset
  refine mt (Subgroup.relIndex_eq_zero_of_le_left (K := Q.box A) ?_)
    (Subgroup.relIndex_inf_ne_zero hD (by simp : (Q.box B).relIndex (Q.box B) ≠ 0))
  intro t ht
  rw [mem_box]
  intro v
  by_cases hv : B v ≤ A v
  · exact hv ((mem_box Q B t).1 ht.2 v)
  · exact hDF t ht.1 v (by simpa using hv)

theorem gqAbs {T H : Type} [CommGroup T] [Group H] {Tv : I → Type} [∀ v, CommGroup (Tv v)] (U : ∀ v, Subgroup (Gv v))
    {C₀ : ∀ v, Subgroup (Tv v)} (C : ∀ v, Subgroup (Tv v)) (P : RPG G Gv K) (Q : RPG T Tv C₀)
    (ιv : ∀ v, Tv v →* Gv v) (θ : G →* G) (θv : ∀ v, Gv v →* Gv v) (f : G → ℂ) (fv : ∀ v, Gv v → ℂ) (δ : G)
    (φ : H →* T) (j : H →* G) (H₀ : Subgroup H)
    (hj : ∀ h v, P.p v (j h) = ιv v (Q.p v (φ h))) (hθ : ∀ v g, P.p v (θ g) = θv v (P.p v g))
    (hf : ∀ g, f g = ∏ᶠ v, fv v (P.p v g)) (hinv : ∀ v, ∀ u ∈ U v, ∀ x, fv v (u⁻¹ * x * θv v u) = fv v x)
    (hc : ∀ v t, (ιv v t)⁻¹ * P.p v δ * θv v (ιv v t) = P.p v δ) (S : Finset I)
    (hS : ∀ v ∈ S, FinOrb (ιv v) (θv v) (U v) (fv v) (P.p v δ))
    (hoff : ∀ v ∉ S, K v ≤ U v ∧ C₀ v ≤ C v ∧ (C v).map (ιv v) ≤ U v ∧ fv v (P.p v δ) = 1 ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ u ∈ U v, y = ιv v t * u)
    (hK : ∀ v ∉ S, (C₀ v).map (ιv v) ≤ K v)
    (hst : ∀ v (y : Gv v ⧸ U v), (stabilizer (Gv v) y).comap (ιv v) ≤ C v ∧ ((stabilizer (Gv v) y).comap (ιv v)).relIndex (C v) ≠ 0)
    (h0 : ∀ z ∈ H₀, ∀ v y, y⁻¹ * P.p v (j z) * y ∈ U v)
    (m1 : (φ.range ⊔ Q.box C).index ≠ 0) (m2 : H₀.relIndex ((Q.box C).comap φ) ≠ 0) :
    gqOn j H₀ (P.box U) (fun y => f (y.out⁻¹ * δ * θ y.out)) =
      mass φ H₀ (Q.box C) * ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) := by
  have hS' : ∀ᶠ v in Filter.cofinite, v ∉ S :=
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by simpa using hv)
  obtain ⟨ι, hι⟩ := rpg_hom P Q ιv (hS'.mono hK)
  have hjι : j = ι.comp φ :=
    MonoidHom.ext fun z => rpg_ext P fun v => by rw [hj, MonoidHom.comp_apply, hι]
  subst hjι
  have hbox : ∀ (g x : G), x • (g : G ⧸ P.box U) = g ↔
      ∀ v, (P.p v g)⁻¹ * P.p v x * P.p v g ∈ U v := by
    intro g x
    rw [smul_mk_iff, mem_box]
    simp only [map_mul, map_inv]
  have hprod := Tf.orbProd I G T Gv Tv K U C₀ C P Q ι ιv θ θv f fv δ hι hθ hf hinv hc S hS hoff
  refine (Tf.gqMass H T G φ ι H₀ (Q.box C) θ (P.box U) f δ ?_ ?_ hprod.1 ?_ m1 m2 ?_ ?_).trans ?_
  · intro u hu x
    rw [hf, hf]
    refine finprod_congr fun v => ?_
    simp only [map_mul, map_inv, hθ]
    exact hinv v _ ((mem_box P U u).1 hu v) _
  · intro t
    exact rpg_ext P fun v => by
      simp only [map_mul, map_inv, hθ, hι]
      exact hc v _
  · intro z hz y
    refine QuotientGroup.induction_on y fun g => ?_
    exact (hbox g _).2 fun v => h0 z hz v _
  · intro y
    refine QuotientGroup.induction_on y fun g _ => ?_
    have hEq : (stabilizer G (g : G ⧸ P.box U)).comap ι =
        Q.box (fun v => (stabilizer (Gv v) ((P.p v g : Gv v ⧸ U v))).comap (ιv v)) := by
      ext t
      rw [Subgroup.mem_comap, mem_stabilizer_iff, hbox, mem_box]
      simp only [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff, hι]
    rw [hEq]
    refine ⟨fun t ht => (mem_box Q C t).2 fun v => (hst v _).1 ((mem_box Q _ t).1 ht v), ?_⟩
    refine box_relIndex_ne_zero_of_local Q _ C (fun v => (hst v _).2) ?_
    refine ((P.ae g).and hS').mono fun v hv t ht => ?_
    obtain ⟨hKU, -, hCU, -⟩ := hoff v hv.2
    rw [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff]
    have hg : P.p v g ∈ U v := hKU hv.1
    exact (U v).mul_mem ((U v).mul_mem ((U v).inv_mem hg) (hCU ⟨t, ht, rfl⟩)) hg
  · intro z hz
    rw [Subgroup.mem_comap, mem_box]
    intro v
    refine (hst v ((1 : Gv v) : Gv v ⧸ U v)).1 ?_
    rw [Subgroup.mem_comap, mem_stabilizer_iff, smul_mk_iff]
    have h1 := h0 z hz v 1
    rwa [MonoidHom.comp_apply, hι] at h1
  · rw [hprod.2]

end UpperTheory.V.Z.Sym.Glob
