import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelianStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NeatUnip

theorem iter_comp {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (α : G ⟶ G) (n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) :
    x ≫ (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = (fun z => z ≫ α)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [← ih, Category.assoc]

theorem finite_order_unipotent_eq_id : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  intro E _ _ k _ _ _ G _ act α n m g r I hG hα hcomm hn hpow hg hI hI2 hr hfin hunip
  classical
  haveI := hG.comm
  haveI := hα
  haveI : ∀ a, IsMonHom (act.act a) := act.hom
  letI cg : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  have act0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  letI inst : Module (𝓞 E) (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { smul := fun a x => Additive.ofMul (x.toMul ≫ act.act a)
    one_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 1) = x
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a * b)) = Additive.ofMul ((x.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm a b, act.mul, Category.assoc]
    smul_zero := fun a => by
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp k)) ⟶ G) ≫ act.act a) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun a x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ act.act a) = Additive.ofMul ((x.toMul ≫ act.act a) * (y.toMul ≫ act.act a))
      rw [MonObj.mul_comp]
    add_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a + b)) = Additive.ofMul ((x.toMul ≫ act.act a) * (x.toMul ≫ act.act b))
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [act0, MonObj.comp_one] }
  have hsmul : ∀ (a : 𝓞 E) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)), a • x = Additive.ofMul (x.toMul ≫ act.act a) :=
    fun _ _ => rfl
  have htors : ∀ (J : Ideal (𝓞 E)) (x : 𝟙_ (Over (Sp k)) ⟶ G),
      (∀ a ∈ J, a • Additive.ofMul x = 0) ↔ ∀ a ∈ J, x ≫ act.act a = 1 := fun J x =>
    forall₂_congr fun a _ => by rw [hsmul]; exact ofMul_eq_zero
  let β : Additive (𝟙_ (Over (Sp k)) ⟶ G) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp k)) ⟶ G) :=
  { toFun := fun x => Additive.ofMul (x.toMul ≫ α)
    map_add' := fun x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ α) = Additive.ofMul ((x.toMul ≫ α) * (y.toMul ≫ α))
      rw [MonObj.mul_comp]
    map_smul' := fun a x => by
      show Additive.ofMul ((x.toMul ≫ act.act a) ≫ α) = Additive.ofMul ((x.toMul ≫ α) ≫ act.act a)
      rw [Category.assoc, hcomm, Category.assoc] }
  have hβ : ∀ x, β x = Additive.ofMul (x.toMul ≫ α) := fun _ => rfl

  let A : AddSubgroup (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { carrier := {x | ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0}
    add_mem' := by
      rintro x y ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨i + j, fun a ha => ?_⟩
      rw [smul_add, hi a (Ideal.pow_le_pow_right (by omega) ha),
        hj a (Ideal.pow_le_pow_right (by omega) ha), add_zero]
    zero_mem' := ⟨0, fun a _ => smul_zero a⟩
    neg_mem' := by
      rintro x ⟨j, hj⟩
      exact ⟨j, fun a ha => by rw [smul_neg, hj a ha, neg_zero]⟩ }
  have memA : ∀ x, x ∈ A ↔ ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0 := fun _ => Iff.rfl
  let βA : A →+ A :=
  { toFun := fun x => ⟨β x.1, by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      exact ⟨j, fun a ha => by rw [← LinearMap.map_smul, hj a ha, map_zero]⟩⟩
    map_zero' := Subtype.ext (map_zero β)
    map_add' := fun x y => Subtype.ext (map_add β x.1 y.1) }
  have hβA : ∀ x : A, ((βA x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β x.1 := fun _ => rfl
  have hβAit : ∀ (N : ℕ) (x : A), ((βA^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β^[N] x.1 := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hβA, ih]
  have hβit : ∀ (N : ℕ) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)),
      β^[N] x = Additive.ofMul ((fun z => z ≫ α)^[N] x.toMul) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  have hsubit : ∀ (N : ℕ) (x : A),
      (((fun z : A => βA z - z)^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) =
        Additive.ofMul ((fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[N] (Additive.toMul x.1)) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AddSubgroup.coe_sub, hβA, ih, hβ,
        toMul_ofMul, ← ofMul_div, div_eq_mul_inv]
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hdivM : ∀ x : Additive (𝟙_ (Over (Sp k)) ⟶ G), ∃ y, g • y = x := by
    intro x
    obtain ⟨y, hy⟩ := GlobalTheory.SS.torusExtension_points_divisible k G (GlobalTheory.TorsionDense.nonempty_torusExtension G hG)
      g hg.one_le x.toMul
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy]; rfl⟩
  obtain ⟨hred1, hred2⟩ := GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion E (Additive (𝟙_ (Over (Sp k)) ⟶ G)) g I hg hI hI2 hdivM
  have key := GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id A βA n g r m hn
    (fun x => Subtype.ext (by
      rw [hβAit, hβit, ← iter_comp, hpow, Category.comp_id]; rfl))
    hg (by omega)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      obtain ⟨y, hy, hy'⟩ := hred1 j x.1 hj
      exact ⟨⟨y, j + 1, hy'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hy)⟩)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      refine ⟨j, Subtype.ext ?_⟩
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
      exact hj _ (Ideal.pow_mem_pow hgI j))
    (by
      obtain ⟨T, hT, hTm⟩ := hfin
      refine ⟨(T.map Additive.ofMul.toEmbedding).subtype (· ∈ A), ?_, fun x hx => ?_⟩
      · rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_map]; exact hT)
      · have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
        obtain ⟨j, hj⟩ := (memA x.1).1 x.2
        have h1 := hred2 j x.1 hj hx'
        rw [Finset.mem_subtype, Finset.mem_map]
        exact ⟨Additive.toMul x.1, hTm _ ((htors I _).1 h1), rfl⟩)
    (fun x hx => by
      have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      have h1 := hred2 j x.1 hj hx'
      refine Subtype.ext ?_
      have h2 := hunip (Additive.toMul x.1) ((htors I _).1 h1)
      rw [hsubit, h2]; rfl)
  have hfix : ∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ α = x := by
    intro j x hx
    have h := congrArg Subtype.val (key ⟨Additive.ofMul x, j, (htors _ x).2 hx⟩)
    exact congrArg Additive.toMul h
  have hγ : IsMonHom (α * (𝟙 G)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hI1 : I ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hI
    exact hg.one_lt.ne hI
  have h1 := GlobalTheory.T.eq_one_of_kills_idealPowerTorsion_semiAbelian E k G act (α * (𝟙 G)⁻¹) I hG hγ
    (fun a => by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp, hcomm, Category.comp_id,
        Category.id_comp])
    hI1
    (fun j x hx => by rw [MonObj.comp_mul, GrpObj.comp_inv, hfix j x hx, Category.comp_id, mul_inv_cancel])
  rw [mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.NeatUnip
