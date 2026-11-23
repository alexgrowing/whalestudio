import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.RigRescale

variable {X Y : Scheme.{0}}

theorem germ_id_pull (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by
  rw [gm_pull (𝟙 Y) f y U h a, Category.id_comp]

theorem germ_pull_g (L : LB X) (f : Y ⟶ X) (y : Y) (P P' : PUnit → L.ι)
    (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') ((L.pull f).g P P') =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (L.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) ⟨hp, hp'⟩ _)

theorem germ_linCombIso {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) (y : Y) (P : PUnit → M.ι)
    (Q : PUnit → L.ι) (hp : f y ∈ M.U (P PUnit.unit)) (hq : f y ∈ L.U (Q PUnit.unit)) :
    gm (𝟙 Y) y ((M.pull f).U P ⊓ (L.pull f).U Q)
        ((LB.linCombIso w (K := PUnit) (fun _ => f) (fun _ => 1)).s (P, Q)) =
      gm f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit)) (w.s (P PUnit.unit, Q PUnit.unit)) := by
  have hm : y ∈ (M.pull f).U P ⊓ (L.pull f).U Q := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (w.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (show f y ∈ M.U (P PUnit.unit) ⊓ L.U (Q PUnit.unit) from ⟨hp, hq⟩) _)

theorem germ_iso_isGen {L M : LB X} (w : LB.Iso L M) (hw : w.IsGen) (f : Y ⟶ X) (y : Y)
    (p p' : M.ι) (q q' : L.ι) (hp : f y ∈ M.U p) (hp' : f y ∈ M.U p') (hq : f y ∈ L.U q)
    (hq' : f y ∈ L.U q') :
    gm f y ((LB.div M L).U (p, q)) (w.s (p, q)) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ *
        gm f y ((LB.div M L).U (p', q')) (w.s (p', q')) := by
  have hm : f y ∈ M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') := ⟨⟨hp, hq⟩, hp', hq'⟩
  have h := (congrArg (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) (hw (p, q) (p', q'))).trans
    (map_mul (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) ((LB.div M L).g (p, q) (p', q'))
      (res inf_le_right (w.s (p', q'))))
  have hg : gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) ((LB.div M L).g (p, q) (p', q')) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ := by
    show gm f y _ (res _ (M.g p p') * (res _ (L.g q q'))⁻¹) = _
    rw [map_mul, map_inv]
    exact congrArg₂ (· * ·) (gm_res f y _ hm _) (congrArg _ (gm_res f y _ hm _))
  calc gm f y ((LB.div M L).U (p, q)) (w.s (p, q))
      = gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) (res inf_le_left (w.s (p, q))) :=
        (gm_res f y _ hm _).symm
    _ = _ := h
    _ = _ := congrArg₂ (· * ·) hg (gm_res f y _ hm _)

theorem germ_gen_isGen (L : LB X) (f : Y ⟶ X) (t : LB.Gen (L.pull f)) (ht : t.IsGen) (y : Y)
    (P P' : PUnit → L.ι) (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P) (t.s P) =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) *
        gm (𝟙 Y) y ((L.pull f).U P') (t.s P') := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  have h := congrArg (gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P')) (ht P P')
  rw [map_mul] at h
  calc gm (𝟙 Y) y ((L.pull f).U P) (t.s P)
      = gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') (res inf_le_left (t.s P)) :=
        (gm_res (𝟙 Y) y _ hm _).symm
    _ = _ := h
    _ = _ := by rw [germ_pull_g L f y P P' hp hp']; exact congrArg _ (gm_res (𝟙 Y) y _ hm _)

theorem alg₁ {M : Type*} [CommGroup M] (a b E A B : M) :
    a * A * (a * b⁻¹ * E * (b * B))⁻¹ = A * (E * B)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg₂ {M : Type*} [CommGroup M] (A E B : M) : A = E * (A * (E * B)⁻¹) * B := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem proj_comp : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G],
    eSec G ≫ (toUnit G).left = 𝟙 (𝟙_ (Over S)).left := by
  intro S G _
  show (η[G] ≫ toUnit G).left = 𝟙 _
  rw [toUnit_unique (η[G] ≫ toUnit G) (𝟙 _)]
  rfl

theorem exists_isGen_maps_rig {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
    (L₁ L₂ : RigLB G) (e : LB.Iso L₁.L L₂.L) (he : e.IsGen) : ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  let W : (PUnit → L₂.L.ι) × (PUnit → L₁.L.ι) → (𝟙_ (Over S)).left.Opens :=
    fun i => (L₂.L.pull (eSec G)).U i.1 ⊓ (L₁.L.pull (eSec G)).U i.2
  let u : ∀ i, Γ((𝟙_ (Over S)).left, W i)ˣ := fun i =>
    res inf_le_left (L₂.rig.s i.1) *
      ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s i *
        res inf_le_right (L₁.rig.s i.2))⁻¹
  have key : ∀ i, ∀ x ∈ W i, gm (𝟙 _) x (W i) (u i) =
      gm (𝟙 _) x ((L₂.L.pull (eSec G)).U i.1) (L₂.rig.s i.1) *
        (gm (eSec G) x ((LB.div L₂.L L₁.L).U (i.1 PUnit.unit, i.2 PUnit.unit))
            (e.s (i.1 PUnit.unit, i.2 PUnit.unit)) *
          gm (𝟙 _) x ((L₁.L.pull (eSec G)).U i.2) (L₁.rig.s i.2))⁻¹ := by
    intro i x hx
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) x _ hx _)
      ((map_inv _ _).trans (congrArg _ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (germ_linCombIso e (eSec G) x i.1 i.2 (mem_pull.1 hx.1) (mem_pull.1 hx.2))
        (gm_res (𝟙 _) x _ hx _))))))
  obtain ⟨c, hc⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨p, hp⟩ := exists_chart L₂.isLB ((eSec G) x)
      obtain ⟨q, hq⟩ := exists_chart L₁.isLB ((eSec G) x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => p, fun _ => q), mem_pull.2 hp, mem_pull.2 hq⟩) u
    (fun i j x hx => by
      rw [key i x hx.1, key j x hx.2,
        germ_gen_isGen L₂.L (eSec G) L₂.rig L₂.rigGen x i.1 j.1 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1),
        germ_gen_isGen L₁.L (eSec G) L₁.rig L₁.rigGen x i.2 j.2 (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2),
        germ_iso_isGen e he (eSec G) x _ (j.1 PUnit.unit) _ (j.2 PUnit.unit) (mem_pull.1 hx.1.1)
          (mem_pull.1 hx.2.1) (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)]
      exact alg₁ _ _ _ _ _)
  let C := pullU (toUnit G).left ⊤ c
  let e' : LB.Iso L₁.L L₂.L := ⟨fun i => e.s i * res (U := (toUnit G).left ⁻¹ᵁ ⊤) (fun _ _ => trivial) C⟩
  have hC : ∀ i, ∀ x ∈ (LB.div L₂.L L₁.L).U i,
      gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e'.s i) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e.s i) * gm (𝟙 _) x ((toUnit G).left ⁻¹ᵁ ⊤) C :=
    fun i x hx => (map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 _) x _ hx _))
  refine ⟨e', ?_, ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    apply unit_ext
    intro x hx
    have hE : gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q)) (e.s (p, q)) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q) ⊓ (LB.div L₂.L L₁.L).U (p', q'))
            ((LB.div L₂.L L₁.L).g (p, q) (p', q')) *
          gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p', q')) (e.s (p', q')) :=
      (gm_res (𝟙 _) x _ hx _).symm.trans (((congrArg (gm (𝟙 _) x _) (he (p, q) (p', q'))).trans
        (map_mul _ _ _)).trans (congrArg _ (gm_res (𝟙 _) x _ hx _)))
    exact (gm_res (𝟙 _) x _ hx _).trans ((hC _ x hx.1).trans ((congrArg (· * _) hE).trans
      ((mul_assoc _ _ _).trans ((congrArg _ ((hC _ x hx.2).symm.trans
        (gm_res (𝟙 _) x _ hx _).symm)).trans (map_mul _ _ _).symm))))
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hx₁ := mem_pull.1 hx.1
    have hx₂ := mem_pull.1 hx.2
    have hcx : gm (𝟙 _) x ⊤ c = gm (𝟙 _) x (W (P, Q)) (u (P, Q)) := by
      rw [← hc (P, Q)]; exact (gm_res (𝟙 _) x _ hx _).symm
    have hσ : gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
        (e'.s (P PUnit.unit, Q PUnit.unit)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
          (e.s (P PUnit.unit, Q PUnit.unit)) * gm (𝟙 _) x ⊤ c := by
      refine (map_mul _ _ _).trans (congrArg _ ?_)
      refine (gm_res (eSec G) x _ (show (eSec G) x ∈ L₂.L.U _ ⊓ L₁.L.U _ from ⟨hx₁, hx₂⟩) _).trans ?_
      refine (gm_pull (eSec G) (toUnit G).left x ⊤ trivial c).trans ?_
      rw [proj_comp]
    have hEq : gm (𝟙 _) x (W (P, Q))
        ((LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
            (e.s (P PUnit.unit, Q PUnit.unit)) *
          (gm (𝟙 _) x ((L₂.L.pull (eSec G)).U P) (L₂.rig.s P) *
            (gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
                (e.s (P PUnit.unit, Q PUnit.unit)) *
              gm (𝟙 _) x ((L₁.L.pull (eSec G)).U Q) (L₁.rig.s Q))⁻¹) := by
      rw [germ_linCombIso e' (eSec G) x P Q hx₁ hx₂, hσ, hcx, key (P, Q) x hx]
    exact (gm_res (𝟙 _) x _ hx _).trans ((alg₂ _ _ _).trans
      ((congrArg₂ (· * ·) hEq.symm (gm_res (𝟙 _) x _ hx _).symm).trans (map_mul _ _ _).symm))

end GlobalTheory.RigRescale
