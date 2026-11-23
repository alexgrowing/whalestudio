import Mathlib
import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
import GroundTheory.ProfiniteCohomology.CupProducts.Graded
import GroundTheory.ProfiniteCohomology.PoincareDuality.Induced
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Map

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)

def compactZmodDualityMap {m r s : ℕ} (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m) :
    cohomology (zmodRep.{u} G n) r →+ (compactCohomologyRes φ D s →+ ZMod n) where
  toFun x := T.comp ((bilinAddHom (compactCupRes φ (zmodMulPairingRight n D hD)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem compactZmodDualityMap_apply {m r s : ℕ} (T : compactCohomologyRes φ D m →+ ZMod n)
    (h : r + s = m) (x : cohomology (zmodRep.{u} G n) r) (y : compactCohomologyRes φ D s) :
    compactZmodDualityMap φ D hD T h x y =
      T (compactCupRes φ (zmodMulPairingRight n D hD) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end Map

section Counting

variable {n : ℕ} [NeZero n]

theorem bijective_of_injective_of_injective_flip {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Finite X] [Finite Y] (β : X →+ Y →+ Z) (t : Z →+ ZMod n)
    (hX : Function.Injective fun x : X => t.comp (β x))
    (hY : Function.Injective fun y : Y => t.comp (β.flip y)) :
    Function.Bijective fun x : X => t.comp (β x) := by
  refine hX.bijective_of_nat_card_le ?_
  calc Nat.card (Y →+ ZMod n) ≤ Nat.card Y := card_addMonoidHom_zmod_le
    _ ≤ Nat.card (X →+ ZMod n) := Nat.card_le_card_of_injective _ hY
    _ ≤ Nat.card X := card_addMonoidHom_zmod_le

end Counting

section DegreeZero

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem injective_cohomologyMapAlong_zero {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (ψ : K →* G) (hψ : Continuous ψ) (A : Rep.{u} k G) [IsDiscreteRep A]
    [IsDiscreteRep (Rep.res ψ A)] :
    Function.Injective (cohomologyMapAlong ψ hψ (𝟙 (Rep.res ψ A)) 0).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 0 x
  have hx' : cohomologyπ (Rep.res ψ A) 0 (cocyclesMapAlong ψ hψ (𝟙 _) 0 z) = 0 :=
    (cohomologyMapAlong_cohomologyπ ψ hψ (𝟙 _) z).symm.trans hx
  have hπ : Function.Injective (cohomologyπ (Rep.res ψ A) 0) :=
    (ModuleCat.mono_iff_injective _).1
      (inferInstanceAs (Mono (CochainComplex.isoHomologyπ₀ (cochainsComplex (Rep.res ψ A))).hom))
  have h0 : cocyclesMapAlong ψ hψ (𝟙 _) 0 z = 0 := hπ (hx'.trans (map_zero _).symm)
  have hz : z = 0 := by
    apply cocycles_ext
    funext σ
    have e := congrArg (fun w => cochainOf (Rep.res ψ A) (cocycleι (Rep.res ψ A) 0 w) Fin.elim0) h0
    simp only [cochainOf_cocycleι_cocyclesMapAlong] at e
    have hL : cochainOf A (cocycleι A 0 z) (⇑ψ ∘ Fin.elim0) = 0 := by
      refine e.trans ?_
      rw [map_zero]
      rfl
    have hR : cochainOf A (cocycleι A 0 (0 : cocycles A 0)) = 0 := by
      rw [map_zero]
      rfl
    have hσ : σ = ⇑ψ ∘ (Fin.elim0 : Fin 0 → K) := Subsingleton.elim _ _
    rw [hσ, hL, hR, Pi.zero_apply]
  rw [hz, map_zero]

end DegreeZero

section CompactZero

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

theorem subsingleton_compactCohomologyRes_zero [Nonempty ι] (A : Rep.{u} k G) [IsDiscreteRep A] :
    Subsingleton (compactCohomologyRes φ A 0) := by
  obtain ⟨v⟩ := ‹Nonempty ι›
  have hinj : Function.Injective (compactToGlobal φ A (fun v => Rep.res (φ v).toMonoidHom A)
      (fun _ => 𝟙 _) 0).hom :=
    (ModuleCat.mono_iff_injective _).1 (mono_compactToGlobal_zero φ A _ _)
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ x : compactCohomologyRes φ A 0, x = 0 by rw [h a, h b]
  intro x
  apply hinj
  rw [map_zero]
  apply injective_cohomologyMapAlong_zero (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) A
  rw [map_zero]
  exact congrFun (ConcreteCategory.congr_hom
    (compactToGlobal_globalToLocal φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) 0) x) v

end CompactZero

section PairWith

variable {k K : Type u} [CommRing k] [Group K] {A B C : Rep.{u} k K}

def pairWithLinear (μ : A ⊗ B ⟶ C) (b : B) : A →ₗ[k] C where
  toFun a := μ.hom (a ⊗ₜ[k] b)
  map_add' a a' := by rw [TensorProduct.add_tmul, map_add]
  map_smul' c a := by rw [← TensorProduct.smul_tmul', map_smul]; rfl

def pairWith (μ : A ⊗ B ⟶ C) (b : B) (hb : ∀ g : K, B.ρ g b = b) : A ⟶ C :=
  Rep.ofHom ⟨pairWithLinear μ b,
    fun g => LinearMap.ext fun a => by
      change μ.hom ((A.ρ g a) ⊗ₜ[k] b) = C.ρ g (μ.hom (a ⊗ₜ[k] b))
      conv_lhs => rw [← hb g]
      exact Rep.hom_comm_apply μ g (a ⊗ₜ[k] b)⟩

theorem pairWith_hom_apply (μ : A ⊗ B ⟶ C) (b : B) (hb : ∀ g : K, B.ρ g b = b) (a : A) :
    (pairWith μ b hb).hom a = μ.hom (a ⊗ₜ[k] b) :=
  rfl

theorem tensorHom_unitHom_comp (μ : A ⊗ B ⟶ C) (b : B) (hb : ∀ g : K, B.ρ g b = b) :
    (𝟙 A ⊗ₘ unitHom B b hb) ≫ μ = (ρ_ A).hom ≫ pairWith μ b hb := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a (c : k) => ?_))
  change μ.hom (a ⊗ₜ[k] (unitHom B b hb).hom c) = (pairWith μ b hb).hom ((ρ_ A).hom.hom (a ⊗ₜ[k] c))
  rw [unitHom_hom_apply, GroundTheory.GroupCoh.rightUnitor_hom_tmul, pairWith_hom_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end PairWith

section ZeroClasses

variable {k K : Type u} [CommRing k] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

def h0Class (A : Rep.{u} k K) [IsDiscreteRep A] (a : A) (ha : ∀ g : K, A.ρ g a = a) :
    cohomology A 0 :=
  cohomologyMap (unitHom A a ha) 0 unitClass

theorem cohomologyMapAlong_h0Class {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ψ : K →* G) (hψ : Continuous ψ) (A : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep (Rep.res ψ A)]
    (a : A) (ha : ∀ g : G, A.ρ g a = a) :
    (cohomologyMapAlong ψ hψ (𝟙 (Rep.res ψ A)) 0).hom (h0Class A a ha) =
      h0Class (Rep.res ψ A) a (fun g => ha (ψ g)) := by
  change cohomologyMapAlong ψ hψ (𝟙 (Rep.res ψ A)) 0 (cohomologyMap (unitHom A a ha) 0 unitClass) =
    cohomologyMap (unitHom (Rep.res ψ A) a fun g => ha (ψ g)) 0 unitClass
  simp only [unitClass]
  rw [cohomologyMap_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cyclesMap]
  funext σ
  simp only [cochainOf_cocycleι_unitCocycle]
  rfl

variable {A B C : Rep.{u} k K} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem cupPairing_h0Class (μ : A ⊗ B ⟶ C) (b : B) (hb : ∀ g : K, B.ρ g b = b) {q : ℕ} (h : q + 0 = q)
    (y : cohomology A q) :
    cupPairing μ h y (h0Class B b hb) = cohomologyMap (pairWith μ b hb) q y := by
  have e := cupPairing_cohomologyMap μ (𝟙 A) (unitHom B b hb) h y unitClass
  rw [cohomologyMap_id] at e
  change cupPairing μ h y (h0Class B b hb) = _ at e
  rw [e, tensorHom_unitHom_comp, ← cohomologyMap_cupPairing, cupPairing_apply,
    cohomologyMap_rightUnitor_cup_unitClass]

end ZeroClasses

section ZModZero

variable {K : Type u} [Group K] {n : ℕ} [NeZero n] (D' : Rep.{u} (ULift.{u} ℤ) K) (hD : ∀ d : D', n • d = 0)

end ZModZero

section Instances

instance isDiscreteRep_zmodRep_base {W : Type u} [Group W] [TopologicalSpace W] (n : ℕ) :
    IsDiscreteRep (zmodRep.{u} W n) :=
  isDiscreteRep_of_isTrivial (zmodRep.{u} W n)

abbrev pairingRes {k G K : Type u} [CommRing k] [Group G] [Group K] (ψ : K →* G) {A B C : Rep.{u} k G}
    (μ : A ⊗ B ⟶ C) : Rep.res ψ A ⊗ Rep.res ψ B ⟶ Rep.res ψ C :=
  (Rep.resFunctor ψ).map μ

end Instances

section LocalGraded

variable {G K : Type u} [Group G] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [TotallyDisconnectedSpace K] (ψ : K →* G) {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G)
  [IsDiscreteRep (Rep.res ψ D)] [IsDiscreteRep (Rep.res ψ (zmodRep.{u} G n))] (hD : ∀ d : D, n • d = 0)

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K]
  [IsDiscreteRep (Rep.res ψ D)] [IsDiscreteRep (Rep.res ψ (zmodRep.{u} G n))] in
theorem pairingRes_zmodMulPairing :
    pairingRes ψ (zmodMulPairing n D hD) =
      (β_ (Rep.res ψ (zmodRep.{u} G n)) (Rep.res ψ D)).hom ≫ pairingRes ψ (zmodMulPairingRight n D hD) :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl))

theorem cupPairing_pairingRes_zmodMulPairing_one (h : 1 + 1 = 2)
    (ξ : cohomology (Rep.res ψ (zmodRep.{u} G n)) 1) (η : cohomology (Rep.res ψ D) 1) :
    cupPairing (pairingRes ψ (zmodMulPairing n D hD)) h ξ η =
      -cupPairing (pairingRes ψ (zmodMulPairingRight n D hD)) h η ξ := by
  rw [pairingRes_zmodMulPairing, cupPairing_apply, cupPairing_apply, cohomologyMap_comp,
    ConcreteCategory.comp_apply, cohomologyMap_braiding_cup h h, mul_one, pow_one, neg_smul]
  erw [one_smul]
  exact map_neg _ _

theorem cupPairing_pairingRes_zmodMulPairing_two_zero (h : 2 + 0 = 2) (h' : 0 + 2 = 2)
    (ξ : cohomology (Rep.res ψ (zmodRep.{u} G n)) 2) (η : cohomology (Rep.res ψ D) 0) :
    cupPairing (pairingRes ψ (zmodMulPairing n D hD)) h ξ η =
      cupPairing (pairingRes ψ (zmodMulPairingRight n D hD)) h' η ξ := by
  rw [pairingRes_zmodMulPairing, cupPairing_apply, cupPairing_apply, cohomologyMap_comp,
    ConcreteCategory.comp_apply, cohomologyMap_braiding_cup h h', mul_zero, pow_zero]
  erw [one_smul]

end LocalGraded

section Cyclic

variable {G : Type u} [Group G] {n : ℕ} (D : Rep.{u} (ULift.{u} ℤ) G) (e : D ≃+ ZMod n)
  (htriv : ∀ (g : G) (d : D), D.ρ g d = d)

def cyclicToZMod : D ⟶ zmodRep.{u} G n :=
  Rep.ofHom ⟨{ toFun := fun d => ULift.up (e d)
               map_add' := fun d d' => by rw [map_add]; rfl
               map_smul' := fun c d => by
                 rw [RingHom.id_apply]
                 obtain ⟨c⟩ := c
                 have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
                   ext
                   simp
                 rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ), map_zsmul]
                 rfl },
    fun g => LinearMap.ext fun d => by
      change ULift.up (e (D.ρ g d)) = ULift.up (e d)
      rw [htriv]⟩

def zmodToCyclic : zmodRep.{u} G n ⟶ D :=
  Rep.ofHom ⟨{ toFun := fun a => e.symm a.down
               map_add' := fun a a' => map_add e.symm a.down a'.down
               map_smul' := fun c a => by
                 rw [RingHom.id_apply]
                 obtain ⟨c⟩ := c
                 have h : (ULift.up c : ULift.{u} ℤ) = ((c : ℤ) : ULift.{u} ℤ) := by
                   ext
                   simp
                 rw [h, Int.cast_smul_eq_zsmul (ULift.{u} ℤ), Int.cast_smul_eq_zsmul (ULift.{u} ℤ)]
                 exact map_zsmul e.symm c a.down },
    fun g => LinearMap.ext fun a => by
      change e.symm a.down = D.ρ g (e.symm a.down)
      rw [htriv]⟩

theorem cyclicToZMod_comp_zmodToCyclic : cyclicToZMod D e htriv ≫ zmodToCyclic D e htriv = 𝟙 D :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun d => e.symm_apply_apply d))

theorem zmodToCyclic_comp_cyclicToZMod : zmodToCyclic D e htriv ≫ cyclicToZMod D e htriv = 𝟙 _ :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => congrArg ULift.up (e.apply_symm_apply a.down)))

variable (hD : ∀ d : D, n • d = 0)

theorem zmodToCyclic_tensor_zmodMulPairingRight [NeZero n] :
    (zmodToCyclic D e htriv ⊗ₘ 𝟙 (zmodRep.{u} G n)) ≫ zmodMulPairingRight n D hD =
      (𝟙 (zmodRep.{u} G n) ⊗ₘ zmodToCyclic D e htriv) ≫ zmodMulPairing n D hD := by
  have he : ∀ a : ZMod n, e.symm a = a.val • e.symm 1 := fun a => by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← nsmul_one, map_nsmul]
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun (a b : ULift.{u} (ZMod n)) => ?_))
  change (zmodMulPairing n D hD).hom (b ⊗ₜ[ULift.{u} ℤ] e.symm a.down) =
    (zmodMulPairing n D hD).hom (a ⊗ₜ[ULift.{u} ℤ] e.symm b.down)
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  rw [zmodMulPairing_tmul, zmodMulPairing_tmul, ZMod.cast_eq_val, ZMod.cast_eq_val, natCast_zsmul, natCast_zsmul,
    he a, he b, smul_smul, smul_smul, mul_comm]

end Cyclic

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {ι : Type u} [Fintype ι] [Nonempty ι] {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] [∀ v, CompactSpace (H v)] [∀ v, TotallyDisconnectedSpace (H v)]
  (φ : ∀ v, H v →ₜ* G) {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
  (hD : ∀ d : D, n • d = 0)

instance isDiscreteRep_res_zmodRep_base (v : ι) :
    IsDiscreteRep (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) :=
  isDiscreteRep_res_toMonoidHom (φ v) _

structure BaseDualityHypotheses (t : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ ZMod n)
    (T : compactCohomologyRes φ D 3 →+ ZMod n) : Prop where
  triv : ∀ (g : G) (d : D), D.ρ g d = d
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  loc_one : ∀ v, Function.Surjective fun ξ : cohomology (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) 1 =>
    (t v).comp ((bilinAddHom (cupPairing (pairingRes (φ v).toMonoidHom
      (zmodMulPairingRight n D hD)) (show 1 + 1 = 2 from rfl))).flip ξ)
  loc_two : ∀ v, Function.Bijective fun ξ : cohomology (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) 2 =>
    (t v).comp ((bilinAddHom (cupPairing (pairingRes (φ v).toMonoidHom
      (zmodMulPairingRight n D hD)) (show 0 + 2 = 2 from rfl))).flip ξ)
  bijective_alt : Function.Bijective T
  T_localToCompact : ∀ ξ, T ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 2).hom ξ) =
    ∑ v, t v (ξ v)
  three_zmod : Subsingleton (cohomology (zmodRep.{u} G n) 3)
  three_D : Subsingleton (cohomology D 3)
  finite_one : Finite (cohomology (zmodRep.{u} G n) 1)
  finite_two : Finite (compactCohomologyRes φ D 2)
  ker_left : ∀ x : cohomology (zmodRep.{u} G n) 1,
    (∀ y : compactCohomologyRes φ D 2, T (compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl) y x) = 0) →
      x = 0
  ker_right : ∀ y : compactCohomologyRes φ D 2,
    (∀ x : cohomology (zmodRep.{u} G n) 1, T (compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl) y x) = 0) →
      y = 0
  swap : ∀ (yc : compactCohomologyRes φ D 1) (xc : compactCohomologyRes φ (zmodRep.{u} G n) 2),
    T (compactCupRes φ (zmodMulPairingRight n D hD) (show 1 + 2 = 3 from rfl) yc
        ((compactToGlobal φ _ (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc)) =
      T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc
        ((compactToGlobal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 1).hom yc))

end Main

section MainProofs

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {ι : Type u} [Fintype ι] [Nonempty ι] {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] [∀ v, CompactSpace (H v)] [∀ v, TotallyDisconnectedSpace (H v)]
  {φ : ∀ v, H v →ₜ* G} {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {hD : ∀ d : D, n • d = 0} {t : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ ZMod n}
  {T : compactCohomologyRes φ D 3 →+ ZMod n}

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Fintype ι] [Nonempty ι] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [IsTopologicalGroup G] [∀ v, IsTopologicalGroup (H v)] [IsDiscreteRep D] in

theorem pairWith_pairingRes_zmodMulPairingRight (v : ι) (a : ZMod n)
    (h : ∀ g : H v, (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)).ρ g (ULift.up a) = ULift.up a) :
    pairWith (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD)) (ULift.up a) h =
      a.val • 𝟙 (Rep.res (φ v).toMonoidHom D) := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun d => ?_))
  change (zmodMulPairing n D hD).hom (ULift.up a ⊗ₜ[ULift.{u} ℤ] d) = (a.val • 𝟙 (Rep.res (φ v).toMonoidHom D)).hom d
  rw [zmodMulPairing_tmul, Rep.nsmul_hom, Representation.IntertwiningMap.coe_nsmul, Pi.smul_apply,
    ZMod.cast_eq_val, natCast_zsmul]
  rfl

namespace BaseDualityHypotheses

variable (hyp : BaseDualityHypotheses φ D hD t T)
include hyp

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] [NeZero n] in

theorem localToCompact_two_surjective :
    Function.Surjective (localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 2).hom :=
  fun _ => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_compact φ D _ (fun _ => 𝟙 _) 2)
    (@Subsingleton.elim _ hyp.three_D _ _)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem T_compactCupRes_zmodH0Class (h : 3 + 0 = 3) (a : ZMod n) (y : compactCohomologyRes φ D 3) :
    T (compactCupRes φ (zmodMulPairingRight n D hD) h y (zmodH0Class a)) = a.val • T y := by
  obtain ⟨ξ, rfl⟩ := hyp.localToCompact_two_surjective y
  have e := compactCup_localToCompact φ (zmodMulPairingRight n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairingRight n D hD))
    (show 2 + 0 = 2 from rfl) h ξ (zmodH0Class a)
  have hloc : ∀ v, cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD)) (show 2 + 0 = 2 from rfl)
      (ξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0).hom
        (zmodH0Class a)) = a.val • ξ v := fun v => by
    rw [show zmodH0Class a = h0Class (zmodRep.{u} G n) (ULift.up a) (fun g => zmodRep_ρ_apply g _) from rfl,
      cohomologyMapAlong_h0Class, cupPairing_h0Class, pairWith_pairingRes_zmodMulPairingRight,
      cohomologyMap_nsmul_id_apply]
  refine (congrArg T e).trans ?_
  rw [show (fun v => cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD))
      (show 2 + 0 = 2 from rfl) (ξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 _) 0).hom (zmodH0Class a))) = a.val • ξ from funext fun v => hloc v, map_nsmul, map_nsmul]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [NeZero n] in

theorem bijective_three (h : 3 + 0 = 3) : Function.Bijective (compactZmodDualityMap φ D hD T h) := by
  have := hyp.three_zmod
  have := subsingleton_compactCohomologyRes_zero φ D
  refine ⟨fun x y _ => Subsingleton.elim x y, fun χ => ⟨0, AddMonoidHom.ext fun y => ?_⟩⟩
  rw [Subsingleton.elim y 0, map_zero, map_zero]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem bijective_zero (h : 0 + 3 = 3) : Function.Bijective (compactZmodDualityMap φ D hD T h) := by
  have key : ∀ (a : ZMod n) (y : compactCohomologyRes φ D 3),
      compactZmodDualityMap φ D hD T h (zmodH0Class a) y = a * T y := fun a y => by
    rw [compactZmodDualityMap_apply, hyp.T_compactCupRes_zmodH0Class, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨y₁, hy₁⟩ := hyp.bijective_alt.2 1
  refine ⟨fun x x' hxx' => ?_, fun χ => ⟨zmodH0Class (χ y₁), AddMonoidHom.ext fun y => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := zmodH0Class_surjective (H := G) (n := n) x
    obtain ⟨a', rfl⟩ := zmodH0Class_surjective (H := G) (n := n) x'
    have e := DFunLike.congr_fun hxx' y₁
    rw [key, key, hy₁, mul_one, mul_one] at e
    rw [e]
  · have hy : y = (T y).val • y₁ := hyp.bijective_alt.1 (by
      rw [map_nsmul, hy₁, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
    rw [key]
    conv_rhs => rw [hy]
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem bijective_one (h : 1 + 2 = 3) : Function.Bijective (compactZmodDualityMap φ D hD T h) := by
  have := hyp.finite_one
  have := hyp.finite_two
  refine bijective_of_injective_of_injective_flip
    (bilinAddHom (compactCupRes φ (zmodMulPairingRight n D hD) ((Nat.add_comm 2 1).trans h))).flip T ?_ ?_
  · intro x x' hxx'
    rw [← sub_eq_zero]
    refine hyp.ker_left _ fun y => ?_
    have e := DFunLike.congr_fun hxx' y
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, bilinAddHom_apply] at e
    rw [map_sub, map_sub, e, sub_self]
  · intro y y' hyy'
    rw [← sub_eq_zero]
    refine hyp.ker_right _ fun x => ?_
    have e := DFunLike.congr_fun hyy' x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, bilinAddHom_apply] at e
    rw [map_sub, LinearMap.sub_apply, map_sub, e, sub_self]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] [NeZero n] in

theorem T_compactCupRes_localToCompact_zero (h : 1 + 2 = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 0) (x : cohomology (zmodRep.{u} G n) 2) :
    T (compactCupRes φ (zmodMulPairingRight n D hD) h
        ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom ξ) x) =
      ∑ v, t v (cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD)) (show 0 + 2 = 2 from rfl)
        (ξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2).hom x)) := by
  have e := compactCup_localToCompact φ (zmodMulPairingRight n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairingRight n D hD))
    (show 0 + 2 = 2 from rfl) h ξ x
  exact (congrArg T e).trans (hyp.T_localToCompact _)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] [NeZero n] in

theorem T_compactCupRes_localToCompact_one (h : 2 + 1 = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) 1) (y : cohomology D 1) :
    T (compactCupRes φ (zmodMulPairing n D hD) h
        ((localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
          (fun _ => 𝟙 _) 1).hom ξ) y) =
      ∑ v, t v (cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD)) (show 1 + 1 = 2 from rfl)
        (ξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1).hom y)) := by
  have e := compactCup_localToCompact φ (zmodMulPairing n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (show 1 + 1 = 2 from rfl) h ξ y
  exact (congrArg T e).trans (hyp.T_localToCompact _)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] [NeZero n] in

theorem T_compactCupRes_localToCompact_two (h : 3 + 0 = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) 2) (y : cohomology D 0) :
    T (compactCupRes φ (zmodMulPairing n D hD) h
        ((localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
          (fun _ => 𝟙 _) 2).hom ξ) y) =
      ∑ v, t v (cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD)) (show 2 + 0 = 2 from rfl)
        (ξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0).hom y)) := by
  have e := compactCup_localToCompact φ (zmodMulPairing n D hD)
    (fun v => pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom (zmodMulPairing n D hD))
    (show 2 + 0 = 2 from rfl) h ξ y
  exact (congrArg T e).trans (hyp.T_localToCompact _)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem compactCupRes_zmodMulPairing_eq (e : D ≃+ ZMod n) (w : compactCohomologyRes φ (zmodRep.{u} G n) 2)
    (y : cohomology D 1) :
    compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) w y =
      compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl)
        ((compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 2).hom w)
        ((cohomologyMap (cyclicToZMod D e hyp.triv) 1).hom y) := by
  rw [compactCupRes_compactCohomologyResMap φ (zmodMulPairingRight n D hD) (zmodMulPairing n D hD)
    (zmodToCyclic D e hyp.triv) (zmodToCyclic D e hyp.triv)
    (zmodToCyclic_tensor_zmodMulPairingRight D e hyp.triv hD)]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, cyclicToZMod_comp_zmodToCyclic, cohomologyMap_id]
  rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem eq_zero_of_forall_compactCupRes_zmodMulPairing (w : compactCohomologyRes φ (zmodRep.{u} G n) 2)
    (hw : ∀ y : cohomology D 1,
      T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) w y) = 0) : w = 0 := by
  obtain ⟨e⟩ := hyp.nonempty_addEquiv
  have h0 : (compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 2).hom w = 0 := by
    refine hyp.ker_right _ fun x => ?_
    have hx : x = (cohomologyMap (cyclicToZMod D e hyp.triv) 1).hom
        ((cohomologyMap (zmodToCyclic D e hyp.triv) 1).hom x) := by
      rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, zmodToCyclic_comp_cyclicToZMod, cohomologyMap_id]
      rfl
    rw [hx, ← compactCupRes_zmodMulPairing_eq hyp e]
    exact hw _
  have hinv : (compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 2).hom
      ((compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 2).hom w) = w := by
    rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp, zmodToCyclic_comp_cyclicToZMod,
      compactCohomologyResMap_id]
    rfl
  rw [← hinv, h0, map_zero]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Nonempty ι] [NeZero n] [Fintype ι]
  [∀ v, CompactSpace (H v)] [∀ v, TotallyDisconnectedSpace (H v)] [IsTopologicalGroup G] hyp in

theorem nsmul_local_cohomology_D (hD' : ∀ d : D, n • d = 0) (q : ℕ)
    (c : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) q) : n • c = 0 :=
  funext fun v => nsmul_cohomology_eq_zero (Rep.res (φ v).toMonoidHom D) (fun d => hD' d) q (c v)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Nonempty ι] in

theorem injective_two (h : 2 + 1 = 3) : Function.Injective (compactZmodDualityMap φ D hD T h) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ y : compactCohomologyRes φ D 1,
      T (compactCupRes φ (zmodMulPairingRight n D hD) ((Nat.add_comm 1 2).trans h) y x) = 0 :=
    fun y => DFunLike.congr_fun hx y

  have hres : ∀ v, (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2).hom x = 0 := by
    intro v
    apply (hyp.loc_two v).1
    refine AddMonoidHom.ext fun η => ?_
    have e := hx' ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom
      (Pi.single v η))
    rw [hyp.T_compactCupRes_localToCompact_zero, Finset.sum_eq_single v (fun w _ hw => by
      rw [Pi.single_eq_of_ne hw, map_zero, LinearMap.zero_apply, map_zero]) (fun hv => absurd (Finset.mem_univ v) hv),
      Pi.single_eq_same] at e
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, bilinAddHom_apply, map_zero,
      AddMonoidHom.zero_apply]
    exact e

  obtain ⟨xc, hxc⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_global φ (zmodRep.{u} G n) _ (fun _ => 𝟙 _) 2)
    (show (globalToLocal φ (zmodRep.{u} G n) _ (fun _ => 𝟙 _) 2).hom x = 0 from funext hres)

  let lam : cohomology D 1 →+ ZMod n :=
    T.comp (bilinAddHom (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl)) xc)
  have hker : (globalToLocal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 1).hom.toAddMonoidHom.ker ≤
      lam.ker := by
    intro y hy
    obtain ⟨yc, rfl⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact_global φ D _ (fun _ => 𝟙 _) 1) hy
    rw [AddMonoidHom.mem_ker]
    change T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc _) = 0
    rw [← hyp.swap yc xc, hxc]
    exact hx' yc
  obtain ⟨Λ, hΛ⟩ := zmod_exists_comp_eq_of_ker_le (nsmul_local_cohomology_D hD 1) _ lam hker
  choose ξ hξ using fun v => hyp.loc_one v (Λ.comp
    (AddMonoidHom.single (fun w => cohomology (Rep.res (φ w).toMonoidHom D) 1) v))

  have hw : ∀ y : cohomology D 1, T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl)
      (xc + (localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
        (fun _ => 𝟙 _) 1).hom ξ) y) = 0 := by
    intro y
    rw [map_add, LinearMap.add_apply, map_add, hyp.T_compactCupRes_localToCompact_one]
    have h1 : T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc y) =
        ∑ v, t v (cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD)) (show 1 + 1 = 2 from rfl)
          ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1).hom y) (ξ v)) := by
      change lam y = _
      rw [← hΛ, AddMonoidHom.comp_apply]
      conv_lhs => rw [← Finset.univ_sum_single ((globalToLocal φ D _ (fun _ => 𝟙 _) 1).hom.toAddMonoidHom y)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      have := DFunLike.congr_fun (hξ v) ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 _) 1).hom y)
      exact this.symm
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [cupPairing_pairingRes_zmodMulPairing_one, map_neg, add_neg_cancel]
  have hw0 := hyp.eq_zero_of_forall_compactCupRes_zmodMulPairing _ hw
  have hxc' : xc = -(localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
      (fun _ => 𝟙 _) 1).hom ξ := eq_neg_of_add_eq_zero_left hw0
  rw [← hxc, hxc', map_neg]
  have hz := ConcreteCategory.congr_hom (localToCompact_compactToGlobal φ (zmodRep.{u} G n)
    (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 1) ξ
  rw [ConcreteCategory.comp_apply] at hz
  rw [hz, neg_eq_zero]
  rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] [Fintype ι] [NeZero n] hyp in
theorem nsmul_cohomology_one_D (hD' : ∀ d : D, n • d = 0) (c : cohomology D 1) : n • c = 0 :=
  nsmul_cohomology_eq_zero D hD' 1 c

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ v, CompactSpace (H v)]
  [∀ v, TotallyDisconnectedSpace (H v)] [Nonempty ι] in

theorem resFunctor_map_zmodToCyclic (e : D ≃+ ZMod n) (v : ι)
    (hζ : ∀ g : H v, (Rep.res (φ v).toMonoidHom D).ρ g (e.symm 1) = e.symm 1) :
    (Rep.resFunctor (φ v).toMonoidHom).map (zmodToCyclic D e hyp.triv) =
      pairWith (pairingRes (φ v).toMonoidHom (zmodMulPairing n D hD)) (e.symm 1) hζ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun (a : ULift.{u} (ZMod n)) => ?_))
  change e.symm a.down = (zmodMulPairing n D hD).hom (a ⊗ₜ[ULift.{u} ℤ] e.symm 1)
  obtain ⟨a⟩ := a
  rw [zmodMulPairing_tmul, ZMod.cast_eq_val, natCast_zsmul, ← map_nsmul, nsmul_one, ZMod.natCast_zmod_val]

omit [CompactSpace G] [TotallyDisconnectedSpace G] [Nonempty ι] in

theorem surjective_two (h : 2 + 1 = 3) : Function.Surjective (compactZmodDualityMap φ D hD T h) := by
  classical
  intro χ
  obtain ⟨e⟩ := hyp.nonempty_addEquiv

  choose ξ hξ using fun v => (hyp.loc_two v).2 (χ.comp
    ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom.toAddMonoidHom.comp
      (AddMonoidHom.single (fun w => cohomology (Rep.res (φ w).toMonoidHom D) 0) v)))
  have hξ' : ∀ v η, t v (cupPairing (pairingRes (φ v).toMonoidHom (zmodMulPairingRight n D hD))
      (show 0 + 2 = 2 from rfl) η (ξ v)) =
      χ ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom (Pi.single v η)) :=
    fun v η => DFunLike.congr_fun (hξ v) η

  have hζ : ∀ g : G, D.ρ g (e.symm 1) = e.symm 1 := fun g => hyp.triv g _
  have hsum : ∑ v, t v ((cohomologyMap ((Rep.resFunctor (φ v).toMonoidHom).map (zmodToCyclic D e hyp.triv)) 2).hom
      (ξ v)) = 0 := by
    have e1 : ∀ v, t v ((cohomologyMap ((Rep.resFunctor (φ v).toMonoidHom).map (zmodToCyclic D e hyp.triv)) 2).hom
        (ξ v)) = χ ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom
          (Pi.single v ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0).hom
            (h0Class D (e.symm 1) hζ)))) := fun v => by
      rw [← hξ', cohomologyMapAlong_h0Class, ← cupPairing_pairingRes_zmodMulPairing_two_zero (φ v).toMonoidHom D hD
        (show 2 + 0 = 2 from rfl), cupPairing_h0Class]
      exact congrArg (fun f => t v ((cohomologyMap f 2).hom (ξ v))) (resFunctor_map_zmodToCyclic hyp e v _)
    rw [Finset.sum_congr rfl fun v _ => e1 v, ← map_sum, ← map_sum]
    have e2 : ∑ v, Pi.single v ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 0).hom
        (h0Class D (e.symm 1) hζ)) = (globalToLocal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom
          (h0Class D (e.symm 1) hζ) := Finset.univ_sum_single _
    rw [e2]
    have hz := ConcreteCategory.congr_hom (globalToLocal_localToCompact φ D
      (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0) (h0Class D (e.symm 1) hζ)
    rw [ConcreteCategory.comp_apply] at hz
    rw [hz]
    exact map_zero χ
  have hδξ : (localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
      (fun _ => 𝟙 _) 2).hom ξ = 0 := by
    have hnat := ConcreteCategory.congr_hom (localToCompact_compactCohomologyMap φ (zmodToCyclic D e hyp.triv)
      (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (zmodToCyclic D e hyp.triv))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) 2) ξ
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    have h0 : (compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 3).hom
        ((localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
          (fun _ => 𝟙 _) 2).hom ξ) = 0 := by
      refine hyp.bijective_alt.1 ?_
      rw [map_zero]
      refine (congrArg T hnat).trans ?_
      rw [hyp.T_localToCompact]
      exact hsum
    have hinv : (compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 3).hom
        ((compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 3).hom
          ((localToCompact φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
            (fun _ => 𝟙 _) 2).hom ξ)) = (localToCompact φ (zmodRep.{u} G n)
              (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom ξ := by
      rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp, zmodToCyclic_comp_cyclicToZMod,
        compactCohomologyResMap_id]
      rfl
    rw [← hinv, h0, map_zero]

  obtain ⟨x₀, hx₀⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_local φ (zmodRep.{u} G n) _ (fun _ => 𝟙 _) 2) hδξ
  have hres : ∀ v, (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2).hom x₀ = ξ v :=
    fun v => congrFun hx₀ v

  have hχδ : ∀ η, χ ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom η) =
      compactZmodDualityMap φ D hD T h x₀
        ((localToCompact φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 0).hom η) := by
    intro η
    rw [compactZmodDualityMap_apply, hyp.T_compactCupRes_localToCompact_zero]
    conv_lhs => rw [← Finset.univ_sum_single η]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hξ', hres v]

  obtain ⟨Λ, hΛ⟩ := zmod_exists_comp_eq_of_ker_le (nsmul_cohomology_one_D hD)
    (compactToGlobal φ D (fun v => Rep.res (φ v).toMonoidHom D) (fun _ => 𝟙 _) 1).hom.toAddMonoidHom
    (χ - compactZmodDualityMap φ D hD T h x₀) (by
      intro y hy
      obtain ⟨η, rfl⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
        (compactCohomology_exact_compact φ D _ (fun _ => 𝟙 _) 0) hy
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, hχδ, sub_self])

  have := hyp.finite_one
  have := hyp.finite_two
  have hbij := bijective_of_injective_of_injective_flip
    (bilinAddHom (compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl))) T
    (fun y y' hyy' => by
      rw [← sub_eq_zero]
      refine hyp.ker_right _ fun x => ?_
      have e := DFunLike.congr_fun hyy' x
      simp only [AddMonoidHom.comp_apply, bilinAddHom_apply] at e
      rw [map_sub, LinearMap.sub_apply, map_sub, e, sub_self])
    (fun x x' hxx' => by
      rw [← sub_eq_zero]
      refine hyp.ker_left _ fun y => ?_
      have e := DFunLike.congr_fun hxx' y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, bilinAddHom_apply] at e
      rw [map_sub, map_sub, e, sub_self])
  obtain ⟨y', hy'⟩ := hbij.2 (Λ.comp (cohomologyMap (zmodToCyclic D e hyp.triv) 1).hom.toAddMonoidHom)
  have hw : ∀ y : cohomology D 1, T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl)
      ((compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 2).hom y') y) = Λ y := by
    intro y
    rw [hyp.compactCupRes_zmodMulPairing_eq e]
    have h1 : (compactCohomologyResMap φ (zmodToCyclic D e hyp.triv) 2).hom
        ((compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 2).hom y') = y' := by
      rw [← ConcreteCategory.comp_apply, ← compactCohomologyResMap_comp, cyclicToZMod_comp_zmodToCyclic,
        compactCohomologyResMap_id]
      rfl
    have h2 : (cohomologyMap (zmodToCyclic D e hyp.triv) 1).hom
        ((cohomologyMap (cyclicToZMod D e hyp.triv) 1).hom y) = y := by
      rw [← ConcreteCategory.comp_apply, ← cohomologyMap_comp, cyclicToZMod_comp_zmodToCyclic, cohomologyMap_id]
      rfl
    rw [h1]
    have h3 := DFunLike.congr_fun hy' ((cohomologyMap (cyclicToZMod D e hyp.triv) 1).hom y)
    simp only [AddMonoidHom.comp_apply, bilinAddHom_apply, LinearMap.toAddMonoidHom_coe] at h3
    rw [h3, h2]
  refine ⟨x₀ + (compactToGlobal φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
    (fun _ => 𝟙 _) 2).hom ((compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 2).hom y'),
    AddMonoidHom.ext fun yc => ?_⟩
  rw [map_add, AddMonoidHom.add_apply, compactZmodDualityMap_apply φ D hD T h
    ((compactToGlobal φ (zmodRep.{u} G n) (fun v => Rep.res (φ v).toMonoidHom (zmodRep.{u} G n))
      (fun _ => 𝟙 _) 2).hom ((compactCohomologyResMap φ (cyclicToZMod D e hyp.triv) 2).hom y')) yc,
    hyp.swap yc, hw]
  have hΛ' := DFunLike.congr_fun hΛ yc
  rw [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply] at hΛ'
  rw [LinearMap.toAddMonoidHom_coe] at hΛ'
  rw [hΛ']
  abel

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem bijective_compactZmodDualityMap {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap φ D hD T h) := by
  rcases r with _ | _ | _ | _ | r
  · obtain rfl : s = 3 := by omega
    exact hyp.bijective_zero h
  · obtain rfl : s = 2 := by omega
    exact hyp.bijective_one h
  · obtain rfl : s = 1 := by omega
    exact ⟨hyp.injective_two h, hyp.surjective_two h⟩
  · obtain rfl : s = 0 := by omega
    exact hyp.bijective_three h
  · omega

end BaseDualityHypotheses

end MainProofs

end GroundTheory.ProfCoh
