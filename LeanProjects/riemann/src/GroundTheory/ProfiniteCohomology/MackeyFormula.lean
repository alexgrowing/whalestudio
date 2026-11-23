import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

variable (U : Subgroup G) (ι : H →* G) (N : Rep.{u} k U)

theorem exists_eq_mul_out_mul (y : G) :
    ∃ u : U, ∃ h : H, y = (u : G) * (DoubleCoset.mk U ι.range y).out * ι h := by
  obtain ⟨a, ha, b, hb, e⟩ :=
    (DoubleCoset.eq U ι.range _ y).1 (DoubleCoset.out_eq' U ι.range (DoubleCoset.mk U ι.range y))
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  exact ⟨⟨a, ha⟩, h, e⟩

theorem doubleCosetMk_mul_mul (x : G) (u : U) (h : H) :
    DoubleCoset.mk U ι.range ((u : G) * x * ι h) = DoubleCoset.mk U ι.range x :=
  ((DoubleCoset.eq U ι.range _ _).2 ⟨u, u.2, ι h, ⟨h, rfl⟩, rfl⟩).symm

theorem coind_apply_eq_of_mul_eq (x : G)
    (F : Representation.coindV (mackeySubgroup U ι x).subtype (mackeyRep U ι N x).ρ)
    {u u' : U} {h h' : H} (e : (u : G) * x * ι h = u' * x * ι h') :
    N.ρ u (F.1 h) = N.ρ u' (F.1 h') := by
  have he : x * ι (h * h'⁻¹) * x⁻¹ = ((u⁻¹ * u' : U) : G) := by
    have e' : x * ι h = (u : G)⁻¹ * (u' * x * ι h') := by
      rw [← e]; group
    rw [map_mul, map_inv, ← mul_assoc, e']
    push_cast
    group
  have hm : h * h'⁻¹ ∈ mackeySubgroup U ι x := by
    rw [mem_mackeySubgroup, he]
    exact (u⁻¹ * u').2
  have h1 := F.2 ⟨_, hm⟩ h'
  have h2 : (mackeySubgroup U ι x).subtype ⟨_, hm⟩ * h' = h := by simp
  have h3 : mackeyConj U ι x ⟨_, hm⟩ = u⁻¹ * u' := Subtype.ext he
  rw [h2] at h1
  rw [h1]
  change N.ρ u (N.ρ (mackeyConj U ι x ⟨_, hm⟩) (F.1 h')) = _
  rw [h3, map_mul, Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply]

theorem coind_apply_eq_of_mul_eq' (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out)
    {d d' : MackeyDoubleCoset U ι} (hd : d = d') {u u' : U} {h h' : H}
    (e : (u : G) * d.out * ι h = u' * d'.out * ι h') :
    N.ρ u ((F d).1 h) = N.ρ u' ((F d').1 h') := by
  subst hd
  exact coind_apply_eq_of_mul_eq U ι N d.out (F d) e

noncomputable def mackeyLiftFun (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out)
    (y : G) : N :=
  N.ρ (exists_eq_mul_out_mul U ι y).choose
    ((F (DoubleCoset.mk U ι.range y)).1 (exists_eq_mul_out_mul U ι y).choose_spec.choose)

theorem mackeyLiftFun_apply (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out)
    (d : MackeyDoubleCoset U ι) (u : U) (h : H) :
    mackeyLiftFun U ι N F ((u : G) * d.out * ι h) = N.ρ u ((F d).1 h) := by
  set y := (u : G) * d.out * ι h with hy
  have hd : DoubleCoset.mk U ι.range y = d := by
    rw [hy, doubleCosetMk_mul_mul, DoubleCoset.out_eq']
  exact coind_apply_eq_of_mul_eq' U ι N F hd
    ((exists_eq_mul_out_mul U ι y).choose_spec.choose_spec.symm.trans hy)

theorem mackeyLiftFun_mem (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out) :
    mackeyLiftFun U ι N F ∈ Representation.coindV U.subtype N.ρ := by
  intro u₀ y
  obtain ⟨u, h, hy⟩ := exists_eq_mul_out_mul U ι y
  rw [hy]
  have e : U.subtype u₀ * ((u : G) * (DoubleCoset.mk U ι.range y).out * ι h) =
      ((u₀ * u : U) : G) * (DoubleCoset.mk U ι.range y).out * ι h := by
    simp [mul_assoc]
  rw [e, mackeyLiftFun_apply, mackeyLiftFun_apply, map_mul, Module.End.mul_apply]

noncomputable def mackeyLift :
    (∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out) →ₗ[k] Rep.coind U.subtype N where
  toFun F := ⟨mackeyLiftFun U ι N F, mackeyLiftFun_mem U ι N F⟩
  map_add' F F' := by
    apply Subtype.ext
    funext y
    simp only [mackeyLiftFun]
    change _ = N.ρ _ ((F _).1 _) + N.ρ _ ((F' _).1 _)
    rw [← map_add]
    rfl
  map_smul' r F := by
    apply Subtype.ext
    funext y
    simp only [mackeyLiftFun]
    change _ = r • N.ρ _ ((F _).1 _)
    rw [← map_smul]
    rfl

theorem mackeyLift_apply (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out)
    (d : MackeyDoubleCoset U ι) (u : U) (h : H) :
    (mackeyLift U ι N F).1 ((u : G) * d.out * ι h) = N.ρ u ((F d).1 h) :=
  mackeyLiftFun_apply U ι N F d u h

theorem mackeyProj_mackeyLift (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out)
    (d : MackeyDoubleCoset U ι) :
    (mackeyProj U ι N d.out).hom (mackeyLift U ι N F) = F d := by
  apply Subtype.ext
  funext h
  rw [mackeyProj_hom_apply]
  have e : d.out * ι h = ((1 : U) : G) * d.out * ι h := by simp
  rw [e, mackeyLift_apply, map_one, Module.End.one_apply]

theorem mackeyLift_mackeyProj (f : Rep.coind U.subtype N) :
    mackeyLift U ι N (fun d => (mackeyProj U ι N d.out).hom f) = f := by
  apply Subtype.ext
  funext y
  obtain ⟨u, h, hy⟩ := exists_eq_mul_out_mul U ι y
  rw [hy, mackeyLift_apply, mackeyProj_hom_apply]
  have e : (u : G) * (DoubleCoset.mk U ι.range y).out * ι h =
      U.subtype u * ((DoubleCoset.mk U ι.range y).out * ι h) := by
    simp [mul_assoc]
  rw [e, f.2]

theorem mackeyLift_ρ (F : ∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out) (h₀ : H) :
    mackeyLift U ι N (fun d => (mackeySummand U ι N d.out).ρ h₀ (F d)) =
      (Rep.coind U.subtype N).ρ (ι h₀) (mackeyLift U ι N F) := by
  apply Subtype.ext
  funext y
  obtain ⟨u, h, hy⟩ := exists_eq_mul_out_mul U ι y
  change _ = (mackeyLift U ι N F).1 (y * ι h₀)
  have e : y * ι h₀ = (u : G) * (DoubleCoset.mk U ι.range y).out * ι (h * h₀) := by
    conv_lhs => rw [hy]
    rw [map_mul, mul_assoc]
  rw [e, mackeyLift_apply]
  conv_lhs => rw [hy]
  rw [mackeyLift_apply]
  rfl

noncomputable def mackeyEquiv :
    Rep.coind U.subtype N ≃ₗ[k] (∀ d : MackeyDoubleCoset U ι, mackeySummand U ι N d.out) where
  toFun f d := (mackeyProj U ι N d.out).hom f
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _
  invFun := mackeyLift U ι N
  left_inv f := mackeyLift_mackeyProj U ι N f
  right_inv F := funext fun d => mackeyProj_mackeyLift U ι N F d

theorem mackeyEquiv_apply_ρ (f : Rep.coind U.subtype N) (h₀ : H) (d : MackeyDoubleCoset U ι) :
    mackeyEquiv U ι N ((Rep.coind U.subtype N).ρ (ι h₀) f) d =
      (mackeySummand U ι N d.out).ρ h₀ (mackeyEquiv U ι N f d) :=
  Rep.hom_comm_apply (mackeyProj U ι N d.out) h₀ f

theorem mackeyLift_single_ρ [DecidableEq (MackeyDoubleCoset U ι)] (d : MackeyDoubleCoset U ι)
    (F : mackeySummand U ι N d.out) (h₀ : H) :
    mackeyLift U ι N (Pi.single d ((mackeySummand U ι N d.out).ρ h₀ F)) =
      (Rep.coind U.subtype N).ρ (ι h₀) (mackeyLift U ι N (Pi.single d F)) := by
  rw [← mackeyLift_ρ]
  congr 1
  funext d'
  by_cases hd : d' = d
  · subst hd
    simp
  · simp [Pi.single_eq_of_ne hd]

open scoped Classical in

noncomputable def mackeyIncl (d : MackeyDoubleCoset U ι) :
    mackeySummand U ι N d.out ⟶ Rep.res ι (Rep.coind U.subtype N) :=
  Rep.ofHom ⟨{
      toFun := fun F => mackeyLift U ι N (Pi.single d F)
      map_add' := fun F F' => by rw [Pi.single_add, map_add]
      map_smul' := fun r F => by rw [Pi.single_smul, map_smul]; rfl },
    fun h₀ => LinearMap.ext fun F => mackeyLift_single_ρ U ι N d F h₀⟩

open scoped Classical in
theorem mackeyIncl_hom_apply (d : MackeyDoubleCoset U ι) (F : mackeySummand U ι N d.out) :
    (mackeyIncl U ι N d).hom F = mackeyLift U ι N (Pi.single d F) :=
  rfl

theorem mackeyIncl_comp_mackeyProj (d : MackeyDoubleCoset U ι) :
    mackeyIncl U ι N d ≫ mackeyProj U ι N d.out = 𝟙 _ := by
  classical
  ext F : 3
  change (mackeyProj U ι N d.out).hom ((mackeyIncl U ι N d).hom F) = F
  rw [mackeyIncl_hom_apply, mackeyProj_mackeyLift]
  simp

theorem mackeyIncl_comp_mackeyProj_of_ne {d d' : MackeyDoubleCoset U ι} (hd : d ≠ d') :
    mackeyIncl U ι N d ≫ mackeyProj U ι N d'.out = 0 := by
  classical
  ext F : 3
  change (mackeyProj U ι N d'.out).hom ((mackeyIncl U ι N d).hom F) = 0
  rw [mackeyIncl_hom_apply, mackeyProj_mackeyLift]
  simp [Pi.single_eq_of_ne (Ne.symm hd)]

section Finite

variable [Fintype (MackeyDoubleCoset U ι)]

open scoped Classical in
theorem sum_mackeyProj_comp_mackeyIncl :
    ∑ d : MackeyDoubleCoset U ι, mackeyProj U ι N d.out ≫ mackeyIncl U ι N d = 𝟙 _ := by
  ext f : 3
  change (∑ d : MackeyDoubleCoset U ι, mackeyProj U ι N d.out ≫ mackeyIncl U ι N d).hom f = f
  let ev : (Rep.res ι (Rep.coind U.subtype N) ⟶ Rep.res ι (Rep.coind U.subtype N)) →+
      Rep.coind U.subtype N := AddMonoidHom.mk' (fun φ => φ.hom f) fun _ _ => rfl
  change ev (∑ d : MackeyDoubleCoset U ι, mackeyProj U ι N d.out ≫ mackeyIncl U ι N d) = f
  rw [map_sum]
  change ∑ d : MackeyDoubleCoset U ι,
    (mackeyIncl U ι N d).hom ((mackeyProj U ι N d.out).hom f) = f
  rw [Finset.sum_congr rfl fun d _ => mackeyIncl_hom_apply U ι N d _, ← map_sum,
    Finset.univ_sum_single]
  exact mackeyLift_mackeyProj U ι N f

noncomputable def mackeyBicone :
    Bicone (fun d : MackeyDoubleCoset U ι => mackeySummand U ι N d.out) where
  pt := Rep.res ι (Rep.coind U.subtype N)
  π d := mackeyProj U ι N d.out
  ι d := mackeyIncl U ι N d
  ι_π d d' := by
    split_ifs with h
    · subst h
      simpa using mackeyIncl_comp_mackeyProj U ι N d
    · exact mackeyIncl_comp_mackeyProj_of_ne U ι N h

noncomputable def mackeyBiconeIsBilimit : (mackeyBicone U ι N).IsBilimit :=
  isBilimitOfTotal _ (sum_mackeyProj_comp_mackeyIncl U ι N)

instance hasBiproduct_mackeySummand :
    HasBiproduct fun d : MackeyDoubleCoset U ι => mackeySummand U ι N d.out :=
  HasBiproduct.mk ⟨_, mackeyBiconeIsBilimit U ι N⟩

noncomputable def mackeyIso :
    Rep.res ι (Rep.coind U.subtype N) ≅ ⨁ fun d : MackeyDoubleCoset U ι => mackeySummand U ι N d.out :=
  biproduct.uniqueUpToIso _ (mackeyBiconeIsBilimit U ι N)

@[reassoc (attr := simp)]
theorem mackeyIso_hom_π (d : MackeyDoubleCoset U ι) :
    (mackeyIso U ι N).hom ≫ biproduct.π (fun d : MackeyDoubleCoset U ι => mackeySummand U ι N d.out) d =
      mackeyProj U ι N d.out := by
  rw [mackeyIso, biproduct.uniqueUpToIso_hom]
  exact biproduct.lift_π _ _

@[reassoc (attr := simp)]
theorem ι_mackeyIso_inv (d : MackeyDoubleCoset U ι) :
    biproduct.ι (fun d : MackeyDoubleCoset U ι => mackeySummand U ι N d.out) d ≫ (mackeyIso U ι N).inv =
      mackeyIncl U ι N d := by
  rw [mackeyIso, biproduct.uniqueUpToIso_inv]
  exact biproduct.ι_desc _ _

end Finite

end GroundTheory.ProfCoh
