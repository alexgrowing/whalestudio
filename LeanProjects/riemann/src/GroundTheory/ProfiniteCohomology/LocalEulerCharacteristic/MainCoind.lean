import Mathlib
import GroundTheory.ProfiniteCohomology.EulerChar
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Iso

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerChar_eq_of_iso {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (e : A ≅ B) :
    eulerChar A = eulerChar B := by
  simp only [eulerChar]
  refine Finset.prod_congr rfl fun q _ => ?_
  let i : cohomology A q ≅ cohomology B q :=
    { hom := cohomologyMap e.hom q
      inv := cohomologyMap e.inv q
      hom_inv_id := by rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
      inv_hom_id := by rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id] }
  rw [Nat.card_congr i.toLinearEquiv.toEquiv]

theorem eulerChar_eq_one_of_subsingleton (A : Rep.{u} k G) [IsDiscreteRep A] [Subsingleton A] :
    eulerChar A = 1 := by
  have h0 : (𝟙 A : A ⟶ A) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hz : ∀ q, ∀ z : cohomology A q, z = 0 := fun q z => by
    have h := congrArg (fun f : cohomology A q ⟶ cohomology A q => f.hom z)
      (show cohomologyMap (𝟙 A) q = cohomologyMap (0 : A ⟶ A) q by rw [h0])
    simpa [cohomologyMap_id, cohomologyMap_zero] using h
  simp only [eulerChar]
  refine Finset.prod_eq_one fun q _ => ?_
  have : Subsingleton (cohomology A q) := ⟨fun x y => by rw [hz q x, hz q y]⟩
  rw [Nat.card_of_subsingleton (0 : cohomology A q)]
  simp

end Iso

section Coind

variable [TopologicalSpace G] (H : OpenSubgroup G) (M : Rep.{u} k G)

noncomputable def coindRes : Rep.{u} k G :=
  Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M)

variable {H M}

theorem coindRes_apply_mul (f : coindRes H M) {h : G} (hh : h ∈ (H : Subgroup G)) (x : G) :
    f.1 (h * x) = M.ρ h (f.1 x) :=
  f.2 ⟨h, hh⟩ x

theorem coindRes_ρ_apply (g : G) (f : coindRes H M) (x : G) :
    ((coindRes H M).ρ g f).1 x = f.1 (x * g) :=
  rfl

noncomputable def coindShift (s : G) : coindRes H M →ₗ[k] coindRes H M where
  toFun f := ⟨fun x => M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s)), by
    intro h x
    change M.ρ (h * x * s⁻¹ * (h * x)⁻¹) (f.1 (h * x * s)) =
      M.ρ (h : G) (M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s)))
    rw [mul_assoc (h : G) x s, coindRes_apply_mul f h.2, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s) + g.1 (x * s)) =
      M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s)) + M.ρ (x * s⁻¹ * x⁻¹) (g.1 (x * s))
    exact map_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change M.ρ (x * s⁻¹ * x⁻¹) (c • f.1 (x * s)) = c • M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s))
    exact map_smul _ _ _

theorem coindShift_apply (s : G) (f : coindRes H M) (x : G) :
    (coindShift s f).1 x = M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s)) :=
  rfl

end Coind

section Step

variable {A : Rep.{u} k G} (T : Module.End k A) (hT : ∀ g : G, Commute T (A.ρ g))
  (D : Submodule k A) (hD : ∀ g : G, D ≤ D.comap (A.ρ g))

include hT hD in
theorem inf_ker_le_comap (g : G) :
    D ⊓ LinearMap.ker T ≤ (D ⊓ LinearMap.ker T).comap (A.ρ g) := by
  rintro x ⟨hx1, hx2⟩
  refine ⟨hD g hx1, ?_⟩
  change T (A.ρ g x) = 0
  rw [← Module.End.mul_apply, (hT g).eq, Module.End.mul_apply, LinearMap.mem_ker.1 hx2, map_zero]

include hT hD in
theorem map_le_comap (g : G) : D.map T ≤ (D.map T).comap (A.ρ g) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨A.ρ g x, hD g hx, ?_⟩
  change T (A.ρ g x) = A.ρ g (T x)
  rw [← Module.End.mul_apply, (hT g).eq, Module.End.mul_apply]

noncomputable abbrev rangeStepComplex : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk
    (Rep.ofHom ⟨Submodule.inclusion inf_le_left, fun _ => rfl⟩ :
      Rep.subrepresentation A _ (inf_ker_le_comap T hT D hD) ⟶ Rep.subrepresentation A D hD)
    (Rep.ofHom ⟨T.restrict (p := D) (q := D.map T) (fun x hx => ⟨x, hx, rfl⟩), fun g => by
      ext x
      exact LinearMap.congr_fun (hT g).eq x.1⟩ :
      Rep.subrepresentation A D hD ⟶ Rep.subrepresentation A (D.map T) (map_le_comap T hT D hD))
    (by
      ext x
      exact LinearMap.mem_ker.1 x.2.2)

end Step

section StepExact

variable {A : Rep.{u} k G} (T : Module.End k A) (hT : ∀ g : G, Commute T (A.ρ g))
  (D : Submodule k A) (hD : ∀ g : G, D ≤ D.comap (A.ρ g))

theorem rangeStepComplex_shortExact : (rangeStepComplex T hT D hD).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro y hy
    have hTy : T y.1 = 0 := congrArg Subtype.val hy
    exact ⟨⟨y.1, y.2, hTy⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 (Submodule.inclusion_injective inf_le_left)
  epi_g := (Rep.epi_iff_surjective _).2 (by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)

theorem card_rangeStep :
    Nat.card D = Nat.card ↥(D ⊓ LinearMap.ker T) * Nat.card ↥(D.map T) := by
  let f : D →ₗ[k] D.map T := T.restrict (p := D) (q := D.map T) (fun x hx => ⟨x, hx, rfl⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [card_eq_card_ker_mul_card_range f, LinearMap.range_eq_top.2 hsurj]
  congr 1
  · exact Nat.card_congr
      { toFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val (LinearMap.mem_ker.1 y.2)⟩
        invFun := fun z => ⟨⟨z.1, z.2.1⟩, LinearMap.mem_ker.2 (Subtype.ext z.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · exact Nat.card_congr (Submodule.topEquiv).toEquiv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerChar_rangeStep [IsDiscreteRep A] [Finite A] {P : ℕ → Prop}
    (hPdvd : ∀ m n, m ∣ n → P n → P m) (hG : HasFiniteCohomology k G P) (hA : P (Nat.card A)) :
    eulerChar (Rep.subrepresentation A D hD) =
      eulerChar (Rep.subrepresentation A _ (inf_ker_le_comap T hT D hD)) *
        eulerChar (Rep.subrepresentation A _ (map_le_comap T hT D hD)) := by
  have hdvd : Nat.card D ∣ Nat.card A :=
    AddSubgroup.card_addSubgroup_dvd_card D.toAddSubgroup
  have key := eulerChar_shortExact hPdvd hG (rangeStepComplex_shortExact T hT D hD) (hPdvd _ _ hdvd hA)
  exact key

end StepExact

section Shift

variable [TopologicalSpace G] {H : OpenSubgroup G} {M : Rep.{u} k G} [hN : (H : Subgroup G).Normal]
  {s : G}

include hN in

theorem commute_coindShift (hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G)) (g : G) :
    Commute (coindShift (H := H) (M := M) s) ((coindRes H M).ρ g) := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  change M.ρ (x * s⁻¹ * x⁻¹) (f.1 (x * s * g)) =
    M.ρ (x * g * s⁻¹ * (x * g)⁻¹) (f.1 (x * g * s))
  have hc : x * (s * g * s⁻¹ * g⁻¹) * x⁻¹ ∈ (H : Subgroup G) := hN.conj_mem _ (hs g) x
  have he : x * s * g = x * (s * g * s⁻¹ * g⁻¹) * x⁻¹ * (x * g * s) := by group
  rw [he, coindRes_apply_mul f hc, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

omit hN in

theorem coindShift_pow_apply (i : ℕ) (f : coindRes H M) (x : G) :
    ((coindShift (H := H) (M := M) s ^ i) f).1 x = M.ρ (x * (s ^ i)⁻¹ * x⁻¹) (f.1 (x * s ^ i)) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, coindShift_apply, ih, ← Module.End.mul_apply, ← map_mul]
    have h1 : x * s⁻¹ * x⁻¹ * (x * s * (s ^ i)⁻¹ * (x * s)⁻¹) = x * (s ^ (i + 1))⁻¹ * x⁻¹ := by
      rw [pow_succ']
      group
    have h2 : x * s * s ^ i = x * s ^ (i + 1) := by rw [pow_succ', mul_assoc]
    rw [h1, h2]

include hN in

theorem coindShift_pow_eq_one {N : ℕ} (hsN : s ^ N ∈ (H : Subgroup G)) :
    coindShift (H := H) (M := M) s ^ N = 1 := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  rw [coindShift_pow_apply]
  change _ = f.1 x
  have hc : x * s ^ N * x⁻¹ ∈ (H : Subgroup G) := hN.conj_mem _ hsN x
  have he : x * s ^ N = x * s ^ N * x⁻¹ * x := by group
  rw [he, coindRes_apply_mul f hc, ← Module.End.mul_apply, ← map_mul,
    show x * (s ^ N)⁻¹ * x⁻¹ * (x * s ^ N * x⁻¹) = 1 by group, map_one, Module.End.one_apply]

end Shift

section CharP

variable {A : Type*} [AddCommGroup A] [Module k A]

theorem charP_end_of_nsmul [Nontrivial A] {p : ℕ} [hp : Fact p.Prime] (h : ∀ a : A, p • a = 0) :
    CharP (Module.End k A) p := by
  refine ⟨fun n => ⟨fun hn => ?_, fun ⟨c, hc⟩ => ?_⟩⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have h1 : n • a = 0 := by
      have := LinearMap.congr_fun hn a
      rwa [Module.End.natCast_apply, LinearMap.zero_apply] at this
    have hord : addOrderOf a = p := by
      rcases (Nat.dvd_prime hp.out).1 (addOrderOf_dvd_of_nsmul_eq_zero (h a)) with h' | h'
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h') ha
      · exact h'
    rw [← hord]
    exact addOrderOf_dvd_of_nsmul_eq_zero h1
  · refine LinearMap.ext fun a => ?_
    rw [Module.End.natCast_apply, LinearMap.zero_apply, hc, mul_comm, mul_nsmul, h]

theorem sub_one_pow_prime_pow {p : ℕ} [Fact p.Prime] (h : ∀ a : A, p • a = 0) (R : Module.End k A)
    (a : ℕ) : (R - 1) ^ (p ^ a) = R ^ (p ^ a) - 1 := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact LinearMap.ext fun _ => Subsingleton.elim _ _
  · have := charP_end_of_nsmul (k := k) h
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right R), one_pow]

theorem sub_one_pow_prime_pow_eq_zero {p : ℕ} [Fact p.Prime] (h : ∀ a : A, p • a = 0)
    (R : Module.End k A) (a : ℕ) (hR : R ^ (p ^ a) = 1) : (R - 1) ^ (p ^ a) = 0 := by
  rw [sub_one_pow_prime_pow h R a, hR, sub_self]

end CharP

section Kernel

variable [TopologicalSpace G] {H : OpenSubgroup G} {M : Rep.{u} k G}

noncomputable def coindResConst (m : M) : coindRes H M :=
  ⟨fun x => M.ρ x m, fun h x => by
    change M.ρ ((h : G) * x) m = M.ρ (h : G) (M.ρ x m)
    rw [map_mul, Module.End.mul_apply]⟩

theorem coindShift_coindResConst (s : G) (m : M) :
    coindShift s (coindResConst (H := H) m) = coindResConst m := by
  refine Subtype.ext (funext fun x => ?_)
  change M.ρ (x * s⁻¹ * x⁻¹) (M.ρ (x * s) m) = M.ρ x m
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem eq_coindResConst_of_coindShift_eq {s : G}
    (hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G)) {f : coindRes H M}
    (hf : coindShift s f = f) : f = coindResConst (H := H) (f.1 1) := by
  have hstep : ∀ y : G, f.1 (y * s) = M.ρ (y * s * y⁻¹) (f.1 y) := fun y => by
    have h := congrArg (fun f : coindRes H M => f.1 y) hf
    change M.ρ (y * s⁻¹ * y⁻¹) (f.1 (y * s)) = f.1 y at h
    rw [← h, ← Module.End.mul_apply, ← map_mul,
      show y * s * y⁻¹ * (y * s⁻¹ * y⁻¹) = 1 by group, map_one, Module.End.one_apply]
  have hpow : ∀ i : ℕ, f.1 (s ^ i) = M.ρ (s ^ i) (f.1 1) := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, hstep, ih, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hi⟩ := hgen x
  change f.1 x = M.ρ x (f.1 1)
  have h := coindRes_apply_mul f hi (s ^ i)
  rw [show x * (s ^ i)⁻¹ * s ^ i = x by group, hpow, ← Module.End.mul_apply, ← map_mul,
    show x * (s ^ i)⁻¹ * s ^ i = x by group] at h
  exact h

variable {A : Rep.{u} k G} in
omit [TopologicalSpace G] in

theorem ker_le_comap (T : Module.End k A) (hT : ∀ g : G, Commute T (A.ρ g)) (g : G) :
    LinearMap.ker T ≤ (LinearMap.ker T).comap (A.ρ g) := by
  intro x hx
  change T (A.ρ g x) = 0
  rw [← Module.End.mul_apply, (hT g).eq, Module.End.mul_apply, LinearMap.mem_ker.1 hx, map_zero]

noncomputable abbrev coindT (s : G) : Module.End k (coindRes H M) :=
  coindShift s - 1

noncomputable def kerShiftEquiv {s : G} (hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G)) :
    M ≃ₗ[k] LinearMap.ker (coindT (H := H) (M := M) s) where
  toFun m := ⟨coindResConst m, by
    change coindShift s (coindResConst (H := H) m) - coindResConst m = 0
    rw [coindShift_coindResConst, sub_self]⟩
  invFun f := f.1.1 1
  left_inv m := by
    change M.ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  right_inv f := by
    have hf : coindShift s f.1 = f.1 := by
      have h : coindShift s f.1 - f.1 = 0 := LinearMap.mem_ker.1 f.2
      rwa [sub_eq_zero] at h
    exact Subtype.ext (eq_coindResConst_of_coindShift_eq (H := H) hgen hf).symm
  map_add' m n := Subtype.ext (Subtype.ext (funext fun x => map_add (M.ρ x) m n))
  map_smul' c m := Subtype.ext (Subtype.ext (funext fun x => map_smul (M.ρ x) c m))

theorem commute_coindShift_sub_one [(H : Subgroup G).Normal] {s : G}
    (hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G)) (g : G) :
    Commute (coindT (H := H) (M := M) s) ((coindRes H M).ρ g) :=
  LinearMap.ext fun f => by
    have h : coindShift s ((coindRes H M).ρ g f) = (coindRes H M).ρ g (coindShift s f) :=
      LinearMap.congr_fun (commute_coindShift hs g).eq f
    change coindShift s ((coindRes H M).ρ g f) - (coindRes H M).ρ g f =
      (coindRes H M).ρ g (coindShift s f - f)
    rw [map_sub, h]

noncomputable def kerShiftIso [(H : Subgroup G).Normal] {s : G}
    (hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G))
    (hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G)) :
    M ≅ Rep.subrepresentation (coindRes H M) (LinearMap.ker (coindT (H := H) (M := M) s))
      (ker_le_comap _ (commute_coindShift_sub_one hs)) :=
  have hcomm : ∀ (g : G) (m : M), kerShiftEquiv hgen (M.ρ g m) =
      ((coindRes H M).ρ g).restrict
        (ker_le_comap _ (commute_coindShift_sub_one hs) g)
        (kerShiftEquiv hgen m) := fun g m =>
    Subtype.ext (Subtype.ext (funext fun x => by
      change M.ρ x (M.ρ g m) = M.ρ (x * g) m
      rw [map_mul, Module.End.mul_apply]))
  { hom := Rep.ofHom ⟨(kerShiftEquiv hgen).toLinearMap, fun g => LinearMap.ext fun m => hcomm g m⟩
    inv := Rep.ofHom ⟨(kerShiftEquiv hgen).symm.toLinearMap, fun g => LinearMap.ext fun f => by
      obtain ⟨m, rfl⟩ := (kerShiftEquiv hgen).surjective f
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      erw [← hcomm g m]
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]⟩
    hom_inv_id := by
      ext m
      exact (kerShiftEquiv hgen).symm_apply_apply m
    inv_hom_id := by
      ext f
      exact congrArg Subtype.val ((kerShiftEquiv hgen).apply_symm_apply f) }

variable [hN : (H : Subgroup G).Normal]

include hN in

noncomputable def coindOfFun (φ : G ⧸ (H : Subgroup G) → M) : coindRes H M :=
  ⟨fun x => M.ρ (x * (Quotient.out (QuotientGroup.mk x : G ⧸ (H : Subgroup G)))⁻¹)
    (φ (QuotientGroup.mk x)), fun h x => by
    have hq : (QuotientGroup.mk ((h : G) * x) : G ⧸ (H : Subgroup G)) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      have e : ((h : G) * x)⁻¹ * x = x⁻¹ * (h : G)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact hN.conj_mem _ (inv_mem h.2) x⁻¹
    change M.ρ ((h : G) * x * (Quotient.out (QuotientGroup.mk ((h : G) * x) :
        G ⧸ (H : Subgroup G)))⁻¹) (φ (QuotientGroup.mk ((h : G) * x))) =
      M.ρ (h : G) (M.ρ (x * (Quotient.out (QuotientGroup.mk x : G ⧸ (H : Subgroup G)))⁻¹)
        (φ (QuotientGroup.mk x)))
    rw [hq, ← Module.End.mul_apply, ← map_mul, mul_assoc]⟩

theorem coindOfFun_injective : Function.Injective (coindOfFun (H := H) (M := M)) := by
  intro φ ψ h
  funext q
  have h' := congrArg (fun f : coindRes H M => f.1 (Quotient.out q)) h
  simpa [coindOfFun, QuotientGroup.out_eq'] using h'

end Kernel

section Main

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem eulerChar_subrepresentation_congr {A : Rep.{u} k G} {W W' : Submodule k A} (h : W = W')
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) (hW' : ∀ g, W' ≤ W'.comap (A.ρ g)) [IsDiscreteRep A] :
    eulerChar (Rep.subrepresentation A W hW) = eulerChar (Rep.subrepresentation A W' hW') := by
  subst h
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

def subrepresentationTopIso (A : Rep.{u} k G)
    (h : ∀ g, (⊤ : Submodule k A) ≤ (⊤ : Submodule k A).comap (A.ρ g)) :
    Rep.subrepresentation A ⊤ h ≅ A where
  hom := Rep.subtype A ⊤ h
  inv := Rep.ofHom ⟨(Submodule.topEquiv : (⊤ : Submodule k A) ≃ₗ[k] A).symm.toLinearMap,
    fun _ => rfl⟩
  hom_inv_id := by
    ext x
    rfl
  inv_hom_id := by
    ext x
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem eq_and_eq_of_mul_eq_mul_of_le {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (h : a * b = A * B)
    (hA : 0 < A) (hB : 0 < B) : a = A ∧ b = B := by
  rcases Nat.lt_or_ge a A with h1 | h1
  · exfalso
    have : a * b < A * B :=
      calc a * b ≤ a * B := Nat.mul_le_mul_left _ hb
        _ < A * B := Nat.mul_lt_mul_of_pos_right h1 hB
    omega
  · have haA : a = A := le_antisymm ha h1
    subst haA
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hA h⟩

variable [CompactSpace G]

theorem card_pow_le_card_coindRes {H : OpenSubgroup G} [(H : Subgroup G).Normal]
    {M : Rep.{u} k G} [Finite M] [Finite (G ⧸ (H : Subgroup G))] :
    Nat.card M ^ Nat.card (G ⧸ (H : Subgroup G)) ≤ Nat.card (coindRes H M) := by
  have : Finite (Rep.res (H : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have : Finite (coindRes H M) := finite_coind H (Rep.res (H : Subgroup G).subtype M)
  rw [← Nat.card_fun]
  exact Nat.card_le_card_of_injective _ coindOfFun_injective

theorem eulerChar_coind_res_eq_pow {P : ℕ → Prop} (hPdvd : ∀ m n, m ∣ n → P n → P m)
    (hPmul : ∀ m n, P m → P n → P (m * n)) (hG : HasFiniteCohomology k G P) (H : OpenSubgroup G)
    [hN : (H : Subgroup G).Normal] [IsCyclic (G ⧸ (H : Subgroup G))] {p a : ℕ} [hp : Fact p.Prime]
    (hcard : Nat.card (G ⧸ (H : Subgroup G)) = p ^ a) (M : Rep.{u} k G) [IsDiscreteRep M]
    [Finite M] (hM : P (Nat.card M)) (hpM : ∀ m : M, p • m = 0) :
    eulerChar (Rep.coind (H : Subgroup G).subtype (Rep.res (H : Subgroup G).subtype M)) =
      eulerChar M ^ (p ^ a) := by
  have hQ : Finite (G ⧸ (H : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ (H : Subgroup G))
  have hmk : (QuotientGroup.mk (Quotient.out q) : G ⧸ (H : Subgroup G)) = q :=
    QuotientGroup.out_eq' q
  set s : G := Quotient.out q

  have hs : ∀ g : G, s * g * s⁻¹ * g⁻¹ ∈ (H : Subgroup G) := by
    intro g
    have hc : (QuotientGroup.mk (g * s) : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s * g) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact (IsCyclic.commGroup (α := G ⧸ (H : Subgroup G))).mul_comm _ _
    have h2 := hN.conj_mem _ (QuotientGroup.eq.1 hc) (g * s)
    have e : s * g * s⁻¹ * g⁻¹ = g * s * ((g * s)⁻¹ * (s * g)) * (g * s)⁻¹ := by group
    rw [e]
    exact h2
  have hsN : s ^ (p ^ a) ∈ (H : Subgroup G) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← hcard]
    exact pow_card_eq_one'
  have hgen : ∀ x : G, ∃ i : ℕ, x * (s ^ i)⁻¹ ∈ (H : Subgroup G) := by
    intro x
    obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hq (QuotientGroup.mk x))
    refine ⟨i, ?_⟩
    have h1 : (QuotientGroup.mk x : G ⧸ (H : Subgroup G)) = QuotientGroup.mk (s ^ i) := by
      rw [QuotientGroup.mk_pow, hmk]
      exact hi.symm
    have h3 := hN.conj_mem _ (inv_mem (QuotientGroup.eq.1 h1)) x
    have e : x * (s ^ i)⁻¹ = x * (x⁻¹ * s ^ i)⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3

  set T : Module.End k (coindRes H M) := coindT (H := H) (M := M) s with hT_def
  have hT : ∀ g : G, Commute T ((coindRes H M).ρ g) := commute_coindShift_sub_one hs
  have hCp : ∀ f : coindRes H M, p • f = 0 := fun f =>
    Subtype.ext (funext fun x => hpM (f.1 x))
  have hTN : T ^ (p ^ a) = 0 :=
    sub_one_pow_prime_pow_eq_zero hCp (coindShift (H := H) (M := M) s) a (coindShift_pow_eq_one hsN)
  let D : ℕ → Submodule k (coindRes H M) := fun j => LinearMap.range (T ^ j)
  have hD : ∀ j (g : G), D j ≤ (D j).comap ((coindRes H M).ρ g) := by
    rintro j g _ ⟨y, rfl⟩
    exact ⟨(coindRes H M).ρ g y, by
      rw [← Module.End.mul_apply, ((hT g).pow_left j).eq, Module.End.mul_apply]⟩
  have hDsucc : ∀ j, (D j).map T = D (j + 1) := fun j => by
    simp only [D]
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
  have hD0 : D 0 = ⊤ := by
    show LinearMap.range (T ^ 0) = ⊤
    rw [pow_zero]
    exact LinearMap.range_eq_top.2 fun x => ⟨x, rfl⟩
  have hDN : D (p ^ a) = ⊥ := by simp [D, hTN]
  have hK : ∀ g : G, LinearMap.ker T ≤ (LinearMap.ker T).comap ((coindRes H M).ρ g) :=
    ker_le_comap T hT

  have : Finite (Rep.res (H : Subgroup G).subtype M) := inferInstanceAs (Finite M)
  have : Finite (coindRes H M) := finite_coind H (Rep.res (H : Subgroup G).subtype M)
  have : IsDiscreteRep (coindRes H M) := isDiscreteRep_coind_res H M
  set c := Nat.card (LinearMap.ker T) with hc
  have hcM : c = Nat.card M := Nat.card_congr (kerShiftEquiv (H := H) (M := M) hgen).toEquiv.symm
  have hstep : ∀ j, Nat.card (D j) =
      Nat.card ↥(D j ⊓ LinearMap.ker T) * Nat.card (D (j + 1)) := fun j => by
    rw [card_rangeStep T (D j), hDsucc]
  have hle : ∀ j, Nat.card ↥(D j ⊓ LinearMap.ker T) ≤ c := fun j =>
    Nat.card_le_card_of_injective _
      (Submodule.inclusion_injective (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T))
  have hcpos : 0 < c := Nat.card_pos
  have hup : ∀ m j, j + m = p ^ a → Nat.card (D j) ≤ c ^ m := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      rw [hDN]
      simp
    | succ m ih =>
      intro j hj
      rw [hstep j, pow_succ']
      exact Nat.mul_le_mul (hle j) (ih (j + 1) (by omega))
  have hlow : c ^ (p ^ a) ≤ Nat.card (D 0) := by
    rw [hD0, Nat.card_congr (Submodule.topEquiv).toEquiv, hcM, ← hcard]
    exact card_pow_le_card_coindRes
  have hexact : ∀ j ≤ p ^ a, Nat.card (D j) = c ^ (p ^ a - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact le_antisymm (hup _ 0 (by simp)) (by simpa using hlow)
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      rw [hstep j] at h1
      have h2 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at h1
      exact (eq_and_eq_of_mul_eq_mul_of_le (hle j) (hup _ (j + 1) (by omega)) h1 hcpos
        (pow_pos hcpos _)).2
  have hfull : ∀ j < p ^ a, D j ⊓ LinearMap.ker T = LinearMap.ker T := by
    intro j hj
    have h1 := hexact j hj.le
    rw [hstep j, hexact (j + 1) hj] at h1
    have h3 : c ^ (p ^ a - j) = c * c ^ (p ^ a - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3] at h1
    have hcard' : Nat.card ↥(D j ⊓ LinearMap.ker T) = c :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hcpos _) h1
    apply Submodule.toAddSubgroup_injective
    refine AddSubgroup.eq_of_le_of_card_ge
      ((Submodule.toAddSubgroup_le _ _).2 (inf_le_right : D j ⊓ LinearMap.ker T ≤ LinearMap.ker T)) ?_
    change Nat.card (LinearMap.ker T) ≤ Nat.card ↥(D j ⊓ LinearMap.ker T)
    rw [hcard']

  have hP : P (Nat.card (coindRes H M)) := by
    have hpow : ∀ n, P (Nat.card M ^ n) := fun n => by
      induction n with
      | zero => exact hPdvd 1 _ (one_dvd _) hM
      | succ n ih =>
        rw [pow_succ]
        exact hPmul _ _ ih hM
    exact hPdvd _ _ (card_coind_dvd H (Rep.res (H : Subgroup G).subtype M)) (hpow _)
  have hchain : ∀ j ≤ p ^ a, eulerChar (Rep.subrepresentation _ (D 0) (hD 0)) =
      eulerChar (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ j *
        eulerChar (Rep.subrepresentation _ (D j) (hD j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      rw [ih (by omega), eulerChar_rangeStep T hT (D j) (hD j) hPdvd hG hP,
        eulerChar_subrepresentation_congr (hfull j (by omega)) _ hK,
        eulerChar_subrepresentation_congr (hDsucc j) _ (hD (j + 1)), pow_succ]
      ring
  have hbot : eulerChar (Rep.subrepresentation _ (D (p ^ a)) (hD (p ^ a))) = 1 := by
    rw [eulerChar_subrepresentation_congr hDN _ (fun _ => bot_le)]
    exact eulerChar_eq_one_of_subsingleton _
  have : IsDiscreteRep (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
    isDiscreteRep_subrepresentation (coindRes H M) ⊤ (fun _ => le_top)
  calc eulerChar (coindRes H M)
      = eulerChar (Rep.subrepresentation (coindRes H M) ⊤ (fun _ => le_top)) :=
        (eulerChar_eq_of_iso (subrepresentationTopIso (coindRes H M) (fun _ => le_top))).symm
    _ = eulerChar (Rep.subrepresentation _ (D 0) (hD 0)) :=
        eulerChar_subrepresentation_congr hD0.symm _ _
    _ = eulerChar (Rep.subrepresentation _ (LinearMap.ker T) hK) ^ (p ^ a) :=
        by rw [hchain (p ^ a) le_rfl, hbot, mul_one]
    _ = eulerChar M ^ (p ^ a) := by
        rw [← eulerChar_eq_of_iso (kerShiftIso (H := H) (M := M) hs hgen)]

theorem eulerChar_res_eq_pow {P : ℕ → Prop} (hPdvd : ∀ m n, m ∣ n → P n → P m)
    (hPmul : ∀ m n, P m → P n → P (m * n)) (hG : HasFiniteCohomology k G P) (H : OpenSubgroup G)
    [(H : Subgroup G).Normal] [IsCyclic (G ⧸ (H : Subgroup G))] {p a : ℕ} [Fact p.Prime]
    (hcard : Nat.card (G ⧸ (H : Subgroup G)) = p ^ a) (M : Rep.{u} k G) [IsDiscreteRep M]
    [Finite M] (hM : P (Nat.card M)) (hpM : ∀ m : M, p • m = 0) :
    eulerChar (Rep.res (H : Subgroup G).subtype M) = eulerChar M ^ (p ^ a) := by
  rw [eulerChar_res_eq_eulerChar_coind H M]
  exact eulerChar_coind_res_eq_pow hPdvd hPmul hG H hcard M hM hpM

end Main

end GroundTheory.ProfCoh
