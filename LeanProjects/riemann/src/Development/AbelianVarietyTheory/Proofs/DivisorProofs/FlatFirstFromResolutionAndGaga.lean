import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalResidueTensorInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.PTors

def HasLev {A : Type} [CommRing A] (O : Type) [Ring O] (L M : Type) [AddCommGroup L] [AddCommGroup M]
    [Module O L] [Module O M] [Module A L] [Module A M] (I : Ideal A) : Prop :=
  ∃ l : L →ₗ[O] M, (∀ x, l x = 0 ↔ x ∈ I • (⊤ : Submodule A L)) ∧ ∀ g : M, (∀ c ∈ I, c • g = 0) → ∃ y, l y = g

section Alg

variable {A : Type} [CommRing A] {O : Type} [Ring O] [Algebra A O] {L M : Type} [AddCommGroup L] [AddCommGroup M]
  [Module O L] [Module O M] [Module A L] [Module A M] [IsScalarTower A O L] [IsScalarTower A O M]

omit [Algebra A O] [IsScalarTower A O L] [IsScalarTower A O M] in
theorem hasLev_top : HasLev O L M (⊤ : Ideal A) :=
  ⟨0, fun x => by simp, fun g hg => ⟨0, by simpa using (hg 1 Submodule.mem_top).symm⟩⟩

theorem HasLev.mul {I J : Ideal A} (hIJ : I ⊔ J = ⊤) (hI : HasLev O L M I) (hJ : HasLev O L M J) :
    HasLev O L M (I * J) := by
  obtain ⟨l₁, k₁, s₁⟩ := hI
  obtain ⟨l₂, k₂, s₂⟩ := hJ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ.symm ▸ Submodule.mem_top : (1 : A) ∈ I ⊔ J)
  have t₁ : ∀ c ∈ I, ∀ x, c • l₁ x = 0 := fun c hc x => by
    rw [← LinearMap.map_smul_of_tower]
    exact (k₁ _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)
  have t₂ : ∀ c ∈ J, ∀ x, c • l₂ x = 0 := fun c hc x => by
    rw [← LinearMap.map_smul_of_tower]
    exact (k₂ _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)
  have u₁ : ∀ x, b • l₁ x = l₁ x := fun x => by
    conv_rhs => rw [← one_smul A (l₁ x), ← hab, add_smul, t₁ a ha, zero_add]
  have u₂ : ∀ x, a • l₂ x = l₂ x := fun x => by
    conv_rhs => rw [← one_smul A (l₂ x), ← hab, add_smul, t₂ b hb, add_zero]
  refine ⟨l₁ + l₂, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun g hg => ?_⟩
  · rw [LinearMap.add_apply] at h
    have h₁ : l₁ x = 0 := by
      have := congrArg (b • ·) h
      simpa only [smul_add, u₁, t₂ b hb, add_zero, smul_zero] using this
    have h₂ : l₂ x = 0 := by rwa [h₁, zero_add] at h
    have e : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul ha ((k₂ x).1 h₂)
    · rw [mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hb ((k₁ x).1 h₁)
  · rw [LinearMap.add_apply, (k₁ x).2 (Submodule.smul_mono_left Ideal.mul_le_left h),
      (k₂ x).2 (Submodule.smul_mono_left Ideal.mul_le_right h), add_zero]
  · obtain ⟨y₁, hy₁⟩ := s₁ (b • g) fun c hc => by
      rw [smul_smul]; exact hg _ (Ideal.mul_mem_mul hc hb)
    obtain ⟨y₂, hy₂⟩ := s₂ (a • g) fun c hc => by
      rw [smul_smul, mul_comm]; exact hg _ (Ideal.mul_mem_mul ha hc)
    refine ⟨b • y₁ + a • y₂, ?_⟩
    simp only [LinearMap.add_apply, map_add, LinearMap.map_smul_of_tower, smul_add]
    rw [u₁, u₂, t₁ a ha, t₂ b hb, hy₁, hy₂, add_zero, zero_add, ← add_smul, add_comm, hab, one_smul]

theorem hasLev_of_prime_pow [IsDedekindDomain A] (q : A) (hq : q ≠ 0) (e : ℕ)
    (h : ∀ w : Ideal A, w.IsMaximal → q ∈ w → ∀ r, HasLev O L M (w ^ r)) (I : Ideal A) :
    q ^ e ∈ I → HasLev O L M I := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h0 => absurd (Ideal.mem_bot.1 h0) (pow_ne_zero _ hq)
  | h1 hu => rw [Ideal.isUnit_iff.1 hu]; exact fun _ => hasLev_top
  | @hpr w i hw =>
    intro hm
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]; exact hasLev_top
    · have hwp := Ideal.isPrime_of_prime hw
      exact h w (hwp.isMaximal hw.ne_zero) (hwp.mem_of_pow_mem e (Ideal.pow_le_self hi.ne' hm)) i
  | @hcp I J hIJ hI hJ =>
    intro hm
    refine HasLev.mul ?_ (hI (Ideal.mul_le_left hm)) (hJ (Ideal.mul_le_right hm))
    exact Ideal.isUnit_iff.1 (hIJ (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))

end Alg

open GlobalTheory.AV GlobalTheory.AV.AbVar in

theorem card_ker_eq_det {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (u u' : A ⟶ A) [IsMonHom u] [IsMonHom u']
    (n : ℕ) (hn : n ≠ 0) (hu : u ≫ u' = (𝟙 A) ^ n)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (φ : L →ₗ[ℤ] L)
    (hφ : LinearMap.det φ ≠ 0) (l : ℕ) (hl : l.Prime) (ev : ℕ → L → (Over.mk x ⟶ A))
    (h1 : ∀ j y z, ev j (y + z) = ev j y * ev j z) (h2 : ∀ j y, ev j (φ y) = ev j y ≫ u)
    (h3 : ∀ j y, ev j y = 1 ↔ ∃ z, y = l ^ j • z)
    (h4 : ∀ j (q : Over.mk x ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ y, ev j y = q) :
    Nat.card {g : Over.mk x ⟶ A // g ≫ u = 1} = (LinearMap.det φ).natAbs := by
  obtain ⟨x', rfl⟩ : ∃ x', x = 𝟙 _ ≫ x' := ⟨x, (Category.id_comp x).symm⟩
  letI : GrpObj ((Over.pullback x').obj A) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj x' A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k ((Over.pullback x').obj A) hA'
  let B : AbVar k := { X := (Over.pullback x').obj A, ab := hA', dim := g, smooth := hg }
  have pb : IsGrpPullback B.X A x' (pullback.fst A.hom x') := isGrpPullback_pullback A x'
  have hbij : ∀ T : Over (Sp k), Function.Bijective (pushHom pb T) := fun T => by
    constructor
    · intro y z e
      apply Over.OverMorphism.ext
      apply pb.1.hom_ext
      · exact congrArg (fun z => z.left) e
      · rw [Over.w, Over.w]
    · intro y
      refine ⟨Over.homMk (pb.1.lift y.left T.hom (Over.w y)) (pb.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pb.1.lift_fst _ _ _)
  let f : B ⟶ B := Hom.mk (A := B) (B := B) ((Over.pullback x').map u)
    (h := inferInstanceAs (IsMonHom ((Over.pullback x').map u)))
  have hf : ∀ (T : Over (Sp k)) (y : T ⟶ B.X), pushHom pb T (y ≫ f.hom) = pushHom pb T y ≫ u := fun T y => by
    apply Over.OverMorphism.ext
    change (y.left ≫ ((Over.pullback x').map u).left) ≫ pullback.fst A.hom x' =
      (y.left ≫ pullback.fst A.hom x') ≫ u.left
    rw [Category.assoc, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  let e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* (Over.mk (𝟙 _ ≫ x') ⟶ A) :=
    MulEquiv.ofBijective (pushHom pb (Over.mk (𝟙 (Sp k)))) (hbij _)
  have ea : ∀ y, e (y ≫ f.hom) = e y ≫ u := fun y => hf _ y
  have hlk : (l : k) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hch := charpoly_eq_lattice_model k B f L φ l hl hlk (fun j y => e.symm (ev j y))
    (fun j y z => by rw [h1, map_mul])
    (fun j y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, h2]))
    (fun j y => by rw [map_eq_one_iff _ e.symm.injective]; exact h3 j y)
    (fun j q => by
      rw [← map_eq_one_iff e e.injective, map_pow, h4 j (e q)]
      exact exists_congr fun y => e.symm_apply_eq.symm)
  have hev := (charpoly_spec k B f).1.2.2 0
  rw [← hch, LinearMap.eval_charpoly, map_zero, zero_sub, Int.cast_zero, zero_sub] at hev
  have hdet : (LinearMap.det (-φ)).natAbs = (LinearMap.det φ).natAbs := by
    rw [← neg_one_smul ℤ φ, LinearMap.det_smul, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hdeg : deg (A := B) (B := B) (-f) = (LinearMap.det φ).natAbs := by
    rw [← hdet, hev, Int.natAbs_natCast]
  have hiso : IsIsogeny (A := B) (B := B) (-f) := by
    by_contra h
    rw [deg, if_neg h] at hdeg
    exact hφ (Int.natAbs_eq_zero.1 hdeg.symm)
  have hneg : ∀ (T : Over (Sp k)) (y : T ⟶ B.X), y ≫ Hom.hom (-f) = 1 ↔ y ≫ f.hom = 1 := fun T y => by
    rw [neg_hom, GrpObj.comp_inv, inv_eq_one]
  have hk := GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed k B B (-f) n (Nat.cast_ne_zero.2 hn) hiso fun T y hy => by
    apply (hbij T).1
    have h := hf T y
    rw [(hneg T y).1 hy, map_one] at h
    rw [map_pow, map_one, ← comp_pow_id_torscard, ← hu, ← Category.assoc, ← h, MonObj.one_comp]
  rw [← hdeg, hk]
  obtain ⟨e', he'⟩ := GlobalTheory.CharpolyLattice.pts_equiv k B
  refine Nat.card_congr (Equiv.subtypeEquiv (e.symm.trans e').toEquiv fun y => ?_)
  obtain ⟨y, rfl⟩ := e.surjective y
  change _ ↔ e' (e.symm (e y)) ≫ Hom.hom (-f) = 1
  rw [e.symm_apply_apply, hneg, ← he', ← ea, map_eq_one_iff e e.injective, map_eq_one_iff e' e'.injective]

section Loc

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def mulLa (c : 𝓞 D.F) : D.La →ₗ[ℤ] D.La :=
  (DistribSMul.toAddMonoidHom D.La (algebraMap (𝓞 D.F) D.O c)).toIntLinearMap

theorem exists_mul_eq_nat {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (hc : c ≠ 0) :
    ∃ (c' : 𝓞 F) (n : ℕ), n ≠ 0 ∧ c' * c = n := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨c', _, ?_, hc'⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc

theorem natAbs_det_mulLa (w : Ideal (𝓞 D.F)) (hw : w.IsMaximal) (H : ℕ) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hH : w ^ H = Ideal.span {c}) :
    letI := D.freeLa
    letI := D.finLa
    (LinearMap.det (mulLa D c)).natAbs = Nat.card (𝓞 D.F ⧸ w) ^ (H * (D.m * D.n)) := by
  letI := D.freeLa
  letI := D.finLa
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hinj : Function.Injective (mulLa D c) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
    have h1 : (n : ℤ) • y = 0 := by
      have h2 : (c' * c) • y = 0 := by
        rw [mul_smul]
        exact (congrArg (c' • ·) hy).trans (smul_zero _)
      rwa [h, Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at h2
    exact (smul_eq_zero.1 h1).resolve_left (Int.natCast_ne_zero.2 hn)
  have h := Submodule.natAbs_det_equiv (LinearMap.range (mulLa D c)) (LinearEquiv.ofInjective _ hinj)
  have e : (LinearMap.range (mulLa D c)).subtype ∘ₗ AddMonoidHom.toIntLinearMap
      ((LinearEquiv.ofInjective _ hinj : D.La ≃ₗ[ℤ] LinearMap.range (mulLa D c)) :
        D.La →+ LinearMap.range (mulLa D c)) = mulLa D c := LinearMap.ext fun _ => rfl
  rw [e] at h
  obtain ⟨g, hgs, -, hgk⟩ := GlobalTheory.UPel.HT.EtLev.latQuot_free p D w H hw
  have hker : LinearMap.range (mulLa D c) = LinearMap.ker g.toIntLinearMap := by
    ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    change _ ↔ g y = 0
    rw [hgk, ← GlobalTheory.UPel.HT.EtLev.mem_smul_top_iff_wSub, hH, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, Submodule.mem_top, hz⟩, fun ⟨z, _, hz⟩ => ⟨z, hz⟩⟩
  rw [h, hker, Nat.card_congr (g.toIntLinearMap.quotKerEquivOfSurjective hgs).toEquiv, Nat.card_fun,
    Nat.card_fin, pow_mul _ H, ← Submodule.cardQuot_apply (w ^ H), ← Ideal.absNorm_apply, map_pow,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_torsion_place {F : Type} [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (w : Ideal (𝓞 F)) (hmax : w.IsMaximal) (hne : w ≠ ⊥) (h : ℕ)
    (hdiv : ∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g))
    (hcount : ∀ (H : ℕ) (c : 𝓞 F), c ≠ 0 → w ^ H = Ideal.span {c} →
      Nat.card {g : M // c • g = 0} = Nat.card (𝓞 F ⧸ w) ^ (H * h)) :
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w) ^ h := by
  have hwnz : w ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w, hwnz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨w, hwnz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hTH : Nat.card (Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w) ^ (H * h) := by
    rw [← hcount H c hc0 hspan, hspan, Submodule.torsionBySet_span_singleton_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Submodule.mem_torsionBy_iff c g)
  have hq : 1 < Nat.card (𝓞 F ⧸ w) := by
    have hfin : Finite (𝓞 F ⧸ w) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w
    exact Finite.one_lt_card
  have hTHfin : Finite (Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F)) ≤
      Submodule.torsionBySet (𝓞 F) M ((w ^ H : Ideal (𝓞 F)) : Set (𝓞 F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w
  haveI : Module.Finite (𝓞 F ⧸ w) (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 F ⧸ w) (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 F) M (w : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.torsion_pow_card F M w h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * h = H * h' := Nat.pow_right_injective hq hall
  rw [hT1, Nat.eq_of_mul_eq_mul_left hH0 he]

theorem exists_lev_of_card (G : Type) [CommGroup G] (act : D.O → G → G)
    (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
    (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ g : G, ∃ g' : G, g' ^ n = g)
    (hcount : letI := D.freeLa
      letI := D.finLa
      ∀ c : 𝓞 D.F, c ≠ 0 → LinearMap.det (mulLa D c) ≠ 0 →
        Nat.card {g : G // act (algebraMap (𝓞 D.F) D.O c) g = 1} = (LinearMap.det (mulLa D c)).natAbs) (e : ℕ) :
    ∃ ev : D.La → G, (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = act c (ev y)) ∧
      (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ q : G, q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  letI : Module D.O (Additive G) := GlobalTheory.EtLevMorita.actModule act hmul hone hcomp hadd
  letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
    show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
    show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hp0 : ((p : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hdiv' : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive G => c • g) := by
    intro c hc g
    obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
    obtain ⟨g', hg'⟩ := hdiv n (Nat.pos_of_ne_zero hn) g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, h, Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl
  have hloc : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → ∀ r,
      HasLev D.O D.La (Additive G) (w ^ r) := by
    intro w hw hpw r
    have hne : w ≠ ⊥ := fun h0 => hp0 (by rwa [h0, Ideal.mem_bot] at hpw)
    have hq : Nat.card (𝓞 D.F ⧸ w) ≠ 0 := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    have h1 := card_torsion_place (Additive G) w hw hne (D.m * D.n) hdiv' fun H c hc hH => by
      have hd := natAbs_det_mulLa D w hw H c hc hH
      rw [← hd, ← hcount c hc (Int.natAbs_ne_zero.1 (by rw [hd]; exact pow_ne_zero _ hq))]
      rfl
    have hall := GlobalTheory.torsion_pow_card D.F _ w (D.m * D.n) hw hne hdiv' h1
    obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.torsionBySet_pow_free_of_natCard D.F _ w (D.m * D.n) r hw hne hall
    obtain ⟨l, l1, l2, l3, l4⟩ := GlobalTheory.EtLevMorita.exists_lev p D w r hw hpw G act hmul hone hcomp hadd
      (fun a => (f a).toMul) (fun a a' => by rw [map_add]; rfl) (fun c a => by rw [hf1]; rfl)
      (fun a a' h => hf2 h) (fun g hg => hf3 (Additive.ofMul g) hg)
    refine ⟨{ toFun := fun y => Additive.ofMul (l y)
              map_add' := fun y z => congrArg Additive.ofMul (l1 y z)
              map_smul' := fun b y => congrArg Additive.ofMul (l2 b y) }, fun y => ?_, fun g hg => l4 g.toMul hg⟩
    rw [GlobalTheory.UPel.HT.EtLev.mem_smul_top_iff_wSub]
    exact l3 y
  obtain ⟨l, l1, l2⟩ := hasLev_of_prime_pow (O := D.O) (L := D.La) (M := Additive G) _ hp0 e hloc
    (Ideal.span {((p : ℕ) : 𝓞 D.F) ^ e}) (Ideal.mem_span_singleton_self _)
  have hk : ∀ y, l y = 0 ↔ ∃ z, y = p ^ e • z := fun y => by
    rw [l1, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact ⟨fun ⟨z, _, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, Submodule.mem_top, hz.symm⟩⟩
  refine ⟨fun y => (l y).toMul, fun y z => congrArg Additive.toMul (l.map_add y z),
    fun c y => congrArg Additive.toMul (l.map_smul c y), hk,
    fun q => ⟨fun hq => l2 (Additive.ofMul q) fun c hc => ?_, ?_⟩⟩
  · obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← ofMul_pow, hq, ofMul_one, smul_zero]
  · rintro ⟨y, rfl⟩
    rw [← toMul_nsmul, ← map_nsmul, (hk _).2 ⟨y, rfl⟩, toMul_zero]

end Loc

theorem act_natCast {O : Type} [Ring O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OActN O G) (n : ℕ) :
    act.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem exists_ev_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∀ e : ℕ, ∃ ev : D.La → (Over.mk x ⟶ o.A), (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = ev y ≫ o.act.act c) ∧ (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  intro p _ D R _ b N _ _ S s o k _ _ _ x β hx e
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  letI := D.freeLa
  letI := D.finLa
  refine exists_lev_of_card D (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => by haveI := o.act.hom c; exact MonObj.mul_comp _ _ _)
    (fun g => by simp only [o.act.one, Category.comp_id])
    (fun c d g => by simp only [o.act.mul, Category.assoc])
    (fun c d g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _)
    (fun n hn g => GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed S o.A o.ab k x n hn g) (fun c hc hd => ?_) e
  obtain ⟨I, -⟩ := o.geom k x β hx
  obtain ⟨l, hl1, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hco : ∀ j, (l ^ j).Coprime p := fun j =>
    Nat.Coprime.pow_left j ((Nat.coprime_primes hl Fact.out).2 (by omega))
  obtain ⟨c', n, hn, h⟩ := exists_mul_eq_nat c hc
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c')
  exact card_ker_eq_det o.A o.ab k x (o.act.act (algebraMap (𝓞 D.F) D.O c))
    (o.act.act (algebraMap (𝓞 D.F) D.O c')) n hn
    (by rw [← o.act.mul, ← map_mul, h, map_natCast, act_natCast]) D.La (mulLa D c) hd l hl
    (fun j => I.ev (l ^ j)) (fun j => I.add _) (fun j y => I.lin _ _ y)
    (fun j => I.ker _ (pow_pos hl.pos j) (hco j)) (fun j => I.onto _ (pow_pos hl.pos j) (hco j))

end GlobalTheory.UPel.HT.PTors
