import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Opp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem proj_quot_of_sat {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) (h : ∀ a : R, a ≠ 0 → ∀ y : M, a • y ∈ N → y ∈ N) :
    Module.Projective R (M ⧸ N) := by
  have htor : Submodule.torsion R (M ⧸ N) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact h a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat R (M ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation R (M ⧸ N) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem exists_ef_eq (D : Datum H) (ψ : D.La →+ ℤ) : ∃ y : D.La, ∀ x, D.EF y x = ψ x := by
  obtain ⟨y, hy⟩ := D.unimod.2 ψ.toIntLinearMap
  exact ⟨y, fun x => by rw [hy]; rfl⟩

theorem fin_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

variable {D : Datum H} {Z : Submodule (𝓞 E) D.La}

theorem sat_int (hZ : IsIsoSat D Z) (n : ℤ) (hn : n ≠ 0) (y : D.La) (hy : n • y ∈ Z) : y ∈ Z := by
  refine hZ.2 n.natAbs y (by omega) ?_
  rcases Int.natAbs_eq n with h1 | h1
  · rw [← natCast_zsmul, ← h1]; exact hy
  · have : ((n.natAbs : ℤ)) • y = -(n • y) := by rw [h1]; simp
    rw [← natCast_zsmul, this]; exact Z.neg_mem hy

theorem proj_int (hZ : IsIsoSat D Z) : Module.Projective ℤ (D.La ⧸ Z.restrictScalars ℤ) := by
  haveI := fin_int D
  exact proj_quot_of_sat _ fun a ha y hy => sat_int hZ a ha y hy

theorem exists_ext (hZ : IsIsoSat D Z) (φ : Z →+ ℤ) : ∃ y : D.La, ∀ z : Z, D.EF z y = φ z := by
  haveI := proj_int hZ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Z.restrictScalars ℤ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ x : D.La, x - σ ((Z.restrictScalars ℤ).mkQ x) ∈ Z := fun x => by
    have : (Z.restrictScalars ℤ).mkQ (x - σ ((Z.restrictScalars ℤ).mkQ x)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmem x⟩) fun x x' => by
    rw [← map_add]; congr 1; ext; simp only [map_add, Submodule.coe_add]; abel)
  refine ⟨-y, fun z => ?_⟩
  have h0 : (Z.restrictScalars ℤ).mkQ (z : D.La) = 0 := (Submodule.Quotient.mk_eq_zero _).2 z.2
  rw [map_neg, ef_swap, neg_neg, hy]
  simp only [AddMonoidHom.mk'_apply, h0, map_zero, sub_zero]

theorem mem_of_perp_perp (hZ : IsIsoSat D Z) (y : D.La) (hy : ∀ p ∈ perp D Z, D.EF y p = 0) : y ∈ Z := by
  haveI := proj_int hZ
  by_contra hyZ
  have hu : (Z.restrictScalars ℤ).mkQ y ≠ 0 := fun h => hyZ ((Submodule.Quotient.mk_eq_zero _).1 h)
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual ℤ (D.La ⧸ Z.restrictScalars ℤ), χ ((Z.restrictScalars ℤ).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℤ _).1 hc)
  obtain ⟨p, hp⟩ := exists_ef_eq D (χ.comp (Z.restrictScalars ℤ).mkQ).toAddMonoidHom
  have hpZ : p ∈ perp D Z := fun z hz => by
    have h0 : (Z.restrictScalars ℤ).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    rw [hp, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, h0, map_zero]
  have := hy p hpZ
  rw [ef_swap, hp, neg_eq_zero] at this
  exact hχ this

theorem perp_sat (D : Datum H) (Z : Submodule (𝓞 E) D.La) (a : 𝓞 E) (ha : a ≠ 0) (y : D.La) (hy : a • y ∈ perp D Z) :
    y ∈ perp D Z := by
  have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
  intro z hz
  have h := (perp D Z).smul_mem a' hy z hz
  rw [smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hn0

theorem exists_opp (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z) : ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  haveI := D.fin
  haveI : Module.Projective (𝓞 E) (D.La ⧸ perp D Z) := proj_quot_of_sat _ (perp_sat D Z)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (perp D Z).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hsx : ∀ q, (perp D Z).mkQ (s q) = q := fun q => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  set C := LinearMap.range s with hC
  have hdec : ∀ x : D.La, x - s ((perp D Z).mkQ x) ∈ perp D Z := fun x =>
    (Submodule.Quotient.mk_eq_zero _).1 (by rw [← Submodule.mkQ_apply, map_sub, hsx, sub_self])
  have hC0 : ∀ c ∈ C, c ∈ perp D Z → c = 0 := by
    rintro _ ⟨q, rfl⟩ h
    have : q = 0 := by rw [← hsx q]; exact (Submodule.Quotient.mk_eq_zero _).2 h
    rw [this, map_zero]
  have hsC : ∀ c ∈ C, s ((perp D Z).mkQ c) = c := by
    rintro _ ⟨q, rfl⟩; rw [hsx]
  have hZx : ∀ (z : D.La), z ∈ Z → ∀ x, D.EF z x = D.EF z (s ((perp D Z).mkQ x)) := fun z hz x => by
    have := hdec x z hz
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  have A1 : ∀ φ : Z →+ ℤ, ∃! b : C, ∀ a : Z, D.EF a b = φ a := by
    intro φ
    obtain ⟨y, hy⟩ := exists_ext hZ φ
    refine ⟨⟨s ((perp D Z).mkQ y), _, rfl⟩, fun a => (hZx a a.2 y).symm.trans (hy a), fun b hb => Subtype.ext ?_⟩
    have h1 : (b : D.La) - s ((perp D Z).mkQ y) ∈ perp D Z := fun z hz => by
      rw [ef_swap, map_sub, hb ⟨z, hz⟩, ← hZx z hz, hy ⟨z, hz⟩, sub_self, neg_zero]
    exact sub_eq_zero.1 (hC0 _ (sub_mem b.2 ⟨_, rfl⟩) h1)

  have A2 : ∀ φ : C →+ ℤ, ∃! z : Z, ∀ c : C, D.EF c z = φ c := by
    intro φ
    have hmC : ∀ x : D.La, s ((perp D Z).mkQ x) ∈ C := fun x => ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmC x⟩) fun x x' => by
      rw [← map_add]; congr 1; ext; simp only [map_add, Submodule.coe_add])
    simp only [AddMonoidHom.mk'_apply] at hy
    have hyZ : -y ∈ Z := mem_of_perp_perp hZ _ fun p hp => by
      have h0 : (perp D Z).mkQ p = 0 := (Submodule.Quotient.mk_eq_zero _).2 hp
      rw [map_neg, LinearMap.neg_apply, hy]
      have : (⟨s ((perp D Z).mkQ p), hmC p⟩ : C) = 0 := Subtype.ext (by show s ((perp D Z).mkQ p) = 0; rw [h0, map_zero])
      rw [this, map_zero, neg_zero]
    have key : ∀ c : C, D.EF c (-y) = φ c := fun c => by
      rw [ef_swap, map_neg, LinearMap.neg_apply, neg_neg, hy]
      congr 1; exact Subtype.ext (hsC c c.2)
    refine ⟨⟨-y, hyZ⟩, key, fun z hz => Subtype.ext ?_⟩
    have hw : ∀ x, D.EF ((z : D.La) - -y) x = 0 := fun x => by
      have h1 := hz ⟨_, hmC x⟩
      have h2 := key ⟨_, hmC x⟩
      rw [hZx _ (sub_mem z.2 hyZ), ef_swap, map_sub]
      rw [h1, h2, sub_self, neg_zero]
    exact sub_eq_zero.1 (D.unimod.1 (LinearMap.ext fun x => by rw [hw, map_zero, LinearMap.zero_apply]))
  let β : LinearMap.BilinForm ℤ C := LinearMap.mk₂ ℤ (fun a b : C => -D.EF a b)
    (fun a a' b => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; abel) (fun n a b => by simp) (fun a b b' => by simp only [Submodule.coe_add, map_add]; abel) (fun n a b => by simp)
  obtain ⟨t, ht⟩ := exists_skew_solve A2 β (fun a b => by
      show -D.EF a b = -(-D.EF b a)
      rw [ef_swap D a b]) (fun c a b => by
      show -D.EF ((c • a : C) : D.La) b = -D.EF a ((H.bar c • b : C) : D.La)
      rw [Submodule.coe_smul, Submodule.coe_smul, D.adj])
  have ht' : ∀ a b : C, D.EF a (t b) + D.EF (t a) b = -D.EF a b := ht
  let g : C →ₗ[𝓞 E] D.La := C.subtype + Z.subtype ∘ₗ t
  have hg : ∀ c, g c = c + t c := fun c => rfl
  have kZ : ∀ (a : Z) (c : C), D.EF a (g c) = D.EF a c := fun a c => by
    rw [hg, map_add, hZ.1 a.2 _ (t c).2, add_zero]
  refine ⟨LinearMap.range g, hZ.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    show D.EF (g b) (g b') = 0
    have h0 : D.EF (t b) (t b') = 0 := hZ.1 (t b).2 _ (t b').2
    rw [hg, hg]
    simp only [map_add, LinearMap.add_apply]
    linear_combination ht' b b' + h0
  · obtain ⟨b, hb, hu⟩ := A1 φ
    refine ⟨⟨g b, b, rfl⟩, fun a => (kZ a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg g (hu b' fun a => (kZ a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := A2 (-(φ.comp g.rangeRestrict.toAddMonoidHom))
    refine ⟨a, ?_, fun a' ha' => hu a' fun c => ?_⟩
    · rintro ⟨_, c, rfl⟩
      show D.EF a (g c) = φ ⟨g c, c, rfl⟩
      rw [kZ, ef_swap, ha c, AddMonoidHom.neg_apply, neg_neg]
      rfl
    · have h1 := ha' ⟨g c, c, rfl⟩
      rw [ef_swap, ← kZ a' c]
      show -D.EF a' (g c) = -φ ⟨g c, c, rfl⟩
      rw [← h1]

end GlobalTheory.LowFilt.Opp
