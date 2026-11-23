import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EpsMemLatSIff

noncomputable section

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.UG.CS
open scoped TensorProduct Matrix

namespace GlobalTheory.Mass.Genus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
local notation "𝓛" => latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮

omit [NumberField F] [Algebra F E] in

theorem exists_den (Λ N : Submodule (𝓞 E) (Fin n → E)) (hΛ : Λ.FG)
    (hN : Submodule.span E (N : Set (Fin n → E)) = ⊤) : ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, m • x ∈ N := by
  obtain ⟨m', hm', hs⟩ := csGlob_single N hN
  obtain ⟨s, rfl⟩ := hΛ
  obtain ⟨m, hm, hi⟩ := adelstabL_den (fun p : s × Fin n => (p.1 : Fin n → E) p.2)
  refine ⟨m * m', mul_ne_zero hm hm', fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have : (m * m') • x = ∑ k, (⟨(m : E) * x k, hi (⟨x, hx⟩, k)⟩ : 𝓞 E) • (Pi.single k (m' : E) : Fin n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, Algebra.smul_def]
        change _ = (m : E) * x j * m'
        simp only [map_mul, eq_intCast]
        ring
      · intro k _ hkj
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hkj), smul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [this]
    exact sum_mem fun k _ => N.smul_mem _ (hs k)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem a hx

omit [NumberField F] [Algebra F E] [NumberField E] in
theorem mem_gmap (γ : GL (Fin n) E) (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) :
    x ∈ Formalism.HermitianLatticesTheory.gmap (glEquiv γ) N ↔ (γ⁻¹).1 *ᵥ x ∈ N := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rwa [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem exists_place (p : Ideal (𝓞 E)) (hp : p.IsMaximal) :
    ∃ v : HeightOneSpectrum (𝓞 F), p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  have h : (p.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p
  exact ⟨⟨_, h.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h (RingOfIntegers.not_isField F)⟩, rfl⟩

theorem exists_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : Ideal (𝓞 E), p.IsMaximal ∧ p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  haveI := v.isMaximal
  refine Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  exact bot_le

theorem eps_glob {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : GL (Fin n) 𝒜) (e : 𝒜) (u : Fin n → 𝒜) :
    e • u ∈ 𝓛 (globLat g Λ) ↔ e • ((g⁻¹).1 *ᵥ u) ∈ 𝓛 Λ := by
  rw [← Matrix.mulVec_smul]
  exact span_recovery_of_integral_adelic_approx integral_adele_approximation_holds F E (Fin n) Λ hΛ hsp g _

theorem exists_glue (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (δ : HeightOneSpectrum (𝓞 F) → GL (Fin n) 𝒜) (hδ : ∀ v, δ v ∈ UPts σ J 𝔸)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ g ∈ UPts σ J 𝔸, (∀ v ∈ S, bc (prV (E := E) v) g = bc (prV (E := E) v) (δ v)) ∧
      ∀ v ∉ S, bc (prV (E := E) v) g = bc (prV (E := E) v) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun _ _ => rfl⟩
  | insert w S _ ih =>
    obtain ⟨g, hg, h1, h2⟩ := ih
    have hne : ∀ v, v ≠ w → bc (prV (E := E) v) (afsplitU w (bc (prV (E := E) w) (δ w)) g) =
        bc (prV (E := E) v) g := fun v hv => by
      apply Units.ext
      rw [afsplit_coe_bc_prV, afsplit_coe_bc_prV, afsplitU_coe, afsplitC_prV_ne w v hv]
    refine ⟨afsplitU w (bc (prV (E := E) w) (δ w)) g,
      afsplitU_mem w σ J _ _ (afsplit_bc_mem σ J w _ (hδ w)) hg, fun v hv => ?_, fun v hv => ?_⟩
    · by_cases h : v = w
      · subst h; exact afsplit_right1 v _ _
      · rw [hne v h, h1 v ((Finset.mem_insert.1 hv).resolve_left h)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [hne v hv.1, h2 v hv.2]

theorem eps_congr (v : HeightOneSpectrum (𝓞 F)) {g h : GL (Fin n) 𝒜}
    (e : bc (prV (E := E) v) g = bc (prV (E := E) v) h) (u : Fin n → 𝒜) :
    afsplitEps E v • ((g⁻¹).1 *ᵥ u) = afsplitEps E v • ((h⁻¹).1 *ᵥ u) := by
  have e' : bc (prV (E := E) v) g⁻¹ = bc (prV (E := E) v) h⁻¹ := by rw [map_inv, map_inv, e]
  rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
  congr 1
  ext i j
  have e'' := Units.ext_iff.1 e'
  have := congrArg (afsplitIE v) (congrFun (congrFun e'' i) j)
  rw [afsplit_coe_bc_prV, afsplit_coe_bc_prV, Matrix.map_apply, Matrix.map_apply, afsplit_decomp,
    afsplit_decomp] at this
  exact this

omit [NumberField F] [NumberField E] in

theorem fixed_mem (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hne : ∃ z, σ z ≠ z) (e : E) (he : σ e = e) :
    ∃ a : F, algebraMap F E a = e := by
  obtain ⟨z, hz⟩ := hne
  let A : Subalgebra F E := AlgHom.equalizer σ (AlgHom.id F E)
  rcases Subalgebra.isSimpleOrder_of_finrank hr |>.eq_bot_or_eq_top A with h | h
  · have : e ∈ A := he
    rw [h] at this
    exact Algebra.mem_bot.1 this
  · have : z ∈ A := h ▸ Algebra.mem_top
    exact absurd this hz

variable {σ : E →ₐ[F] E} (hs : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e) {J : Matrix (Fin n) (Fin n) E}
  {Λ : Submodule (𝓞 E) (Fin n → E)}

theorem globLat_mem_genus (hfix : ∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) (hne : ∃ z, σ z ≠ z)
    (hJ : IsHerm (σ : E →+* E) J) (hdet : J.det ≠ 0) (hΛ : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : GL (Fin n) 𝒜) (hg : g ∈ UPts σ J 𝔸) :
    letI := starOfInv (σ : E →+* E) hs
    globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus (formJ (σ : E →+* E) hs J 1) Λ := by
  letI := starOfInv (σ : E →+* E) hs
  have hL := global_lattice_isLattice_holds F E (Fin n) Λ hΛ hsp g
  refine ⟨hL, fun p hp => ?_⟩
  obtain ⟨v, hv⟩ := exists_place (F := F) p hp
  obtain ⟨D, hD, hc⟩ := GlobalTheory.GenusCong.eps_mem_latS_iff F E n Λ hΛ hsp v
  obtain ⟨γ, hγ, X, hX, e⟩ := GlobalTheory.Mass.OnePlace.weak_approx_at F E σ hs hne n J hJ hdet v D hD g hg
  refine ⟨glEquiv γ⁻¹, (unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).1 (inv_mem hγ), ?_⟩
  ext x
  rw [mem_gmap, inv_inv, GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n Λ hΛ hsp v p hp.isPrime hv,
    GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n _ (Module.Finite.iff_fg.2 hL.fg) hL.span_eq_top v p hp.isPrime hv,
    eps_glob hΛ hsp, hc _ X hX e ((g⁻¹).1 *ᵥ _), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right,
    csEquiv_bc_mulVec]

theorem exists_globLat_eq (hfix : ∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e)
    (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (N : Submodule (𝓞 E) (Fin n → E))
    (hN : letI := starOfInv (σ : E →+* E) hs; N ∈ Formalism.HermitianLatticesTheory.genus (formJ (σ : E →+* E) hs J 1) Λ) :
    ∃ g ∈ UPts σ J 𝔸, globLat g Λ = N := by
  letI := starOfInv (σ : E →+* E) hs
  obtain ⟨hL, hG⟩ := hN
  have hNf : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hL.fg
  have h1 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ UJ (σ : E →+* E) J, ∀ x : Fin n → E,
      afsplitEps E v • (((bc ιA γ)⁻¹).1 *ᵥ fun i => ιA (x i)) ∈ 𝓛 Λ ↔
        (afsplitEps E v • fun i => ιA (x i)) ∈ 𝓛 N := by
    intro v
    obtain ⟨p, hp, hv⟩ := exists_over (E := E) v
    obtain ⟨u, hu, e⟩ := hG p hp
    obtain ⟨γ, rfl⟩ := Formalism.UG.Final.HermBridgeSurj E (Fin n) _ u hu
    refine ⟨γ, (unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).2 hu, fun x => ?_⟩
    rw [← map_inv, csEquiv_bc_mulVec, ← GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n Λ hΛ hsp v p hp.isPrime hv,
      ← GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n N hNf hL.span_eq_top v p hp.isPrime hv, ← e, mem_gmap]
  choose γ hγ hγ' using h1
  obtain ⟨a, ha, haN⟩ := exists_den Λ N (Module.Finite.iff_fg.1 hΛ) hL.span_eq_top
  obtain ⟨b, hb, hbΛ⟩ := exists_den N Λ hL.fg hsp
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((a * b : ℤ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {((a * b : ℤ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Int.cast_ne_zero.2 (mul_ne_zero ha hb)
    exact (Ideal.finite_factors hne).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  obtain ⟨g, hg, g1, g2⟩ := exists_glue σ J (fun v => bc ιA (γ v))
    (fun v => rational_points_le_holds F E (Fin n) σ J 𝔸 ⟨γ v, hγ v, rfl⟩) hfin.toFinset
  have hL' := global_lattice_isLattice_holds F E (Fin n) Λ hΛ hsp g
  have key : ∀ p : Ideal (𝓞 E), p.IsMaximal →
      Formalism.HermitianLatticesTheory.loc (K := E) p (globLat g Λ) = Formalism.HermitianLatticesTheory.loc (K := E) p N := by
    intro p hp
    obtain ⟨v, hv⟩ := exists_place (F := F) p hp
    ext x
    rw [GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n _ (Module.Finite.iff_fg.2 hL'.fg) hL'.span_eq_top v p hp.isPrime hv,
      eps_glob hΛ hsp]
    by_cases h : v ∈ hfin.toFinset
    · rw [eps_congr v (g1 v h), hγ', GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n N hNf hL.span_eq_top v p hp.isPrime hv]
    · rw [eps_congr v (g2 v h), inv_one, Units.val_one, Matrix.one_mulVec,
        ← GlobalTheory.LocDict.mem_loc_iff F E σ hs hfix n Λ hΛ hsp v p hp.isPrime hv]
      have hm : ((a * b : ℤ) : 𝓞 E) ∉ p := fun h' => h (hfin.mem_toFinset.2 (by
        change _ ∈ v.asIdeal
        rw [← hv, Ideal.mem_comap, map_intCast]; exact h'))
      have hc : ((a * b : ℤ) : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p := by
        refine Submonoid.subset_closure ⟨hm, fun t ht => ?_⟩
        have : t = ((a * b : ℤ) : 𝓞 E) := RingOfIntegers.coe_injective (by
          rw [ht, map_intCast]; exact map_intCast (σ : E →+* E) _)
        rwa [this]
      constructor
      · rintro ⟨s, hs', hx⟩
        refine ⟨_, mul_mem hc hs', ?_⟩
        rw [mul_smul, Int.cast_smul_eq_zsmul, mul_comm, mul_smul]
        exact zsmul_mem (haN _ hx) _
      · rintro ⟨s, hs', hx⟩
        refine ⟨_, mul_mem hc hs', ?_⟩
        rw [mul_smul, Int.cast_smul_eq_zsmul, mul_smul]
        exact zsmul_mem (hbΛ _ hx) _
  have lg := (Formalism.HermitianLatticesTheory.locBasic (𝓞 E) E (Fin n → E) RingOfIntegers.coe_injective).2.2.1
  exact ⟨g, hg, le_antisymm (lg _ _ fun p hp => (key p hp).le) (lg _ _ fun p hp => (key p hp).ge)⟩

local notation "Γ" => Subgroup.subgroupOf (ratPts σ J 𝔸) (UPts σ J 𝔸)
local notation "𝒦" => Subgroup.subgroupOf (levelAfL σ J Λ) (UPts σ J 𝔸)

theorem mk_eq_iff (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (g g' : UPts σ J 𝔸) :
    letI := starOfInv (σ : E →+* E) hs
    DoubleCoset.mk Γ 𝒦 g = DoubleCoset.mk Γ 𝒦 g' ↔
      ∃ u ∈ Formalism.HermitianLatticesTheory.isom (formJ (σ : E →+* E) hs J 1),
        Formalism.HermitianLatticesTheory.gmap u (globLat (g : GL (Fin n) 𝒜) Λ) = globLat (g' : GL (Fin n) 𝒜) Λ := by
  letI := starOfInv (σ : E →+* E) hs
  constructor
  · intro h
    obtain ⟨c, ⟨γ, hγ, e⟩, k, hk, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
    refine ⟨glEquiv γ, (unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).1 hγ, ?_⟩
    rw [← global_lattice_equiv_holds F E (Fin n) Λ γ g k hk.2, e]
    rfl
  · rintro ⟨u, hu, e⟩
    obtain ⟨γ, rfl⟩ := Formalism.UG.Final.HermBridgeSurj E (Fin n) _ u hu
    exact (class_injective_of_span_recovery (span_recovery_of_integral_adelic_approx integral_adele_approximation_holds) global_lattice_equiv_holds F E (Fin n) σ J Λ hΛ hsp g' g γ
      ((unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).2 hu) e.symm).symm

theorem conj_mem_stab_iff (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (g : GL (Fin n) 𝒜) (γ : GL (Fin n) E) :
    g⁻¹ * bc ιA γ * g ∈ stabGL (𝓛 Λ) ↔ Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) = globLat g Λ := by
  constructor
  · intro h
    rw [← global_lattice_equiv_holds F E (Fin n) Λ γ g _ (inv_mem h)]
    congr 1
    group
  · intro h
    rw [← global_lattice_equiv_holds F E (Fin n) Λ γ g 1 (one_mem _), mul_one] at h
    refine (inv_mem_iff (H := stabGL (𝓛 Λ))).1 fun u => ?_
    have h1 := eps_glob hΛ hsp g 1 (g.1 *ᵥ u)
    have h2 := eps_glob hΛ hsp (bc ιA γ * g) 1 (g.1 *ᵥ u)
    rw [h, h1, one_smul, one_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
    rw [h2]
    simp only [mul_inv_rev, inv_inv, mul_assoc]

omit [NumberField E] in
theorem bc_injective : Function.Injective (bc (n := Fin n) ιA) := by
  haveI : Nontrivial 𝒜 := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    haveI : Nontrivial 𝔸 := (evalV F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩).toRingHom.domain_nontrivial
    exact (Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := 𝔸)
      (algebraMap F E).injective).nontrivial
  intro x y e
  exact Units.ext (Matrix.map_injective (ιA).injective (congrArg Units.val e : x.1.map ιA = y.1.map ιA))

theorem card_stabAt_of_injective {A B : Type} [Group A] [Group B] (φ : A →* B) (hφ : Function.Injective φ)
    (U : Subgroup A) (V K : Subgroup B) (hU : ∀ a ∈ U, φ a ∈ V) (g : V) :
    Nat.card (stabAt ((U.map φ).subgroupOf V) ((V ⊓ K).subgroupOf V) g) =
      Nat.card {a : A // a ∈ U ∧ (g : B)⁻¹ * φ a * g ∈ K} := by
  refine (Nat.card_eq_of_bijective (fun a : {a : A // a ∈ U ∧ (g : B)⁻¹ * φ a * g ∈ K} =>
    (⟨⟨⟨_, hU a.1 a.2.1⟩, a.1, a.2.1, rfl⟩,
      Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem g.2) (hU a.1 a.2.1)) g.2, a.2.2⟩⟩ :
      stabAt ((U.map φ).subgroupOf V) ((V ⊓ K).subgroupOf V) g)) ⟨fun x y e => ?_, ?_⟩).symm
  · exact Subtype.ext (hφ (congrArg (fun z => z.1.1.1) e))
  · rintro ⟨⟨⟨c, hc⟩, γ, hγ, e⟩, h⟩
    obtain rfl : φ γ = c := e
    exact ⟨⟨γ, hγ, h.2⟩, rfl⟩

theorem card_stabAt (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (g : UPts σ J 𝔸) :
    letI := starOfInv (σ : E →+* E) hs
    Nat.card (stabAt Γ 𝒦 g) =
      Nat.card (Formalism.ThetaLiftIndependence.autL (formJ (σ : E →+* E) hs J 1) (globLat (g : GL (Fin n) 𝒜) Λ)) := by
  letI := starOfInv (σ : E →+* E) hs
  refine (card_stabAt_of_injective (bc ιA) bc_injective (UJ (σ : E →+* E) J) (UPts σ J 𝔸) (stabGL (𝓛 Λ))
    (fun γ hγ => rational_points_le_holds F E (Fin n) σ J 𝔸 ⟨γ, hγ, rfl⟩) g).trans ?_
  refine Nat.card_eq_of_bijective (fun γ => ⟨glEquiv γ.1,
    (unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).1 γ.2.1,
    (conj_mem_stab_iff hΛ hsp _ _).1 γ.2.2⟩) ⟨fun x y e => ?_, ?_⟩
  · have e1 : glEquiv x.1 = glEquiv y.1 := congrArg Subtype.val e
    exact Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective e1))
  · rintro ⟨u, hu, h⟩
    obtain ⟨γ, rfl⟩ := Formalism.UG.Final.HermBridgeSurj E (Fin n) _ u hu
    exact ⟨⟨γ, (unitary_isometry_lattice_holds E _ hs (Fin n) J 1 one_ne_zero (map_one _) _).2 hu,
      (conj_mem_stab_iff hΛ hsp _ _).2 h⟩, rfl⟩

end GlobalTheory.Mass.Genus

open GlobalTheory.Mass.Genus Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem GlobalTheory.Mass.classMass_lattice_eq_genus_mass {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hd : IsTotDef σ J) (hs : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e) (Λ : Submodule (𝓞 E) (Fin M → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin M → E)) = ⊤) :
    letI := starOfInv (σ : E →+* E) hs
    GlobalTheory.Mass.classMass ((ratPts σ J (Af F)).subgroupOf (UPts σ J (Af F)))
                 ((levelAfL σ J Λ).subgroupOf (UPts σ J (Af F))) =
      Formalism.HermitianLatticesTheory.mass (formJ (σ : E →+* E) hs J 1) Λ := by
  classical
  letI := starOfInv (σ : E →+* E) hs
  have hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (σ : E →+* E) J := Matrix.ext fun i j => hJ.1 i j
  have hne : ∃ z, σ z ≠ z := by
    by_contra! h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := hσ.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hσ.2.2.2 τ x
    rw [h] at this
    exact this.symm
  have hfix := fixed_mem σ hσ.2.2.1 hne
  haveI := Formalism.UG.Final.ClassSetFiniteL F E _ σ J hτ hH hJ.2.isUnit hd Λ hΛ hsp
  have hgen := globLat_mem_genus hs hfix hne hH hJ.2 hΛ hsp
  have hsur := exists_globLat_eq (J := J) hs hfix hΛ hsp
  have hmk := mk_eq_iff (J := J) hs hΛ hsp
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps (formJ (σ : E →+* E) hs J 1) Λ s := by
    let f : ClassSet ((ratPts σ J (Af F)).subgroupOf (UPts σ J (Af F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (Af F))) → Submodule (𝓞 E) (Fin M → E) :=
      fun c => globLat (c.out : UPts σ J (Af F)).1 Λ
    refine ⟨(Set.finite_range f).toFinset, fun N hN => ?_, fun N hN => ?_⟩
    · obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hN
      exact hgen _ c.out.2
    · obtain ⟨g, hg, rfl⟩ := hsur N hN
      refine ⟨f (DoubleCoset.mk _ _ ⟨g, hg⟩), ⟨(Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩,
        (hmk _ ⟨g, hg⟩).1 (DoubleCoset.out_eq' _ _ _)⟩, ?_⟩
      rintro N ⟨hN', h⟩
      obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hN'
      rw [← (hmk c.out ⟨g, hg⟩).2 h, DoubleCoset.out_eq']
  rw [Formalism.HermitianLatticesTheory.mass, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set s := hex.choose
  choose g hg hgN using fun N : s => hsur N (h1 N N.2)
  rw [GlobalTheory.Mass.classMass_eq_sum_of_bijective (fun N : s => (⟨g N, hg N⟩ : UPts σ J (Af F))) ⟨fun N N' e => ?_,
    fun c => ?_⟩, ← Finset.sum_coe_sort s]
  · refine Finset.sum_congr rfl fun N _ => ?_
    rw [card_stabAt hs hΛ hsp, hgN]
  · have := (hmk _ _).1 e
    simp only [hgN] at this
    exact Subtype.ext ((h2 N' (h1 N' N'.2)).unique ⟨N.2, this⟩
      ⟨N'.2, 1, one_mem _, csAsm_gmap_one _⟩)
  · obtain ⟨N, ⟨hN, h⟩, -⟩ := h2 _ (hgen _ c.out.2)
    refine ⟨⟨N, hN⟩, ?_⟩
    rw [← DoubleCoset.out_eq' _ _ c]
    refine (hmk _ _).2 ?_
    simpa only [hgN] using h

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem GlobalTheory.Mass.unitaryMass_lattice_eq_genus_mass {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hd : IsTotDef σ J) (hs : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e) (Λ : Submodule (𝓞 E) (Fin M → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (hsp : Submodule.span E (Λ : Set (Fin M → E)) = ⊤) :
    letI := starOfInv (σ : E →+* E) hs
    GlobalTheory.Mass.unitaryMass σ J (((levelAfL σ J Λ).subgroupOf (UPts σ J (Af F))).comap
                 (GlobalTheory.Mass.swapPts (Af F) σ J : HA (Af F) σ J →* UPts σ J (Af F))) =
      Formalism.HermitianLatticesTheory.mass (formJ (σ : E →+* E) hs J 1) Λ :=
  (GlobalTheory.Mass.unitaryMass_comap_swapPts σ J _).trans (GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ hJ hd hs Λ hΛ hsp)
