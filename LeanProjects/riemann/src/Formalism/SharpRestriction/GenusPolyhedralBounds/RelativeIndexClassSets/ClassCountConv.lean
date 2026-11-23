import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.HermitianLattices.StatementLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountSurj
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountWaLat

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.MainNotions.Gaps.CC.Surj

open Formalism.UG Formalism.UG.CS Formalism.UG.P

section Conv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
local notation "Sv[" v "]" => tensInt (F := F) (adicCompletion F v) (intOE E)
  (ValuationSubring.toSubring (adicCompletionIntegers F v))
local notation "ιv[" v "]" => inclE (F := F) (E := E) (adicCompletion F v)

theorem conv_eps_tmul (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    afsplitEps E v * ιA e = e ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F) := by
  rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  show ((1 : E) ⊗ₜ[F] afsplitI v (1 : v.adicCompletion F)) * (e ⊗ₜ[F] (1 : 𝔸)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem conv_tmul_smul (a : F) (e : E) (c : 𝔸) :
    e ⊗ₜ[F] (a • c) = ((1 : E) ⊗ₜ[F] c) * ιA (algebraMap F E a * e) := by
  show _ = ((1 : E) ⊗ₜ[F] c) * ((algebraMap F E a * e) ⊗ₜ[F] (1 : 𝔸))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def]

theorem conv_one_tmul_mem {c : 𝔸} (hc : c ∈ intAd F) : (1 : E) ⊗ₜ[F] c ∈ 𝒮 :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem conv_tmul_mem (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) (a : F) {c : 𝔸}
    (hc : c ∈ intAd F) (hy : (algebraMap F E a) • y ∈ Λ) :
    (fun i => y i ⊗ₜ[F] (a • c)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  have : (fun i => y i ⊗ₜ[F] (a • c)) =
      (⟨_, conv_one_tmul_mem (E := E) hc⟩ : 𝒮) • (fun i => ιA (((algebraMap F E a) • y) i)) := by
    funext i
    rw [conv_tmul_smul]
    rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

theorem conv_eps_mem (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E)
    (d : 𝓞 F) (hd : d ∉ v.asIdeal) (hy : (algebraMap F E (d : F)) • y ∈ Λ) :
    (fun i => afsplitEps E v * ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (d : F)) = 1 := by
    rw [levelaf_valued_algebraMap]
    exact (valuation_eq_one_iff_notMem (K := F) (v := v)).2 hd
  have hdv0 : algebraMap F (v.adicCompletion F) (d : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hc : (algebraMap F (v.adicCompletion F) (d : F))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have h1 : afsplitI v (1 : v.adicCompletion F) =
      (d : F) • afsplitI v (algebraMap F (v.adicCompletion F) (d : F))⁻¹ := by
    rw [← map_smul, Algebra.smul_def, mul_inv_cancel₀ hdv0]
  have := conv_tmul_mem Λ y (d : F) (afsplitI_mem_intAd v _ hc) hy
  rw [← h1] at this
  simpa only [conv_eps_tmul] using this

theorem conv_exists_den (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (y : n → E) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (algebraMap F E (D : F)) • y ∈ Λ := by
  classical
  obtain ⟨m, hm0, hm⟩ := csGlob_single Λ hspan
  obtain ⟨m', hm'0, hm'⟩ := adelstabL_den y
  refine ⟨((m' * m : ℤ) : 𝓞 F), Int.cast_ne_zero.2 (mul_ne_zero hm'0 hm0), ?_⟩
  have : (algebraMap F E (((m' * m : ℤ) : 𝓞 F) : F)) • y =
      ∑ k, (⟨(m' : E) * y k, hm' k⟩ : 𝓞 E) • (Pi.single k (m : E) : n → E) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
      show _ = (m' : E) * y j * (m : E)
      simp only [Int.cast_mul, map_mul, map_intCast]
      ring
    · intro k _ hkj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hkj), smul_zero]
    · exact fun h => absurd (Finset.mem_univ j) h
  rw [this]
  exact sum_mem fun k _ => Λ.smul_mem _ (hm k)

theorem conv_incl_mem_iff (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (x : n → E) :
    (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 Λ ↔ x ∈ Λ := by
  conv_rhs => rw [← global_lattice_one_holds F E n Λ hfin hspan]
  show _ ↔ ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 Λ
  rw [inv_one, Units.val_one, one_mulVec]

theorem conv_eps_mem_conv (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (y : n → E)
    (h : (fun i => afsplitEps E v * ιA (y i)) ∈ latS (F := F) 𝔸 𝒮 Λ) :
    ∃ d : 𝓞 F, d ∉ v.asIdeal ∧ (algebraMap F E (d : F)) • y ∈ Λ := by
  obtain ⟨D0, hD0, hD0y⟩ := conv_exists_den (F := F) Λ hspan y
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hD : π * D0 ≠ 0 := mul_ne_zero hπ0 hD0
  have hDv : π * D0 ∈ v.asIdeal := Ideal.mul_mem_right _ _ hπv
  have hDy : (algebraMap F E ((π * D0 : 𝓞 F) : F)) • y ∈ Λ := by
    have : (algebraMap F E ((π * D0 : 𝓞 F) : F)) • y =
        (algebraMap (𝓞 F) (𝓞 E) π) • ((algebraMap F E (D0 : F)) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
      rw [mul_assoc]
      rfl
    rw [this]
    exact Λ.smul_mem _ hD0y
  have ha : (1 - afsplitI v (1 : v.adicCompletion F) : 𝔸) ∈ intAd F :=
    sub_mem (one_mem _) (afsplitI_mem_intAd v 1 (one_mem _))
  obtain ⟨r, z, hz, hr⟩ := csGlob_intAdApprox F (π * D0) hD _ ha
  have hrv : r ∈ v.asIdeal := by
    have hv := congrArg (fun a : 𝔸 => a v) hr
    simp only [afsplit_sub_apply, afsplit_one_apply, afsplitI_self, sub_self, afsplit_add_apply,
      afsplit_mul_apply] at hv
    have e1 : (algebraMap (𝓞 F) 𝔸 r) v = algebraMap F (v.adicCompletion F) (r : F) := rfl
    have e2 : (algebraMap (𝓞 F) 𝔸 (π * D0)) v =
        algebraMap F (v.adicCompletion F) ((π * D0 : 𝓞 F) : F) := rfl
    rw [e1, e2] at hv
    have e3 : algebraMap F (v.adicCompletion F) (r : F) =
        -(algebraMap F (v.adicCompletion F) ((π * D0 : 𝓞 F) : F) * z v) := by
      linear_combination -hv
    rw [← valuation_lt_one_iff_mem (K := F), ← levelaf_valued_algebraMap, e3, Valuation.map_neg,
      map_mul, levelaf_valued_algebraMap]
    have h1 : v.valuation F ((π * D0 : 𝓞 F) : F) < 1 := (valuation_lt_one_iff_mem (K := F) v _).2 hDv
    have h2 : Valued.v (z v) ≤ 1 := hz v
    calc _ ≤ v.valuation F ((π * D0 : 𝓞 F) : F) * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  refine ⟨1 - r, fun hmem => ?_, ?_⟩
  · have : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.add_mem hmem hrv
      rwa [sub_add_cancel] at this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · rw [← conv_incl_mem_iff (F := F) Λ hfin hspan]
    have hz' := conv_tmul_mem Λ y ((π * D0 : 𝓞 F) : F) hz hDy
    have hsum := add_mem h hz'
    convert hsum using 1
    funext i
    rw [Pi.add_apply, conv_eps_tmul, ← TensorProduct.tmul_add]
    have e4 : afsplitI v (1 : v.adicCompletion F) + ((π * D0 : 𝓞 F) : F) • z =
        algebraMap (𝓞 F) 𝔸 (1 - r) := by
      rw [map_sub, map_one (algebraMap (𝓞 F) 𝔸), Algebra.smul_def, ← IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸]
      linear_combination -hr
    rw [e4, csGlob_tmul_int]
    rfl

theorem conv_prV_latS (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜)
    (hu : u ∈ latS (F := F) 𝔸 𝒮 Λ) :
    (fun i => prV (E := E) v (u i)) ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact Submodule.subset_span ⟨x, hx, by funext i; exact (afsplit_prV_inclE v (x i)).symm⟩
  | zero =>
    have := zero_mem (latS (F := F) (v.adicCompletion F) Sv[v] Λ)
    convert this using 1
    funext i
    simp
  | add u w _ _ hu hw =>
    have := add_mem hu hw
    convert this using 1
    funext i
    simp
  | smul a u _ hu =>
    have := Submodule.smul_mem _ (⟨_, afsplit_prV_int v (a : 𝒜) a.2⟩ : Sv[v]) hu
    convert this using 1
    funext i
    show prV (E := E) v ((a : 𝒜) * u i) = _
    rw [map_mul]
    rfl

theorem conv_IE_latS (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F)
    (hu : u ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ) :
    (fun i => afsplitIE v (u i)) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have := Submodule.smul_mem (latS (F := F) 𝔸 𝒮 Λ) (⟨_, afsplit_eps_int (E := E) v⟩ : 𝒮)
      (Submodule.subset_span ⟨x, hx, rfl⟩)
    convert this using 1
    funext i
    show afsplitIE v (ιv[v] (x i)) = afsplitEps E v * ιA (x i)
    rw [← afsplit_decomp, afsplit_prV_inclE]
  | zero =>
    have := zero_mem (latS (F := F) 𝔸 𝒮 Λ)
    convert this using 1
    funext i
    simp
  | add u w _ _ hu hw =>
    have := add_mem hu hw
    convert this using 1
    funext i
    simp
  | smul a u _ hu =>
    have := Submodule.smul_mem _ (⟨_, afsplit_IE_int v (a : E ⊗[F] v.adicCompletion F) a.2⟩ : 𝒮) hu
    convert this using 1
    funext i
    show afsplitIE v ((a : E ⊗[F] v.adicCompletion F) * u i) = _
    rw [map_mul]
    rfl

theorem conv_IE_latS_iff (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) :
    (fun i => afsplitIE v (u i)) ∈ latS (F := F) 𝔸 𝒮 Λ ↔
      u ∈ latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  refine ⟨fun h => ?_, conv_IE_latS v Λ u⟩
  have := conv_prV_latS v Λ _ h
  simpa only [afsplit_prV_IE] using this

theorem conv_bc_mulVec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (γ : GL n A)
    (x : n → A) :
    ((bc φ γ : GL n B) : Matrix n n B) *ᵥ (fun i => φ (x i)) =
      fun i => φ (((γ : Matrix n n A) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem conv_locIff [StarRing E] (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜)
    (p : Ideal (𝓞 E)) [p.IsPrime] (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E))) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p (globLat g Λ) ↔
      (((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i)) ∈
        latS (F := F) (v.adicCompletion F) Sv[v] Λ := by
  have hlat := global_lattice_isLattice_holds F E n Λ hfin hspan g
  have hfinM : Module.Finite (𝓞 E) (globLat g Λ) := Module.Finite.iff_fg.2 hlat.fg
  have hspanM := hlat.span_eq_top
  rw [mem_loc_iff σ hσ hfix p v.asIdeal hv]
  have step1 : (∃ d : 𝓞 F, d ∉ v.asIdeal ∧ (algebraMap F E (d : F)) • x ∈ globLat g Λ) ↔
      (fun i => afsplitEps E v * ιA (x i)) ∈ latS (F := F) 𝔸 𝒮 (globLat g Λ) :=
    ⟨fun ⟨d, hd, hx⟩ => conv_eps_mem v _ x d hd hx, conv_eps_mem_conv v _ hfinM hspanM x⟩
  rw [step1, ← conv_IE_latS_iff]
  refine Iff.trans (span_recovery_of_integral_adelic_approx csGlob_intAdApprox F E n Λ hfin hspan g
    (fun i => afsplitEps E v * ιA (x i))) ?_
  have h1 : (((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i)) =
      fun i => prV (E := E) v ((((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ fun i => ιA (x i)) i) := by
    rw [← map_inv, ← conv_bc_mulVec]
    rfl
  have h2 : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => afsplitEps E v * ιA (x i)) =
      fun i => afsplitIE v (((((bc (prV (E := E) v) g)⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => ιv[v] (x i))) i) := by
    rw [h1]
    funext i
    rw [afsplit_decomp]
    have : (fun i => afsplitEps E v * ιA (x i)) = afsplitEps E v • (fun i => ιA (x i)) := rfl
    rw [this, mulVec_smul]
    rfl
  rw [h2]

end Conv

section Genus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem conv_mem_gmap {R : Type} [CommRing R] [Algebra R E] (γ : GL n E)
    (L : Submodule R (n → E)) (x : n → E) :
    x ∈ Formalism.HermitianLatticesTheory.gmap (glEquiv γ) L ↔ ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ (glEquiv γ y) ∈ L
    rw [glEquiv_apply', mulVec_mulVec, Units.inv_mul, one_mulVec]
    exact hy
  · intro hy
    refine ⟨_, hy, ?_⟩
    show glEquiv γ _ = x
    rw [glEquiv_apply', mulVec_mulVec, Units.mul_inv, one_mulVec]

theorem conv_genus (hWA : WeakApprox1) [StarRing E] (σ : E →ₐ[F] E)
    (hσ : (σ : E →+* E) = starRingEnd E)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ)
    (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E) (J : Matrix n n E) (hJ : J = gram h)
    (hherm : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ := by
  refine ⟨global_lattice_isLattice_holds F E n Λ hfin hspan g, fun p hp => ?_⟩
  have := hp.isPrime
  have hpne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  obtain ⟨a, hap, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hne : p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 hap (Algebra.IsIntegral.isIntegral a)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p.comap (algebraMap (𝓞 F) (𝓞 E)), Ideal.comap_isPrime _ _, hne⟩
  have hstar : ∀ e, σ e = star e := fun e => congrArg (fun f : E →+* E => f e) hσ
  have hinv : ∀ e, σ (σ e) = e := fun e => by rw [hstar, hstar, star_star]
  obtain ⟨γ, hγ, hk⟩ := hWA F E n σ J hinv hθ hherm hdet Λ hfin hspan v _
    (afsplit_bc_mem σ J v g hg)
  refine ⟨glEquiv γ, ?_, ?_⟩
  · rw [← hermitian_lattice_correspondence_holds E n h γ, ← hJ, ← hσ]
    exact hγ
  · ext x
    rw [conv_locIff σ hσ hfix Λ hfin hspan g p v rfl x, conv_mem_gmap]
    have h1 := conv_locIff σ hσ hfix Λ hfin hspan 1 p v rfl (((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x)
    rw [global_lattice_one_holds F E n Λ hfin hspan, map_one, inv_one, Units.val_one, one_mulVec] at h1
    rw [h1, (inv_mem hk) _, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← mulVec_mulVec,
      conv_bc_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]

end Genus

section StdIn

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {k : ℕ}

theorem genusIn_of_core (hc : WACore) (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ) :
    GenusIn σ (1 : Matrix (Fin k) (Fin k) E) := fun g hg =>
  conv_genus (wal_main hc) σ (sig_eq_star σ hσ) hfix hθ (Formalism.MainNotions.StandardLattice.stdForm E k) 1 gram_stdForm.symm
    (cT_one _) (by simp) (Formalism.MainNotions.StandardLattice.stdLat E k) stdLat_finite stdLat_span g hg

end StdIn

end Formalism.MainNotions.Gaps.CC.Surj
