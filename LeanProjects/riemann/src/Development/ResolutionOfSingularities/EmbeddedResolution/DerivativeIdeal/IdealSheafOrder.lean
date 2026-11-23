import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
namespace FunctorialResolution.EmbeddedResolution

open AlgebraicGeometry TopologicalSpace

universe u

variable {X : Scheme.{u}}

noncomputable def stalkIdeal (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)

private theorem map_germ_ideal_congr {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (W W' : X.affineOpens) (h : W = W') (hW : x ∈ W.1) (hW' : x ∈ W'.1) :
    Ideal.map (X.presheaf.germ W.1 x hW).hom (I.ideal W)
      = Ideal.map (X.presheaf.germ W'.1 x hW').hom (I.ideal W') := by
  subst h
  rfl

open CategoryTheory in
private theorem map_germ_ideal_affineBasicOpen {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (f : Γ(X, U.1)) (hxU : x ∈ U.1)
    (hxf : x ∈ (X.affineBasicOpen f).1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U)
      = Ideal.map (X.presheaf.germ (X.affineBasicOpen f).1 x hxf).hom
          (I.ideal (X.affineBasicOpen f)) := by
  have hxf' : x ∈ X.basicOpen f := hxf
  have hgerm : (X.presheaf.germ (X.basicOpen f) x hxf').hom.comp
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      = (X.presheaf.germ U.1 x hxU).hom := by
    rw [← CommRingCat.hom_comp, X.presheaf.germ_res]
  have h1 : Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom
      (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U))
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
    rw [Ideal.map_map, hgerm]
  rw [← h1]
  exact congrArg (fun J : Ideal Γ(X, X.basicOpen f) =>
    Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom J) (I.map_ideal_basicOpen U f)

private theorem map_germ_ideal_eq {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (V U : X.affineOpens) (hxV : x ∈ V.1) (hxU : x ∈ U.1) :
    Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V)
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter V.2 U.2 x ⟨hxV, hxU⟩
  have hxg : x ∈ X.basicOpen g := by rw [← hfg]; exact hxf
  have hW : X.affineBasicOpen f = X.affineBasicOpen g := Subtype.ext hfg
  rw [map_germ_ideal_affineBasicOpen I x V f hxV hxf,
    map_germ_ideal_affineBasicOpen I x U g hxU hxg]
  exact map_germ_ideal_congr I x (X.affineBasicOpen f) (X.affineBasicOpen g) hW hxf hxg

theorem stalkIdeal_eq_map_germ (I : X.IdealSheafData) (x : X) (U : X.affineOpens)
    (hx : x ∈ U.1) :
    stalkIdeal I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  have h : stalkIdeal I x = ⨆ V : {V : X.affineOpens // x ∈ V.1.1},
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1) := rfl
  rw [h]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨V, hxV⟩
    exact le_of_eq (map_germ_ideal_eq I x V U hxV hx)
  · exact le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩

theorem germ_mem_stalkIdeal (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    {s : Γ(X, U.1)} (hs : s ∈ I.ideal U) :
    (X.presheaf.germ U.1 x hx).hom s ∈ stalkIdeal I x := by
  have h : Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) ≤ stalkIdeal I x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩
  exact SetLike.le_def.mp h (Ideal.mem_map_of_mem _ hs)

theorem stalkIdeal_top (x : X) : stalkIdeal (⊤ : X.IdealSheafData) x = ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have h1 : (1 : Γ(X, U.1)) ∈ (⊤ : X.IdealSheafData).ideal U := by simp
  have h3 : Ideal.map (X.presheaf.germ U.1 x hxU).hom ((⊤ : X.IdealSheafData).ideal U) ≤
      stalkIdeal (⊤ : X.IdealSheafData) x :=
    le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom ((⊤ : X.IdealSheafData).ideal V.1)) ⟨U, hxU⟩
  have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U.1 x hxU).hom h1
  rw [map_one] at h2
  exact (Ideal.eq_top_iff_one _).mpr (SetLike.le_def.mp h3 h2)

theorem stalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  have h : ∀ U : X.affineOpens, (⊥ : X.IdealSheafData).ideal U = ⊥ := fun U => by simp
  simp only [stalkIdeal, h, Ideal.map_bot, iSup_bot]

theorem stalkIdeal_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    stalkIdeal I x ≤ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)) ≤
      ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1)
  exact iSup_mono fun U => Ideal.map_mono (h U.1)

private theorem map_germ_le_stalkIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : {U : X.affineOpens // x ∈ U.1.1}) :
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1) ≤ stalkIdeal I x :=
  le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
    Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) U

private theorem stalkIdeal_sup_le {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x ≤ stalkIdeal I x ⊔ stalkIdeal J x := by
  show (⨆ U : {U : X.affineOpens // x ∈ U.1.1},
      Ideal.map (X.presheaf.germ U.1.1 x U.2).hom ((I ⊔ J).ideal U.1)) ≤
      stalkIdeal I x ⊔ stalkIdeal J x
  refine iSup_le fun U => ?_
  have h1 : (I ⊔ J).ideal U.1 = I.ideal U.1 ⊔ J.ideal U.1 := rfl
  rw [h1, Ideal.map_sup]
  exact sup_le (le_sup_of_le_left (map_germ_le_stalkIdeal I x U))
    (le_sup_of_le_right (map_germ_le_stalkIdeal J x U))

theorem stalkIdeal_sup (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x :=
  le_antisymm (stalkIdeal_sup_le I J x)
    (sup_le (stalkIdeal_mono le_sup_left x) (stalkIdeal_mono le_sup_right x))

theorem stalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hmul : (I * J).ideal U = I.ideal U * J.ideal U :=
    congrFun (Scheme.IdealSheafData.ideal_mul ..) U
  rw [stalkIdeal_eq_map_germ (I * J) x U hxU, stalkIdeal_eq_map_germ I x U hxU,
    stalkIdeal_eq_map_germ J x U hxU, hmul, Ideal.map_mul]

private theorem idealSheafData_one_eq_top {X : Scheme.{u}} :
    (1 : X.IdealSheafData) = ⊤ := rfl

theorem stalkIdeal_pow (I : X.IdealSheafData) (n : ℕ) (x : X) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, idealSheafData_one_eq_top, stalkIdeal_top, Ideal.one_eq_top]
  | succ n ih =>
    rw [pow_succ, pow_succ, stalkIdeal_mul, ih]

private theorem germ_mem_maximalIdeal_iff_not_mem_basicOpen {X : Scheme.{u}} (x : X) (U : X.Opens) (hxU : x ∈ U)
    (f : Γ(X, U)) :
    (X.presheaf.germ U x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen f := by
  have h := AlgebraicGeometry.Scheme.mem_basicOpen X f x hxU
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn hx
    exact hn (h.mp hx)
  · intro hn hu
    exact hn (h.mpr hu)

private theorem mem_support_iff_forall_germ_mem_maximalIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hxU : x ∈ U.1) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal U,
      (X.presheaf.germ U.1 x hxU).hom f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hxU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff]
  constructor
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f).mpr (h f hf)
  · intro h f hf
    exact (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f).mp (h f hf)

theorem mem_support_iff_stalkIdeal_le_maximalIdeal (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem x
  have hxU : x ∈ U.1 := hxU0
  rw [stalkIdeal_eq_map_germ I x U hxU, Ideal.map_le_iff_le_comap,
    mem_support_iff_forall_germ_mem_maximalIdeal I x U hxU]
  constructor
  · intro h f hf
    exact h f hf
  · intro h f hf
    exact h hf

theorem mem_support_iff_stalkIdeal_ne_top (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≠ ⊤ := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
  refine ⟨fun h htop => ?_, fun h => IsLocalRing.le_maximalIdeal h⟩
  rw [htop, top_le_iff] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h

noncomputable def orderAt (I : X.IdealSheafData) (x : X) : ℕ∞ :=
  idealOrder (stalkIdeal I x)

theorem orderAt_eq_idealOrder (I : X.IdealSheafData) (x : X) :
    orderAt I x = idealOrder (stalkIdeal I x) := rfl

theorem le_orderAt_iff (I : X.IdealSheafData) (x : X) (n : ℕ) :
    (n : ℕ∞) ≤ orderAt I x ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n :=
  le_idealOrder_iff (stalkIdeal I x) n

theorem orderAt_top (x : X) : orderAt (⊤ : X.IdealSheafData) x = 0 := by
  rw [orderAt_eq_idealOrder, stalkIdeal_top, idealOrder_top]

theorem orderAt_bot (x : X) : orderAt (⊥ : X.IdealSheafData) x = ⊤ := by
  rw [orderAt_eq_idealOrder, stalkIdeal_bot, idealOrder_bot]

theorem orderAt_le_of_le {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    orderAt J x ≤ orderAt I x :=
  idealOrder_le_of_le (stalkIdeal_mono h x)

theorem orderAt_sup (I J : X.IdealSheafData) (x : X) :
    orderAt (I ⊔ J) x = min (orderAt I x) (orderAt J x) := by
  rw [orderAt_eq_idealOrder, stalkIdeal_sup, idealOrder_sup]
  rfl

theorem add_orderAt_le_orderAt_mul (I J : X.IdealSheafData) (x : X) :
    orderAt I x + orderAt J x ≤ orderAt (I * J) x := by
  rw [orderAt_eq_idealOrder (I * J), stalkIdeal_mul]
  exact add_idealOrder_le_idealOrder_mul (stalkIdeal I x) (stalkIdeal J x)

theorem mul_orderAt_le_orderAt_pow (I : X.IdealSheafData) (c : ℕ) (x : X) :
    (c : ℕ∞) * orderAt I x ≤ orderAt (I ^ c) x := by
  rw [orderAt_eq_idealOrder (I ^ c), stalkIdeal_pow]
  exact mul_idealOrder_le_idealOrder_pow (stalkIdeal I x) c

theorem one_le_orderAt_iff_mem_support (I : X.IdealSheafData) (x : X) :
    1 ≤ orderAt I x ↔ x ∈ I.support := by
  rw [orderAt_eq_idealOrder, one_le_idealOrder_iff, mem_support_iff_stalkIdeal_le_maximalIdeal]

theorem orderAt_eq_zero_iff_not_mem_support (I : X.IdealSheafData) (x : X) :
    orderAt I x = 0 ↔ x ∉ I.support := by
  rw [orderAt_eq_idealOrder, idealOrder_eq_zero_iff,
    mem_support_iff_stalkIdeal_le_maximalIdeal]

theorem orderAt_ne_top_of_stalkIdeal_ne_bot [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (x : X) (h : stalkIdeal I x ≠ ⊥) : orderAt I x ≠ ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_idealOrder]
  exact idealOrder_ne_top_of_ne_bot h

theorem orderAt_eq_top_iff [IsLocallyNoetherian X] (I : X.IdealSheafData) (x : X) :
    orderAt I x = ⊤ ↔ stalkIdeal I x = ⊥ := by
  constructor
  · intro h
    by_contra hne
    exact orderAt_ne_top_of_stalkIdeal_ne_bot I x hne h
  · intro h
    rw [orderAt_eq_idealOrder, h, idealOrder_bot]

theorem orderAt_eq_of_stalkIdeal_eq {I J : X.IdealSheafData} {x : X}
    (h : stalkIdeal I x = stalkIdeal J x) : orderAt I x = orderAt J x := by
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder, h]

theorem orderAt_eq_one_iff (I : X.IdealSheafData) (x : X) :
    orderAt I x = 1 ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        ¬ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  constructor
  · intro h
    constructor
    · have ha : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := by rw [h]; simp
      simpa using (le_orderAt_iff I x 1).mp ha
    · intro hle
      have h2 := (le_orderAt_iff I x 2).mpr hle
      rw [h] at h2
      have h3 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
      omega
  · rintro ⟨ha, hb⟩
    have ha' : ((1 : ℕ) : ℕ∞) ≤ orderAt I x := (le_orderAt_iff I x 1).mpr (by simpa using ha)
    have hb' : ¬ ((2 : ℕ) : ℕ∞) ≤ orderAt I x := fun hc => hb ((le_orderAt_iff I x 2).mp hc)
    rcases eq_or_ne (orderAt I x) ⊤ with htop | hfin
    · exact absurd (htop ▸ le_top) hb'
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hn] at ha' hb' ⊢
      have hn1 : 1 ≤ n := by exact_mod_cast ha'
      have hn2 : ¬ (2 ≤ n) := fun hc => hb' (by exact_mod_cast hc)
      have hn3 : n = 1 := by omega
      rw [hn3, Nat.cast_one]

private theorem maximalIdeal_not_le_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ¬ IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hle
  refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_ ?_)
  · rw [Ideal.smul_eq_mul, ← pow_two]
    exact hle
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge

theorem orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (h : stalkIdeal I x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥) :
    orderAt I x = 1 := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_one_iff]
  refine ⟨h.le, ?_⟩
  rw [h]
  exact maximalIdeal_not_le_sq hne

private theorem mem_of_vanishingIdeal_le {R : Type*} [CommRing R]
    (W : Set (PrimeSpectrum R)) (hW : IsClosed W) (q : PrimeSpectrum R)
    (h : PrimeSpectrum.vanishingIdeal W ≤ q.asIdeal) : q ∈ W := by
  have h0 : q ∈ PrimeSpectrum.zeroLocus
      ((PrimeSpectrum.vanishingIdeal W : Ideal R) : Set R) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun y hy => h hy)
  rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq] at h0

private theorem map_algebraMap_eq_maximalIdeal {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (J : Ideal R) (hJ : J.IsRadical) (hJp : J ≤ p)
    (hmin : ∀ q : Ideal R, q.IsPrime → J ≤ q → q ≤ p → q = p) :
    Ideal.map (algebraMap R S) J = IsLocalRing.maximalIdeal S := by
  have hmap : Ideal.map (algebraMap R S) p = IsLocalRing.maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hcomap_le : Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S) ≤ p := by
    intro r hr
    by_contra hrp
    rw [Ideal.mem_comap] at hr
    have hrp' : r ∈ p.primeCompl := hrp
    have hunit : IsUnit (algebraMap R S r) := IsLocalization.map_units S ⟨r, hrp'⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp hr
    rw [mem_nonunits_iff] at hnu
    exact hnu hunit
  refine le_antisymm (le_trans (Ideal.map_mono hJp) (le_of_eq hmap)) ?_
  have hle : IsLocalRing.maximalIdeal S ≤ (Ideal.map (algebraMap R S) J).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    have : P.IsPrime := hPprime
    have hPmax : P ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hPprime.ne_top
    have h1 : Ideal.comap (algebraMap R S) P = p := by
      refine hmin _ (Ideal.comap_isPrime (algebraMap R S) P) ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap]
        exact hPle
      · exact le_trans (Ideal.comap_mono hPmax) hcomap_le
    have heq : IsLocalRing.maximalIdeal S = P := by
      rw [← hmap, ← h1]
      exact IsLocalization.map_under p.primeCompl S P
    exact heq.le
  refine hle.trans ?_
  rw [← IsLocalization.map_radical p.primeCompl S J]
  exact Ideal.map_mono hJ

theorem stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint (Z : TopologicalSpace.Closeds X) (ξ : X)
    (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal Z) ξ
      = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem ξ
  have hxU : ξ ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hZcl : IsClosed (Z : Set X) := Z.2
  have hcont : Continuous (⇑(hU.fromSpec)) := (hU.fromSpec).continuous
  have hξT : ξ ∈ T := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hξZ : ξ ∈ (Z : Set X) := hT.1.2 hξT
  have hWclosed : IsClosed ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
    hZcl.preimage hcont
  have hJdef : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
      = PrimeSpectrum.vanishingIdeal (⇑hU.fromSpec ⁻¹' (Z : Set X)) := rfl
  have hfp : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) = ξ :=
    hU.fromSpec_primeIdealOf ⟨ξ, hxU⟩
  have hmemW : hU.primeIdealOf ⟨ξ, hxU⟩ ∈ (⇑(hU.fromSpec) ⁻¹' (Z : Set X)) := by
    show (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ∈ (Z : Set X)
    rw [hfp]
    exact hξZ
  rw [stalkIdeal_eq_map_germ _ ξ U hxU, hJdef]
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk ξ) :=
    (X.presheaf.germ U.1 ξ hxU).hom.toAlgebra
  have hloc : IsLocalization (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal.primeCompl
      (X.presheaf.stalk ξ) := hU.isLocalization_stalk ⟨ξ, hxU⟩
  have halg : (X.presheaf.germ U.1 ξ hxU).hom
      = algebraMap Γ(X, U.1) (X.presheaf.stalk ξ) := rfl
  rw [halg]
  refine map_algebraMap_eq_maximalIdeal (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal _
    (PrimeSpectrum.isRadical_vanishingIdeal _) ?_ ?_
  · intro f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf _ hmemW
  · intro q hq hJq hqp
    have hQW : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈
        ((⇑hU.fromSpec ⁻¹' (Z : Set X)) : Set (PrimeSpectrum Γ(X, U.1))) :=
      mem_of_vanishingIdeal_le _ hWclosed ⟨q, hq⟩ hJq
    have hQP : (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ hU.primeIdealOf ⟨ξ, hxU⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        PrimeSpectrum.mem_zeroLocus]
      exact fun y hy => hqp hy
    have hzspec : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ⤳ ξ := by
      have hmapped := hQP.map hcont
      rwa [hfp] at hmapped
    have hzZ : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ (Z : Set X) := hQW
    have hirr : IsIrreducible
        (closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))}) :=
      isIrreducible_singleton.closure
    have hsubZ : closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} ⊆ (Z : Set X) :=
      hZcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hzZ)
    have hTsub : T ⊆ closure {(⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))} := by
      rw [← hξ]
      exact closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzspec)) isClosed_closure
    have hmax := hT.2 ⟨hirr, hsubZ⟩ hTsub
    have hzT : (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) ∈ T :=
      hmax (subset_closure (Set.mem_singleton _))
    have hξz : ξ ⤳ (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      specializes_iff_mem_closure.mpr (by rw [hξ]; exact hzT)
    have hind : Topology.IsInducing (⇑(hU.fromSpec)) :=
      (hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing
    have h3 : (⇑(hU.fromSpec)) (hU.primeIdealOf ⟨ξ, hxU⟩) ⤳
        (⇑(hU.fromSpec)) (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) := by
      rw [hfp]
      exact hξz
    have hPQ : hU.primeIdealOf ⟨ξ, hxU⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1)) :=
      hind.specializes_iff.mp h3
    have hpq : (hU.primeIdealOf ⟨ξ, hxU⟩).asIdeal ≤ q := by
      have h2 := specializes_iff_mem_closure.mp hPQ
      rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
      exact fun y hy => h2 hy
    exact le_antisymm hqp hpq

theorem orderAt_vanishingIdeal_eq_one [IsLocallyNoetherian X] (Z : TopologicalSpace.Closeds X)
    (ξ : X) (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≠ ⊥) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal _ ξ
    (stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint Z ξ T hT hξ) hne

private theorem maximalIdeal_ne_bot_of_not_isField {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ¬ IsField R) : IsLocalRing.maximalIdeal R ≠ ⊥ :=
  fun hb => h (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)

theorem orderAt_vanishingIdeal_eq_one_of_not_isField [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) (ξ : X) (T : Set X)
    (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hfield : ¬ IsField (X.presheaf.stalk ξ)) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 :=
  orderAt_vanishingIdeal_eq_one Z ξ T hT hξ (maximalIdeal_ne_bot_of_not_isField hfield)

private theorem map_maximalIdeal_of_inverse {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) :
    Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hx
    have h2 := hu.map g
    rwa [hgf] at h2
  · intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
    have hgz : g z ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hz
      have h2 := hu.map f
      rwa [hfg] at h2
    have h3 : f (g z) ∈ Ideal.map f (IsLocalRing.maximalIdeal R) := Ideal.mem_map_of_mem _ hgz
    rwa [hfg] at h3

private theorem idealOrder_map_of_inverse {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) (J : Ideal R) :
    idealOrder (Ideal.map f J) = idealOrder J := by
  have hf := map_maximalIdeal_of_inverse f g hgf hfg
  have hg := map_maximalIdeal_of_inverse g f hfg hgf
  have h1 : idealOrder J ≤ idealOrder (Ideal.map f J) :=
    idealOrder_le_idealOrder_map f hf.le J
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have h2 : Ideal.map g (Ideal.map f J) = J := by
    rw [Ideal.map_map, hcomp, Ideal.map_id]
  have h3 : idealOrder (Ideal.map f J) ≤ idealOrder (Ideal.map g (Ideal.map f J)) :=
    idealOrder_le_idealOrder_map g hg.le (Ideal.map f J)
  rw [h2] at h3
  exact le_antisymm h3 h1

open CategoryTheory in
private theorem hom_hom_apply_of_comp_eq {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (x : A) : g.hom (f.hom x) = k.hom x := by
  rw [← hk, CommRingCat.hom_comp]
  rfl

open CategoryTheory in
theorem orderAt_comap_of_isOpenImmersion {Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  obtain ⟨U, sectionFrameQuotient⟩ := Y.exists_affineOpens_mem y
  have hyU : y ∈ U.1 := sectionFrameQuotient
  have hVaff : IsAffineOpen (h ''ᵁ U.1) := U.2.image_of_isOpenImmersion h
  have hxV : h.base y ∈ (h ''ᵁ U.1) := ⟨y, hyU, rfl⟩
  let appEquiv : Γ(X, h ''ᵁ U.1) ≃+* Γ(Y, U.1) := (h.appIso U.1).commRingCatIsoToRingEquiv
  have hid : (I.comap h).ideal U
      = Ideal.map ((h.appIso U.1).hom).hom (I.ideal ⟨h ''ᵁ U.1, hVaff⟩) := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I h U]
    exact Ideal.comap_symm appEquiv ..
  have key : (h.appIso U.1).inv ≫
        (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)
      = Y.presheaf.germ U.1 y hyU := by
    rw [← Category.assoc, Scheme.Hom.appIso_inv_app]
    exact Y.presheaf.germ_res _ y hxV
  have hcat : (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
      = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y := by
    calc (h.appIso U.1).hom ≫ Y.presheaf.germ U.1 y hyU
        = (h.appIso U.1).hom ≫ ((h.appIso U.1).inv ≫
            (h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV)) := by rw [key]
      _ = h.app (h ''ᵁ U.1) ≫ Y.presheaf.germ (h ⁻¹ᵁ h ''ᵁ U.1) y hxV := by
          rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV ≫ h.stalkMap y :=
          (Scheme.Hom.germ_stalkMap h (h ''ᵁ U.1) y hxV).symm
  have hcomp : (Y.presheaf.germ U.1 y hyU).hom.comp ((h.appIso U.1).hom).hom
      = ((h.stalkMap y).hom).comp (X.presheaf.germ (h ''ᵁ U.1) (h.base y) hxV).hom := by
    have h4 := congrArg CommRingCat.Hom.hom hcat
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp] at h4
  have hsgf : ∀ x, ((inv (h.stalkMap y)).hom) ((h.stalkMap y).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (IsIso.hom_inv_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  have hsfg : ∀ x, ((h.stalkMap y).hom) ((inv (h.stalkMap y)).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (IsIso.inv_hom_id (h.stalkMap y)) x, CommRingCat.hom_id]
    rfl
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder,
    stalkIdeal_eq_map_germ (I.comap h) y U hyU,
    stalkIdeal_eq_map_germ I (h.base y) ⟨h ''ᵁ U.1, hVaff⟩ hxV, hid, Ideal.map_map, hcomp,
    ← Ideal.map_map]
  exact idealOrder_map_of_inverse (h.stalkMap y).hom (inv (h.stalkMap y)).hom hsgf hsfg _

open CategoryTheory in
theorem orderAt_comap_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (J : B.IdealSheafData)
    (x : ↥A) : orderAt (J.comap f) x = orderAt J (f.base x) :=
  orderAt_comap_of_isOpenImmersion f J x

noncomputable def orderAtLeastLocus (I : X.IdealSheafData) (m : ℕ) : Set X :=
  {x : X | (m : ℕ∞) ≤ orderAt I x}

theorem mem_orderAtLeastLocus_iff (I : X.IdealSheafData) (m : ℕ) (x : X) :
    x ∈ orderAtLeastLocus I m ↔ (m : ℕ∞) ≤ orderAt I x := Iff.rfl

theorem mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    x ∈ orderAtLeastLocus I m ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ m := by
  rw [mem_orderAtLeastLocus_iff, le_orderAt_iff]

theorem orderAtLeastLocus_zero (I : X.IdealSheafData) : orderAtLeastLocus I 0 = Set.univ := by
  ext x
  simp [mem_orderAtLeastLocus_iff]

theorem mem_orderAtLeastLocus_one_iff (I : X.IdealSheafData) (x : X) :
    x ∈ orderAtLeastLocus I 1 ↔ x ∈ I.support := by
  rw [mem_orderAtLeastLocus_iff, Nat.cast_one, one_le_orderAt_iff_mem_support]

theorem orderAtLeastLocus_one (I : X.IdealSheafData) : orderAtLeastLocus I 1 = {x : X | x ∈ I.support} := by
  ext x
  exact mem_orderAtLeastLocus_one_iff I x

theorem orderAtLeastLocus_top_eq_empty (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus (⊤ : X.IdealSheafData) m = ∅ := by
  ext x
  simp only [mem_orderAtLeastLocus_iff, Set.mem_empty_iff_false, iff_false, not_le, orderAt_top]
  have h : 0 < m := hm
  exact_mod_cast h

theorem orderAtLeastLocus_subset_of_le (I : X.IdealSheafData) {m m' : ℕ} (h : m ≤ m') :
    orderAtLeastLocus I m' ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  refine le_trans ?_ hx
  exact_mod_cast h

theorem orderAtLeastLocus_subset_of_le_ideal {I J : X.IdealSheafData} (h : I ≤ J) (m : ℕ) :
    orderAtLeastLocus J m ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  exact le_trans hx (orderAt_le_of_le h x)

theorem inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul (I J : X.IdealSheafData) (m m' : ℕ) :
    orderAtLeastLocus I m ∩ orderAtLeastLocus J m' ⊆ orderAtLeastLocus (I * J) (m + m') := by
  rintro x ⟨hx, hx'⟩
  rw [mem_orderAtLeastLocus_iff] at hx hx' ⊢
  calc ((m + m' : ℕ) : ℕ∞) = (m : ℕ∞) + (m' : ℕ∞) := by push_cast; ring
    _ ≤ orderAt I x + orderAt J x := add_le_add hx hx'
    _ ≤ orderAt (I * J) x := add_orderAt_le_orderAt_mul I J x

theorem orderAtLeastLocus_subset_orderAtLeastLocus_pow (I : X.IdealSheafData) (c m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (I ^ c) (c * m) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  calc ((c * m : ℕ) : ℕ∞) = (c : ℕ∞) * (m : ℕ∞) := by push_cast; ring
    _ ≤ (c : ℕ∞) * orderAt I x := by gcongr
    _ ≤ orderAt (I ^ c) x := mul_orderAt_le_orderAt_pow I c x

end FunctorialResolution.EmbeddedResolution
