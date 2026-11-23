import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

lemma map_germ_ideal_eq_of_le {W : Scheme.{u}} (G : W.IdealSheafData) {U V : W.affineOpens} (h : U ≤ V)
    (x : W) (hx : x ∈ U.1) :
    Ideal.map (W.presheaf.germ V.1 x (h hx)).hom (G.ideal V) =
      Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by
  rw [← G.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  first
  | (congr 2; exact (TopCat.Presheaf.germ_res W.presheaf _ x hx).symm)
  | (erw [TopCat.Presheaf.germ_res])
  | simp [TopCat.Presheaf.germ_res]

lemma ds_stalkId_eq_map {W : Scheme.{u}} (G : W.IdealSheafData) (U : W.affineOpens) (x : W)
    (hx : x ∈ U.1) :
    FinalTheorems.stalkId G x = Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by
  unfold FinalTheorems.stalkId
  apply le_antisymm
  · refine iSup₂_le fun U' hx' => ?_
    have hxi : x ∈ U.1 ⊓ U'.1 := by
      first
      | exact ⟨hx, hx'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      | simp [hx, hx']
    obtain ⟨O, hO, hxO, hOle⟩ : ∃ O ∈ W.affineOpens, x ∈ O ∧ O ≤ U.1 ⊓ U'.1 := by
      first
      | (obtain ⟨f, hf1, hf2⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨x, hx'⟩ hx
         exact ⟨W.basicOpen f, U.2.basicOpen f, hf2, le_inf (W.basicOpen_le f) hf1⟩)
      | exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_affine_open W)) hxi
      | exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hxi
    let U'' : W.affineOpens := ⟨O, hO⟩
    have h1 : U'' ≤ U := (le_inf_iff.mp hOle).1
    have h2 : U'' ≤ U' := (le_inf_iff.mp hOle).2
    exact ((map_germ_ideal_eq_of_le G h2 x hxO).trans (map_germ_ideal_eq_of_le G h1 x hxO).symm).le
  · exact le_iSup₂ (f := fun (U : W.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U)) U hx

lemma ds_spread {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] (I : Ideal R) (a : R) (ha : a ∈ I)
    (hmap : I.map (algebraMap R S) = Ideal.span {algebraMap R S a})
    (hnzd : algebraMap R S a ∈ nonZeroDivisors S) :
    ∃ σ : R, σ ∉ P ∧ ∀ (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away σ T],
      I.map (algebraMap R T) = Ideal.span {algebraMap R T a} ∧
        algebraMap R T a ∈ nonZeroDivisors T := by
  obtain ⟨sI, hsI⟩ := IsNoetherian.noetherian I
  obtain ⟨sJ, hsJ⟩ := IsNoetherian.noetherian (LinearMap.ker (LinearMap.mulRight R a))

  have key : ∀ i ∈ I, ∃ c ∈ P.primeCompl, c * i ∈ Ideal.span {a} := by
    intro i hi
    have hi' : algebraMap R S i ∈ Ideal.span {algebraMap R S a} := by
      rw [← hmap]; exact Ideal.mem_map_of_mem _ hi
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hi'
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    have e : algebraMap R S (r * a) = algebraMap R S (↑s * i) := by
      rw [map_mul, map_mul, ← hy, ← IsLocalization.mk'_spec S r s]; ring
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e
    exact ⟨↑d * ↑s, P.primeCompl.mul_mem d.2 s.2,
      Ideal.mem_span_singleton'.mpr ⟨↑d * r, by linear_combination hd⟩⟩

  have key2 : ∀ j ∈ LinearMap.ker (LinearMap.mulRight R a), ∃ d ∈ P.primeCompl, d * j = 0 := by
    intro j hj
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply] at hj
    have h1 : algebraMap R S j * algebraMap R S a = 0 := by rw [← map_mul, hj, map_zero]
    have h2 : algebraMap R S j = algebraMap R S 0 := by
      rw [map_zero]
      first
      | exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hnzd).mp h1
      | exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp (by rw [zero_mul]; exact h1)
      | exact (mem_nonZeroDivisors_iff.mp hnzd).1 _ h1
      | exact mem_nonZeroDivisors_iff.mp hnzd _ h1
      | exact hnzd.1 _ h1
      | exact hnzd _ h1
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) h2
    exact ⟨d, d.2, by rw [hd, mul_zero]⟩
  choose! cI hcP hcA using key
  choose! dJ hdP hdA using key2
  have memI : ∀ i ∈ sI, i ∈ I := fun i hi => by
    rw [← hsI]; exact Submodule.subset_span (Finset.mem_coe.mpr hi)
  have memJ : ∀ j ∈ sJ, j ∈ LinearMap.ker (LinearMap.mulRight R a) := fun j hj => by
    rw [← hsJ]; exact Submodule.subset_span (Finset.mem_coe.mpr hj)
  obtain ⟨C, hC⟩ : ∃ C : R, C = ∏ i ∈ sI, cI i := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : R, D = ∏ j ∈ sJ, dJ j := ⟨_, rfl⟩
  have hCP : C ∈ P.primeCompl := by
    rw [hC]; exact prod_mem fun i hi => hcP i (memI i hi)
  have hDP : D ∈ P.primeCompl := by
    rw [hD]; exact prod_mem fun j hj => hdP j (memJ j hj)
  have hDk : ∀ x ∈ LinearMap.ker (LinearMap.mulRight R a), D * x = 0 := by
    have hle : LinearMap.ker (LinearMap.mulRight R a) ≤ LinearMap.ker (LinearMap.mulLeft R D) := by
      rw [← hsJ, Submodule.span_le]
      intro j hj
      have hj' : j ∈ sJ := Finset.mem_coe.mp hj
      have hj0 : dJ j * j = 0 := hdA j (memJ j hj')
      obtain ⟨e, he⟩ : dJ j ∣ D := by rw [hD]; exact Finset.dvd_prod_of_mem dJ hj'
      show j ∈ LinearMap.ker (LinearMap.mulLeft R D)
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, he]
      linear_combination e * hj0
    intro x hx
    have hx' := hle hx
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx'
  refine ⟨C * D, P.primeCompl.mul_mem hCP hDP, ?_⟩
  intro T _ _ _
  have hunit : IsUnit (algebraMap R T (C * D)) :=
    IsLocalization.map_units T (⟨C * D, Submonoid.mem_powers _⟩ : Submonoid.powers (C * D))
  constructor
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, ← hsI, Submodule.span_le]
      intro i hi
      have hi' : i ∈ sI := Finset.mem_coe.mp hi
      have hcu : IsUnit (algebraMap R T (cI i)) := by
        refine isUnit_of_dvd_unit (map_dvd _ ?_) hunit
        rw [hC]; exact (Finset.dvd_prod_of_mem cI hi').trans (dvd_mul_right _ _)
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hcA i (memI i hi'))
      have e1 : algebraMap R T (cI i) * algebraMap R T i =
          algebraMap R T r * algebraMap R T a := by
        rw [← map_mul, ← map_mul, hr]
      show algebraMap R T i ∈ Ideal.span {algebraMap R T a}
      refine Ideal.mem_span_singleton'.mpr ⟨↑hcu.unit⁻¹ * algebraMap R T r, ?_⟩
      apply hcu.mul_left_cancel
      linear_combination (algebraMap R T r * algebraMap R T a) * hcu.mul_val_inv - e1
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ ha))
  · have H : ∀ z : T, z * algebraMap R T a = 0 → z = 0 := by
      intro z hz
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (C * D)) z
      have e1 : algebraMap R T (r * a) = algebraMap R T 0 := by
        rw [map_zero, map_mul, ← IsLocalization.mk'_spec T r s]
        linear_combination (algebraMap R T ↑s) * hz
      obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
        IsLocalization.exists_of_eq (M := Submonoid.powers (C * D)) e1
      have hk' : (C * D) ^ k * (r * a) = 0 := hk.trans (mul_zero _)
      have hmem : (C * D) ^ k * r ∈ LinearMap.ker (LinearMap.mulRight R a) := by
        rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_assoc]; exact hk'
      have h0 := hDk _ hmem
      rw [IsLocalization.mk'_eq_zero_iff]
      refine ⟨⟨(C * D) ^ (k + 1), k + 1, rfl⟩, ?_⟩
      show (C * D) ^ (k + 1) * r = 0
      linear_combination C * h0
    first
    | exact mem_nonZeroDivisors_iff.mpr H
    | exact mem_nonZeroDivisors_iff_right.mpr H
    | exact mem_nonZeroDivisors_iff.mpr ⟨H, fun z hz => H z (by rw [mul_comm]; exact hz)⟩
    | exact ⟨H, fun z hz => H z (by rw [mul_comm]; exact hz)⟩
    | exact H

lemma ds_gen_of_span {S : Type*} [CommRing S] [IsLocalRing S] (A : Set S) (t : S)
    (ht0 : t ∈ nonZeroDivisors S) (hA : Ideal.span A = Ideal.span {t}) :
    ∃ y ∈ A, ∃ c : Sˣ, y = c * t := by
  by_contra hcon
  push_neg at hcon
  have hsub : Ideal.span A ≤ IsLocalRing.maximalIdeal S * Ideal.span {t} := by
    rw [Ideal.span_le]
    intro y hy
    have hyt : y ∈ Ideal.span {t} := by rw [← hA]; exact Ideal.subset_span hy
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hyt
    have hr' : r ∈ IsLocalRing.maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hcon y hy hu.unit (by rw [hu.unit_spec, hr])
    show y ∈ IsLocalRing.maximalIdeal S * Ideal.span {t}
    rw [← hr]
    exact Ideal.mul_mem_mul hr' (Ideal.mem_span_singleton_self t)
  have ht : t ∈ IsLocalRing.maximalIdeal S * Ideal.span {t} := by
    apply hsub; rw [hA]; exact Ideal.mem_span_singleton_self t
  obtain ⟨m, hm, hmt⟩ : ∃ m ∈ IsLocalRing.maximalIdeal S, m * t = t := by
    first
    | exact Ideal.mem_mul_span_singleton.mp ht
    | (obtain ⟨m, hm, hmt⟩ := Ideal.mem_span_singleton_mul.mp (by rwa [mul_comm] at ht)
       exact ⟨m, hm, by rw [mul_comm]; exact hmt⟩)
  have h1 : (1 - m) * t = 0 := by rw [sub_mul, one_mul, hmt, sub_self]
  have h2 : 1 - m = 0 := by
    first
    | exact (mul_right_mem_nonZeroDivisors_eq_zero_iff ht0).mp h1
    | exact (mul_cancel_right_mem_nonZeroDivisors ht0).mp (by rw [zero_mul]; exact h1)
    | exact (mem_nonZeroDivisors_iff.mp ht0).1 _ h1
    | exact mem_nonZeroDivisors_iff.mp ht0 _ h1
    | exact ht0.1 _ h1
    | exact ht0 _ h1
  have hm1 : m = 1 := (sub_eq_zero.mp h2).symm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hm1] at hm
  exact hm isUnit_one

section LocGen

variable {W : Scheme.{u}} {ι' : Type*} (V : ι' → W.Opens) (g : ∀ c, Γ(W, V c))

def dsK (x : W) : Ideal (W.presheaf.stalk x) :=
  ⨅ (c) (hc : x ∈ V c), Ideal.span {W.presheaf.germ (V c) x hc (g c)}

variable {V g}

lemma dsK_eq (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {x : W} (c) (hc : x ∈ V c) :
    dsK V g x = Ideal.span {W.presheaf.germ (V c) x hc (g c)} := by
  unfold dsK
  apply le_antisymm
  · exact iInf₂_le c hc
  · refine le_iInf₂ fun c' hc' => ?_
    obtain ⟨u, hu⟩ := hg c c' x hc hc'
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨↑u, by rw [hu, mul_comm]⟩

variable (V g)

def dsJ (U : W.affineOpens) : Ideal Γ(W, U) :=
  ⨅ (x) (hx : x ∈ U.1), Ideal.comap (W.presheaf.germ U.1 x hx).hom (dsK V g x)

variable {V g}

lemma mem_dsJ {U : W.affineOpens} {f : Γ(W, U)} :
    f ∈ dsJ V g U ↔ ∀ x (hx : x ∈ U.1), W.presheaf.germ U.1 x hx f ∈ dsK V g x := by
  unfold dsJ
  simp only [Submodule.mem_iInf, Ideal.mem_comap]
  all_goals exact Iff.rfl

end LocGen

section LocGen

variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}

private lemma exists_pow_mul_mem_span_of_germ_mem {X : Scheme.{u}} {O : X.Opens} (hO : IsAffineOpen O)
    (s a h : Γ(X, O))
    (hloc : ∀ (x : X) (hx : x ∈ O), IsUnit (X.presheaf.germ O x hx s) →
      X.presheaf.germ O x hx a ∈ Ideal.span {X.presheaf.germ O x hx h}) :
    ∃ m : ℕ, s ^ m * a ∈ Ideal.span {h} := by
  let Q : Ideal Γ(X, O) := Submodule.comap (LinearMap.mulRight Γ(X, O) a) (Ideal.span {h})
  have hQ : ∀ r, r ∈ Q ↔ r * a ∈ Ideal.span {h} := fun r => by
    simp only [Q, Submodule.mem_comap, LinearMap.mulRight_apply]
  suffices hs : s ∈ Q.radical by
    obtain ⟨m, hm⟩ := hs
    exact ⟨m, (hQ _).mp hm⟩
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro p ⟨hQp, hp⟩
  by_contra hsp
  obtain ⟨x, hx⟩ : ∃ x : O, hO.primeIdealOf x = ⟨p, hp⟩ := by
    first
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       exact congrArg (fun f : Spec Γ(X, O) ⟶ Spec Γ(X, O) => f (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)))
         hO.isoSpec.inv_hom_id)
    | (refine ⟨hO.isoSpec.inv.base (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       simp [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply]
       done)
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       show hO.isoSpec.hom (hO.isoSpec.inv _) = _
       rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
       try rfl
       done)
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       simp only [IsAffineOpen.primeIdealOf]
       rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
       try rfl
       try simp
       done)
  have hL := hO.isLocalization_stalk x
  have hxp : (hO.primeIdealOf x).asIdeal = p := by rw [hx]
  have hsu : IsUnit (X.presheaf.germ O x x.2 s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) (hO.primeIdealOf x).asIdeal
      s).mpr (by show s ∉ (hO.primeIdealOf x).asIdeal; rw [hxp]; exact hsp)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hloc x x.2 hsu)
  obtain ⟨⟨b, u⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hO.primeIdealOf x).asIdeal.primeCompl y
  have hy' : IsLocalization.mk' (X.presheaf.stalk x) b u *
      algebraMap Γ(X, O) (X.presheaf.stalk x) h = algebraMap Γ(X, O) (X.presheaf.stalk x) a := hy
  have e : algebraMap Γ(X, O) (X.presheaf.stalk x) (↑u * a) =
      algebraMap Γ(X, O) (X.presheaf.stalk x) (b * h) := by
    rw [map_mul, map_mul, ← IsLocalization.mk'_spec (X.presheaf.stalk x) b u]
    linear_combination -(algebraMap Γ(X, O) (X.presheaf.stalk x) ↑u) * hy'
  obtain ⟨v, hv⟩ := IsLocalization.exists_of_eq (M := (hO.primeIdealOf x).asIdeal.primeCompl) e
  have hvu : (v : Γ(X, O)) * (u : Γ(X, O)) ∈ Q := by
    rw [hQ]; exact Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, O)) * b, by linear_combination -hv⟩
  have hvu' : (v : Γ(X, O)) * (u : Γ(X, O)) ∉ p := by
    rw [← hxp]; exact (hO.primeIdealOf x).asIdeal.primeCompl.mul_mem v.2 u.2
  exact hvu' (hQp hvu)

lemma ds_local (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z)
    (c : ι') (t : Γ(W, U)) (htc : W.basicOpen t ≤ V c) :
    ∃ m : ℕ, ∀ z (hz : z ∈ W.basicOpen t),
      W.presheaf.germ U.1 z (W.basicOpen_le t hz) (s ^ m * a) ∈ dsK V g z := by
  have hOU : W.basicOpen t ≤ U.1 := W.basicOpen_le t
  have hO : IsAffineOpen (W.basicOpen t) := U.2.basicOpen t
  let ρ := W.presheaf.map (homOfLE hOU).op
  let g' : Γ(W, W.basicOpen t) := W.presheaf.map (homOfLE htc).op (g c)
  have gU : ∀ z (hz : z ∈ W.basicOpen t) (f : Γ(W, U)),
      W.presheaf.germ (W.basicOpen t) z hz (ρ f) = W.presheaf.germ U.1 z (hOU hz) f :=
    fun z hz f => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gV : ∀ z (hz : z ∈ W.basicOpen t),
      W.presheaf.germ (W.basicOpen t) z hz g' = W.presheaf.germ (V c) z (htc hz) (g c) :=
    fun z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hK : ∀ z (hz : z ∈ W.basicOpen t),
      dsK V g z = Ideal.span {W.presheaf.germ (W.basicOpen t) z hz g'} := by
    intro z hz; rw [gV z hz]; exact dsK_eq hg c (htc hz)
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_span_of_germ_mem hO (ρ s) (ρ a) g' (by
    intro z hz hu
    rw [← hK z hz, gU z hz]
    apply ha z (hOU hz)
    have hu' : IsUnit (W.presheaf.germ U.1 z (hOU hz) s) := by rw [← gU z hz]; exact hu
    first
    | exact (Scheme.mem_basicOpen W s z (hOU hz)).mpr hu'
    | exact (W.mem_basicOpen s z (hOU hz)).mpr hu'
    | simpa [Scheme.mem_basicOpen] using hu')
  refine ⟨m, fun z hz => ?_⟩
  rw [hK z hz, ← gU z hz]
  first
  | rw [map_mul, map_pow]
  | simp only [map_mul, map_pow]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
  rw [← hy, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end LocGen

end

end ReciprocityTheory.AnForm.R
