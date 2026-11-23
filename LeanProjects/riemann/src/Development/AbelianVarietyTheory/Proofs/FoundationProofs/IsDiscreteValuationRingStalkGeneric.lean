import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE

universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.DvrModel

open PrimeSection

variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}

local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)

variable (K) in

theorem isLocalization_away (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors V)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha ↦ ?_).2 inferInstance
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hϖ
  exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩

variable (f) in

theorem notMem_basicOpen_iff (hϖ : Irreducible ϖ) (x : H) :
    x ∉ H.basicOpen cst[f, V, ϖ] ↔ f x = closedPoint V := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  change ¬ ϖ ∉ (f x).asIdeal ↔ _
  rw [not_not]
  constructor
  · intro h
    refine PrimeSpectrum.ext ((maximalIdeal.isMaximal V).eq_of_le (f x).2.ne_top ?_).symm
    rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
  · intro h
    rw [h]
    exact hϖ.not_isUnit

theorem isOpenImmersion_generic
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :
    IsOpenImmersion j := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away K hϖ
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip
    (IsOpenImmersion.of_isLocalization ϖ)

theorem opensRange_generic (hϖ : Irreducible ϖ) [IsOpenImmersion j]
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :
    j.opensRange = H.basicOpen cst[f, V, ϖ] := by
  have := isLocalization_away K hϖ
  have hr := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    change f (j y) ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V))
    rw [← hr, ← Scheme.Hom.comp_apply, hK.w]
    exact ⟨fK y, rfl⟩
  · obtain ⟨z, hz⟩ : f x ∈ Set.range (PrimeSpectrum.comap (algebraMap V K)) := hr.ge hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hK x z hz.symm
    exact ⟨y, hy⟩

theorem mem_range_special
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∈ Set.range i ↔ f x = closedPoint V := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, hs.w]
    exact PrimeSpectrum.comap_residue V (fs y)
  · intro h
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hs x (closedPoint _)
      (h.trans (PrimeSpectrum.comap_residue V _).symm)
    exact ⟨y, hy⟩

variable (f) in
omit [IsDiscreteValuationRing V] in

theorem res_mem_nonZeroDivisors [Flat f] {c : V} (hc : c ≠ 0) {U : H.Opens}
    (hU : IsAffineOpen U) :
    H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, c] ∈ nonZeroDivisors Γ(H, U) := by
  have hf := f.flat_appLE (isAffineOpen_top _) hU le_top
  let := (f.appLE ⊤ U le_top).hom.toAlgebra
  have hc' : (Scheme.ΓSpecIso (.of V)).inv c ≠ 0 :=
    (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1).2 hc
  have : Module.Flat Γ(Spec (.of V), ⊤) Γ(H, U) := hf
  have := IsSMulRegular.of_flat (S := Γ(H, U)) (IsSMulRegular.of_ne_zero hc')
  exact mem_nonZeroDivisors_iff_left.2 fun z hz ↦ this (hz.trans (smul_zero _).symm)

theorem isIntegral [Flat f] [IsIntegral HK]
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) : IsIntegral H := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isOpenImmersion_generic hK
  exact isIntegral_of_basicOpen (fun U hU ↦ res_mem_nonZeroDivisors f hϖ.ne_zero hU) j
    (opensRange_generic hϖ hK)

theorem notMem_basicOpen_iff_specializes (hϖ : Irreducible ϖ) [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∉ H.basicOpen cst[f, V, ϖ] ↔ i (genericPoint Hs) ⤳ x := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 ((notMem_basicOpen_iff f hϖ x).1 h)
    exact ((genericPoint_spec Hs).specializes trivial).map i.continuous
  · intro h hx
    exact (notMem_basicOpen_iff f hϖ _).2 ((mem_range_special hs _).1 ⟨_, rfl⟩)
      (h.mem_open (H.basicOpen _).isOpen hx)

theorem prime_res (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) {U : H.Opens}
    (hU : IsAffineOpen U) {x : H} (hx : x ∈ U) (hfx : f x = closedPoint V) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, ϖ]) := by
  obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 hfx
  have : Nonempty (i ⁻¹ᵁ U) := ⟨⟨y, hx⟩⟩
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  rw [← Ideal.span_singleton_prime
      (nonZeroDivisors.ne_zero (res_mem_nonZeroDivisors f hϖ.ne_zero hU)),
    ← ker_app_eq_span (β := CommRingCat.ofHom (residue V)) residue_surjective
      (ker_residue.trans hϖ.maximalIdeal_eq) hs hU]
  exact RingHom.ker_isPrime _

theorem prime_res_generic (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (U : H.Opens)
    (hU : IsAffineOpen U) (h : i (genericPoint Hs) ∈ U) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op cst[f, V, ϖ]) :=
  prime_res hϖ hs hU h ((mem_range_special hs _).1 ⟨_, rfl⟩)

variable (f) in
theorem isLocallyNoetherian [LocallyOfFiniteType f] : IsLocallyNoetherian H :=
  LocallyOfFiniteType.isLocallyNoetherian f

theorem isDiscreteValuationRing_stalk_generic (hϖ : Irreducible ϖ) [Flat f]
    [LocallyOfFiniteType f] [IsIntegral H] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) :
    IsDiscreteValuationRing (H.presheaf.stalk (i (genericPoint Hs))) ∧
      Irreducible (H.presheaf.germ ⊤ (i (genericPoint Hs)) trivial cst[f, V, ϖ]) :=
  haveI := isLocallyNoetherian f
  isDiscreteValuationRing_stalk (notMem_basicOpen_iff_specializes hϖ hs) (prime_res_generic hϖ hs)

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in

theorem appTop_cst (hw : j ≫ f = fK ≫ Spec.map (CommRingCat.ofHom (algebraMap V K))) (c : V) :
    j.appTop cst[f, V, c] = cst[fK, K, algebraMap V K c] := by
  have h₁ := congrArg (fun φ : HK ⟶ Spec (.of V) ↦ φ.appTop ((Scheme.ΓSpecIso (.of V)).inv c)) hw
  have h₂ := congrArg (fun φ : CommRingCat.of V ⟶ Γ(Spec (.of K), ⊤) ↦ φ c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K)))
  exact h₁.trans (congrArg fK.appTop h₂.symm)

theorem pull_U {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a : PUnit → L.ι) :
    (L.pull φ).U a = φ ⁻¹ᵁ L.U (a ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ ↦ φ) a ⟨⟩) fun _ hy ↦ Set.mem_iInter.2 fun _ ↦ hy

theorem wchart_comp {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ] (h : Z ⟶ Y)
    (φ : κ → (Y ⟶ X)) (a : κ → L.ι) :
    LB.wchart L (fun k ↦ h ≫ φ k) a = h ⁻¹ᵁ LB.wchart L φ a :=
  le_antisymm (LB.wchart_comp_le L h φ a) fun _ hy ↦
    Set.mem_iInter.2 fun k ↦ Set.mem_iInter.1 hy k

theorem coe_pull_g {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull φ).g a b : Γ(Y, (L.pull φ).U a ⊓ (L.pull φ).U b)) =
      φ.appLE (L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩)) _ (inf_le_inf (pull_U L φ a).le (pull_U L φ b).le)
        (L.g (a ⟨⟩) (b ⟨⟩) : Γ(X, L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩))) :=
  congrArg Units.val (LB.lcg_pull L φ a b)

theorem coe_res_pullGen {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ]
    (φ : κ → (Y ⟶ X)) (ε : κ → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (a : κ → L.ι)
    {A : Z.Opens} (hA : A ≤ LB.wchart L (fun k ↦ h ≫ φ k) a) :
    (res hA (LB.ts (LB.pullGen L φ ε c h) a) : Γ(Z, A)ˣ) =
      h.appLE (LB.wchart L φ a) A (hA.trans (LB.wchart_comp_le L h φ a))
        (LB.ts c a : Γ(Y, LB.wchart L φ a)ˣ) :=
  res_appLE h (LB.wchart_comp_le L h φ a) hA _

section Main

variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))

include hK hs

theorem existsUnique_isUnit_appLE_eq {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {a₀ : ι} {A : (Spec (.of V)).Opens} (hyA : closedPoint V ∈ A) (hA : A ≤ e ⁻¹ᵁ U a₀)
    {A' : (Spec (.of K)).Opens} (hA' : A' = Spec.map (CommRingCat.ofHom (algebraMap V K)) ⁻¹ᵁ A)
    (hA'' : A' ≤ eK ⁻¹ᵁ W a₀) {u : Γ(Spec (.of V), A)} (hu : IsUnit u)
    (hur : (Spec.map (CommRingCat.ofHom (algebraMap V K))).appLE A A' hA'.le u =
      eK.appLE (W a₀) A' hA'' (r a₀)) :
    ∃! s : ∀ a, Γ(H, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have := isLocalization_away K hϖ
  have := IsOpenImmersion.of_isLocalization (S := K) ϖ
  refine existsUnique_of_exists_of_unique
    (exists_isUnit_appLE_eq (notMem_basicOpen_iff_specializes hϖ hs) (prime_res_generic hϖ hs)
      (opensRange_generic hϖ hK) hW hU hg hr hru e _ eK heK ?_ hyA hA hA' hA'' hu hur)
    fun s s' h h' ↦ funext fun a ↦ appLE_injective j (hW a) ((h.2.2 a).trans (h'.2.2 a).symm)
  rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, he]
  rfl

theorem existsUnique_gen {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {L : LB H} (hL : L.IsLB) (r : LB.Gen (L.pull j)) (hr : r.IsGen) (ρ : LB.Gen (L.pull e))
    (hρ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
      (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K))))) :
    ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r := by
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover hL (e (closedPoint V))
  have hc := congrArg Units.val
    (hρ (fun _ ↦ a₀) (fun _ ↦ a₀) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl)
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.s fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact congrArg Units.val (hr _ _))
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := (L.pull e).U fun _ ↦ a₀)
    ((pull_U L e _).ge h₀) (pull_U L e _).le
    (A' := LB.wchart L (fun _ : PUnit ↦ eK ≫ j) (fun _ ↦ a₀) ⊓
      LB.wchart L (fun _ : PUnit ↦ Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e) fun _ ↦ a₀)
    (by rw [heK, inf_idem]; exact wchart_comp L _ (fun _ ↦ e) _)
    (inf_le_left.trans (wchart_comp L eK (fun _ ↦ j) _).le) (ρ.s _).isUnit
    ((coe_res_pullGen L (fun _ ↦ e) _ ρ _ (fun _ ↦ a₀) inf_le_right).symm.trans
      (hc.symm.trans (coe_res_pullGen L (fun _ ↦ j) _ r eK (fun _ ↦ a₀) inf_le_left)))
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr (a ⟨⟩)))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ r' a) ⟨fun a ↦ Units.isUnit _, fun a b ↦ congrArg Units.val (h₁ a b),
      fun a ↦ congrArg (fun c : LB.Gen (L.pull j) ↦ (c.s fun _ ↦ a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

theorem existsUnique_gen_linComb {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {X : Scheme.{u}} {L : LB X} (hL : L.IsLB) {κ : Type u} [Fintype κ] (φ : κ → (H ⟶ X))
    (ε : κ → ℤ) (r : LB.Gen (LB.LinComb L (fun k ↦ j ≫ φ k) ε)) (hr : r.IsGen) (a₀ : κ → L.ι)
    (h₀ : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ a₀) (h₀' : ⊤ ≤ eK ⁻¹ᵁ LB.wchart L (fun k ↦ j ≫ φ k) a₀)
    (u : Vˣ) (hu : eK.appLE _ ⊤ h₀' (LB.ts r a₀ : Γ(HK, LB.wchart L (fun k ↦ j ≫ φ k) a₀)) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap V K u)) :
    ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L φ ε c j = r := by
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b) (W := LB.wchart L fun k ↦ j ≫ φ k)
    (wchart_comp L j φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts r a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L r).1 hr a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := ⊤) trivial h₀ (A' := ⊤) rfl h₀'
    (u.isUnit.map (Scheme.ΓSpecIso (.of V)).inv.hom) (by
      rw [hu]
      exact (congrArg (fun ψ : CommRingCat.of V ⟶ Γ(Spec (.of K), ⊤) ↦ ψ u)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K)))).symm)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

theorem sec_eq_zero_of_mem_span_pow (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB) (s : L.Sec)
    (h : ∀ a (n : ℕ), s.f a ∈
      Ideal.span {H.presheaf.map (homOfLE (le_top : L.U a ≤ ⊤)).op cst[f, V, ϖ]} ^ n)
    (a : L.ι) : s.f a = 0 := by
  have := isIntegral hK
  have := isLocallyNoetherian f
  obtain ⟨b, hb⟩ := LB.mem_of_cover hL (i (genericPoint Hs))
  refine eq_zero_of_forall_pow_dvd_germ (fun a b ↦ L.g a b) s.f s.compat hb
    ((notMem_basicOpen_iff_specializes hϖ hs _).2 specializes_rfl) (fun n ↦ ?_) a
  have := h b n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  have := map_dvd (H.presheaf.germ _ _ hb).hom this
  rwa [map_pow, germ_res] at this

theorem sec_eq_zero_of_app_eq_zero (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB) (s : L.Sec)
    {Z : ℕ → Scheme.{u}} {k : ∀ n, Z n ⟶ H}
    {p : ∀ n, Z n ⟶ Spec (.of (V ⧸ Ideal.span {ϖ ^ n}))}
    (hZ : ∀ n, IsPullback (k n) (p n) f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})))))
    (h : ∀ a n, (k n).app (L.U a) (s.f a) = 0) (a : L.ι) : s.f a = 0 := by
  have := isIntegral hK
  have := isLocallyNoetherian f
  obtain ⟨b, hb⟩ := LB.mem_of_cover hL (i (genericPoint Hs))
  refine eq_zero_of_forall_pow_dvd_germ (fun a b ↦ L.g a b) s.f s.compat hb
    ((notMem_basicOpen_iff_specializes hϖ hs _).2 specializes_rfl) (fun n ↦ ?_) a
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset hb
  have hAU : A ≤ L.U b := hAU
  have hm : H.presheaf.map (homOfLE hAU).op (s.f b) ∈ RingHom.ker ((k n).app A).hom := by
    change (k n).app A _ = 0
    rw [← ConcreteCategory.comp_apply, (k n).naturality, ConcreteCategory.comp_apply, h, map_zero]
  rw [ker_app_eq_span (β := CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})))
    Ideal.Quotient.mk_surjective Ideal.mk_ker (hZ n) hA, Ideal.mem_span_singleton] at hm
  have := map_dvd (H.presheaf.germ _ _ hxA).hom hm
  rwa [germ_res, germ_res, map_pow, map_pow, map_pow] at this

theorem existsUnique_zpow_mul_chart (hϖ : Irreducible ϖ) {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(H, U a),
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s a) := by
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := fK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hτ : ∀ n : ℤ, ((Units.map φ.toMonoidHom (Units.mk0 _ h0) ^ n : Γ(HK, ⊤)ˣ) : Γ(HK, ⊤)) =
      cst[fK, K, algebraMap V K ϖ ^ n] := fun n ↦ by
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val]
    rfl
  have := existsUnique_zpow_mul_appLE (notMem_basicOpen_iff_specializes hϖ hs)
    (prime_res_generic hϖ hs) (opensRange_generic hϖ hK) hW hU hg
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm hr hr0
  simpa only [hτ, notMem_basicOpen_iff f hϖ] using this

theorem existsUnique_zpow_mul_sec (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB)
    (r : (L.pull j).Sec) (hr0 : ∃ a, r.f a ≠ 0) :
    ∃! n : ℤ, ∃ s : L.Sec,
      (∀ a : PUnit → L.ι, j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
        HK.presheaf.map (homOfLE le_top).op cst[fK, K, algebraMap V K ϖ ^ n] * r.f a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by
  obtain ⟨n, ⟨s, hc, hsr, hx⟩, huniq⟩ := existsUnique_zpow_mul_chart hK hs hϖ
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.f fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact r.compat _ _)
    (hr0.elim fun a ha ↦ ⟨a ⟨⟩, ha⟩)
  refine ⟨n, ⟨⟨s, hc⟩, fun a ↦ hsr (a ⟨⟩), hx⟩, ?_⟩
  rintro m ⟨s', hsr', hx'⟩
  exact huniq m ⟨s'.f, s'.compat, fun a ↦ hsr' fun _ ↦ a, hx'⟩

end Main

theorem isIntegral_of_geometricallyIntegral {X S Z : Scheme.{u}} {q : X ⟶ S}
    [GeometricallyIntegral q] {F : Type u} [Field F] {y : Spec (.of F) ⟶ S} {k : Z ⟶ X}
    {p : Z ⟶ Spec (.of F)} (h : IsPullback k p q y) : IsIntegral Z :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ h

example (n : Type u) [Finite n] :
    let q := 𝔸(n; Spec (.of V)) ↘ Spec (.of V)
    Flat q ∧ LocallyOfFiniteType q ∧
      IsIntegral (pullback q (Spec.map (CommRingCat.ofHom (algebraMap V K)))) ∧
      IsIntegral (pullback q (Spec.map (CommRingCat.ofHom (residue V)))) ∧
      ∃ e : Spec (.of V) ⟶ 𝔸(n; Spec (.of V)), e ≫ q = 𝟙 _ := by
  refine ⟨?_, inferInstance, isIntegral_of_geometricallyIntegral (.of_hasPullback _ _),
    isIntegral_of_geometricallyIntegral (.of_hasPullback _ _),
    AffineSpace.homOfVector (𝟙 _) 0, AffineSpace.homOfVector_over _ _⟩
  rw [(Iso.inv_comp_eq _).1 (AffineSpace.SpecIso_inv_over (n := n) (.of V))]
  have : Flat (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := V)))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2
      (inferInstanceAs (Module.Flat V (MvPolynomial n V))))
  infer_instance

end GlobalTheory.DvrModel

namespace GlobalTheory.PrimeElement

theorem subalgebra_inf_subalgebra {R : Type*} [CommRing R] [IsDomain R] {π : R}
    [(Ideal.span {π}).IsPrime] (hπ : π ≠ 0) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Localization.subalgebra.ofField K (Submonoid.powers π)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hπ) ⊓
      Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl
        (Ideal.span {π}).primeCompl_le_nonZeroDivisors = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  exact (range_inf_range (π := π)
    (Localization.subalgebra.ofField K (Submonoid.powers π)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ))
    (Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl
      (Ideal.span {π}).primeCompl_le_nonZeroDivisors) K hπ).le ⟨⟨⟨x, hx.1⟩, rfl⟩, ⟨⟨x, hx.2⟩, rfl⟩⟩

end GlobalTheory.PrimeElement

namespace GlobalTheory.DvrModel

theorem prime_element_and_extension :
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R)
      [(Ideal.span {π}).IsPrime], π ≠ 0 →
      ∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
        (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
        (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
        [Algebra A F] [IsScalarTower R A F] [Algebra S F] [IsScalarTower R S F],
      ∃ (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : IsFractionRing S F),
        Irreducible (algebraMap R S π) ∧
        (algebraMap A F).range ⊓ (algebraMap S F).range = (algebraMap R F).range ∧
        (∀ y : A, IsUnit y →
          (IsDiscreteValuationRing.maximalIdeal S).valuation F (algebraMap A F y) = 1 →
          ∃ r : R, IsUnit r ∧ algebraMap R A r = y) ∧
        ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) ∧
    ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] (ϖ : V), Irreducible ϖ →
      ∀ (H HK Hs : Scheme.{u}) (f : H ⟶ Spec (.of V)) [Flat f] [LocallyOfFiniteType f]
        (j : HK ⟶ H) (fK : HK ⟶ Spec (.of K)) [IsIntegral HK]
        (i : Hs ⟶ H) (fs : Hs ⟶ Spec (.of (ResidueField V))) [IsIntegral Hs],
      IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))) →
      IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))) →
      ∀ L : LB H, L.IsLB →
      (∀ (e : Spec (.of V) ⟶ H) (eK : Spec (.of K) ⟶ HK), e ≫ f = 𝟙 _ →
        eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e →
        ∀ (r : LB.Gen (L.pull j)) (ρ : LB.Gen (L.pull e)), r.IsGen →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
          (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K)))) →
        ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r) ∧
      (∀ s : L.Sec, (∀ a (n : ℕ), (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {ϖ ^ n}))))).app (L.U a) (s.f a) = 0) →
        ∀ a, s.f a = 0) ∧
      ∀ r : (L.pull j).Sec, (∃ a, r.f a ≠ 0) →
        ∃! n : ℤ, ∃ s : L.Sec,
          (∀ a : PUnit → L.ι,
            j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
              HK.presheaf.map (homOfLE le_top).op
                (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n))) * r.f a) ∧
          ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by
  refine ⟨fun R _ _ _ π _ hπ A _ _ _ S _ _ _ F _ _ _ _ _ _ _ ↦ ?_,
    fun V _ _ _ K _ _ _ ϖ hϖ H HK Hs f _ _ j fK _ i fs _ hK hs L hL ↦
      ⟨fun e eK he heK r ρ hr hρ ↦ existsUnique_gen hK hs he heK hL r hr ρ hρ,
        fun s h ↦ sec_eq_zero_of_app_eq_zero hK hs hϖ hL s (fun _ ↦ .of_hasPullback _ _) h,
        existsUnique_zpow_mul_sec hK hs hϖ hL⟩⟩
  have h₁ := PrimeElement.isDomain_atPrime (π := π) S
  have h₂ := PrimeElement.isDiscreteValuationRing (π := π) S hπ
  have h₃ : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {π}).primeCompl S F
  exact ⟨h₁, h₂, h₃, PrimeElement.irreducible_algebraMap S hπ,
    PrimeElement.range_inf_range A S F hπ,
    fun y hy h ↦ PrimeElement.exists_unit_algebraMap_eq_of_valuation_eq_one S F hπ hy h,
    fun x ↦ PrimeElement.eq_zero_of_forall_pow_dvd
      ((Ideal.span_singleton_prime hπ).1 inferInstance).not_isUnit⟩

end GlobalTheory.DvrModel
