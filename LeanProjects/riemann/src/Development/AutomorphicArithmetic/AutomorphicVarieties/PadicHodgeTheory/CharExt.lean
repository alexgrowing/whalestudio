import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ce_ext {D W B : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group W] [Group B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (V : Subgroup D) [V.Normal] (hV : IsOpen (V : Set D))
    (hχ : ∀ s, i s ∈ V → χ s = 1) : ∃ ψ : D →* B, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = χ s := by
  set π : W →* D ⧸ V := (QuotientGroup.mk' V).comp i with hπdef
  have hopen : ∀ d : D, IsOpen {y : D | d⁻¹ * y ∈ V} := fun d =>
    hV.preimage (continuous_mul_left d⁻¹)
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨s, hs⟩ := hi.exists_mem_open (hopen d) ⟨d, by simp⟩
      exact ⟨s, (QuotientGroup.eq.mpr hs).symm⟩
  have hker : π.ker ≤ χ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    apply hχ
    simpa [hπdef, QuotientGroup.eq_one_iff] using hw
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨((QuotientGroup.lift π.ker χ hker).comp e.symm.toMonoidHom).comp (QuotientGroup.mk' V), ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y : D | x⁻¹ * y ∈ V}, hopen x, by simp, ?_⟩
    intro y hy
    have : (QuotientGroup.mk' V y) = QuotientGroup.mk' V x := (QuotientGroup.eq.mpr hy).symm
    simp only [MonoidHom.coe_comp, Function.comp_apply, this]
  · intro s
    have h1 : QuotientGroup.mk' V (i s) = e (QuotientGroup.mk s) := rfl
    simp only [MonoidHom.coe_comp, Function.comp_apply, h1, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl

private theorem ce_eq {D W Y : Type} [TopologicalSpace D] {i : W → D} (hi : DenseRange i) {f g : D → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ s, f (i s) = g (i s)) : f = g := by
  funext x
  obtain ⟨s, hs⟩ := hi.exists_mem_open ((hf.isOpen_fiber (f x)).inter (hg.isOpen_fiber (g x))) ⟨x, rfl, rfl⟩
  have h1 : f (i s) = f x := hs.1
  have h2 : g (i s) = g x := hs.2
  rw [← h1, ← h2, h s]

private theorem ce_lim {D W R : Type} [Group D] [TopologicalSpace D] [Group W] [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (i : W →* D) (hi : DenseRange i) (χ : W →* Rˣ)
    (H : ∀ N : ℕ, ∃ ψ : D →* R ⧸ I ^ N, IsLocallyConstant ψ ∧ ∀ s, ψ (i s) = Ideal.Quotient.mk _ (χ s : R)) :
    ∃! ψ : D →* Rˣ, UpperTheory.V.Alg.AdicCont I (fun g => (ψ g : R)) ∧ ∀ s, ψ (i s) = χ s := by
  have key : ∀ x y : R, (∀ N, Ideal.Quotient.mk (I ^ N) x = Ideal.Quotient.mk (I ^ N) y) → x = y := by
    intro x y h
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.mp (h n)
  choose φ hφc hφs using H
  let r : ℕ → D → R := fun n g => Function.surjInv Ideal.Quotient.mk_surjective (φ n g)
  have hr : ∀ n g, Ideal.Quotient.mk (I ^ n) (r n g) = φ n g := fun n g =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (φ n g)
  have hcomp : ∀ m n, m ≤ n → ∀ g, Ideal.Quotient.mk (I ^ m) (r n g) = φ m g := by
    intro m n hmn
    have hle : I ^ n ≤ I ^ m := Ideal.pow_le_pow_right hmn
    have hfun : (fun g => Ideal.Quotient.mk (I ^ m) (r n g)) = fun g => Ideal.Quotient.factor hle (φ n g) := by
      funext g
      rw [← hr n g, Ideal.Quotient.factor_mk]
    have h2 := ce_eq hi (f := fun g => Ideal.Quotient.factor hle (φ n g)) (g := fun g => φ m g)
      ((hφc n).comp _) (hφc m) (fun s => by
        show Ideal.Quotient.factor hle (φ n (i s)) = φ m (i s)
        rw [hφs n s, hφs m s, Ideal.Quotient.factor_mk])
    intro g
    exact (congrFun hfun g).trans (congrFun h2 g)
  have hlim : ∀ g, ∃ L : R, ∀ n, Ideal.Quotient.mk (I ^ n) L = φ n g := by
    intro g
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => r n g) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      apply Ideal.Quotient.eq.mp
      rw [hcomp m m le_rfl, hcomp m n hmn])
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    rw [← hr n g]
    exact (Ideal.Quotient.eq.mpr this).symm
  choose f hf using hlim
  have fmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    key _ _ fun N => by rw [map_mul, hf, hf, hf, map_mul]
  have f1 : f 1 = 1 := key _ _ fun N => by rw [hf, map_one, map_one]
  let u : D → Rˣ := fun g => ⟨f g, f g⁻¹, by rw [← fmul, mul_inv_cancel, f1], by rw [← fmul, inv_mul_cancel, f1]⟩
  let ψ : D →* Rˣ := { toFun := u, map_one' := Units.ext f1, map_mul' := fun a b => Units.ext (fmul a b) }
  have hψv : ∀ g, ((ψ g : Rˣ) : R) = f g := fun g => rfl
  have hψc : UpperTheory.V.Alg.AdicCont I (fun g => (ψ g : R)) := by
    intro N
    have : (fun g => Ideal.Quotient.mk (I ^ N) ((ψ g : Rˣ) : R)) = fun g => φ N g := funext fun g => hf g N
    rw [this]
    exact hφc N
  have hψs : ∀ s, ψ (i s) = χ s := fun s =>
    Units.ext (key _ _ fun N => by rw [hψv, hf, hφs])
  refine ⟨ψ, ⟨hψc, hψs⟩, ?_⟩
  rintro ψ' ⟨hc, hs⟩
  ext g
  refine key _ _ fun N => ?_
  have h3 := ce_eq hi (f := fun g => Ideal.Quotient.mk (I ^ N) ((ψ' g : Rˣ) : R))
    (g := fun g => Ideal.Quotient.mk (I ^ N) ((ψ g : Rˣ) : R)) (hc N) (hψc N) (fun s => by
      show Ideal.Quotient.mk (I ^ N) ((ψ' (i s) : Rˣ) : R) = Ideal.Quotient.mk (I ^ N) ((ψ (i s) : Rˣ) : R)
      rw [hs s, hψs s])
  exact congrFun h3 g

private theorem ce_open {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {B : Type} [Group B] [Finite B] (χ : Weil h →* B)
    (hχ : IsLocallyConstant fun σ : Ine (F := F) A => χ (ineIncl h σ)) :
    ∃ V : Subgroup (G F Ω), V.Normal ∧ IsOpen (V : Set (G F Ω)) ∧ ∀ s : Weil h, (s : G F Ω) ∈ V → χ s = 1 := by
  classical
  have hO : IsOpen {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := hχ.isOpen_fiber 1
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp hO
  have h1O : (1 : G F Ω) ∈ O := by
    have : (1 : Ine (F := F) A) ∈ {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := by simp
    rw [← hOeq] at this
    exact this
  obtain ⟨U, hUO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOo h1O
  haveI hUfi : U.toSubgroup.FiniteIndex := U.toOpenSubgroup.finiteIndex_of_finite_quotient
  have he : U.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hn : 0 < Nat.card B := Nat.card_pos
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree F Ω A w h (U.toSubgroup.index * Nat.card B)
    (Nat.mul_pos (Nat.pos_of_ne_zero he) hn)
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  have hfix := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {ζ})
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hfix.inter U.isOpen')
    ⟨one_mem _, one_mem U.toSubgroup⟩
  refine ⟨V.toSubgroup, inferInstance, V.isOpen', ?_⟩
  intro s hs
  have hsV := hV hs
  have hsζ : (s : G F Ω) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hsV.1 ζ (IntermediateField.mem_adjoin_simple_self F ζ)
  have hsU : (s : G F Ω) ∈ U.toSubgroup := hsV.2
  obtain ⟨m, hm⟩ := hζ s hsζ
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hfr : χ (frob h) ^ deg s = 1 := by
    rw [hm, zpow_mul, zpow_natCast, mul_comm, pow_mul, pow_card_eq_one', one_pow, one_zpow]
  have hpow : ((frob h : Weil h) : G F Ω) ^ deg s ∈ U.toSubgroup := by
    rw [hm, zpow_mul, zpow_natCast, pow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.pow_index_mem _ _) _) _
  have hτeq : ineIncl h τ = (frob h ^ deg s)⁻¹ * s := eq_inv_mul_of_mul_eq hτ.symm
  have hτU : ((ineIncl h τ : Weil h) : G F Ω) ∈ U.toSubgroup := by
    rw [hτeq, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpow) hsU
  have hτ1 : χ (ineIncl h τ) = 1 := by
    have : τ ∈ {σ : Ine (F := F) A | χ (ineIncl h σ) = 1} := by
      rw [← hOeq]
      exact hUO hτU
    exact this
  rw [hτ, map_mul, map_zpow, hfr, hτ1, one_mul]

theorem UpperTheory.V.Loc.charExt :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)] (ξ : (w.adicCompletion F)ˣ →* Rˣ), UpperTheory.V.Alg.AdicCont (IsLocalRing.maximalIdeal R) (fun x => (ξ x : R)) → ∃! ψ : ↥(Dec (F := F) A) →* Rˣ, UpperTheory.V.Alg.AdicCont (IsLocalRing.maximalIdeal R) (fun g => (ψ g : R)) ∧ OnArt a ψ Set.univ ξ := by
  intro _ F Ω _ _ _ _ _ A w h a ha R _ _ _ _ _ ξ hξ
  classical
  set i : Weil h →* Dec (F := F) A := Subgroup.inclusion (Weil_le_Dec h) with hi_def
  have hi : DenseRange i := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  set χ : Weil h →* Rˣ := ξ.comp a with hχ_def
  have H : ∀ N : ℕ, ∃ ψ : Dec (F := F) A →* R ⧸ IsLocalRing.maximalIdeal R ^ N, IsLocallyConstant ψ ∧
      ∀ s, ψ (i s) = Ideal.Quotient.mk _ (χ s : R) := by
    intro N
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := (inferInstance : Finite (IsLocalRing.ResidueField R))
    haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    let χN : Weil h →* (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ :=
      (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)).toMonoidHom).comp χ
    have hloc : IsLocallyConstant fun σ : Ine (F := F) A => χN (ineIncl h σ) := by
      refine IsLocallyConstant.desc _ (fun u : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ => (u : R ⧸ IsLocalRing.maximalIdeal R ^ N)) ?_ Units.val_injective
      exact (hξ N).comp_continuous ha.cont
    obtain ⟨V, hVn, hVo, hV⟩ := ce_open h χN hloc
    let V' : Subgroup (Dec (F := F) A) := V.comap (Dec (F := F) A).subtype
    haveI : V'.Normal := hVn.comap _
    have hV'o : IsOpen (V' : Set (Dec (F := F) A)) := hVo.preimage continuous_subtype_val
    obtain ⟨ψ, hψl, hψ⟩ := ce_ext i hi χN V' hV'o (fun s hs => hV s hs)
    refine ⟨(Units.coeHom _).comp ψ, hψl.comp (fun u : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ => (u : R ⧸ IsLocalRing.maximalIdeal R ^ N)), fun s => ?_⟩
    show ((ψ (i s) : (R ⧸ IsLocalRing.maximalIdeal R ^ N)ˣ) : R ⧸ IsLocalRing.maximalIdeal R ^ N) = _
    rw [hψ s]
    rfl
  obtain ⟨ψ, ⟨hψc, hψs⟩, huniq⟩ := ce_lim (IsLocalRing.maximalIdeal R) i hi χ H
  refine ⟨ψ, ⟨hψc, ?_⟩, ?_⟩
  · intro s g hgs _
    have hg : g = i s := Subtype.ext hgs
    rw [hg, hψs]
    rfl
  · rintro ψ' ⟨hc, hon⟩
    exact huniq ψ' ⟨hc, fun s => hon s (i s) rfl trivial⟩
