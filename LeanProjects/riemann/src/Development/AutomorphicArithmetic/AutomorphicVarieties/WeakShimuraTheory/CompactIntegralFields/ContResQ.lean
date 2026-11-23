import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private theorem lc_ker {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group M]
    (φ : H →* M) (h : IsOpen (φ.ker : Set H)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H)) := h.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy
  have : φ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

private theorem fin_chars (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [hl : Fact l.Prime] (N : ℕ) (hN : N ≠ 0) (K H : Subgroup (G F Ω)) (hK : IsOpen (K : Set (G F Ω)))
    (hH : IsOpen (H : Set (G F Ω))) (M : Subgroup (G F Ω))
    (hM : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := F) A, g ∈ K → g ∈ M) :
    Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : G F Ω) ∈ M → φ g = 1} := by
  haveI : IsGalois F Ω := {}
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let V : Subgroup (G F Ω) := (H ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ
  have hVo : IsOpen (V : Set (G F Ω)) := (hH.inter hK).inter (stabilizer_isOpen_of_isIntegral ζ)
  let E : IntermediateField F Ω := IntermediateField.fixedField V
  have hE : E.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)
  haveI : NumberField E := NumberField.of_module_finite F E
  have hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V := fun σ => by
    rw [← hE, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => σ.commutes ⟨x, hx⟩
  have hgal : V ≤ Base.galOf F E Ω := fun u hu x => x.2 ⟨u, hu⟩
  have hζE : ζ ∈ E := fun v => v.2.2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective
  haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype
  let e : G E Ω →* H := (Base.galEmb F E Ω).codRestrict H fun σ => (hmem σ).1.1
  have he : Continuous e := ((Base.galEmbTop F E Ω).1.continuous).subtype_mk _
  haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo
  have hfin : Finite (H ⧸ e.range) := by
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have h2 : V.subgroupOf H ≤ e.range := fun x hx => ⟨Kum.toGal E hgal ⟨x, hx⟩, Subtype.ext rfl⟩
    haveI := Subgroup.finiteIndex_of_le h2
    infer_instance
  refine Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} ×
      (H ⧸ e.range → Multiplicative (ZMod l)))
    (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e g)), ((lc_ker φ.1 φ.2.1).comp_continuous he).comp _,
      fun a b => by simp only [map_mul, toAdd_mul], fun A hA g hg => by
        show Multiplicative.toAdd (φ.1 (e g)) = 0
        rw [φ.2.2 (e g) (hM A hA _ ⟨hg.1, hg.2⟩ (hmem g).1.2), toAdd_one]⟩, fun q => φ.1 q.out)) ?_
  intro φ ψ h
  have h1 : ∀ g, φ.1 (e g) = ψ.1 (e g) := fun g =>
    Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)
  have h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out := congrFun (congrArg Prod.snd h)
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := QuotientGroup.mk_out_eq_mul e.range x
  have h3 := h2 (QuotientGroup.mk x)
  rw [hg, map_mul, map_mul, h1] at h3
  exact mul_right_cancel h3

private theorem l_mem {l : ℕ} [Fact l.Prime] (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
  rwa [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0

private theorem char_res {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : CharP (ResidueField c.O) l :=
  (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact l_mem c)

private theorem inc_max {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) :
    ∀ x ∈ maximalIdeal c.O, inc h x ∈ maximalIdeal c'.O := by
  letI : Algebra c.O c'.O := (inc h).toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite ℤ_[l] c'.O := inferInstance
  haveI : Module.Finite c.O c'.O := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul c.O c'.O := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective h)
  haveI : Algebra.IsIntegral c.O c'.O := Algebra.IsIntegral.of_finite _ _
  haveI : IsLocalHom (algebraMap c.O c'.O) := Algebra.IsIntegral.isLocalHom _ _
  exact fun x hx => map_nonunit (algebraMap c.O c'.O) x hx

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem cont_resQ (T : Tower D) : Continuous (resQ T.F) := (Base.galEmbTop ℚ T.F Ω).1.continuous

private theorem ok_of (hD : D.Good) (T : Tower D) (hT : T.Ok) (W : Finset ℕ) (k : Type) [Field k] (a : c.O →+* k)
    (ha : ∀ x ∈ maximalIdeal c.O, a x = 0) : (T.fr W).Ok a := by
  obtain ⟨-, -, -, -, -, f6, -, -, -, -, f11, -⟩ := facts D hD
  let j : ResidueField c.O →+* k := Ideal.Quotient.lift _ a ha
  have hj : ∀ x, a x = j (residue c.O x) := fun _ => rfl
  haveI := char_res c
  refine ⟨fun i g => ?_, ?_, fun i i' hi => ?_, ?_, fun i => ?_⟩
  · have e : lab T.pr i.rev = (lab T.pr i).rev := by
      generalize T.pr = b
      revert b i
      decide
    show D.ps (lab T.pr i) (resQ T.F g) * D.ps (lab T.pr i.rev) (resQ T.F g) = D.th (resQ T.F g)
    rw [e, ← f6 (lab T.pr i)]
    rfl
  · rintro g ⟨A, -, -, hg⟩ i
    have h1 : residue c.O (D.ps (lab T.pr i) (resQ T.F g) : c.O) = 1 := by
      simpa [Raw.rbar, Raw.r0, diagRep] using congrFun (congrFun hg (lab T.pr i)) (lab T.pr i)
    rw [hj, ← map_one j]
    exact congrArg j h1
  · rw [hj, hj, ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 (hT.dist i i' hi))).map j
  · have h2 : (2 : ResidueField c.O) ≠ 0 := fun h => hD.l_odd
      ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff (ResidueField c.O) l 2).1 (by exact_mod_cast h)))
    simpa only [map_ofNat] using (IsUnit.mk0 _ h2).map j
  · exact ((f11 (lab T.pr i) 1).comp_continuous (cont_resQ T)).comp
      (Ideal.Quotient.lift _ a fun x hx => ha x (by rwa [pow_one] at hx))

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.std :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (W : Finset ℕ) (c' : Coef l) (h : c.O ≤ c'.O), (0 ∉ W → (T.fr W).Std l (inc h)) ∧ ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr W).Ok a := by
  intro hP Ω _ _ _ l hl c D T hT W c' h
  have hD : D.Good := hT.2.elim (fun x => x.1.1) fun x => x.1.1
  refine ⟨fun hW => ?_, ok_of hD T hT.1 W⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, f11, f12, -⟩ := facts D hD
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  have ok : (T.fr W).Ok ((residue c'.O).comp (inc h)) :=
    ok_of hD T hT.1 W _ _ fun x hx => (residue_eq_zero_iff _).2 (inc_max h x hx)
  haveI := char_res c'
  refine ⟨ok, char_res c', fun i n => ?_, fun H hH _ => ?_, fun v => isClosed_Dec _, fun v => ?_, ?_⟩
  · exact ((f11 (lab T.pr i) n).comp_continuous (cont_resQ T)).comp
      (Ideal.quotientMap (maximalIdeal c'.O ^ n) (inc h)
        ((Ideal.pow_right_mono (fun x hx => inc_max h x hx) n).trans (Ideal.le_comap_pow _ n)))
  · refine fin_chars T.F Ω l (∏ p ∈ insert l W, p) (Finset.prod_ne_zero_iff.2 fun p hp => ?_)
      (D.rbar.ker.comap (resQ T.F)) H (f12.preimage (cont_resQ T)) hH _ fun A hA g hg hg' => ?_
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hl.out.ne_zero
      · exact fun e => hW (e ▸ hp)
    · refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, fun p hp hpA => hA ?_, hg, hg'⟩)
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
      rw [hm, Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (natCast_mem A m))) hpA
  · have hA : T.pl v ≠ ⊤ := fun e => by
      have h1 := T.ovl v
      have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
      have h2 := ((T.pl v).valuation_le_one_iff (l : Ω)⁻¹).2 (e ▸ ValuationSubring.mem_top _)
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0))] at h2
      exact absurd h1 (not_lt.2 h2)
    obtain ⟨w, hw⟩ := (Kum.placeDict T.F Ω).2.1 _ hA
    exact Pa.phiDec hP.loc.lf l T.F Ω _ w hw
  · rintro v s ⟨hs, m, hm⟩
    refine ⟨hs, fun i => ?_⟩
    let γ : G T.F Ω →* (ResidueField c'.O)ˣ := (Units.map ((residue c'.O).comp (inc h)).toMonoidHom).comp ((T.fr W).χ i)
    have ho : IsClosed (γ.ker : Set (G T.F Ω)) := by
      have e : (γ.ker : Set (G T.F Ω)) = {g | ((residue c'.O).comp (inc h)) ((T.fr W).χ i g) = 1} :=
        Set.ext fun g => Units.ext_iff
      rw [e]
      exact (ok.lc i).isClosed_fiber 1
    have h1 : γ (s ^ l ^ m) = 1 := Subgroup.topologicalClosure_minimal _
      ((Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker γ)) ho hm
    rw [map_pow] at h1
    have h2 : ((γ s : ResidueField c'.O) - 1) ^ l ^ m = 0 := by
      rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero) |>.1 h2)
