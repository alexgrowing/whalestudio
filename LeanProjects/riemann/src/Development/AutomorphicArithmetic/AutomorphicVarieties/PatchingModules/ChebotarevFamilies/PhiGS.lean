import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have e : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = ((g⁻¹ • x).out : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hm := QuotientGroup.eq.mp e
  simpa [mul_inv_rev, mul_assoc] using hm

private theorem core_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H K : Subgroup Γ)
    [Finite (Γ ⧸ H)] (hK : IsOpen (K : Set Γ)) (hKH : K ≤ H) :
    ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧ ∀ k ∈ U, ∀ y : Γ ⧸ H, (y.out)⁻¹ * k * y.out ∈ K ∧ k • y = y := by
  refine ⟨⋂ y : Γ ⧸ H, (fun k => (y.out)⁻¹ * k * y.out) ⁻¹' (K : Set Γ), ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun y =>
      hK.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · simp
  · intro k hk y
    have hy : (y.out)⁻¹ * k * y.out ∈ K := Set.mem_iInter.mp hk y
    refine ⟨hy, ?_⟩
    rw [← QuotientGroup.out_eq' y, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have hi := H.inv_mem (hKH hy)
    simpa [mul_assoc] using hi

private theorem mult_map_mul_right_eq_of_chi_eq_one {Γ : Type} [Group Γ] (H : Subgroup Γ) (g g' : Γ) (x : Γ ⧸ H)
    (h : (g⁻¹ * g') • (g⁻¹ • x) = g⁻¹ • x) : g'⁻¹ • x = g⁻¹ • x := by
  calc g'⁻¹ • x = (g⁻¹ * g')⁻¹ • (g⁻¹ • x) := by
        rw [← mul_smul]
        congr 1
        group
    _ = g⁻¹ • x := by rw [inv_smul_eq_iff, h]

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  obtain ⟨U₀, hU₀o, hU₀1, hU₀⟩ := core_lemma H H hH le_rfl
  have hρ : ContAction (permR (ZMod n) H) := by
    show Continuous fun p : Γ × (Γ ⧸ H → ZMod n) => permR (ZMod n) H p.1 p.2
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨g, m⟩
    have hmem : {p : Γ × (Γ ⧸ H → ZMod n) | g⁻¹ * p.1 ∈ U₀ ∧ p.2 = m} ∈ nhds (g, m) := by
      apply IsOpen.mem_nhds
      · exact (hU₀o.preimage (continuous_const.mul continuous_fst)).inter
          ((isOpen_discrete {m}).preimage continuous_snd)
      · simp [hU₀1]
    filter_upwards [hmem] with p hp
    obtain ⟨hk, hp2⟩ := hp
    show permR (ZMod n) H p.1 p.2 = permR (ZMod n) H g m
    rw [hp2]
    funext y
    rw [permR_apply, permR_apply, mult_map_mul_right_eq_of_chi_eq_one H g p.1 y (hU₀ _ hk (g⁻¹ • y)).2]
  have hcoc : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) →
      (fun (g : Γ) (x : Γ ⧸ H) => Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩))
        ∈ Z1 (permR (ZMod n) H) := by
    intro φ hφ
    show Continuous _ ∧ _
    constructor
    · have hKo : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
        rw [Subgroup.coe_map]
        exact hH.isOpenMap_subtype_val _ hφ
      obtain ⟨U, hUo, hU1, hU⟩ := core_lemma H (φ.ker.map H.subtype) hKo (Subgroup.map_subtype_le _)
      apply IsLocallyConstant.continuous
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have hmem : {g' : Γ | g⁻¹ * g' ∈ U} ∈ nhds g :=
        (hUo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [hU1])
      filter_upwards [hmem] with g' hk
      funext x
      obtain ⟨hK, hfix⟩ := hU _ hk (g⁻¹ • x)
      obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.mp hK
      have e1 := mult_map_mul_right_eq_of_chi_eq_one H g g' x hfix
      have e2 : (⟨(x.out)⁻¹ * g' * (g'⁻¹ • x).out, sec_mem H g' x⟩ : H) =
          ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩ * b := by
        apply Subtype.ext
        show (x.out)⁻¹ * g' * (g'⁻¹ • x).out = (x.out)⁻¹ * g * (g⁻¹ • x).out * (b : Γ)
        rw [show (b : Γ) = _ from hbv, e1]
        group
      show Multiplicative.toAdd (φ _) = Multiplicative.toAdd (φ _)
      rw [e2, map_mul, (MonoidHom.mem_ker).mp hb, mul_one]
    · intro g h
      funext x
      simp only [Pi.add_apply, permR_apply]
      rw [← toAdd_mul, ← map_mul]
      refine congrArg (fun y : H => Multiplicative.toAdd (φ y)) (Subtype.ext ?_)
      show (x.out)⁻¹ * (g * h) * ((g * h)⁻¹ • x).out =
        (x.out)⁻¹ * g * (g⁻¹ • x).out * (((g⁻¹ • x).out)⁻¹ * h * (h⁻¹ • (g⁻¹ • x)).out)
      rw [mul_inv_rev, mul_smul]
      group
  haveI := h (Γ ⧸ H → ZMod n) (permR (ZMod n) H) hρ
  refine Finite.of_injective (fun χ : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} =>
    (Submodule.Quotient.mk ⟨_, hcoc χ.1 χ.2⟩ : H1 (permR (ZMod n) H))) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp ((Submodule.Quotient.eq _).mp hEq))
  apply Subtype.ext
  ext h0
  obtain ⟨x0, hx0⟩ : ∃ x0 : Γ ⧸ H, x0 = ((1 : Γ) : Γ ⧸ H) := ⟨_, rfl⟩
  have ha : x0.out ∈ H := by
    have e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) := by rw [QuotientGroup.out_eq', hx0]
    simpa using H.inv_mem (QuotientGroup.eq.mp e)
  obtain ⟨g, hg⟩ : ∃ g : Γ, g = x0.out * h0 * (x0.out)⁻¹ := ⟨_, rfl⟩
  have hgH : g ∈ H := hg ▸ H.mul_mem (H.mul_mem ha h0.2) (H.inv_mem ha)
  have hgx0 : g⁻¹ • x0 = x0 := by
    rw [hx0, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using hgH
  have hel : ∀ (y : Γ ⧸ H) (hy : y = g⁻¹ • x0) (pr : (x0.out)⁻¹ * g * y.out ∈ H),
      (⟨(x0.out)⁻¹ * g * y.out, pr⟩ : H) = h0 := by
    intro y hy pr
    apply Subtype.ext
    show (x0.out)⁻¹ * g * y.out = (h0 : Γ)
    rw [hy, hgx0, hg]
    group
  have hx : m (g⁻¹ • x0) - m x0 =
      Multiplicative.toAdd (φ ⟨(x0.out)⁻¹ * g * (g⁻¹ • x0).out, sec_mem H g x0⟩) -
        Multiplicative.toAdd (ψ ⟨(x0.out)⁻¹ * g * (g⁻¹ • x0).out, sec_mem H g x0⟩) :=
    congrFun (congrFun hm g) x0
  rw [hel _ rfl, hgx0, sub_self] at hx
  have hx' : (0 : ZMod n) = Multiplicative.toAdd (φ h0) - Multiplicative.toAdd (ψ h0) := hx
  have h2 : Multiplicative.toAdd (φ h0) = Multiplicative.toAdd (ψ h0) :=
    (sub_eq_zero (G := ZMod n)).mp hx'.symm
  exact Multiplicative.toAdd.injective h2

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.phiGS :
    GlobalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), PhiCond V.frame.Γ l := by
  intro hGF l _ L Ω _ _ _ _ _ _ s V
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Plc (Lp L)), (S : Set (Plc (Lp L))) = V.S' :=
    ⟨V.fin.toFinset, V.fin.coe_toFinset⟩
  show PhiCond (ReciprocityTheory.Gal.GS Ω V.S') l
  rw [← hS]
  have key : PhiCond (ReciprocityTheory.Gal.GS Ω (S : Set (Plc (Lp L)))) (l ^ 1) := by
    apply phi_condition_of_finite_cohomology
    intro M _ _ _ _ _ ρ hρ
    have habove : ReciprocityTheory.Gal.ContainsAbove S l := by
      intro v hv
      have hv' : v ∈ V.S' := V.sub (Or.inl hv)
      rw [← hS] at hv'
      exact_mod_cast hv'
    exact (hGF (Lp L) Ω l 1 M S ρ one_pos habove hρ).2.1
  rw [pow_one] at key
  exact key
