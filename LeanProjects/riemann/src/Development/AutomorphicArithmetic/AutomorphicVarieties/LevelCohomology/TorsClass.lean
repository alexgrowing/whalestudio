import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KwlOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Control
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem sep_tors {M : Type} [AddCommGroup M] (l : ℕ) [Fact l.Prime] (x : AddSubgroup.torsionBy M l)
    (h : ∀ φ : AddSubgroup.torsionBy M l →+ ZMod l, φ x = 0) : x = 0 := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod l) (AddSubgroup.torsionBy M l) := AddSubgroup.torsionBy.zmodModule
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod l) x).1 fun φ => h φ.toAddMonoidHom

private theorem hom_kill (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    {M : Type} [AddCommGroup M] (f : G ℚ Ω → M) (h1 : IsLocallyConstant f) (h2 : ∀ a b, f (a * b) = f a + f b)
    (h3 : ∀ g, l • f g = 0)
    (h4 : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, f g = 0) :
    ∀ g ∈ cycU l (⊤ : Subgroup (G ℚ Ω)), f g = 0 := by
  intro g hg
  have hmu : g ∈ fixMu ℚ Ω (l ^ 2) := by
    rw [(fixLev ℚ Ω l 1 2).1]
    exact cycU_le_levU l ⊤ 2 hg
  have hx : f g ∈ AddSubgroup.torsionBy M l := AddSubgroup.torsionBy.nsmul_iff.2 (h3 g)
  have key : (⟨f g, hx⟩ : AddSubgroup.torsionBy M l) = 0 := by
    apply sep_tors l
    intro φ
    let ι : G ℚ Ω → AddSubgroup.torsionBy M l := fun a => ⟨f a, AddSubgroup.torsionBy.nsmul_iff.2 (h3 a)⟩
    have hι : IsLocallyConstant ι := by
      intro s
      have hpre : ι ⁻¹' s = f ⁻¹' (Subtype.val '' s) := by
        ext a
        simp only [ι, Set.mem_preimage, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun h => ⟨AddSubgroup.torsionBy.nsmul_iff.2 (h3 a), h⟩, fun ⟨_, h⟩ => h⟩
      rw [hpre]
      exact h1 _
    have hψ : (fun a => φ (ι a)) ∈ UnrHom ℚ Ω l := by
      refine ⟨hι.comp φ, ?_, ?_⟩
      · intro a b
        show φ (ι (a * b)) = φ (ι a) + φ (ι b)
        rw [← map_add]
        congr 1
        exact Subtype.ext (h2 a b)
      · intro A hA g' hg'
        show φ (ι g') = 0
        have h0 : ι g' = 0 := Subtype.ext (h4 A hA g' hg')
        rw [h0, map_zero]
    exact kwl Ω l hl _ hψ g hmu
  simpa using congrArg Subtype.val key

private theorem pow_cong (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ) (e : ℕ) (he : l - 1 ∣ e) :
    (l : ℤ_[l]) ∣ ((u ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  have hker : ∀ x : ℤ_[l], PadicInt.toZMod x = 0 → (l : ℤ_[l]) ∣ x := by
    intro x hx
    have hmem : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hx
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact hmem
  apply hker
  have hw : (Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u) ^ (-(e : ℤ)) = 1 := by
    obtain ⟨k, rfl⟩ := he
    rw [zpow_neg, zpow_natCast, pow_mul, ZMod.units_pow_card_sub_one_eq_one, one_pow, inv_one]
  have hmap : PadicInt.toZMod ((u ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) =
      (((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u) ^ (-(e : ℤ)) : (ZMod l)ˣ) : ZMod l) := by
    rw [← map_zpow]
    rfl
  rw [map_sub, hmap, hw, Units.val_one, map_one, sub_self]

private theorem tors_class {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [DiscreteTopology M] (ρ : Representation R Γ M) (l : ℕ) (h : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) (x : H1 ρ) :
    ∃ n : ℕ, (l : R) ^ n • x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hfin : (Set.range (z : Γ → M)).Finite := (isCompact_range z.2.1).finite_of_discrete
  choose N hN using h
  refine ⟨hfin.toFinset.sup N, ?_⟩
  have hbound : ∀ g, l ^ (hfin.toFinset.sup N) • (z : Γ → M) g = 0 := by
    intro g
    have hle : N ((z : Γ → M) g) ≤ hfin.toFinset.sup N :=
      Finset.le_sup (f := N) (by simp)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, add_comm, pow_add, mul_smul, hN, smul_zero]
  have hzero : ((l : R) ^ (hfin.toFinset.sup N) • z : Z1 ρ) = 0 := by
    apply Subtype.ext
    funext g
    show ((l : R) ^ (hfin.toFinset.sup N) • (z : Γ → M)) g = 0
    rw [Pi.smul_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hbound g
  rw [← Submodule.Quotient.mk_smul, hzero, Submodule.Quotient.mk_zero]

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.X.zOne :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], l ≠ 2 → ∀ e : ℕ, 1 ≤ e → l - 1 ∣ e → Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ hl e he1 he
  classical
  show Module.length O (ShaU (twist₂ l ((1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)))) l ⊤) = 0
  rw [inv_one]
  have act : ∀ (g : G ℚ Ω) (m : QO l O), (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) g m =
      algebraMap ℤ_[l] O (((cycZ ℚ Ω l g ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) • m := by
    intro g m
    simp [twist₂, scalRep_apply, chiO]
  have hcontm : ∀ m₀ : QO l O, Continuous fun g : G ℚ Ω => (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) g m₀ := by
    intro m₀
    have hcontρ : Continuous fun p : G ℚ Ω × QO l O => (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) p.1 p.2 :=
      (contTw ℚ Ω l).2.2 O 1 (-(e : ℤ)) (by simp)
    have hpair : Continuous fun g : G ℚ Ω => ((g, m₀) : G ℚ Ω × QO l O) :=
      Continuous.prodMk continuous_id continuous_const
    have h := hcontρ.comp hpair
    exact h
  set ρ : Representation O (G ℚ Ω) (QO l O) := twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ))) with hρ
  have hl0 : (l : O) ≠ 0 := by
    have hinj := (UpperTheory.V.Base.dvrFacts l O).1
    intro h
    have h' : ((l : ℤ_[l])) = 0 := hinj (by simpa using h)
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have trivl : ∀ (g : G ℚ Ω) (y : QO l O), l • y = 0 → ρ g y = y := by
    intro g y hy
    obtain ⟨c, hc⟩ := pow_cong l (cycZ ℚ Ω l g) e he
    have hA : algebraMap ℤ_[l] O (((cycZ ℚ Ω l g ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) =
        1 + (l : O) * algebraMap ℤ_[l] O c := by
      rw [← map_natCast (algebraMap ℤ_[l] O), ← map_mul, ← hc, ← map_one (algebraMap ℤ_[l] O), ← map_add]
      congr 1
      ring
    rw [act, hA, add_smul, one_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hy, smul_zero, add_zero]
  have trivk : ∀ g ∈ (cycZ ℚ Ω l).ker, ∀ m : QO l O, ρ g m = m := by
    intro g hg m
    rw [act, (MonoidHom.mem_ker).1 hg]
    simp
  have hctrl := (control ℚ Ω l O (⊤ : Subgroup (G ℚ Ω)) (by simp) (Or.inl hl) 1 (-(e : ℤ)) (by simp)
    (by omega)).1
  have hzero : ∀ x : ShaU ρ l ⊤, (l : O) • x = 0 → x = 0 := by
    intro x hx
    apply hctrl
    rw [map_zero]
    obtain ⟨y, hyS⟩ := x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx' : (l : O) • (Submodule.Quotient.mk z : H1U ρ ⊤) = 0 := by
      simpa using congrArg Subtype.val hx
    obtain ⟨m, hm⟩ := (mk_eq_mk ρ ⊤ ((l : O) • z) 0).1
      (by rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_zero]; exact hx')
    simp only [Submodule.coe_smul, Submodule.coe_zero, Pi.smul_apply, Pi.zero_apply, sub_zero] at hm
    obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 (l : O) hl0 m
    let z' : G ℚ Ω → QO l O := fun g => (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m')
    have htors : ∀ g, l • z' g = 0 := by
      intro g
      rw [← Nat.cast_smul_eq_nsmul O]
      show (l : O) • ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m')) = 0
      rw [smul_sub, smul_sub, ← map_smul, hm', hm ⟨g, trivial⟩]
      exact sub_self _
    have hcz : ∀ a b : G ℚ Ω, (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a * b, trivial⟩ =
        (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a, trivial⟩ + ρ a ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨b, trivial⟩) :=
      fun a b => z.2.2 ⟨a, trivial⟩ ⟨b, trivial⟩
    have hadd : ∀ a b, z' (a * b) = z' a + z' b := by
      intro a b
      have hc : z' (a * b) = z' a + ρ a (z' b) := by
        show (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a * b, trivial⟩ - (ρ (a * b) m' - m') =
          (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a, trivial⟩ - (ρ a m' - m') +
            ρ a ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨b, trivial⟩ - (ρ b m' - m'))
        rw [hcz, map_mul, Module.End.mul_apply, map_sub, map_sub]
        abel
      rw [hc, trivl a _ (htors b)]
    have hlc : IsLocallyConstant z' := by
      rw [IsLocallyConstant.iff_continuous]
      have h1 : Continuous fun g : G ℚ Ω => (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ :=
        z.2.1.comp (continuous_id.subtype_mk fun _ => trivial)
      exact h1.sub ((hcontm m').sub continuous_const)
    have hunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, z' g = 0 := by
      intro A hA g hg
      obtain ⟨m₁, hm₁⟩ := (mk_mem_locSel.1 hyS) (Ine (F := ℚ) A) (Or.inr ⟨A, rfl⟩)
      have hgk : g ∈ (cycZ ℚ Ω l).ker := (places ℚ Ω l A).2.2.2 hA hg
      have hzg : (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ = ρ g m₁ - m₁ := hm₁ ⟨g, trivial⟩ hg
      show (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m') = 0
      rw [hzg, trivk g hgk m₁, trivk g hgk m', sub_self, sub_self, sub_self]
    have hk := hom_kill Ω l hl z' hlc hadd htors hunr
    apply Subtype.ext
    rw [selRes, LinearMap.restrict_apply]
    show resU ρ _ (Submodule.Quotient.mk z) = 0
    rw [resU_mk_eq_zero]
    refine ⟨m', fun u => ?_⟩
    have hu := hk u u.2
    exact sub_eq_zero.1 hu
  haveI : CompactSpace (⊤ : Subgroup (G ℚ Ω)) := isCompact_iff_compactSpace.mp (by simpa using isCompact_univ)
  have hgen : ∀ n : ℕ, ∀ x : ShaU ρ l ⊤, (l : O) ^ n • x = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply hzero
      rw [smul_smul, ← pow_succ']
      exact hx
  have hall : ∀ x : ShaU ρ l ⊤, x = 0 := by
    intro x
    obtain ⟨n, hn⟩ := tors_class (ρ.comp (⊤ : Subgroup (G ℚ Ω)).subtype) l (qoFacts l O).2.1 (x : H1U ρ ⊤)
    exact hgen n x (Subtype.ext (by simpa using hn))
  rw [Module.length_eq_zero_iff]
  exact ⟨fun a b => by rw [hall a, hall b]⟩
