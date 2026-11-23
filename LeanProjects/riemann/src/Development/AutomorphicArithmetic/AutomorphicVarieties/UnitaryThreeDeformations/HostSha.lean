import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaAbsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactorGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem len_union {R H : Type} [CommRing R] [AddCommGroup H] [Module R H] (T : Submodule R H)
    (P : ℕ → Submodule R H) (hm : Monotone P) (hT : ∀ x ∈ T, ∃ k, x ∈ P k) (V : ℕ)
    (hV : ∀ k, Module.length R (P k) ≤ V) : Module.length R T ≤ V := by
  simp only [Module.length_submodule] at hV ⊢
  have hlt : ⨆ k, Order.height (P k) < ⊤ := lt_of_le_of_lt (iSup_le hV) (ENat.coe_lt_top V)
  obtain ⟨k, hk⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  refine le_trans (Order.height_mono fun x hx => ?_) (hV k)
  obtain ⟨k', hk'⟩ := hT x hx
  have h1 : P k = P (max k k') := by
    by_contra h
    have h2 := Order.height_strictMono (lt_of_le_of_ne (hm (le_max_left k k')) h) (hk ▸ hlt)
    exact absurd h2 (not_lt.2 (hk ▸ le_iSup (fun k => Order.height (P k)) _))
  exact h1 ▸ hm (le_max_right k k') hk'

section

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type} (F : Frame O G Γ ι)
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]

private theorem tors_le (hF : F.Ok) (a : O) (j : OQ a →ₗ[O] M) (hj : Function.Injective j)
    (hr : ∀ m : M, a • m = 0 → ∃ y, j y = m) (hd : ∀ m : M, ∃ m', a • m' = m)
    (ρ : Representation O Γ M) (hρ : ρ = Formalism.GaloisCohomology.scalRep M F.Ψ⁻¹) (hcont : ContAction ρ) (P : Submodule O (H1 ρ))
    (hP : ∀ z : Z1 ρ, Submodule.Quotient.mk z ∈ P →
      ∀ v, ∃ m, ∀ g : F.D v, z.1 (F.loc v g) = ρ (F.loc v g) m - m)
    (ha : ∀ x ∈ P, a • x = 0) : Module.length O P ≤ F.shaLen a := by
  have he : ∀ g y, j (oqRep F.Ψ⁻¹ a g y) = ρ g (j y) := fun g y => hρ ▸ map_smul j _ y
  let J := mapH1 (oqRep F.Ψ⁻¹ a) ρ j continuous_of_discreteTopology he
  have hle : P ≤ (F.ShaO a).map J := by
    intro x hx
    obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h0 : (a • z₀).1 ∈ B1 ρ := (Submodule.Quotient.mk_eq_zero ((B1 ρ).comap (Z1 ρ).subtype) (x := a • z₀)).1 (ha _ hx)
    obtain ⟨m₀, hm₀⟩ := (mem_coboundaries1 _ _).1 h0
    obtain ⟨m₁, rfl⟩ := hd m₀
    have hm₁ : ∀ g, a • z₀.1 g = ρ g (a • m₁) - a • m₁ := hm₀
    have hk : ∀ g, a • (z₀.1 g - (ρ g m₁ - m₁)) = 0 := fun g => by
      rw [smul_sub, hm₁, map_smul, smul_sub, sub_self]
    choose y hy using fun g => hr _ (hk g)
    have hc : Continuous fun g => ρ g m₁ := hcont.comp (Continuous.prodMk_left m₁)
    have hyZ : y ∈ Z1 (oqRep F.Ψ⁻¹ a) := by
      refine ⟨?_, fun g h => hj ?_⟩
      · have h1 : Continuous (j ∘ y) := by
          rw [show j ∘ y = _ from funext hy]
          exact z₀.2.1.sub (hc.sub continuous_const)
        exact (((IsLocallyConstant.iff_continuous _).2 h1).desc _ _ hj).continuous
      · rw [map_add, he, hy, hy, hy, z₀.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
        abel
    have hloc : ∀ v, ∃ m, ∀ g : F.D v, j (y (F.loc v g)) = ρ (F.loc v g) m - m := fun v => by
      obtain ⟨m, hm⟩ := hP z₀ hx v
      refine ⟨m - m₁, fun g => ?_⟩
      rw [hy, hm, map_sub]
      abel
    refine ⟨Submodule.Quotient.mk ⟨y, hyZ⟩, Submodule.subset_span ⟨⟨y, hyZ⟩, rfl, fun v hv s hs => hj ?_, fun v hv => ?_⟩, ?_⟩
    · obtain ⟨m, hm⟩ := hloc v
      have h1 : F.Ψ (F.loc v s) = 1 := hF.teich v hv s hs
      show j (y _) = _
      rw [hm, map_zero]
      simp [hρ, h1]
    · obtain ⟨m, hm⟩ := hloc v
      obtain ⟨x, -, hx⟩ := hF.x v hv
      have h1 : IsUnit ((F.Ψ (F.loc v x) : O) - 1) := by
        have : ((F.Ψv v x : Oˣ) : O) ^ 2 - 1 = ((F.Ψ (F.loc v x) : O) - 1) * ((F.Ψ (F.loc v x) : O) + 1) := by
          show ((F.Ψ (F.loc v x) : Oˣ) : O) ^ 2 - 1 = _
          ring
        exact isUnit_of_mul_isUnit_left (this ▸ hx)
      have h2 : a • (ρ (F.loc v x) m - m) = 0 := by
        rw [← hm, hy, hk]
      have h3 : a • m = 0 := by
        refine h1.smul_eq_zero.1 ?_
        have h4 := congrArg (fun t => -((F.Ψ (F.loc v x) : Oˣ) : O) • t) h2
        simp only [hρ, Formalism.GaloisCohomology.scalRep_apply, MonoidHom.inv_apply, smul_zero] at h4
        rw [← h4, smul_comm _ a, smul_comm _ a, smul_sub, smul_smul _ _ m, smul_smul _ _ m, ← sub_smul, smul_smul]
        congr 2
        rw [neg_mul, Units.mul_inv]
        ring
      obtain ⟨m', rfl⟩ := hr m h3
      exact ⟨m', fun g => hj (by rw [map_sub, he]; exact hm g)⟩
    · refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨-m₁, fun g => ?_⟩)
      show j (y g) - z₀.1 g = _
      rw [hy, map_neg]
      abel
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans
    (Module.length_le_of_surjective (J.submoduleMap _) (LinearMap.submoduleMap_surjective _ _))

private theorem sha_le [CompactSpace Γ] (hF : F.Ok) (p : O) (htor : ∀ m : M, ∃ n : ℕ, p ^ n • m = 0)
    (hex : ∀ k : ℕ, ∃ w : M, (∀ y : O, y • w = 0 ↔ p ^ k ∣ y) ∧ ∀ m : M, p ^ k • m = 0 → ∃ y : O, m = y • w)
    (hd : ∀ (k : ℕ) (m : M), ∃ m', p ^ k • m' = m)
    (ρ : Representation O Γ M) (hρ : ρ = Formalism.GaloisCohomology.scalRep M F.Ψ⁻¹) (hcont : ContAction ρ)
    {D : ι → Type} [∀ v, Group (D v)] [∀ v, TopologicalSpace (D v)] (φ : ∀ v, D v →* Γ) (hφ : ∀ v, Continuous (φ v))
    (hD : ∀ v (g : F.D v), ∃ g', φ v g' = F.loc v g) (V : ℕ) (hV : ∀ k : ℕ, F.shaLen (p ^ k) ≤ V) :
    Module.length O (Sha1 ρ φ hφ) ≤ V := by
  refine len_union _ (fun k => Sha1 ρ φ hφ ⊓ Submodule.torsionBy O _ (p ^ k)) (fun k k' h => inf_le_inf_left _
      (Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ h))) (fun x hx => ?_) V fun k => ?_
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hfin : (Set.range z.1).Finite := (isCompact_range z.2.1).finite_of_discrete
    choose n hn using htor
    obtain ⟨k, hk⟩ := (hfin.image n).bddAbove
    refine ⟨k, hx, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩
    have h0 : p ^ k • z = 0 := Subtype.ext (funext fun g => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' (hk ⟨_, ⟨g, rfl⟩, rfl⟩)
      show p ^ (d + n (z.1 g)) • z.1 g = 0
      rw [pow_add, mul_smul, hn, smul_zero])
    rw [← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]
  · obtain ⟨w, hw, hgen⟩ := hex k
    have hker : Ideal.span {p ^ k} = LinearMap.ker (LinearMap.toSpanSingleton O _ w) := by
      ext y
      rw [Ideal.mem_span_singleton, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hw]
    refine le_trans (tors_le F hF (p ^ k) (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ w) hker.le)
      (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hker.ge)) (fun m hm => ?_) (hd k)
      ρ hρ hcont _ (fun z hz v => ?_) fun x hx => hx.2) (hV k)
    · obtain ⟨y, rfl⟩ := hgen m hm
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
    · have h1 := (Submodule.mem_iInf _).1 hz.1 v
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h1))
      refine ⟨m, fun g => ?_⟩
      obtain ⟨g', hg⟩ := hD v g
      rw [← hg]
      exact hm g'

end

theorem UpperTheory.V.UnitaryThreeInertia.vlen_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ V : ℕ, (∀ a : c.O, a ≠ 0 → F.shaLen a ≤ V) → Vlen Ω c e ψ ≤ V := by
  intro Ω _ _ _ l hl c N _ e ψ o₁ hH S A F hF V hV
  have hok := hostFrame_ok Ω c e ψ o₁ hH S A F hF
  have hS : (S : Set Pl) = Formalism.GaloisCohomology.Above ℚ (l * N) := Set.ext hF.mem
  have hsurj : Function.Surjective (toGS (F := ℚ) Ω (S : Set Pl)) := QuotientGroup.mk_surjective
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : CompactSpace (Gam Ω S) := hsurj.compactSpace (continuous_toGS Ω _)
  obtain ⟨θ, hθ, hc⟩ := Chr.factorGS ℚ Ω l c.O N e (Chr.dirG ℚ Ω ψ)
    (fun g hg => by
      show ψ.toUnitHom (Chr.cls ℚ Ω N g) = 1
      rw [MonoidHom.mem_ker.1 hg, map_one]) S hS
  have hθ' : θ = F.Ψ⁻¹ := MonoidHom.ext fun g => by
    obtain ⟨g, rfl⟩ := hsurj g
    have h1 := DFunLike.congr_fun hθ g
    have h2 := DFunLike.congr_fun hF.Ψ g
    rw [hF.π] at h2
    exact h1.trans (congrArg Inv.inv h2.symm)
  have hlen := (Chr.litV ℚ Ω l c.O e (Chr.dirG ℚ Ω ψ)).1 (l * N) S A
    (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) hS hF.isOver θ hθ hc
  refine le_of_eq_of_le hlen.symm ?_
  obtain ⟨-, htor, hdiv, -⟩ := Base.qoFacts l c.O
  obtain ⟨-, hex, hgen, -⟩ := ML.qoCyc l c.O
  have hl0 : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine sha_le F hok (l : c.O) (fun m => ?_) (fun k => ?_) (fun k => hdiv _ (pow_ne_zero k hl0)) (Base.twist₂ l θ)
    (by rw [hθ']) hc _ _ (fun v g => ⟨⟨g.1, hF.D v ▸ g.2⟩, ?_⟩) V fun k => hV _ (pow_ne_zero k hl0)
  · obtain ⟨n, hn⟩ := htor m
    exact ⟨n, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn]⟩
  · obtain ⟨w, hw⟩ := hex _ (pow_ne_zero k hl0)
    exact ⟨w, hw, hgen _ w (pow_ne_zero k hl0) hw⟩
  · show toGS Ω _ g.1 = F.π g.1
    rw [hF.π]
