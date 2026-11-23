import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem qz_total (l : ℕ) [Fact l.Prime] (a b : QZ l) : ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
  have key : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
    intro x y h
    by_cases hy : y = 0
    · subst hy
      exact ⟨0, by simpa using h⟩
    · refine ⟨⟨x / y, ?_⟩, ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · show x = x / y * y
        field_simp
  rcases le_total ‖x‖ ‖y‖ with h | h
  · obtain ⟨c, hc⟩ := key x y h
    exact ⟨c, Or.inl (congrArg (Submodule.Quotient.mk (p := ZlSub l)) hc)⟩
  · obtain ⟨c, hc⟩ := key y x h
    exact ⟨c, Or.inr (congrArg (Submodule.Quotient.mk (p := ZlSub l)) hc)⟩

private theorem len_le_one (l : ℕ) [Fact l.Prime] (K : Type) [AddCommGroup K] [Module ℤ_[l] K]
    (h1 : ∀ x : K, (l : ℤ_[l]) • x = 0) (h2 : ∀ a b : K, ∃ c : ℤ_[l], a = c • b ∨ b = c • a) :
    Module.length ℤ_[l] K ≤ 1 := by
  rcases subsingleton_or_nontrivial K with h | h
  · simp
  haveI : IsSimpleModule ℤ_[l] K := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    refine or_iff_not_imp_left.2 fun hN => eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    obtain ⟨c, hc | hc⟩ := h2 x y
    · by_cases hu : IsUnit c
      · obtain ⟨u, rfl⟩ := hu
        have : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by rw [hc, smul_smul, Units.inv_mul, one_smul]
        rw [this]; exact N.smul_mem _ hx
      · have hm : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
        obtain ⟨d, rfl⟩ := hm
        rw [mul_smul, h1, smul_zero] at hc
        exact absurd hc hx0
    · rw [hc]; exact N.smul_mem _ hx
  exact (Module.length_eq_one ℤ_[l] K).le

section Index

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M)
  (H : Subgroup Γ) (hH : ∀ g g', g ∉ H → g' ∉ H → g * g' ∈ H)
include hH

private theorem val_eq (z : Z1 ρ) (hz : ∀ g ∈ H, z.1 g = 0) {g g' : Γ} (hg : g ∉ H) (hg' : g' ∉ H) :
    z.1 g' = z.1 g := by
  have h := z.2.2 g (g⁻¹ * g')
  rw [hz _ (hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) hg'), map_zero, add_zero, mul_inv_cancel_left] at h
  exact h

private theorem two_smul_mk (z : Z1 ρ) (hz : ∀ g ∈ H, z.1 g = 0) {g₀ : Γ} (hg₀ : g₀ ∉ H) :
    (2 : R) • (Submodule.Quotient.mk z : H1 ρ) = 0 := by
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨-z.1 g₀, fun g => ?_⟩)
  show (2 : R) • z.1 g = _
  by_cases hg : g ∈ H
  · have h := z.2.2 g g₀
    rw [val_eq ρ H hH z hz hg₀ (fun h => hg₀ ((H.mul_mem_cancel_left hg).1 h)), hz g hg, zero_add] at h
    rw [hz g hg, map_neg, ← h, sub_self, smul_zero]
  · have h := z.2.2 g g₀
    rw [hz _ (hH _ _ hg hg₀), val_eq ρ H hH z hz hg₀ hg] at h
    rw [val_eq ρ H hH z hz hg₀ hg, map_neg, two_smul, ← eq_neg_of_add_eq_zero_left h.symm, sub_neg_eq_add]

private theorem eq_smul_of_val (z z' : Z1 ρ) (hz : ∀ g ∈ H, z.1 g = 0) (hz' : ∀ g ∈ H, z'.1 g = 0) {g₀ : Γ}
    (hg₀ : g₀ ∉ H) (c : R) (h : z.1 g₀ = c • z'.1 g₀) : z = c • z' := by
  refine Subtype.ext (funext fun g => ?_)
  show z.1 g = c • z'.1 g
  by_cases hg : g ∈ H
  · rw [hz g hg, hz' g hg, smul_zero]
  · rw [val_eq ρ H hH z hz hg₀ hg, val_eq ρ H hH z' hz' hg₀ hg, h]

end Index

private theorem mul_mem_princ (u v : ℤ_[2]ˣ) (hu : u ∉ KStar.TotallyRealRoots.princ 2 2) (hv : v ∉ KStar.TotallyRealRoots.princ 2 2) :
    u * v ∈ KStar.TotallyRealRoots.princ 2 2 := by
  have key : ∀ a b : (ZMod 4)ˣ, a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
  rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker] at *
  rw [map_mul]
  exact key _ _ hu hv

private theorem exists_vanish (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (D : LData F Ω 2) (e : ℤ) (he : e ≠ 0) (x : H1 (qzTw D e)) (hx : resInf D e x = 0) :
    ∃ z : Z1 (qzTw D e), x = Submodule.Quotient.mk z ∧
      ∀ g ∈ (KStar.TotallyRealRoots.princ 2 2).comap D.chi, z.1 g = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let H : Subgroup (G F Ω) := (KStar.TotallyRealRoots.princ 2 2).comap (cycZ F Ω 2)
  have hcl : IsClosed (H : Set (G F Ω)) :=
    ((KStar.TotallyRealRoots.princ 2 2).isClosed_of_isOpen (KStar.TotallyRealRoots.isOpen_princ 2)).preimage (continuous_cycZ F Ω 2)
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (G F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[F] Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hcl.isCompact
  let χ : H →* ℤ_[2]ˣ := (cycZ F Ω 2).comp H.subtype
  have hχ : Continuous χ := (continuous_cycZ F Ω 2).comp continuous_subtype_val
  have hV : IsClosed (χ.range : Set ℤ_[2]ˣ) := (isCompact_range hχ).isClosed
  obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := existsGen 2 χ.range hV (Or.inr (by rintro _ ⟨g, rfl⟩; exact g.2))
  have hne : χ γ ^ (-e) ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := KStar.Tree.exists_cyc_pow_ne_one 2 F Ω (2 * e.natAbs) (by omega)
    have hg2 : g * g ∈ H := by
      by_cases h : g ∈ H
      · exact H.mul_mem h h
      · show cycZ F Ω 2 (g * g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [map_mul]
        exact mul_mem_princ _ _ h h
    have hc : IsClosed (((zpowGroupHom (-e) : ℤ_[2]ˣ →* ℤ_[2]ˣ).ker : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
      isClosed_singleton.preimage (continuous_zpow (-e))
    have h3 := Subgroup.topologicalClosure_minimal _ ((Subgroup.zpowers_le (H := (zpowGroupHom (-e) : ℤ_[2]ˣ →* ℤ_[2]ˣ).ker)).2 h) hc
      (hγ ⟨⟨_, hg2⟩, rfl⟩)
    have h4 : (cycZ F Ω 2 (g * g)) ^ (-e) = 1 := h3
    apply hg
    show cycZ F Ω 2 g ^ (2 * e.natAbs) = 1
    rw [pow_mul, sq, ← map_mul, pow_natAbs_eq_one, ← inv_eq_one, ← zpow_neg]
    exact h4
  let φ : H →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := (toGS Ω _).comp H.subtype
  have hφ : Continuous φ := (continuous_toGS Ω _).comp continuous_subtype_val
  have hchi : ∀ g : H, D.chi (φ g) = χ g := fun g => DFunLike.congr_fun D.hchi g.1
  have hB := cobOfGen 2 H χ ℤ_[2] (QZ 2) ((qzTw D e).comp φ) γ hχ
    ((contTw F Ω 2 D e).1.comp (hφ.prodMap continuous_id))
    (fun g hg m => by
      show qzTw D e (φ g) m = m
      rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul])
    (fun g => hγ ⟨g, rfl⟩)
    (by
      have := (qzBasic 2).1 (((χ γ ^ (-e) : ℤ_[2]ˣ) : ℤ_[2]) - 1)
        (fun h => hne (Units.ext (sub_eq_zero.1 h)))
      intro m
      obtain ⟨a, ha⟩ := this m
      refine ⟨a, ?_⟩
      show qzTw D e (φ γ) a - a = m
      rw [qzTw_apply, hchi, ← ha]
      beta_reduce
      rw [sub_smul, one_smul])
    (fun g => z.1 (φ g)) ⟨z.2.1.comp hφ, fun a b => by beta_reduce; rw [map_mul, z.2.2]; rfl⟩
    (fun g hg => congrFun hx ⟨g.1, trivial, hg⟩)
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hB
  have hb : d0 (qzTw D e) m ∈ B1 (qzTw D e) := ⟨m, rfl⟩
  refine ⟨z - ⟨_, coboundaries_le_cocycles _ (contTw F Ω 2 D e).1 hb⟩, ?_, fun g hg => ?_⟩
  · exact (Submodule.Quotient.eq _).2 (by rw [sub_sub_cancel]; exact hb)
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hg' : g ∈ H := by
      have : D.chi (toGS Ω _ g) = cycZ F Ω 2 g := DFunLike.congr_fun D.hchi g
      show cycZ F Ω 2 g ∈ KStar.TotallyRealRoots.princ 2 2
      rw [← this]; exact hg
    exact sub_eq_zero.2 (hm ⟨g, hg'⟩)

theorem UpperTheory.V.Kum.resInfKer :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Module.length ℤ_[l] (LinearMap.ker (resInf D e)) ≤ errTwo l := by
  intro F Ω _ _ _ _ _ l _ D e he
  by_cases hP : Procyc F Ω l
  · rw [LinearMap.ker_eq_bot.2 (resInfInj F Ω l D e he hP)]
    simp
  · rw [Procyc, not_or, not_not, not_forall] at hP
    obtain ⟨rfl, g, hg⟩ := hP
    have hg₀ : toGS Ω _ g ∉ (KStar.TotallyRealRoots.princ 2 2).comap D.chi := by
      intro h
      have : D.chi (toGS Ω _ g) = cycZ F Ω 2 g := DFunLike.congr_fun D.hchi g
      rw [Subgroup.mem_comap, this] at h
      exact hg h
    have hH : ∀ a b, a ∉ (KStar.TotallyRealRoots.princ 2 2).comap D.chi → b ∉ (KStar.TotallyRealRoots.princ 2 2).comap D.chi →
        a * b ∈ (KStar.TotallyRealRoots.princ 2 2).comap D.chi := fun a b ha hb => by
      rw [Subgroup.mem_comap, map_mul]
      exact mul_mem_princ _ _ ha hb
    rw [errTwo, if_pos rfl]
    refine len_le_one 2 _ (fun x => Subtype.ext ?_) fun a b => ?_
    · obtain ⟨z, hz, h0⟩ := exists_vanish F Ω D e he x.1 x.2
      show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
      rw [hz, Nat.cast_ofNat]
      exact two_smul_mk _ _ hH z h0 hg₀
    · obtain ⟨z, hz, h0⟩ := exists_vanish F Ω D e he a.1 a.2
      obtain ⟨z', hz', h0'⟩ := exists_vanish F Ω D e he b.1 b.2
      obtain ⟨c, hc | hc⟩ := qz_total 2 (z.1 (toGS Ω _ g)) (z'.1 (toGS Ω _ g))
      · refine ⟨c, Or.inl (Subtype.ext ?_)⟩
        show a.1 = c • b.1
        rw [hz, hz', eq_smul_of_val _ _ hH z z' h0 h0' hg₀ c hc, Submodule.Quotient.mk_smul]
      · refine ⟨c, Or.inr (Subtype.ext ?_)⟩
        show b.1 = c • a.1
        rw [hz, hz', eq_smul_of_val _ _ hH z' z h0' h0 hg₀ c hc, Submodule.Quotient.mk_smul]
