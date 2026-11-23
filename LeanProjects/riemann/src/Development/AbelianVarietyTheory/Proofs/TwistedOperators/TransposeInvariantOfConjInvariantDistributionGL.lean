import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatDistributionEqZeroBaireStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixConjTransposeBySymmetricTausskyZassenhausStatement

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology

noncomputable section

namespace GlobalTheory.GelfandKazhdan

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def pull (t : G ≃ₜ G) : SB G →ₗ[ℂ] SB G where
  toFun φ := ⟨fun x => φ.1 (t x), φ.2.1.comp_continuous t.continuous, φ.2.2.comp_homeomorph t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [TopologicalSpace G] in
theorem anti_one {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) : t 1 = 1 := by
  have := hm 1 1
  rw [one_mul] at this
  exact left_eq_mul.1 this

omit [TopologicalSpace G] in
theorem anti_inv {t : G → G} (hm : ∀ x y, t (x * y) = t y * t x) (x : G) : t x⁻¹ = (t x)⁻¹ := by
  have := hm x x⁻¹
  rw [mul_inv_cancel, anti_one hm] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem exists_stable (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x) (ht : ∀ x, t (t x) = x)
    (K₀ : Subgroup G) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) :
    ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ (∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧ ∀ j ∈ J, t j ∈ J := by
  intro U hU
  obtain ⟨J, ho, hJU, hJK, hn⟩ := hb U hU
  refine ⟨{ carrier := {y | y ∈ J ∧ t y ∈ J}
            mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, by rw [hm]; exact mul_mem hb.2 ha.2⟩
            one_mem' := ⟨one_mem _, by rw [anti_one hm]; exact one_mem _⟩
            inv_mem' := fun ha => ⟨inv_mem ha.1, by rw [anti_inv hm]; exact inv_mem ha.2⟩ },
    ho.inter (ho.preimage t.continuous), fun y hy => hJU hy.1, fun y hy => hJK hy.1,
    fun x hx j hj => ⟨hn x hx j hj.1, ?_⟩, fun j hj => ⟨hj.2, by rw [ht]; exact hj.1⟩⟩
  have := hn _ (inv_mem (hK x hx)) _ hj.2
  rw [hm, hm, anti_inv hm, ← mul_assoc]
  rwa [inv_inv] at this

theorem invariant_of_anti [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x)
    (ht : ∀ x, t (t x) = x) (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G))
    (hKc : IsCompact (K₀ : Set G)) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hs : ∀ x, ∃ s, t s = s ∧ s * x = t x * s) (T : SB G →ₗ[ℂ] ℂ)
    (hT : ∀ (g : G) (φ ψ : SB G), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) (φ : SB G) :
    T (pull t φ) = T φ := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose J hJo hJU hJK hJn hJt using fun m =>
    exists_stable t hm ht K₀ hK hb (U m) (hU.1.mem_of_mem trivial)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable S := hSc.to_subtype
  let K : S → ℕ → Subgroup G := fun c m => J m ⊓ (J m).comap (MulAut.conj (c : G)).toMonoidHom
  have hKm : ∀ c m y, y ∈ K c m ↔ y ∈ J m ∧ (c : G) * y * (c : G)⁻¹ ∈ J m := fun c m y => Iff.rfl
  have hD : T - T.comp (pull t) = 0 := by
    refine GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire G S K (fun c m => ?_) (fun c V hV => ?_) _ fun x => ?_
    · have ho : IsOpen (K c m : Set G) :=
        (hJo m).inter ((hJo m).preimage (f := fun y => (c : G) * y * (c : G)⁻¹) (by fun_prop))
      exact ⟨ho, hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun y hy => hJK m hy.1⟩
    · obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hV
      exact ⟨m, fun y hy => hm (hJU m hy.1)⟩
    · obtain ⟨s, hts, hsx⟩ := hs x
      obtain ⟨c, hc, hcS⟩ := hSd.inter_open_nonempty _
        (hKo.preimage (f := fun y => y * s⁻¹) (by fun_prop)) ⟨s, by simp⟩
      have hc' : c * s⁻¹ ∈ K₀ := hc
      refine ⟨⟨c, hcS⟩, fun m ψ hψ => ?_⟩
      have hK' : ∀ y, y ∈ K ⟨c, hcS⟩ m ↔ y ∈ J m ∧ s * y * s⁻¹ ∈ J m := fun y => by
        rw [hKm]
        refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · have := hJn m _ (inv_mem hc') _ h
          convert this using 1
          simp only []
          group
        · have := hJn m _ hc' _ h
          convert this using 1
          simp only []
          group
      have hτ : ∀ y, t (s * y * s⁻¹) = s⁻¹ * t y * s := fun y => by
        rw [hm, hm, anti_inv hm, hts, mul_assoc]
      have hτK : ∀ y ∈ K ⟨c, hcS⟩ m, s⁻¹ * t y * s ∈ K ⟨c, hcS⟩ m := fun y hy => by
        rw [hK'] at hy ⊢
        refine ⟨hτ y ▸ hJt m _ hy.2, ?_⟩
        convert hJt m _ hy.1 using 1
        group
      have h1 : ∀ y, y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} →
          s⁻¹ * t y * s ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨_, hτK b hb, _, hτK a ha, ?_⟩
        have : t x = s * x * s⁻¹ := by rw [hsx]; group
        rw [hm, hm, this]
        group
      have h2 : ∀ y, s⁻¹ * t (s⁻¹ * t y * s) * s = y := fun y => by
        rw [hm, hm, anti_inv hm, hts, ht]
        group
      have h3 : T ψ = T (pull t ψ) := hT s _ _ fun y => by
        show ψ.1 y = ψ.1 (t (s * y * s⁻¹))
        rw [hτ, hψ]
        by_cases hy : y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h1 y hy)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h => hy (h2 y ▸ h1 _ h)]
      exact sub_eq_zero.2 h3
  exact (sub_eq_zero.1 (LinearMap.congr_fun hD φ)).symm

end General

section Transpose

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trGL (g : GL n R) : GL n R :=
  ⟨g.val.transpose, g.inv.transpose, by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]⟩

theorem trGL_trGL (g : GL n R) : trGL (trGL g) = g := rfl

theorem trGL_mul (g h : GL n R) : trGL (g * h) = trGL h * trGL g :=
  Units.ext (Matrix.transpose_mul _ _)

theorem continuous_trGL [TopologicalSpace R] : Continuous (trGL : GL n R → GL n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩

def trHomeo [TopologicalSpace R] : GL n R ≃ₜ GL n R where
  toFun := trGL
  invFun := trGL
  left_inv := trGL_trGL
  right_inv := trGL_trGL
  continuous_toFun := continuous_trGL
  continuous_invFun := continuous_trGL

end Transpose

theorem transpose_invariant (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (T : SB (GL n k) →ₗ[ℂ] ℂ)
    (hT : ∀ (g : GL n k) (φ ψ : SB (GL n k)), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ)
    (φ ψ : SB (GL n k)) (h : ∀ x y : GL n k, y.val = x.val.transpose → ψ.1 x = φ.1 y) :
    T ψ = T φ := by
  have e : ψ = pull trHomeo φ := Subtype.ext (funext fun x => h x (trGL x) rfl)
  rw [e]
  refine invariant_of_anti trHomeo trGL_mul trGL_trGL (KO k n) SplitFlip.isOpen_KO
    SplitFlip.isCompact_KO (fun x hx => ?_) (exists_open_normalised_subgroup_subset k n)
    (fun x => ?_) T hT φ
  · obtain ⟨h1, h2⟩ := (SplitFlip.mem_KO_iff _).1 hx
    exact (SplitFlip.mem_KO_iff _).2 ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  · obtain ⟨P, ⟨s, rfl⟩, h1, h2⟩ := GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus k n x.val
    exact ⟨s, Units.ext h1, Units.ext h2⟩

end GlobalTheory.GelfandKazhdan
