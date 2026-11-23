import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllipticCurveLatticeBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.CommonField

def Curve {R : Type} [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) : Prop :=
  P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)

def HomOf {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A)
    (Q : Out.PolAV (Sp R)) (t : epsR R ⟶ Q.A) (a : R₁) : Prop :=
  ∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)

theorem Curve.isTangent {R : Type} [CommRing R] {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A}
    {Lf : (R →+* ℂ) → PeriodPair} (h : Curve P v Lf) : IsTangent v := by
  obtain ⟨-, hb, -, -⟩ := h
  unfold IsLieBasis at hb
  exact hb.1 0

theorem HomOf.up (hB : Out.PolBaseChangeSt) {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁]
    {ρ : R →+* R₀} {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} {Q : Out.PolAV (Sp R)} {t : epsR R ⟶ Q.A} {a : R₀}
    (h : HomOf ρ P v Q t a) (g : R₀ →+* R₁) : HomOf (g.comp ρ) P v Q t (g a) := by
  obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB ρ P
  obtain ⟨Q₀, ψ, hψ⟩ := exists_isPolFibre hB ρ Q
  obtain ⟨v₀, hv, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  obtain ⟨t₀, ht, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
  obtain ⟨f, hf, hfa⟩ := h P₀ Q₀ φ ψ v₀ t₀ hφ hψ hv ht
  exact hom_deriv_baseChange R P Q v t R₀ ρ P₀ Q₀ φ ψ v₀ t₀ f a hφ hψ hv ht hf hfa R₁ g

theorem HomOf.fibre {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁]
    {f : R →+* R₀} {g : R₀ →+* R₁} {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} {Q : Out.PolAV (Sp R)}
    {t : epsR R ⟶ Q.A} {a : R₁} (h : HomOf (g.comp f) P v Q t a)
    {P₀ Q₀ : Out.PolAV (Sp R₀)} {φ : P₀.A.left ⟶ P.A.left} {ψ : Q₀.A.left ⟶ Q.A.left} {v₀ : epsR R₀ ⟶ P₀.A}
    {t₀ : epsR R₀ ⟶ Q₀.A} (hφ : IsPolFibre f P P₀ φ) (hψ : IsPolFibre f Q Q₀ ψ) (hv : IsVecOver f φ v v₀)
    (ht : IsVecOver f ψ t t₀) : HomOf g P₀ v₀ Q₀ t₀ a := by
  intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ h₁ h₂ h₃ h₄
  have w₁ : φ₁ ≫ P₀.A.hom = P₁.A.hom ≫ spMap g := h₁.2.1.1.w
  have w₂ : ψ₁ ≫ Q₀.A.hom = Q₁.A.hom ≫ spMap g := h₂.2.1.1.w
  exact h P₁ Q₁ (φ₁ ≫ φ) (ψ₁ ≫ ψ) v₁ t₁ (PolFibre.comp hφ h₁) (PolFibre.comp hψ h₂)
    ((PolFibre.vec_iff hφ.2.1.1 w₁ hv).1 h₃) ((PolFibre.vec_iff hψ.2.1.1 w₂ ht).1 h₄)

def multipliers (L L' : PeriodPair) : Submodule ℤ ℂ where
  carrier := {α | ∀ z ∈ L.lattice, α * z ∈ L'.lattice}
  add_mem' ha hb z hz := by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
  zero_mem' z _ := by rw [zero_mul]; exact zero_mem _
  smul_mem' n a ha z hz := by rw [smul_mul_assoc]; exact Submodule.smul_mem _ n (ha z hz)

theorem multipliers_fg (L L' : PeriodPair) : (multipliers L L').FG := by

  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hle : (multipliers L L').map (LinearMap.mulRight ℤ L.ω₁) ≤ L'.lattice := by
    rintro _ ⟨α, hα, rfl⟩
    exact hα _ L.ω₁_mem_lattice
  have hfg : L'.lattice.FG := Submodule.fg_span (Set.toFinite _)
  exact Submodule.fg_of_fg_map_injective _ (mul_left_injective₀ hω) (hfg.of_le hle)

def DefinedOver {R : Type} [CommRing R] {k : IntermediateField ℚ ℂ} (ρ : R →+* k) (P : Out.PolAV (Sp R))
    (v : epsR R ⟶ P.A) (Q : Out.PolAV (Sp R)) (t : epsR R ⟶ Q.A) (N : IntermediateField ℚ ℂ) (α : ℂ) : Prop :=
  ∃ (hk : k ≤ N) (a : N), (a : ℂ) = α ∧ HomOf ((IntermediateField.inclusion hk).toRingHom.comp ρ) P v Q t a

theorem DefinedOver.mono (hB : Out.PolBaseChangeSt) {R : Type} [CommRing R] {k : IntermediateField ℚ ℂ}
    {ρ : R →+* k} {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} {Q : Out.PolAV (Sp R)} {t : epsR R ⟶ Q.A}
    {N N' : IntermediateField ℚ ℂ} {α : ℂ} (h : DefinedOver ρ P v Q t N α) (hN : N ≤ N') :
    DefinedOver ρ P v Q t N' α := by
  obtain ⟨hk, a, ha, hh⟩ := h
  refine ⟨hk.trans hN, IntermediateField.inclusion hN a, ha, ?_⟩
  have e : (IntermediateField.inclusion (hk.trans hN)).toRingHom.comp ρ =
      (IntermediateField.inclusion hN).toRingHom.comp ((IntermediateField.inclusion hk).toRingHom.comp ρ) := by
    ext; rfl
  rw [e]
  exact hh.up hB _

theorem exists_field (hU : ThetaUnifAV) (hB : Out.PolBaseChangeSt) {R : Type} [CommRing R]
    {k : IntermediateField ℚ ℂ} [FiniteDimensional ℚ k] (ρ : R →+* k) {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A}
    {Q : Out.PolAV (Sp R)} {t : epsR R ⟶ Q.A} {L L' : (R →+* ℂ) → PeriodPair} (hP : Curve P v L)
    (hQ : Curve Q t L') : ∃ N : IntermediateField ℚ ℂ, FiniteDimensional ℚ N ∧ k ≤ N ∧
      ∀ α : ℂ, (∀ z ∈ (L ((algebraMap k ℂ).comp ρ)).lattice, α * z ∈ (L' ((algebraMap k ℂ).comp ρ)).lattice) →
        DefinedOver ρ P v Q t N α := by
  classical
  have hv := hP.isTangent
  have ht := hQ.isTangent
  set s := (algebraMap k ℂ).comp ρ with hs
  obtain ⟨G, hG⟩ := multipliers_fg (L s) (L' s)

  have key : ∀ α ∈ multipliers (L s) (L' s),
      ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ DefinedOver ρ P v Q t K₁ α := by
    intro α hα
    have hhom := (EllipticHom.multiplier_iff_exists_hom hU hB R P Q v t s (L s) (L' s) α hP.1 hQ.1 hv ht
      (hP.2.2.2 s) (hQ.2.2.2 s)).1 hα
    obtain ⟨K₁, hk, a, hK, ha, hh⟩ :=
      hom_deriv_descends_to_numberField hU hB R P Q v t k ρ α inferInstance hv hQ.2.2.1 hhom
    exact ⟨K₁, hK, hk, a, ha, hh⟩
  choose! K hK hD using key
  have hGm : ∀ β ∈ G, β ∈ multipliers (L s) (L' s) := fun β hβ => hG ▸ Submodule.subset_span hβ
  have : ∀ β : G, FiniteDimensional ℚ (K β) := fun β => hK β (hGm β β.2)

  let N : IntermediateField ℚ ℂ := k ⊔ ⨆ β : G, K β
  have hkN : k ≤ N := le_sup_left
  refine ⟨N, inferInstance, hkN, ?_⟩
  intro α hα
  let S : Set N := {a | HomOf ((IntermediateField.inclusion hkN).toRingHom.comp ρ) P v Q t a}
  let T : AddSubgroup ℂ := (AddSubgroup.closure S).map (algebraMap N ℂ).toAddMonoidHom
  have hGT : ∀ β ∈ G, β ∈ T := by
    intro β hβ
    have hKN : K β ≤ N := le_sup_of_le_right (le_iSup (fun (j : G) => K j) ⟨β, hβ⟩)
    obtain ⟨_, a, ha, hh⟩ := (hD β (hGm β hβ)).mono hB hKN
    exact ⟨a, AddSubgroup.subset_closure hh, ha⟩
  have hspan : multipliers (L s) (L' s) ≤ T.toIntSubmodule := by
    rw [← hG, Submodule.span_le]
    exact hGT
  obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 (hspan hα)
  exact ⟨hkN, a, rfl, HomDerivative.hom_derivative_closure hB R P Q v t N _ S ht (fun _ hb => hb) a ha⟩

theorem exists_common_field : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (K : Type) [Field
    K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀
    : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞
    K))), (∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞
    M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞
    K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+*
    ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧
    IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ'
    : P'.A.left ⟶ P.A.left) (v'
    : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞
    M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u'
    : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀
    s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t
    C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t
    C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L
    C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap
    M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞
    K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b
    : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞
    K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y
    : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) → ∃ (M
    : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v
    : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞
    M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ
    : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ'
    : P'.A.left ⟶ P.A.left) (v'
    : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞
    M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u'
    : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀
    s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t
    C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t
    C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L
    C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap
    M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞
    K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁
    : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁
    : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M)
    M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M)
    M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫
    f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁
    : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁
    : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M)
    M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M)
    M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t
    C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫
    f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q
    C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁
    : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M)
    M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M)
    M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫
    f₁)) := by
  intro hU hB K _ _ hK2 σ₀ hσ 𝔟 hyp
  classical
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, ⟨c, hc, hL₀⟩, β, hβ, h₁, h₂⟩ := hyp
  have cP : Curve P v L₀ := hP
  have cQ : ∀ C, Curve (Q C) (t C) (L C) := hQ

  obtain ⟨N₀, hN₀, hMN₀, hD₀⟩ := exists_field hU hB (algebraMap (𝓞 M) M) cP cP
  choose N₁ hN₁ hMN₁ hD₁ using fun C => exists_field hU hB (algebraMap (𝓞 M) M) cP (cQ C)
  choose N₂ hN₂ hMN₂ hD₂ using fun C => exists_field hU hB (algebraMap (𝓞 M) M) (cQ C) cP
  have : FiniteDimensional ℚ N₀ := hN₀
  have : ∀ C, FiniteDimensional ℚ (N₁ C) := hN₁
  have : ∀ C, FiniteDimensional ℚ (N₂ C) := hN₂
  let N : IntermediateField ℚ ℂ := N₀ ⊔ (⨆ C, N₁ C) ⊔ ⨆ C, N₂ C
  have l₀ : N₀ ≤ N := le_sup_left.trans le_sup_left
  have l₁ : ∀ C, N₁ C ≤ N := fun C => (le_iSup N₁ C).trans (le_sup_right.trans le_sup_left)
  have l₂ : ∀ C, N₂ C ≤ N := fun C => (le_iSup N₂ C).trans le_sup_right
  have hMN : M ≤ N := hMN₀.trans l₀
  have hNf : FiniteDimensional ℚ N := inferInstance
  have hNn : NumberField N := ⟨⟩

  let f : 𝓞 M →+* 𝓞 N := RingOfIntegers.mapRingHom (IntermediateField.inclusion hMN).toRingHom
  have ef : (algebraMap (𝓞 N) N).comp f =
      (IntermediateField.inclusion hMN).toRingHom.comp (algebraMap (𝓞 M) M) := by
    ext x; rfl
  have ec : ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp f =
      (algebraMap M ℂ).comp (algebraMap (𝓞 M) M) := by
    ext x; rfl
  obtain ⟨P', φ, hφ⟩ := exists_isPolFibre hB f P
  obtain ⟨v', hv, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  choose Q' ψ hψ using fun C => exists_isPolFibre hB f (Q C)
  choose t' ht using fun C => (existsUnique_isVecOver (hψ C).2.1.1 (t C)).exists

  have hb : ∀ C, ∃ b : N, (b : ℂ) = β C := by
    intro C
    have hm : ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice,
        β C * z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
      intro z hz
      have h := h₁ C 1 (fun b _ => by rw [_root_.one_mul]; exact RingOfIntegers.isIntegral_coe b) z hz
      rwa [_root_.map_one, _root_.mul_one] at h
    obtain ⟨_, b, hb, _⟩ := (hD₁ C (β C) hm).mono hB (l₁ C)
    exact ⟨b, hb⟩
  choose b hbv using hb
  refine ⟨N, hNn, (IntermediateField.inclusion hMN).toRingHom.comp κ, P', v', fun s => L₀ (s.comp f), Q', t',
    fun C s => L C (s.comp f), fun C => Units.map f.toMonoidHom (δ C), fun a => hκ a,
    curve_lattice_baseChange _ P v L₀ _ f P' φ v' hP hφ hv,
    fun C => curve_lattice_baseChange _ (Q C) (t C) (L C) _ f (Q' C) (ψ C) (t' C) (hQ C) (hψ C) (ht C),
    fun C s => hδ C (s.comp f), ⟨c, hc, fun z => ?_⟩, b, fun C h => hβ C ?_, ?_, ?_, ?_⟩
  · have h := hL₀ z
    rw [← ec] at h
    exact h
  · rw [← hbv C, h]
    rfl
  ·
    intro a
    have hm : ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice,
        σ₀ (a : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
      intro z hz
      obtain ⟨a', rfl⟩ := (hL₀ z).1 hz
      refine (hL₀ _).2 ⟨a * a', ?_⟩
      rw [show ((a * a' : 𝓞 K) : K) = (a : K) * a' from rfl, _root_.map_mul]
      ring
    obtain ⟨_, e, he, hh⟩ := (hD₀ _ hm).mono hB l₀
    have hee : e = (IntermediateField.inclusion hMN).toRingHom.comp κ (a : K) :=
      Subtype.ext (he.trans (hκ a).symm)
    have hh' : HomOf ((algebraMap (𝓞 N) N).comp f) P v P v e := by
      rw [ef]; exact hh
    have h := HomOf.fibre hh' hφ hφ hv hv
    rw [hee] at h
    exact h
  ·
    intro C x hx
    obtain ⟨_, e, he, hh⟩ := (hD₁ C _ (h₁ C x hx)).mono hB (l₁ C)
    have hee : e = b C * (IntermediateField.inclusion hMN).toRingHom.comp κ x := by
      apply Subtype.ext
      rw [he, IntermediateField.coe_mul, hbv C]
      exact congrArg (β C * ·) (hκ x).symm
    have hh' : HomOf ((algebraMap (𝓞 N) N).comp f) P v (Q C) (t C) e := by
      rw [ef]; exact hh
    have h := HomOf.fibre hh' hφ (hψ C) hv (ht C)
    rw [hee] at h
    exact h
  ·
    intro C y hy
    obtain ⟨_, e, he, hh⟩ := (hD₂ C _ (h₂ C y hy)).mono hB (l₂ C)
    have hee : e = (b C)⁻¹ * (IntermediateField.inclusion hMN).toRingHom.comp κ (y : K) := by
      apply Subtype.ext
      rw [he, IntermediateField.coe_mul, IntermediateField.coe_inv, hbv C]
      exact congrArg ((β C)⁻¹ * ·) (hκ y).symm
    have hh' : HomOf ((algebraMap (𝓞 N) N).comp f) (Q C) (t C) P v e := by
      rw [ef]; exact hh
    have h := HomOf.fibre hh' (hψ C) hφ (ht C) hv
    rw [hee] at h
    exact h

end GlobalTheory.CommonField
