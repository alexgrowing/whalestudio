import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PerSpan

theorem compact_alt_alt (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) :
    CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) ∧ T2Space (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  have := hA.proper
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hp : IsProjOver A.hom := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB A.hom).2
    ⟨inferInstance, H, GlobalTheory.isAmpleLB_of_veryAmpleBy hs⟩
  have h1 := PtsOver.compactSpace (F := ℂ) hp (𝟙 _)
  have h2 := PtsOver.t2Space (C := ℂ) A.hom (𝟙 _)
  exact ⟨(overHomeomorph A).symm.compactSpace, (overHomeomorph A).symm.t2Space⟩

theorem eq_top_of_compact_quotient (g : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] (π : (Fin g → ℂ) → H) (hadd : ∀ z w, π (z + w) = π z * π w) (hc : Continuous π)
    (hs : Function.Surjective π) (W : Submodule ℂ (Fin g → ℂ)) (hW : ∀ z, π z = 1 → z ∈ W) : W = ⊤ := by
  by_contra hne
  obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hne)
  let f : Multiplicative (Fin g → ℂ) →* H := MonoidHom.mk' (fun z => π z.toAdd) fun a b => hadd _ _
  have : SigmaCompactSpace (Multiplicative (Fin g → ℂ)) := inferInstanceAs (SigmaCompactSpace (Fin g → ℂ))
  have hopen : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hs hc
  have hU : IsOpen (π '' ball 0 1) := hopen _ (isOpen_ball (x := (0 : Fin g → ℂ)) (ε := 1))
  have h0 : π 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hne' : (interior (π '' ball 0 1)).Nonempty := by
    rw [hU.interior_eq]
    exact ⟨π 0, 0, mem_ball_self one_pos, rfl⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates (isCompact_univ (X := H)) hne'
  choose lift hlift using hs
  let ℓ' := LinearMap.toContinuousLinearMap ℓ
  have heq : ∀ a b, π a = π b → ℓ a = ℓ b := fun a b h => by
    have h1 : π (a - b) = 1 := by
      have := hadd (a - b) b
      rw [sub_add_cancel, h] at this
      exact right_eq_mul.1 this
    have h2 := hle (hW _ h1)
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
  have hbd : ∀ z, ‖ℓ z‖ ≤ ‖ℓ'‖ + ∑ c ∈ t, ‖ℓ (lift c)‖ := fun z => by
    obtain ⟨c, hct, hcz⟩ : ∃ c ∈ t, c * π z ∈ π '' ball 0 1 := by
      have := ht (Set.mem_univ (π z))
      simpa using this
    obtain ⟨w, hw, hwz⟩ := hcz
    have h1 : π w = π (lift c + z) := by rw [hwz, hadd, hlift]
    have h2 := heq _ _ h1
    rw [map_add] at h2
    have h3 : ℓ z = ℓ w - ℓ (lift c) := by rw [h2]; ring
    have h4 : ‖ℓ w‖ ≤ ‖ℓ'‖ := by
      have := ℓ'.le_opNorm w
      have hw' : ‖w‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hw).le
      calc ‖ℓ w‖ = ‖ℓ' w‖ := rfl
        _ ≤ ‖ℓ'‖ * ‖w‖ := this
        _ ≤ ‖ℓ'‖ * 1 := by gcongr
        _ = ‖ℓ'‖ := mul_one _
    have h5 : ‖ℓ (lift c)‖ ≤ ∑ c ∈ t, ‖ℓ (lift c)‖ :=
      Finset.single_le_sum (f := fun c => ‖ℓ (lift c)‖) (fun _ _ => norm_nonneg _) hct
    rw [h3]
    exact (norm_sub_le _ _).trans (add_le_add h4 h5)
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hℓ (LinearMap.ext hcon)
  set C := ‖ℓ'‖ + ∑ c ∈ t, ‖ℓ (lift c)‖
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 0)
  have := hbd (((C + 1 : ℝ) / ‖ℓ v‖ : ℂ) • v)
  rw [map_smul, smul_eq_mul, norm_mul] at this
  have hn : ‖ℓ v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have h6 : ‖((C + 1 : ℝ) / ‖ℓ v‖ : ℂ)‖ * ‖ℓ v‖ = C + 1 := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, norm_norm, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      div_mul_cancel₀ _ hn]
  linarith

section Fibre
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (x : Sp ℂ ⟶ Sp R)

def toFibre (p : Over.mk x ⟶ G) : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift p.left (𝟙 _) (by simpa using Over.w p)) (pullback.lift_snd _ _ _)

def ofFibre (y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) : Over.mk x ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h := Over.w y
    have h' : y.left ≫ pullback.snd G.hom x = 𝟙 _ := h
    simp only [Over.mk_left, Over.mk_hom, Category.assoc, pullback.condition]
    rw [← Category.assoc, h']
    exact Category.id_comp x)

theorem ofFibre_toFibre (p : Over.mk x ⟶ G) : ofFibre G x (toFibre G x p) = p :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

theorem toFibre_ofFibre (y : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) : toFibre G x (ofFibre G x y) = y := by
  refine Over.OverMorphism.ext ?_
  have h' : y.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w y
  refine pullback.hom_ext ?_ ?_
  · exact pullback.lift_fst _ _ _
  · exact (pullback.lift_snd _ _ _).trans h'.symm

theorem ofFibre_mul (y y' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback x).obj G) :
    ofFibre G x (y * y') = ofFibre G x y * ofFibre G x y' := by
  let ρ : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) := Over.homMk (𝟙 _) (by simp)
  have e : ∀ a, ofFibre G x a = ρ ≫ Out.toBase pullback.condition a := fun a =>
    Over.OverMorphism.ext (by simp [ofFibre, ρ, Out.toBase])
  rw [e, e, e, GlobalTheory.UU.toBase_mul_pullback, MonObj.comp_mul]

theorem toFibre_mul (p p' : Over.mk x ⟶ G) : toFibre G x (p * p') = toFibre G x p * toFibre G x p' := by
  have := ofFibre_mul G x (toFibre G x p) (toFibre G x p')
  rw [ofFibre_toFibre, ofFibre_toFibre] at this
  rw [← this, toFibre_ofFibre]

end Fibre

theorem ofFibre_one {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] (x : Sp ℂ ⟶ Sp R) :
    ofFibre G x 1 = 1 := by
  have := ofFibre_mul G x 1 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

theorem isHolTo_slice_at {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {b : V} (hb : b ∈ B) {c : V × V' → (Sp ℂ ⟶ X)}
    (h : IsHolTo (B ×ˢ Set.univ) c) : IsHolTo Set.univ (fun z => c (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : V' => (b, z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hb, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩

theorem isHolTo_ex_slice {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z => (e.ex b z).left) :=
  isHolTo_slice_at (V := Fin n → ℂ) (V' := Fin g → ℂ) (X := G.left) (b := b) (B := B)
    (c := fun bz => (e.ex bz.1 bz.2).left) hb e.hol

theorem isHolTo_snd {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {c : V' → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ c) :
    IsHolTo (Set.univ ×ˢ Set.univ) (fun p : V × V' => c p.2) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage (continuous_snd (X := V) (Y := V'))
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_self, true_and] using h3
  · exact h2.comp differentiable_snd.differentiableOn fun z hz => ⟨trivial, hz.2⟩

def famExpAtPoint {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ z := e.ex b z
  add _ _ z w := e.add b hb z w
  hol := isHolTo_snd (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (e.ex b z).left) (isHolTo_ex_slice e hb)
  diff _ _ a := e.diff b hb a
  log b₀ _ := by
    obtain ⟨V, N, f, L, h1, h2, h3, h4⟩ := e.log b hb
    have hφ : Continuous (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) := by fun_prop
    have hφ' : Continuous (fun p : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, p.2)) := by fun_prop
    refine ⟨V, N, f, fun p => L (b, p.2), h1, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp' (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) h2
        (analyticAt_const.prod analyticAt_snd)
    · exact (hφ'.tendsto (b₀, 0)).eventually h3
    · exact (hφ.tendsto (b₀, _)).eventually h4

theorem exists_linear_lift_at_point (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ) (b : Fin n → ℂ) (hb : b ∈ B) (m : ℕ) (u : (Fin m → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G))
    (hadd : ∀ z w, u (z + w) = u z * u w) (hhol : IsHolTo Set.univ (fun z => (u z).left)) :
    ∃ h : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e.ex b (h z) = u z := by
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (famExpAtPoint e hb) m Set.univ
    (fun _ z => u z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (u z).left) hhol)
  exact ⟨h 0, (hh 0 trivial).1⟩

section TorusExp

def gammaEquiv : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv

def expUnit (z : ℂ) : Γ(Sp ℂ, ⊤)ˣ :=
  Units.map gammaEquiv.symm.toRingHom.toMonoidHom (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))

theorem gamma_expUnit (z : ℂ) : gammaEquiv (expUnit z).val = Complex.exp z := gammaEquiv.apply_symm_apply _

theorem expUnit_ext {u v : Γ(Sp ℂ, ⊤)ˣ} (h : gammaEquiv u.val = gammaEquiv v.val) : u = v :=
  Units.ext (gammaEquiv.injective h)

theorem expUnit_add (z w : ℂ) : expUnit (z + w) = expUnit z * expUnit w :=
  expUnit_ext (by rw [Units.val_mul, map_mul, gamma_expUnit, gamma_expUnit, gamma_expUnit, Complex.exp_add])

theorem expUnit_eq_one {z : ℂ} (h : Complex.exp z = 1) : expUnit z = 1 :=
  expUnit_ext (by rw [gamma_expUnit, h, Units.val_one, map_one])

variable {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)

def pairing (w : Fin d → ℂ) (χ : X) : ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) * w a

theorem pairing_add_left (z w : Fin d → ℂ) (χ : X) : pairing β (z + w) χ = pairing β z χ + pairing β w χ := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_add_right (w : Fin d → ℂ) (χ χ' : X) : pairing β w (χ + χ') = pairing β w χ + pairing β w χ' := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_basis (w : Fin d → ℂ) (a : Fin d) : pairing β w (β a) = w a := by
  simp [pairing, Finsupp.single_apply]

def torusHom (w : Fin d → ℂ) : Multiplicative X →* Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ :=
  MonoidHom.mk' (fun χ => expUnit (pairing β w χ.toAdd)) fun χ χ' => by
    rw [toAdd_mul, pairing_add_right, expUnit_add]

def torusExp (w : Fin d → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X :=
  (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).symm (torusHom β w)

theorem torusExp_add (z w : Fin d → ℂ) : torusExp β (z + w) = torusExp β z * torusExp β w := by
  rw [torusExp, torusExp, torusExp, ← map_mul]
  congr 1
  ext χ
  show (expUnit _).val = (expUnit _ * expUnit _).val
  rw [pairing_add_left, expUnit_add]

theorem monoidHom_ext_basis {U : Type} [CommGroup U] {f f' : Multiplicative X →* U}
    (h : ∀ a, f (Multiplicative.ofAdd (β a)) = f' (Multiplicative.ofAdd (β a))) : f = f' := by
  have e : ∀ (φ : Multiplicative X →* U) (χ : X),
      φ (Multiplicative.ofAdd χ) = ∏ a, φ (Multiplicative.ofAdd (β a)) ^ (β.repr χ a) := fun φ χ => by
    conv_lhs => rw [← β.sum_repr χ]
    rw [ofAdd_sum, map_prod]
    exact Finset.prod_congr rfl fun a _ => by rw [ofAdd_zsmul, map_zpow]
  refine MonoidHom.ext fun χ => ?_
  exact (e f χ.toAdd).trans ((Finset.prod_congr rfl fun a _ => by rw [h a]).trans (e f' χ.toAdd).symm)

theorem torusExp_surjective : Function.Surjective (torusExp (X := X) β) := fun s => by
  let u := GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ))) s
  let w : Fin d → ℂ := fun a => Complex.log (gammaEquiv (u (Multiplicative.ofAdd (β a))).val)
  refine ⟨w, ?_⟩
  have : torusHom β w = u := monoidHom_ext_basis β fun a => by
    refine expUnit_ext ?_
    show gammaEquiv (expUnit _).val = _
    rw [gamma_expUnit, toAdd_ofAdd, pairing_basis]
    refine Complex.exp_log ?_
    exact (((u (Multiplicative.ofAdd (β a))).isUnit).map gammaEquiv).ne_zero
  rw [torusExp, this]
  exact (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).symm_apply_apply s

theorem torusExp_period (a : Fin d) : torusExp (X := X) β (Pi.single a (2 * Real.pi * Complex.I)) = 1 := by
  have : torusHom (X := X) β (Pi.single a (2 * Real.pi * Complex.I)) = 1 := by
    refine MonoidHom.ext fun χ => expUnit_eq_one ?_
    have e : pairing β (Pi.single a (2 * Real.pi * Complex.I)) χ.toAdd =
        ((β.repr χ.toAdd a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp [pairing, Pi.single_apply]
    rw [e]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [torusExp, this, map_one]

theorem valAt'_torusFst (t : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) (α : torusRing ZU X) :
    valAt' (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X) ⊤ ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α) =
      gammaEquiv ((Rosenlicht.coord t).hom α) := by
  rw [valAt'_eq_valR, valR_eq _ _ (le_preimage_top _)]
  have h3 : (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X).appLE ⊤ ⊤ (le_preimage_top _) =
      (t.left ≫ Rosenlicht.torusFst (Sp ℂ) X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  simp only [valMap, h3]
  rfl

theorem valAt'_torusFst' (t : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X) (α : torusRing ZU X) :
    valAt' (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α) = gammaEquiv ((Rosenlicht.coord t).hom α) :=
  valAt'_torusFst t α

theorem torusExp_hol_char (w : Fin d → ℂ) (χ : X) : gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom (AddMonoidAlgebra.single χ 1)) = Complex.exp (pairing β w χ) := by
  have e : GlobalTheory.SplitTorusPoints.toHom (torusExp β w) = torusHom β w :=
    (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X _).apply_symm_apply _
  rw [← GlobalTheory.SplitTorusPoints.toHom_val, e]
  exact gamma_expUnit _

theorem differentiable_pairing (χ : X) : Differentiable ℂ (fun w : Fin d → ℂ => pairing β w χ) := by
  unfold pairing
  fun_prop

theorem differentiable_torusExp_coord (α : torusRing ZU X) :
    Differentiable ℂ (fun w : Fin d → ℂ => gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom α)) := by
  induction α using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    simp only [map_add]
    exact hf.add hf'
  | single χ r =>
    have e : (AddMonoidAlgebra.single χ r : AddMonoidAlgebra (ULift.{0} ℤ) X) =
        r.down • AddMonoidAlgebra.single χ 1 := by
      rw [AddMonoidAlgebra.smul_single]
      congr 1
      ext
      simp
    have e' : ∀ w : Fin d → ℂ, gammaEquiv ((Rosenlicht.coord (torusExp β w)).hom (AddMonoidAlgebra.single χ r)) =
        r.down • Complex.exp (pairing β w χ) := fun w => by
      rw [← torusExp_hol_char, e, map_zsmul, map_zsmul]
    simp only [e']
    exact ((differentiable_pairing β χ).cexp).const_smul _

theorem isHolTo_torusExp : IsHolTo Set.univ (fun w => (torusExp (X := X) β w).left) := by
  have h1 : IsHolTo Set.univ (fun w => (torusExp (X := X) β w).left ≫ Rosenlicht.torusFst (Sp ℂ) X) := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine (T := Spec (torusRing ZU X)) isOpen_univ fun r => ?_
    obtain ⟨α, rfl⟩ : ∃ α, r = (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom α :=
      ⟨(Scheme.ΓSpecIso (torusRing ZU X)).hom.hom r, by simp⟩
    simp only [valAt'_torusFst]
    exact (differentiable_torusExp_coord β α).differentiableOn.congr fun w _ => valAt'_torusFst _ α
  have h2 : IsHolTo (V := Fin d → ℂ) Set.univ (fun _ => 𝟙 (Sp ℂ)) :=
    fun U f => ⟨by simp only [Set.mem_univ, true_and]; exact isOpen_const, differentiableOn_const _⟩
  exact GlobalTheory.HolPullback.isHolTo_of_components (Fin d → ℂ) Set.univ _ _ _ _ (pullback.fst _ _) (pullback.snd _ _) _ _ _
    (IsPullback.of_hasPullback (splitTorusAff ZU X).hom (toZ (Sp ℂ))) isOpen_univ h1
    (by
      convert h2 using 2 with w
      exact Over.w (torusExp (X := X) β w))

theorem exists_torusExp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (d : ℕ) (t : (Fin d → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X)),
      (∀ z w, t (z + w) = t z * t w) ∧ IsHolTo Set.univ (fun z => (t z).left) ∧ Function.Surjective t ∧
      ∀ a : Fin d, t (Pi.single a (2 * Real.pi * Complex.I)) = 1 :=
  ⟨_, torusExp (Module.finBasis ℤ X), torusExp_add _, isHolTo_torusExp _, torusExp_surjective _, torusExp_period _⟩

end TorusExp

end GlobalTheory.CompanionTheory.Ar.Flat.PerSpan

namespace GlobalTheory.CompanionTheory.Ar.Flat

open PerSpan

theorem span_per_eq_top : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Submodule.span ℂ (e.per b) = ⊤ := by
  intro R _ G _ _ g n M B ψ e hG b hb
  obtain ⟨T⟩ := hG.fibres ℂ (spMap (ψ b))
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R G g n M B ψ e hG b hb
  have hq := T.q_hom
  have hi := T.i_hom
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := hG.smooth
  have := T.q_quasiCompact
  have := T.q_surjective
  have hlft : LocallyOfFiniteType T.q.left := by
    have : LocallyOfFiniteType (T.q.left ≫ T.B.hom) := by
      rw [Over.w]
      show LocallyOfFiniteType (pullback.snd G.hom (spMap (ψ b)))
      infer_instance
    exact locallyOfFiniteType_of_comp _ T.B.hom
  obtain ⟨d, t, tadd, thol, tsurj, tper⟩ := exists_torusExp T.X
  have := (compact_alt_alt T.B T.isAbelian).1
  have := (compact_alt_alt T.B T.isAbelian).2
  have := isTopologicalGroup_over (C := ℂ) T.B
  let x := spMap (ψ b)
  let u : (Fin d → ℂ) → (Over.mk x ⟶ G) := fun w => ofFibre G x (t w ≫ T.i)
  have uadd : ∀ z w, u (z + w) = u z * u w := fun z w => by
    simp only [u, tadd, MonObj.mul_comp, ofFibre_mul]
  have uhol : IsHolTo Set.univ (fun z => (u z).left) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp thol (T.i.left ≫ pullback.fst G.hom x)
  obtain ⟨h, hh⟩ := exists_linear_lift_at_point R G g n M B ψ e b hb d u uadd uhol
  have hW : ∀ a, h (Pi.single a (2 * Real.pi * Complex.I)) ∈ Submodule.span ℂ (e.per b) := fun a => by
    refine Submodule.subset_span ?_
    show e.ex b _ = 1
    rw [hh]
    simp only [u, tper, MonObj.one_comp, ofFibre_one]
  have hW' : ∀ w, h w ∈ Submodule.span ℂ (e.per b) := fun w => by
    have e1 : w = ∑ a, (w a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
      ext c
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      simp [Finset.sum_apply, Pi.single_apply, h2]
    rw [e1, map_sum]
    exact Submodule.sum_mem _ fun a _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hW a)
  let π : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ T.B) := fun z => toFibre G x (e.ex b z) ≫ T.q
  refine eq_top_of_compact_quotient g _ π (fun z w => ?_) ?_ (fun y => ?_) _ (fun z hz => ?_)
  · simp only [π, e.add b hb, toFibre_mul, MonObj.mul_comp]
  · refine (continuous_over_comp T.q).comp ?_
    refine (isEmbedding_left _).continuous_iff.2 ?_
    refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom x)).continuous_iff.2 ?_
    refine Continuous.prodMk ?_ ?_
    · have := isHolTo_ex_slice e hb
      refine (continuous_of_differentiableOn (fun U f => ?_)).congr fun z => (pullback.lift_fst _ _ _).symm
      simpa using this U f
    · exact continuous_const.congr fun z => (pullback.lift_snd _ _ _).symm
  · obtain ⟨p, hp⟩ := GlobalTheory.SS.SemiDivisible.exists_lift_point T.q y
    obtain ⟨z, hz⟩ := hsurj (ofFibre G x p)
    refine ⟨z, ?_⟩
    simp only [π, hz, toFibre_ofFibre, hp]
  · have hk : toFibre G x (e.ex b z) ≫ T.q = toUnit _ ≫ η[T.B] := hz
    let s := T.isKernel.lift (toFibre G x (e.ex b z)) (toUnit _) hk
    have hs : s ≫ T.i = toFibre G x (e.ex b z) := T.isKernel.lift_fst _ _ _
    obtain ⟨w, hw⟩ := tsurj s
    have h1 : e.ex b (h w) = e.ex b z := by
      rw [hh]
      simp only [u, hw, hs, ofFibre_toFibre]
    have h2 : z - h w ∈ e.per b := by
      show e.ex b _ = 1
      have := e.add b hb (z - h w) (h w)
      rw [sub_add_cancel, h1] at this
      exact right_eq_mul.1 this
    have := Submodule.add_mem _ (Submodule.subset_span h2) (hW' w)
    rwa [sub_add_cancel] at this

end GlobalTheory.CompanionTheory.Ar.Flat
