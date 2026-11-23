import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.AlgChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LocalResidues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralJets

section Unit

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {k : Type} [Field k] (t : Spec (CommRingCat.of k) ⟶ S)

theorem unitAt_square (hsq : SquareSt) (P : PolAV S) (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq S P (Over.mk t) x₁ x₂ (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨SectionArithmetic.pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [SectionArithmetic.sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV S) (b : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (Over.mk t) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square t hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square t hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

theorem exists_root [IsAlgClosed k] (hmul : MulNSt) (P : PolAV S) (a₀ : Over.mk t ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : Over.mk t ⟶ P.A, b ^ r = a₀ := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hmul S P r hr
  obtain ⟨u, hu⟩ := SectionDivision.exists_section (pullback.snd (mulA P.A r).left a₀.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ (mulA P.A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu, Category.id_comp]
  have hw : (u ≫ pullback.fst (mulA P.A r).left a₀.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

end Unit

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem exists_unit_sec (hL : Laws) (hTW : TwistBCSpanStatement) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D : DegPre V) (r : ℕ) (hr : 4 ≤ r) (χ : D.X) :
    ∃ β : D.SecB r χ, (η[D.P.A]).left (closedPoint V) ∈ nonzeroLocus β := by
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  have hf : IsLocalHom f := inferInstance
  let t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of V) := Spec.map (CommRingCat.ofHom f)
  let T : Over (Spec (CommRingCat.of V)) := Over.mk t
  let P := D.P
  have hLB := P.isLB
  let o : T ⟶ T ⊗ P.A := lift (𝟙 T) 1
  let y : (T ⊗ P.A).left := o.left (closedPoint k)
  have hy : (snd T P.A).left y = (η[D.P.A]).left (closedPoint V) := by
    have e : o ≫ snd T P.A = toUnit T ≫ η[P.A] := lift_snd _ _
    have e2 := congrArg (fun q => q.left (closedPoint k)) e
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at e2
    refine e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg _ ?_))
    exact IsLocalRing.comap_closedPoint f
  obtain ⟨b, hb⟩ := exists_root t hL.mulN P (toUnit _ ≫ D.c χ) r (by omega)
  have hE := unitAt_iter t hL.square P b y (r - 2)
  have hr2 : r - 2 + 2 = r := by omega
  have hr2' : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
  rw [hr2, hb, hr2'] at hE
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso P.A.left.topIso.hom)
  let hb' : (T ⊗ P.A).left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := (translPt P.A b).left ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hbι : hb' ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = (translPt P.A b).left := by
    show ((translPt P.A b).left ≫ inv (P.A.hom ⁻¹ᵁ ⊤).ι) ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨hgen, -⟩ := hL.ample _ P r hr
  obtain ⟨M', s', hcov'⟩ := hgen ⊤ (isAffineOpen_top _)
  obtain ⟨m0, hm0⟩ : ∃ m0, hb' y ∈ nonzeroLocus (s' m0) := Opens.mem_iSup.1 (by rw [hcov']; trivial)
  obtain ⟨kk', hkk'⟩ := Opens.mem_iSup.1 hm0
  have hG : UnitAt P.L (fun _ : Fin r => hb' ≫ (P.A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) y :=
    ⟨SectionArithmetic.pullSec (s' m0) hb', fun J hJ => by
      have := SectionArithmetic.sval_pullSec (s' m0) hb' (𝟙 _) y hJ
      rw [Category.id_comp] at this
      exact (congrArg IsUnit this).mpr (SectionArithmetic.isUnit_sval (s' m0) hb' y hJ kk' hkk')⟩
  obtain ⟨c, hc⟩ := exists_gen_of_local (V := V) P.L hLB ![(D.c χ).left, (η[P.A]).left] ![-1, 1]
  have hC : UnitAt P.L (fun i => (T ⊗ P.A).hom ≫ ![(D.c χ).left, (η[P.A]).left] i) ![-1, 1] y :=
    ⟨SectionArithmetic.pullSec (Geo.Tor.genSec c hc) (T ⊗ P.A).hom, fun J hJ => by
      rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ, sval_genSec c hc _ y hJ]
      exact Units.isUnit _⟩
  have a0 : (snd T P.A).left ≫ D.famφB χ 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.famφB χ 1 = (translPt P.A (toUnit T ≫ D.c χ)).left := by
    show (snd T P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ) = snd T P.A * (toUnit _ ≫ D.c χ) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.c χ)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm]
    show _ = (fst T P.A ≫ toUnit T ≫ D.c χ) * snd T P.A
    rw [← Category.assoc, comp_toUnit]
  have a2 : (snd T P.A).left ≫ D.famφB χ 2 = (T ⊗ P.A).hom ≫ (D.c χ).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.c χ).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  have a3 : (snd T P.A).left ≫ D.famφB χ 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.famφB χ i) (DegPre.famε r) y := by
    refine UnitAt.congr hLB (formEq_of_add fun U _ hh => ?_) ((hE.mul hG).mul hC)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_three,
      Fin.sum_univ_two]
    simp only [Sum.elim_inl, Sum.elim_inr, hbι, DegPre.famε, Matrix.cons_val, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← natCast_zsmul]
    module
  obtain ⟨m, c', β, hβ⟩ := hTW V D r (by omega) χ k f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart hLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  refine ⟨β i, ?_⟩
  rw [← hy]
  exact Opens.mem_iSup.2 ⟨_, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

section Alg

variable {F R : Type} [CommRing F] [CommRing R] [Algebra F R]

theorem one_le_pow {V : Submodule F R} (h1 : 1 ≤ V) : ∀ n : ℕ, 1 ≤ V ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    calc (1 : Submodule F R) = 1 * 1 := (_root_.mul_one 1).symm
      _ ≤ V ^ n * V := mul_le_mul' (one_le_pow h1 n) h1

theorem pow_mono {V : Submodule F R} (h1 : 1 ≤ V) {a b : ℕ} (hab : a ≤ b) : V ^ a ≤ V ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc V ^ a = V ^ a * 1 := (_root_.mul_one _).symm
    _ ≤ V ^ a * V ^ c := mul_le_mul' le_rfl (one_le_pow h1 c)

theorem pow_le_ideal_pow {W : Submodule F R} {m : Ideal R} (h : W ≤ m.restrictScalars F) :
    ∀ k : ℕ, W ^ k ≤ (m ^ k).restrictScalars F
  | 0 => by
    intro x _
    simp [Ideal.one_eq_top]
  | k + 1 => by
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    rw [Submodule.restrictScalars_mem, pow_succ]
    exact Ideal.mul_mem_mul (pow_le_ideal_pow h k ha) (h hb)

theorem pow_le_of_aug {V : Submodule F R} (h1 : 1 ≤ V) (aug : R →ₐ[F] F) (D : ℕ)
    (hD : RingHom.ker aug ^ (D + 1) = ⊥) (n : ℕ) : V ^ n ≤ V ^ D := by
  set m := RingHom.ker aug
  set W : Submodule F R := V ⊓ m.restrictScalars F
  have hVW : V ≤ 1 ⊔ W := by
    intro v hv
    have hc : v - algebraMap F R (aug v) ∈ m := by
      show aug _ = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    refine Submodule.mem_sup.2 ⟨algebraMap F R (aug v), Submodule.algebraMap_mem _, v - algebraMap F R (aug v),
      ⟨V.sub_mem hv (h1 (Submodule.algebraMap_mem _)), hc⟩, add_sub_cancel _ _⟩
  have hWm : W ≤ m.restrictScalars F := inf_le_right
  have key : ∀ n k : ℕ, W ^ k * V ^ n ≤ V ^ D := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero, _root_.mul_one]
      rcases le_or_gt k D with hk | hk
      · exact (pow_le_pow_left' (inf_le_left : W ≤ V) k).trans (pow_mono h1 hk)
      · refine (pow_le_ideal_pow hWm k).trans ?_
        intro x hx
        have : x ∈ m ^ (D + 1) := Ideal.pow_le_pow_right hk hx
        rw [hD, Ideal.mem_bot] at this
        rw [this]; exact zero_mem _
    | succ n ih =>
      intro k
      calc W ^ k * V ^ (n + 1) = W ^ k * (V ^ n * V) := by rw [pow_succ]
        _ ≤ W ^ k * (V ^ n * (1 ⊔ W)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hVW)
        _ = W ^ k * V ^ n ⊔ W ^ (k + 1) * V ^ n := by
          rw [Submodule.mul_sup, _root_.mul_one, Submodule.mul_sup, ← _root_.mul_assoc, pow_succ, mul_right_comm (W ^ k) W]
        _ ≤ _ := sup_le (ih k) (ih (k + 1))
  simpa using key n 0

theorem mem_span_pow {s : Set R} (h1 : (1 : R) ∈ s) (hs : Algebra.adjoin F s = ⊤) (aug : R →ₐ[F] F) (D : ℕ)
    (hD : RingHom.ker aug ^ (D + 1) = ⊥) (a : R) : a ∈ Submodule.span F s ^ D := by
  have h1' : 1 ≤ Submodule.span F s := Submodule.one_le.2 (Submodule.subset_span h1)
  have ha : a ∈ Algebra.adjoin F s := hs ▸ trivial
  suffices h : ∃ n, a ∈ Submodule.span F s ^ n by
    obtain ⟨n, hn⟩ := h
    exact pow_le_of_aug h1' aug D hD n hn
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by rw [pow_one]; exact Submodule.subset_span hx⟩
  | algebraMap c => exact ⟨0, by rw [pow_zero]; exact Submodule.algebraMap_mem c⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨max n₁ n₂, add_mem (pow_mono h1' (le_max_left _ _) h₁) (pow_mono h1' (le_max_right _ _) h₂)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n₁, h₁⟩ := hx
    obtain ⟨n₂, h₂⟩ := hy
    exact ⟨n₁ + n₂, by rw [pow_add]; exact Submodule.mul_mem_mul h₁ h₂⟩

end Alg

section Chart

open Chart

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {g : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ G}

theorem subalgebra_eq_top (hx : IsUnivChart G g x) (n : ℕ) (B : Subalgebra R (JetR R (Fin g) n))
    (y : Spec (CommRingCat.of B) ⟶ G.left) (hy : Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫ y = (x n).left) :
    B = ⊤ := by
  have hw : y ≫ G.hom = (sp (R₀ := R) B).hom := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ G.hom)
    have e : Spec.map (φ ≫ CommRingCat.ofHom B.val.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap R (JetR R (Fin g) n))) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hy]
      exact Over.w (x n)
    have e' := Spec.map_injective e
    rw [← hφ]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R B))
    congr 1
    ext r
    exact congrArg (fun q => q.hom r) e'
  let y' : sp (R₀ := R) B ⟶ G := Over.homMk y hw
  have hy' : spMap B.val ≫ y' = x n := Over.OverMorphism.ext hy
  let aug := (jetAug R (Fin g) n).comp B.val
  have hker : RingHom.ker aug ^ (n + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have hle : Ideal.map B.val (RingHom.ker aug) ≤ RingHom.ker (jetAug R (Fin g) n) :=
      Ideal.map_le_iff_le_comap.mpr fun s hs => hs
    have := Ideal.mem_map_of_mem B.val ht
    rw [Ideal.map_pow] at this
    have h2 := Ideal.pow_right_mono hle _ this
    rw [ker_jetAug_pow, Ideal.mem_bot] at h2
    exact Ideal.mem_bot.2 (Subtype.ext h2)
  have h0 : spMap (jetAug R (Fin g) n) ≫ x n = 1 := spMap_jetAug_alt hx n
  have h1 : spMap aug ≫ y' = 1 := by
    rw [← h0, ← hy', ← Category.assoc, spMap_comp]
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := hx.2.2 B aug n hker y' h1
  obtain ⟨ψ₀, -, hu⟩ := hx.2.2 (JetR R (Fin g) n) (jetAug R (Fin g) n) n (ker_jetAug_pow _ _) (x n) h0
  have e1 : B.val.comp ψ = ψ₀ := hu _ ⟨hψ1, by rw [← spMap_comp, Category.assoc, ← hψ2, hy']⟩
  have e2 : AlgHom.id R _ = ψ₀ := hu _ ⟨rfl, by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, spMap_left]
    show _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]⟩
  refine eq_top_iff.2 fun a _ => ?_
  have : a = B.val (ψ a) := AlgHom.congr_fun (e2.trans e1.symm) a
  rw [this]
  exact (ψ a).2

theorem jet_mem [IsLocalRing R] (hx : IsUnivChart G g x) (n : ℕ) (O : G.left.Opens)
    (hO : (η[G]).left (closedPoint R) ∈ O) (p : (sp (R₀ := R) (JetR R (Fin g) n)).left) : (x n).left p ∈ O := by
  let q := jetAug R (Fin g) n
  have hq : Function.Surjective q := aug_surj q
  have hker : RingHom.ker q.toRingHom ≤ p.asIdeal := fun a ha => by
    obtain ⟨m, hm⟩ := elt_nil _ (ker_jetAug_nil (R := R) (Fin g) n) a ha
    exact p.isPrime.mem_of_pow_mem m (by rw [hm]; exact zero_mem _)
  have := p.isPrime
  have hprime : (p.asIdeal.map q.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let p₀ : ↥(Spec (CommRingCat.of R)) := (⟨p.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum R)
  have hp : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap q.toRingHom (Ideal.map q.toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]
  have h0 : spMap q ≫ x n = toUnit _ ≫ η[G] := spMap_jetAug_alt hx n
  have e := congrArg (fun y : sp R ⟶ G => y.left.base p₀) h0
  simp only [Over.comp_left, spMap_left, Scheme.Hom.comp_apply] at e
  rw [← hp]
  refine (congrArg (· ∈ O) e).mpr ?_
  exact ((IsLocalRing.specializes_closedPoint (R := R) ((toUnit (sp (R₀ := R) R)).left p₀)).map
    (η[G]).left.continuous).mem_open O.isOpen hO

end Chart

section Ratio

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_ratio (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (τ : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (hτ : τ.IsGen) :
    ∃ u : Γ(Z, ⊤), ∀ z J, Good L z J → sval s h z J = gs (𝟙 Z) z ⊤ u * (val τ (𝟙 Z) z J).val := by
  obtain ⟨w, hw⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (formEq_of_add fun U _ hh => by simp [Fintype.sum_sum_type])
    (pullMulSec s h (LB.invGen L _ _ τ) (invGen_isGen _ _ _ _ hτ))
  have le : (⊤ : Z.Opens) ≤ LB.wchart L (K := PEmpty) (Y := Z) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Z.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim), fun z J hJ => ?_⟩
  have e := hw Z (𝟙 Z) z J hJ
  rw [sval_pullMulSec _ _ _ _ _ z hJ, Category.id_comp, val_inv, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg (· * _) ((gs_res (𝟙 Z) z le trivial _).trans e).symm)
  rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Ratio

section Main

open Chart

def germOf {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) : A →+* (Spec (CommRingCat.of A)).presheaf.stalk z :=
  ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem germOf_eq {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) (a : A) :
    germOf z a = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
  (gs_eq (𝟙 _) z ⊤ trivial _).symm

theorem germOf_hom {A : Type} [CommRing A] (z : Spec (CommRingCat.of A)) (u : Γ(Spec (CommRingCat.of A), ⊤)) :
    germOf z ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom u) = gs (𝟙 _) z ⊤ u := by
  rw [germOf_eq]
  congr 1
  simp

theorem germOf_ext {A : Type} [CommRing A] {a b : A} (h : ∀ z, germOf z a = germOf z b) : a = b :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    (fn_ext (V := ⊤) fun z _ => (germOf_eq z a).symm.trans ((h z).trans (germOf_eq z b)))

theorem isUnit_of_germOf {A : Type} [CommRing A] {a : A} (h : ∀ z, IsUnit (germOf z a)) : IsUnit a := by
  have : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    (Spec (CommRingCat.of A)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => h z
  simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem gs_const {V A : Type} [CommRing V] [CommRing A] (f : V →+* A) (z : Spec (CommRingCat.of A)) (c : V) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) = germOf z (f c) := by
  have e := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [germOf_eq, e]
  exact (congrArg (fun q => gs q z ⊤ _) (Category.id_comp _).symm).trans (gs_pull (𝟙 _) _ z ⊤ trivial _).symm

theorem jets (hL : Laws) (hTW : TwistBCSpanStatement) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D : DegPre V) (q n : ℕ) (hq : 4 * n + 4 ≤ q) (χ : D.X) (g : ℕ)
    (x : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin g) m) ⟶ D.P.A) (hx : IsUnivChart D.P.A g x)
    (τ : LB.Gen (LB.LinComb (Y := Spec (CommRingCat.of (JetR V (Fin g) n))) D.P.L (fun i => (x n).left ≫ D.famφB χ i) (DegPre.famε q))) (hτ : τ.IsGen)
    (a : JetR V (Fin g) n) : ∃ β : D.SecB q χ, ∀ (z : Spec (CommRingCat.of (JetR V (Fin g) n))) (J),
      Good D.P.L z J → sval β (x n).left z J = germOf z a * (val τ (𝟙 _) z J).val := by
  obtain ⟨r, rfl⟩ : ∃ r, q = 4 * n + r := ⟨q - 4 * n, by omega⟩
  have hLB := D.P.isLB
  obtain ⟨β₀, hβ₀⟩ := exists_unit_sec hL hTW V D r (by omega) χ
  let xn : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ D.P.A.left := (x n).left
  let W := (D.P.A.hom ⁻¹ᵁ ⊤).toScheme
  let iw : W ⟶ D.P.A.left := (D.P.A.hom ⁻¹ᵁ ⊤).ι
  have : IsIso iw := inferInstanceAs (IsIso D.P.A.left.topIso.hom)
  have : IsIso (⊤ : (Spec (CommRingCat.of V)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (CommRingCat.of V)).topIso.hom)
  let h0 : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ W := xn ≫ inv iw
  have h0i : h0 ≫ iw = xn := by
    show (xn ≫ inv iw) ≫ iw = xn
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨-, hva⟩ := hL.ample _ D.P 4 le_rfl
  obtain ⟨M, s, hcov, hs⟩ := hva ⊤ (isAffineOpen_top _)
  obtain ⟨i0, hi0⟩ : ∃ i0, inv iw ((η[D.P.A]).left (closedPoint V)) ∈ nonzeroLocus (s i0) :=
    Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hz0 : ∀ z, h0 z ∈ nonzeroLocus (s i0) := fun z => jet_mem hx n (inv iw ⁻¹ᵁ nonzeroLocus (s i0)) hi0 z
  have hle : ⊤ ≤ h0 ⁻¹ᵁ nonzeroLocus (s i0) := fun z _ => hz0 z
  obtain ⟨hD, rr, hrel, hsurj⟩ := hs i0
  let π := h0.appLE (nonzeroLocus (s i0)) ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin g) n))).hom
  have hπ : ∀ z b, germOf z (π.hom b) = gs h0 z _ b := fun z b =>
    (germOf_hom z _).trans ((gs_appLE h0 _ ⊤ hle (𝟙 _) z trivial b).trans (by rw [Category.id_comp]))
  have hπs : Spec.map π ≫ hD.fromSpec = h0 := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec h0 hD (isAffineOpen_top _) hle
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  let ρ : Fin (M + 1) → JetR V (Fin g) n := fun i => π.hom (rr i)
  have hσ0 : ∀ z J, Good D.P.L z J → IsUnit (sval (s i0) h0 z J) := fun z J hJ => by
    obtain ⟨kk, hkk⟩ := Opens.mem_iSup.1 (hz0 z)
    exact SectionArithmetic.isUnit_sval (s i0) h0 z hJ kk hkk
  have hβ0 : ∀ z J, Good D.P.L z J → IsUnit (sval β₀ xn z J) := fun z J hJ => by
    obtain ⟨kk, hkk⟩ := Opens.mem_iSup.1 (jet_mem hx n _ hβ₀ z)
    exact SectionArithmetic.isUnit_sval β₀ xn z hJ kk hkk
  have hrelv : ∀ i z J, Good D.P.L z J → sval (s i) h0 z J = germOf z (ρ i) * sval (s i0) h0 z J := fun i z J hJ =>
    (LocalResidues.sval_rel (s i) (s i0) _ (rr i) (hrel i) h0 z hJ (hz0 z)).trans (by rw [← hπ])
  have good : ∀ z : Spec (CommRingCat.of (JetR V (Fin g) n)), ∃ J, Good D.P.L z J := fun z => by
    choose J hJ using fun ψ : Spec (CommRingCat.of (JetR V (Fin g) n)) ⟶ D.P.A.left => exists_chart hLB (ψ z)
    exact ⟨J, hJ⟩
  have hρ1 : ρ i0 = 1 := germOf_ext fun z => by
    obtain ⟨J, hJ⟩ := good z
    rw [map_one]
    exact ((hσ0 z J hJ).mul_left_inj.1 ((hrelv i0 z J hJ).symm.trans (_root_.one_mul _).symm))

  have hadj : Algebra.adjoin V (Set.range ρ) = ⊤ := by
    have hq' : (h0 ≫ (D.P.A.hom ∣_ ⊤)) ≫ (⊤ : (Spec (CommRingCat.of V)).Opens).ι =
        Spec.map (CommRingCat.ofHom (algebraMap V (JetR V (Fin g) n))) := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, h0i]
      exact Over.w (x n)
    have hc : ∀ b, π.hom (((D.P.A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i0)) le_top).hom b) ∈
        Algebra.adjoin V (Set.range ρ) := fun b => by
      let e := (⊤ : (Spec (CommRingCat.of V)).Opens).ι
      let c : V := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (((inv e).app ⊤).hom b)
      have : π.hom (((D.P.A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i0)) le_top).hom b) = algebraMap V _ c :=
        germOf_ext fun z => by
          refine (hπ z _).trans ((gs_appLE _ _ _ _ h0 z (hz0 z) b).trans (Eq.trans ?_ (gs_const _ z c)))
          have e1 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c = ((inv e).app ⊤).hom b := by simp [c]
          rw [e1]
          refine Eq.trans ?_ (gs_pull _ (inv e) z ⊤ trivial b).symm
          rw [← hq', Category.assoc (h0 ≫ _), IsIso.hom_inv_id, Category.comp_id]
      rw [this]
      exact Subalgebra.algebraMap_mem _ c
    have hall : ∀ b, π.hom b ∈ Algebra.adjoin V (Set.range ρ) := fun b => by
      obtain ⟨p, rfl⟩ := hsurj b
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval₂Hom_C]; exact hc c
      | add p p' hp hp' => rw [map_add, map_add]; exact add_mem hp hp'
      | mul_X p i hp =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine subalgebra_eq_top hx n _ (Spec.map (CommRingCat.ofHom
      (π.hom.codRestrict (Algebra.adjoin V (Set.range ρ)) hall)) ≫ hD.fromSpec ≫ iw) ?_
    rw [← Category.assoc, ← Spec.map_comp]
    refine Eq.trans ?_ h0i
    rw [← hπs, Category.assoc]
    rfl

  have key : ∀ α : Fin n → Fin (M + 1), ∃ S : D.SecB (4 * n + r) χ, ∀ z J, Good D.P.L z J →
      sval S xn z J = germOf z (∏ l, ρ (α l)) * (sval (s i0) h0 z J ^ n * sval β₀ xn z J) := by
    intro α
    obtain ⟨S, hS⟩ := exists_sec hLB (φ' := D.famφB χ) (ε' := DegPre.famε (4 * n + r))
      (formEq_of_add fun U _ hh => by
        have e : inv iw ≫ (D.P.A.hom ⁻¹ᵁ ⊤).ι = D.famφB χ 0 := IsIso.inv_hom_id iw
        rw [Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
        simp only [Sum.elim_inl, Sum.elim_inr, e, DegPre.famε, Matrix.cons_val, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Fintype.card_prod, ← natCast_zsmul]
        push_cast
        module)
      (SectionArithmetic.mulSec (SectionArithmetic.powSec fun l => SectionArithmetic.pullSec (s (α l)) (inv iw)) β₀)
    refine ⟨S, fun z J hJ => ?_⟩
    have hp : ∀ i, sval (SectionArithmetic.pullSec (s i) (inv iw)) xn z J = germOf z (ρ i) * sval (s i0) h0 z J := fun i =>
      (SectionArithmetic.sval_pullSec (s i) (inv iw) xn z hJ).trans (hrelv i z J hJ)
    have e1 : (∏ i, sval (SectionArithmetic.pullSec (s (α i)) (inv iw)) xn z J) =
        germOf z (∏ l, ρ (α l)) * sval (s i0) h0 z J ^ n :=
      (Finset.prod_congr rfl fun i _ => hp (α i)).trans (by rw [Finset.prod_mul_distrib, Fin.prod_const, map_prod])
    rw [hS _ xn z J hJ, SectionArithmetic.sval_mulSec _ _ _ z hJ, SectionArithmetic.sval_powSec _ _ z hJ, ← _root_.mul_assoc]
    exact congrArg₂ (· * ·) e1 rfl

  obtain ⟨S₀, hS₀⟩ := key fun _ => i0
  obtain ⟨u, hu⟩ := exists_ratio hLB S₀ xn τ hτ
  let w : JetR V (Fin g) n := (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin g) n))).hom.hom u
  have hw : ∀ z J, Good D.P.L z J →
      sval (s i0) h0 z J ^ n * sval β₀ xn z J = germOf z w * (val τ (𝟙 _) z J).val := fun z J hJ => by
    have := hS₀ z J hJ
    rw [hu z J hJ, hρ1, Finset.prod_const_one, map_one, _root_.one_mul, ← germOf_hom] at this
    exact this.symm
  obtain ⟨w', hw'⟩ : IsUnit w := isUnit_of_germOf fun z => by
    obtain ⟨J, hJ⟩ := good z
    exact isUnit_of_mul_isUnit_left ((congrArg IsUnit (hw z J hJ)).mp (((hσ0 z J hJ).pow n).mul (hβ0 z J hJ)))
  let N : Submodule V (JetR V (Fin g) n) :=
    { carrier := {v | ∃ β : D.SecB (4 * n + r) χ, ∀ z J, Good D.P.L z J →
        sval β xn z J = germOf z (v * w) * (val τ (𝟙 _) z J).val}
      add_mem' := by
        rintro v v' ⟨β, hβ⟩ ⟨β', hβ'⟩
        refine ⟨SectionArithmetic.secAdd β β', fun z J hJ => ?_⟩
        rw [add_mul, map_add, add_mul, ← hβ z J hJ, ← hβ' z J hJ]
        exact gs_add xn z _ (hJ.mem _ xn) _ _
      zero_mem' := ⟨SectionArithmetic.secZero _, fun z J hJ => by
        rw [zero_mul, map_zero, zero_mul]
        exact (gs_eq xn z _ (hJ.mem _ xn) _).trans ((congrArg _ (map_zero _)).trans (map_zero _))⟩
      smul_mem' := by
        rintro c v ⟨β, hβ⟩
        refine ⟨SectionArithmetic.secCMul (V := D.P.A.hom ⁻¹ᵁ ⊤) (fun _ _ _ => trivial)
          ((D.P.A.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c)) β, fun z J hJ => ?_⟩
        rw [Algebra.smul_def, _root_.mul_assoc, map_mul, _root_.mul_assoc, ← hβ z J hJ, ← gs_const]
        refine (gs_mul xn z _ (hJ.mem _ xn) _ _).trans (congrArg₂ (· * ·) ?_ rfl)
        refine (gs_res xn z _ (hJ.mem _ xn) _).trans ((gs_pull xn D.P.A.hom z ⊤ trivial _).trans ?_)
        exact congrArg (fun q => gs q z ⊤ _) (Over.w (x n)) }
  have hN : Submodule.span V (Set.range ρ) ^ n ≤ N := by
    rw [Submodule.span_pow (Set.range ρ)]
    refine Submodule.span_le.2 fun v hv => ?_
    obtain ⟨t, rfl⟩ := Set.mem_pow.1 hv
    choose α hα using fun l => (t l).2
    obtain ⟨S, hS⟩ := key α
    refine ⟨S, fun z J hJ => ?_⟩
    have : (List.ofFn fun i => (t i : JetR V (Fin g) n)).prod = ∏ l, ρ (α l) := by
      rw [List.prod_ofFn]
      exact Finset.prod_congr rfl fun l _ => (hα l).symm
    rw [hS z J hJ, hw z J hJ, this, map_mul (germOf z), _root_.mul_assoc]
  obtain ⟨β, hβ⟩ := hN (mem_span_pow (s := Set.range ρ) ⟨i0, hρ1⟩ hadj (jetAug V (Fin g) n) n (ker_jetAug_pow _ _) (a * ↑w'⁻¹))
  refine ⟨β, fun z J hJ => (hβ z J hJ).trans ?_⟩
  rw [← hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Main

theorem integral_jets : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (q n : ℕ), 4 * n + 4 ≤ q → ∀ (χ : D.X) (g : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := V) (Chart.JetR V (Fin g) m) ⟶ D.P.A), Chart.IsUnivChart D.P.A g x → ∀ τ : LB.Gen (LB.LinComb D.P.L (fun i => (x n).left ≫ D.famφB χ i) (DegPre.famε q)), τ.IsGen → ∀ a : Chart.JetR V (Fin g) n, ∃ β : D.SecB q χ, (∀ (z : (Chart.sp (R₀ := V) (Chart.JetR V (Fin g) n)).left) (J), Good D.P.L z J → sval (β) (x n).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Chart.JetR V (Fin g) n))).inv.hom (a)) * (val τ (𝟙 _) z J).val) := by
  intro hL hTW V _ _ _ D q n hq χ g x hx τ hτ a
  obtain ⟨β, hβ⟩ := jets hL hTW V D q n hq χ g x hx τ hτ a
  exact ⟨β, fun z J hJ => (hβ z J hJ).trans (congrArg (· * _) (germOf_eq z a))⟩

end GlobalTheory.IntegralJets
