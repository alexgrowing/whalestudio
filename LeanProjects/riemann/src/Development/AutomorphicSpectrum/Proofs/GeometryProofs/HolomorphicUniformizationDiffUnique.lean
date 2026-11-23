import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ggeo.DualFibre

theorem exists_complex_point (A : Over (Sp ℂ)) [LocallyOfFiniteType A.hom] (V : A.left.Opens)
    (hV : (V : Set A.left).Nonempty) : ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, ⊤ ≤ x.left ⁻¹ᵁ V := by
  obtain ⟨r, hr, hz⟩ := GlobalTheory.ZH.SecProp.exists_point A.hom V.isOpen.isLocallyClosed hV
  exact ⟨Over.homMk r hr, fun z _ => hz z⟩

section Translate

variable {A : Over (Sp ℂ)} [GrpObj A]

def tr (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : A ⟶ A := (toUnit A ≫ c) * 𝟙 A

theorem comp_tr (x c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : x ≫ tr c = c * x := by
  rw [tr, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (𝟙 _),
    Category.id_comp]

theorem tr_comp_tr (c d : 𝟙_ (Over (Sp ℂ)) ⟶ A) : tr c ≫ tr d = tr (d * c) := by
  have h : tr c ≫ toUnit A = toUnit A := toUnit_unique _ _
  change tr c ≫ ((toUnit A ≫ d) * 𝟙 A) = (toUnit A ≫ (d * c)) * 𝟙 A
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, h, MonObj.comp_mul, _root_.mul_assoc]
  rfl

theorem tr_one : tr (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = 𝟙 A := by
  change (toUnit A ≫ 1) * 𝟙 A = 𝟙 A
  simp

instance isIso_tr_left (c : 𝟙_ (Over (Sp ℂ)) ⟶ A) : IsIso (tr c).left :=
  ⟨(tr c⁻¹).left, by rw [← Over.comp_left, tr_comp_tr, inv_mul_cancel, tr_one]; rfl,
    by rw [← Over.comp_left, tr_comp_tr, mul_inv_cancel, tr_one]; rfl⟩

theorem exists_affine_mem [PreirreducibleSpace A.left] [LocallyOfFiniteType A.hom]
    (hcomm : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ A, x * y = y * x) (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U ∧ ⊤ ≤ a.left ⁻¹ᵁ U := by
  obtain ⟨_, ⟨W, hW, rfl⟩, h0, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left (default : PrimeSpectrum ℂ))) isOpen_univ
  have h1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ W := (GlobalTheory.top_le_preimage_iff_mem _ _).2 h0
  have h2 : ⊤ ≤ (a⁻¹).left ⁻¹ᵁ ((tr a).left ⁻¹ᵁ W) := by
    rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, mul_inv_cancel]
    exact h1
  obtain ⟨b, hb⟩ := exists_complex_point A (W ⊓ (tr a).left ⁻¹ᵁ W)
    (nonempty_preirreducible_inter W.isOpen ((tr a).left ⁻¹ᵁ W).isOpen ⟨_, h0⟩
      ⟨_, h2 (Set.mem_univ (default : PrimeSpectrum ℂ))⟩)
  obtain ⟨hb1, hb2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hb
  refine ⟨(tr b).left ⁻¹ᵁ W, hW.preimage_of_isIso _, ?_, ?_⟩
  · rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, _root_.mul_one]
    exact hb1
  · rw [← GlobalTheory.top_le_preimage_comp, ← Over.comp_left, comp_tr, hcomm, ← comp_tr, Over.comp_left,
      GlobalTheory.top_le_preimage_comp]
    exact hb2

end Translate

section Dual

variable {A : Over (Sp ℂ)}

theorem red_surjective (p : Sp (DualNumber ℂ)) :
    p ∈ Set.range (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
  have h := range_comap_of_surjective ℂ (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom : Set (DualNumber ℂ)) := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h1 : a * a = 0 := by
      ext <;> simp [h0]
    exact (PrimeSpectrum.isPrime p).mul_mem_iff_mem_or_mem.1 (h1 ▸ Ideal.zero_mem _) |>.elim id id
  rw [← h] at hp
  exact hp

def basePt (v : epsR ℂ ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ A :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left) (by
    have h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
    rw [Category.assoc, Over.w v]
    exact h)

theorem top_le_of_basePt (v : epsR ℂ ⟶ A) (U : A.left.Opens) (h : ⊤ ≤ (basePt v).left ⁻¹ᵁ U) :
    ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surjective p
  have := h (Set.mem_univ q)
  simpa [basePt] using this

end Dual

section Germ

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem fderiv_eq_zero_of_affine (D : Fin g → ℂ) (U : A.left.Opens) (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (hD : ∀ f : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 D = 0)
    (U₁ : A.left.Opens) (f : Γ(A.left, U₁)) (h1 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U₁) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U₁ f) 0 D = 0 := by
  have m0 := (GlobalTheory.top_le_preimage_iff_mem _ _).1 h0
  have m1 := (GlobalTheory.top_le_preimage_iff_mem _ _).1 h1
  obtain ⟨q, hq1, hq0⟩ := hU.exists_basicOpen_le (V := U₁) ⟨_, m1⟩ m0
  have hBU : A.left.basicOpen q ≤ U := A.left.basicOpen_le q
  have hB0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen q := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hq0
  have hloc := hU.isLocalization_basicOpen q
  obtain ⟨n, p, e⟩ := IsLocalization.Away.surj (S := Γ(A.left, A.left.basicOpen q)) q (resG _ hq1 f)
  have e' : resG _ hq1 f * resG _ hBU (q ^ n) = resG _ hBU p := by
    rw [map_pow]
    exact e
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen q →
      valAt' (u.ex z).left U₁ f * valAt' (u.ex z).left U (q ^ n) = valAt' (u.ex z).left U p := by
    intro z hz
    have := congrArg (valAt' (u.ex z).left (A.left.basicOpen q)) e'
    rwa [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hz, GlobalTheory.valAt'_res _ _ _ hz, GlobalTheory.valAt'_res _ _ _ hz] at this
  have hev : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen q :=
    (u.hol _ 0).1.mem_nhds hB0
  have df : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U₁ f) 0 :=
    (u.hol U₁ f).2.differentiableAt ((u.hol U₁ f).1.mem_nhds h1)
  have dqn : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U (q ^ n)) 0 :=
    (u.hol U (q ^ n)).2.differentiableAt ((u.hol U (q ^ n)).1.mem_nhds h0)
  have H := (df.hasFDerivAt.mul dqn.hasFDerivAt).congr_of_eventuallyEq
    (f₁ := fun z => valAt' (u.ex z).left U p) (hev.mono fun z hz => (hval z hz).symm)
  have H2 := congrArg (fun T => T D) H.fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hD, smul_eq_mul, mul_zero,
    zero_add] at H2
  have hne : valAt' (u.ex 0).left U (q ^ n) ≠ 0 := by
    rw [GlobalTheory.valAt'_pow _ h0]
    exact pow_ne_zero _ ((GlobalTheory.top_le_preimage_basicOpen_iff _ U q).1 hB0)
  exact (mul_eq_zero.1 H2.symm).resolve_left hne

end Germ

theorem eq_of_isDiff_of_not_isTangent : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → ConnectedSpace A.left → ∀ (v : epsR ℂ ⟶ A), ¬ IsTangent v → ∀ (w w' : Fin g → ℂ), u.IsDiff w v → u.IsDiff w' v → w = w' := by
  intro A _ L g u hs hc v _ w w' h h'
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : PreirreducibleSpace A.left := ⟨by
    have := GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth A.hom (Classical.arbitrary A.left)
    rwa [PreconnectedSpace.connectedComponent_eq_univ] at this⟩
  have hcomm : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ A, x * y = y * x := fun x y => by
    obtain ⟨z, rfl⟩ := u.ex_onto x
    obtain ⟨z', rfl⟩ := u.ex_onto y
    rw [← u.ex_add, ← u.ex_add, add_comm]
  obtain ⟨U, hU, h0, ha⟩ := exists_affine_mem hcomm (basePt v)
  have e1 : u.ex 0 = 1 := GlobalTheory.TangentOrigin.ex_zero u
  rw [← e1] at h0
  have hv := top_le_of_basePt v U ha
  have hDU : ∀ f : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 (w - w') = 0 := fun f => by
    rw [map_sub, ← h U hv f, ← h' U hv f, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.TorusTransfer.eq_zero_of_fderiv_eq_zero u (w - w')
    fun U₁ f h1 => fderiv_eq_zero_of_affine u _ U hU h0 hDU U₁ f h1)

end GlobalTheory.CompanionTheory.Ggeo.DualFibre
