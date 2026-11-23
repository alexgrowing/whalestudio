import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubringStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.Special

theorem exists_lift {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ∃ x' : Z' ⟶ W.toScheme, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h (x := p) trivial

theorem le_comp {Z Z' Z'' : Scheme.{0}} (g : Z'' ⟶ Z') (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ W := fun p _ => h (x := g p) trivial

theorem le_powOver {S Z' : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ)
    (x : Z' ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι) (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun p _ => Set.mem_iInter.2 fun _ => h (x := p) trivial

theorem exists_chart {Z : Scheme.{0}} {K : Type} [Field K] (L : LB Z) (hL : L.IsLB) (x : Sp K ⟶ Z) :
    ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have h : x (default : PrimeSpectrum K) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨j, fun p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact hj

theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (hL : L.IsLB)
    {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (y : Sp R ⟶ S) (x : Sp K ⟶ G.left) (hx : x ≫ G.hom = spMap f ≫ y) (τ : L.ι → K) (hτ : IsFrm L x τ)
    (U : S.Opens) (hU : IsAffineOpen U) (hyU : ⊤ ≤ y ⁻¹ᵁ U) {n : ℕ} (b : Fin n → LB.Sec (Out.powOver G L U 4))
    (hb : AmpleSpan.EmbedsBy (G.hom ∣_ U) b) (cf : Fin n → R) (hcf : ∃ i, IsUnit (cf i))
    (hv : ∀ i (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U).ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U 4).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * τ j ^ 4)
    (U' : S.Opens) (hyU' : ⊤ ≤ y ⁻¹ᵁ U') (b' : LB.Sec (Out.powOver G L U' 5)) (cf' : R) (hcf' : IsUnit cf')
    (hv' : ∀ (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U').toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U').ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j)) = f cf' * τ j ^ 5) :
    ∃ (z : Sp R ⟶ G.left) (σ : L.ι → R), z ≫ G.hom = y ∧ spMap f ≫ z = x ∧ IsFrm L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ L.U j → f (σ j) = τ j := by
  classical
  have hxU : ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hx]
    exact le_comp _ _ _ hyU
  obtain ⟨x₁, hx₁⟩ := exists_lift x _ hxU
  obtain ⟨j₀, hj₀⟩ := exists_chart L hL x
  obtain ⟨u₀, hu₀⟩ := (hτ.1 j₀ hj₀).pow 4
  obtain ⟨z₁, ⟨hz₁, hz₂, hz₃⟩, -⟩ := GlobalTheory.T.existsUnique_lift_coords_localSubring S G L U 4 n b R K f y x₁ cf j₀ u₀ hL hU hb hf hyU
    (by rw [← Category.assoc, hx₁, hx]) (by rw [hx₁]; exact hj₀)
    (fun i => by rw [hu₀]; exact hv i x₁ j₀ hx₁ hj₀) hcf
  have hz : spMap f ≫ z₁ ≫ (G.hom ⁻¹ᵁ U).ι = x := by rw [← Category.assoc, hz₂, hx₁]
  have hzy : (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ≫ G.hom = y := by rw [Category.assoc, hz₁]
  have hzU' : ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ (G.hom ⁻¹ᵁ U') := by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hyU'
  obtain ⟨z₂, hz₄⟩ := exists_lift _ _ hzU'
  have key : ∀ j, ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ r : R, IsUnit r ∧ f r = τ j := by
    intro j hj
    have hxj : ⊤ ≤ x ⁻¹ᵁ L.U j := by rw [← hz]; exact le_comp _ _ _ hj
    obtain ⟨u, hu⟩ := hz₃ j hj
    obtain ⟨i, hi⟩ := hcf
    have h4 : f u = τ j ^ 4 := by
      have e := hv i x₁ j hx₁ hxj
      rw [← hz₂, HolHom.valR_spMap _ _ _ (le_powOver G L U 4 z₁ j hj), hu, map_mul] at e
      exact mul_left_cancel₀ (hi.map f).ne_zero e
    have e := hv' (spMap f ≫ z₂) j (by rw [Category.assoc, hz₄, hz]) hxj
    rw [HolHom.valR_spMap _ _ _ (le_powOver G L U' 5 z₂ j (by rw [hz₄]; exact hj))] at e
    obtain ⟨c, rfl⟩ := hcf'
    set a := valR z₂ ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j))
    have hc : f (↑c⁻¹ : R) * f c = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hu' : f (↑u⁻¹ : R) * f u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hr : f (↑c⁻¹ * ↑u⁻¹ * a) = τ j := by
      rw [map_mul, map_mul, e]
      rw [h4] at hu'
      linear_combination (f (↑u⁻¹ : R) * τ j ^ 5) * hc + τ j * hu'
    refine ⟨_, ?_, hr⟩
    have : (↑c⁻¹ * ↑u⁻¹ * a) ^ 4 = (u : R) := hf (by rw [map_pow, hr, h4])
    exact (isUnit_pow_iff (by norm_num : 4 ≠ 0)).1 (this ▸ u.isUnit)
  choose! σ hσ using key
  refine ⟨z₁ ≫ (G.hom ⁻¹ᵁ U).ι, σ, hzy, hz, ⟨fun j hj => (hσ j hj).1, fun j j' hj => hf ?_⟩,
    fun j hj => (hσ j hj).2⟩
  have h1 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_left : L.U j ⊓ L.U j' ≤ _))
  have h2 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_right : L.U j ⊓ L.U j' ≤ _))
  rw [map_mul, (hσ j h1).2, (hσ j' h2).2, ← HolHom.valR_spMap _ _ _ hj, hz]
  exact hτ.2 j j' (by rw [← hz]; exact le_comp _ _ _ hj)

theorem germs_local (Γ : Germs) (w : ℂ) : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, h, map_one, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)

theorem specPts_nonempty : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (k : Type) [CommRing k] (s₀ : S ⟶ Sp k) [LocallyOfFiniteType s₀] (b₀ : k →+* ℂ), y ≫ s₀ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp b₀) → AnFin A → Φ.Rational → Nonempty (SpecPts Φ Γ) := by
  intro h1 h2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ k _ s₀ _ b₀ hy hA hΦ
  classical
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C'⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  haveI := o.proper
  obtain ⟨x₀, hx₀⟩ := hΦ.1 0
  have hy₀ : spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ x₀ ≫ o.t.G.hom = y := by
    rw [← Category.assoc, hx₀]
    exact Over.w (Φ.x 0)
  set y₀ := x₀ ≫ o.t.G.hom
  have hin : ∀ U : S.Opens, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ y₀ ⁻¹ᵁ U := by
    intro U hU p _
    rw [← hy₀] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hs₀ : y₀ ≫ s₀ = spMap ((algebraMap ℂ Conv.convLaurent).comp b₀) := by
    refine HolHom.point_ext (isAffineOpen_top _) le_top le_top fun g => Subtype.ext ?_
    have e1 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (y₀ ≫ s₀) ⊤ le_top g
    have e2 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩)
      (spMap ((algebraMap ℂ Conv.convLaurent).comp b₀)) ⊤ le_top g
    rw [← Category.assoc, hy₀, hy] at e1
    rw [← spMap_comp] at e2
    exact e1.symm.trans e2
  obtain ⟨T₁, hT₁, y₁, hy₁U, hy₁, -⟩ :=
    Conv.exists_halfRing_point s₀ b₀ y₀ hs₀ C.aff (hin _ C.mem) (max C.T C'.T)
  obtain ⟨T, hT, hU'⟩ := Conv.exists_le_preimage_inclusion y₁ (U := C'.U) (by rw [hy₁]; exact hin _ C'.mem)
  set yT := spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) : Conv.halfRing T₁ →+* Conv.halfRing T) ≫ y₁ with hyT
  have hU : ⊤ ≤ yT ⁻¹ᵁ C.U := le_comp _ _ _ hy₁U
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y := by
    rw [← hy₀, ← hy₁, hyT, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    rfl
  have hC : C.T ≤ T := ((le_max_left _ _).trans hT₁).trans hT
  have hC' : C'.T ≤ T := ((le_max_right _ _).trans hT₁).trans hT
  have key : ∀ (w : ℂ) (hw : T < w.im) (v : A.V), ∃ (z : Sp (Γ.R w) ⟶ o.t.G.left) (σ : o.t.PP.L.ι → Γ.R w),
      z ≫ o.t.G.hom = spMap (Subalgebra.inclusion (Γ.le T w hw)).toRingHom ≫ yT ∧
      spMap (Γ.R w).val.toRingHom ≫ z = (Φ.x v).left ∧ IsFrm o.t.PP.L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ o.t.PP.L.U j → (Γ.R w).val.toRingHom (σ j) = Φ.τ v j := by
    intro w hw v
    haveI := germs_local Γ w
    have hw₁ := hC.trans_lt hw
    have hw₂ := hC'.trans_lt hw
    obtain ⟨i, hi⟩ := C.bpf w hw₁ v
    obtain ⟨i', hi'⟩ := C'.bpf w hw₂ v
    refine exists_ext o.t.G o.t.PP.L o.t.PP.isLB (Γ.R w).val.toRingHom Subtype.val_injective _ (Φ.x v).left ?_
      (Φ.τ v) (Φ.frm v) C.U C.aff (le_comp _ _ _ hU) C.b C.emb
      (fun i => Subalgebra.inclusion (Γ.le _ w hw₁) (C.cf i v)) ⟨i, Γ.unit w _ (by rw [Γ.ev_eq]; exact hi)⟩
      (fun i x' j => C.val i v x' j) C'.U (le_comp _ _ _ hU') (C'.b i')
      (Subalgebra.inclusion (Γ.le _ w hw₂) (C'.cf i' v)) (Γ.unit w _ (by rw [Γ.ev_eq]; exact hi'))
      (fun x' j => C'.val i' v x' j)
    rw [← Category.assoc, ← spMap_comp]
    exact (Over.w (Φ.x v)).trans hgen.symm
  choose z σ hz1 hz2 hz3 hz4 using key
  have hpi : ∀ (w : ℂ) (hw : T < w.im) (v : A.V),
      (spMap (Γ.ev w).toRingHom ≫ z w hw v) ≫ o.t.G.hom = Conv.halfCurve yT w := by
    intro w hw v
    rw [Category.assoc, hz1, ← Category.assoc, ← spMap_comp, Conv.halfCurve_eq yT hw]
    congr 2
    exact RingHom.ext fun r => Γ.ev_eq T w hw r
  exact ⟨{
    T := T
    yT := yT
    yT_gen := hgen
    xt := fun w hw v => Over.homMk (z w hw v) (hz1 w hw v)
    xt_gen := hz2
    τt := fun w v => if hw : T < w.im then σ w hw v else fun _ => 1
    τt_frm := fun w hw v => by rw [dif_pos hw]; exact hz3 w hw v
    τt_gen := fun w hw v j hj => by rw [dif_pos hw]; exact hz4 w hw v j hj
    yw := Conv.halfCurve yT
    yw_eq := fun w hw => Conv.halfCurve_eq yT hw
    pi := fun w v => if hw : T < w.im then Over.homMk (spMap (Γ.ev w).toRingHom ≫ z w hw v) (hpi w hw v) else 1
    pi_eq := fun w hw v => by rw [dif_pos hw]; rfl }⟩

end GlobalTheory.ArcPts.Special
