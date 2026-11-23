import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DetLine.CoverU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigSpread
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt)
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}

theorem exists_eigBasisAt {R : Type} [CommRing R] {x : Sp R ⟶ S} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
    (hx : IsUnivChart _ n xc) (χ : 𝓞 E →+* R) {m : ℕ} (B : Fin m → Fin n → R)
    (hB : ∀ i, B i ∈ ReciprocityTheory.ChartRestriction.G.Chart.eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) χ)
    (hu : ∀ v ∈ ReciprocityTheory.ChartRestriction.G.Chart.eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) χ,
      ∃! a : Fin m → R, v = ∑ j, a j • B j) :
    ∃ v : Fin m → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v := by
  refine ⟨fun i => Over.homMk (vec t x xc (B i)) (vec_tan hx _).1,
    fun i => ⟨(vec_tan hx _).2, (vec_eig_iff hx χ _).2 (hB i)⟩, fun w hw => ?_⟩
  obtain ⟨cc, hcc⟩ := vec_exists hx w.left ⟨Over.w w, hw.1⟩
  have he := (vec_eig_iff hx χ cc).1 (fun a => by rw [← hcc]; exact hw.2 a)
  refine (existsUnique_congr fun a => ?_).1 (hu cc he)
  rw [← comb_iff hx, ← hcc]
  exact exists_congr fun u => and_congr Iff.rfl
    ⟨fun h => Over.OverMorphism.ext h.symm, fun h => by rw [h]⟩

variable {l : Level H} (c : Coeff l)

theorem exists_local_basis {X : Scheme.{0}} (π : X ⟶ S) (s : X ⟶ Sp c.F) {m : ℕ} {τ : E →+* ℂ}
    (hm : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ X), y ≫ s = spMap φ →
      LieMult t.act (y ≫ π) (φ.comp (embK c τ)) m) {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L)
    (x : Sp L ⟶ X) (hφ : x ≫ s = spMap φ) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback (x ≫ π)).obj t.G}
    (hx : IsUnivChart _ n xc) (P : Matrix (Fin n) (Fin n) L)
    (hP : ∀ v, P *ᵥ v ∈ eig c φ hx τ ∧ (v ∈ eig c φ hx τ → P *ᵥ v = v)) :
    ∃ B : Fin m → Fin n → L, (∀ j, P *ᵥ B j = B j) ∧ ∀ v, ∃! a : Fin m → L, P *ᵥ v = ∑ j, a j • B j := by
  let k : Type := AlgebraicClosure (IsLocalRing.ResidueField L)
  let ψk : L →+* k := (algebraMap (IsLocalRing.ResidueField L) k).comp (IsLocalRing.residue L)
  obtain ⟨xk, hxk, hk⟩ := eig_bc c φ hx ψk
  have B : Module.Basis (Fin m) L (eig c φ hx τ) := by
    have he : IsIdempotentElem P.mulVecLin := LinearMap.ext fun v => (hP _).2 (hP v).1
    have hr : LinearMap.range P.mulVecLin = eig c φ hx τ :=
      Submodule.ext fun v => ⟨fun ⟨v', h⟩ => by rw [← h]; exact (hP v').1, fun h => ⟨v, (hP v).2 h⟩⟩
    have fr := Formalism.L2.Pj.LocFrM.range_free _ he
    have fi : Module.Finite L (LinearMap.range P.mulVecLin) := Module.Finite.range _
    rw [hr] at fr fi
    refine Module.finBasisOfFinrankEq L _ ((hk τ).2.2.trans ?_)
    have h := hm k (ψk.comp φ) (spMap ψk ≫ x)
      (by rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap])
    rw [Category.assoc] at h
    exact ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult (isGrpPullback_id t.G) (Category.comp_id _) hxk t.act t.act.act
      (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) _ (fun a => rfl)
      ((ψk.comp φ).comp (embK c τ)) h
  refine ⟨fun i => B i, fun i => (hP _).2 (B i).2, fun v => ?_⟩
  have key : ∀ a : Fin m → L, (P *ᵥ v = ∑ j, a j • (B j : Fin n → L)) ↔ B.equivFun ⟨_, (hP v).1⟩ = a := fun a => by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp
  simp only [key]
  exact existsUnique_eq'

theorem exists_affine_bases {X : Scheme.{0}} (π : X ⟶ S) (s : X ⟶ Sp c.F) (m : (E →+* ℂ) → ℕ)
    (hm : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ X), y ≫ s = spMap φ →
      ∀ τ, LieMult t.act (y ≫ π) (φ.comp (embK c τ)) (m τ)) (U : X.Opens) (z : X) (hzU : z ∈ U) :
    ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : c.F →+* Γ(X, W)), z ∈ W ∧ W ≤ U ∧
      (show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ s = spMap j ∧
      ∀ τ, ∃ v : Fin (m τ) → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G),
        IsEigBasisAt t.act ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) (j.comp (embK c τ)) v := by
  obtain ⟨U₀, hU₀, hz, x₀, hx₀, C, n, xc, hx⟩ := exists_affine_chart t π z
  let j : Sp Γ(X, U₀) ⟶ X := hU₀.fromSpec
  let φ₀ : c.F →+* Γ(X, U₀) := (Spec.preimage (j ≫ s)).hom
  have hφ₀ : spMap φ₀ = j ≫ s := Spec.map_preimage _
  have hov : ∀ {R : Type} [CommRing R] (ψ : Γ(X, U₀) →+* R), (spMap ψ ≫ j) ≫ s = spMap (ψ.comp φ₀) :=
    fun ψ => by rw [Category.assoc, ← hφ₀, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨P, hP⟩ := exists_projectors c φ₀ hx
  let L : Type := X.presheaf.stalk z
  letI : Algebra Γ(X, U₀) L := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  have hloc := hU₀.isLocalization_stalk ⟨z, hz⟩
  obtain ⟨xL, hxL, hvL⟩ := vec_bc_of_chart C hx (algebraMap Γ(X, U₀) L)
    (x' := (spMap (algebraMap Γ(X, U₀) L) ≫ j) ≫ π) (by rw [hx₀, Category.assoc])
  have hPL := hP _ hxL hvL
  choose B hB hB' using fun τ =>
    exists_local_basis c π s (fun k _ _ φ y hy => hm k φ y hy τ) _ _ (hov _) hxL _ (hPL τ)
  choose g hg B₀ hB₀ using fun τ =>
    spread_basis (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl (P τ) (B τ) (hB τ) (hB' τ)
  obtain ⟨f, hfU, hzf⟩ := hU₀.exists_basicOpen_le (V := U) ⟨z, hzU⟩ hz
  let g₀ : Γ(X, U₀) := f * ∏ τ, g τ
  have hU := hU₀.basicOpen g₀
  let ρ : Γ(X, U₀) →+* Γ(X, X.basicOpen g₀) := (X.presheaf.map (homOfLE (X.basicOpen_le g₀)).op).hom
  have hρ : spMap ρ ≫ j = hU.fromSpec := hU₀.map_fromSpec hU _
  have hu : IsUnit (ρ g₀) := X.toRingedSpace.isUnit_res_basicOpen g₀
  have hx₁ : (show Sp Γ(X, X.basicOpen g₀) ⟶ X from hU.fromSpec) ≫ π = spMap ρ ≫ x₀ := by
    rw [hx₀, ← hρ, Category.assoc]
  obtain ⟨xc', hx', hv⟩ := vec_bc_of_chart C hx ρ hx₁
  have hP' := hP _ hx' hv
  refine ⟨_, hU, ρ.comp φ₀, ?_, ?_, by rw [← hρ]; exact hov ρ, fun τ => ?_⟩
  · rw [Scheme.basicOpen_mul]
    refine ⟨hzf, ?_⟩
    show z ∈ X.basicOpen _
    rw [Scheme.mem_basicOpen _ _ _ hz]
    exact IsLocalization.map_units L
      (⟨_, Submonoid.prod_mem _ fun τ _ => hg τ⟩ : (hU₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)
  · rw [Scheme.basicOpen_mul]
    exact inf_le_left.trans hfU
  · have q := hB₀ τ _ ρ (isUnit_of_dvd_unit
      (map_dvd ρ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)).mul_left f)) hu)
    exact exists_eigBasisAt hx' _ (fun i => ρ ∘ B₀ τ i) (fun i => by rw [← q.1 i]; exact (hP' τ _).1)
      fun v hv => q.2 v ((hP' τ v).2 hv)

variable {D : Datum H}

theorem lieMult_univ (Xo : Moduli D l) (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (y : Sp k ⟶ Xo.XF c)
    (hy : y ≫ pullback.snd _ _ = spMap φ) (τ : E →+* ℂ) :
    LieMult Xo.univ.t.act (y ≫ pullback.fst _ _) (φ.comp (embK c τ)) (D.mult τ) := by
  have hd := (Xo.univ.geom k (y ≫ pullback.fst _ _) (φ.comp (IntermediateField.inclusion c.le).toRingHom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm)).1 (φ.comp (embK c τ))
  unfold Datum.mult
  split_ifs with h
  · exact hd.1 (congrArg φ (Subtype.ext h))
  · exact hd.2 fun h' => h (congrArg Subtype.val (φ.injective h'))

theorem mult_conj {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) : D.mult (conjEmb τ) = D.q := by
  refine if_neg fun h => ?_
  have h3 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h
  rw [hτ] at h3
  have h5 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h3
  have h6 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  simp [pow_two, h5] at h6
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.DetLine.CoverU

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.DetLine
  GlobalTheory.DetLine.CoverU in

theorem GlobalTheory.DetLine.frameCover_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) D.p D.q := by
  intro E _ _ _ H D l Xo c U τ hτ z hz
  obtain ⟨W, hW, j, hzW, hWU, hj, hb⟩ :=
    exists_affine_bases (t := Xo.univ.t) c (toX Xo c) (toF Xo c) D.mult (lieMult_univ c Xo) U z hz
  have h₁ := hb τ
  have h₂ := hb (conjEmb τ)
  rw [show D.mult τ = D.p from if_pos hτ] at h₁
  rw [mult_conj hτ] at h₂
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  refine ⟨W, hW, j, v, w, hzW, hj, hW.range_fromSpec.le.trans hWU, hv, ?_⟩
  rw [comp_chi_bar]
  exact hw
