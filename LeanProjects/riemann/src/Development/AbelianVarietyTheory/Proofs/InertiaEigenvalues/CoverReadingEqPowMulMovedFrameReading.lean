import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsObjMapOfCoprime
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in

theorem exists_latEquiv (L₁ L₂ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : (L₁ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (L₂ : Set _)) :
    ∃ f : L₂ ≃ₗ[𝓞 E] L₁, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let f : L₂ →ₗ[𝓞 E] L₁ :=
    { toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), by
        rw [← SetLike.mem_coe, h]
        exact ⟨a, a.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
      map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul]) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun a b hab => Subtype.ext ?_, fun v => ?_⟩, fun _ => rfl⟩
  · rw [← hli a, ← hli b]
    exact congrArg _ (congrArg Subtype.val hab)
  · have hv : (v : Fin r → E) ∈ (L₁ : Set (Fin r → E)) := v.2
    rw [h] at hv
    obtain ⟨u, hu, e⟩ := hv
    exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem perFr_move (X X' : Data E r) (hΨ : ∀ τ, τ ∈ X'.Ψ ↔ τ ∈ X.Ψ) (hp : X'.p0 = X.p0) (hG : X'.Gm = X.Gm)
    (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X'.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (x' : Frame X'.Ψ r)
    (hx : ∀ τ (h : τ ∈ X.Ψ) (h' : τ ∈ X'.Ψ), mat x' ⟨τ, h'⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h⟩)
    (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x' ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  rw [hG] at hγ
  unfold perFr
  rw [hp, hG]
  by_cases h₁ : τ ∈ X.Ψ
  · rw [dif_pos h₁, dif_pos ((hΨ τ).2 h₁), hx τ h₁, GlobalTheory.PerMove.emb_mulVec, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _), Matrix.mul_one]
  · rw [dif_neg h₁, dif_neg (mt (hΨ τ).1 h₁)]
    by_cases h₂ : conjEmb τ ∈ X.Ψ
    · rw [dif_pos h₂, dif_pos ((hΨ _).2 h₂), hx _ h₂]
      simp only [GlobalTheory.PerMove.emb_mulVec, GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
    · rw [dif_neg h₂, dif_neg (mt (hΨ _).1 h₂)]

end Lattice

theorem congr_one {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (L : AddSubgroup (Fin n → A))
    (M : ℕ) (z : Fin n → A) : ∃ w ∈ L, (f 1).1 *ᵥ z = z + M • w :=
  ⟨0, zero_mem _, by rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]⟩

theorem congr_of_mul {A : Type} [AddCommGroup A] (L : AddSubgroup A) (M p : ℕ) {x : A}
    (h : ∃ w ∈ L, x = (M * p) • w) : ∃ w ∈ L, x = M • w := by
  obtain ⟨w, hw, e⟩ := h
  exact ⟨p • w, nsmul_mem hw p, e.trans (mul_smul M p w)⟩

set_option maxHeartbeats 1000000 in

theorem move_mark {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _)) :
    ∃ δ : GL (Fin r) D.host.E,
      (∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (δ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x)) ∧
      ∀ (M p : ℕ), M ≠ 0 → ∀ (v₁ v₂ : Fin r → D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E),
        (∃ w ∈ latGHat V (γ₁ * h), finVec V (v₁ ∘ Fin.cast hr) - (finHom V (γ₁ * h)).1.mulVec z = M • w) →
        (∃ w ∈ latGHat V (γ₂ * h), finVec V (v₂ ∘ Fin.cast hr) - (finHom V (γ₂ * h)).1.mulVec z = (M * p) • w) →
        ∃ u ∈ L₁, (δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v₂ = v₁ + M • u := by
  subst hr
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  obtain ⟨δ, -, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hmem : ∀ v, v ∈ L₁ ↔ finVec V v ∈ latGHat V (γ₁ * h) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL₁]
    exact Set.ext_iff.1 (Set.image_id _) v
  refine ⟨δ, fun τ θ hθ x => ?_, fun M p hM v₁ v₂ z h₁ h₂ => ?_⟩
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]
  · have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
    obtain ⟨-, ht⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
      (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) M (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
    rw [hprod] at ht
    obtain ⟨y, hy, e⟩ := ht (finVec V v₂) (finVec V v₁) z z (congr_one _ _ M z) (congr_of_mul _ M p h₂) h₁
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V M hM (δ.1 *ᵥ v₂ - v₁) y (by
      rw [← e, hδf]
      funext i
      exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem w).2 (hw ▸ hy), sub_eq_iff_eq_add'.1 e'⟩

section Geo

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem point_over (d : DeltaDat Xo c n) (hd : d.IsLev) (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (hle : KA l ≤ KA d.l₂)
    {σ : KA l →+* ℂ} {σ₂ : KA d.l₂ →+* ℂ} (hσ : σ₂.comp (IntermediateField.inclusion hle).toRingHom = σ)
    {ι : Type} {g g₂ : ℕ} (e : Fin g ≃ ι) (e₂ : Fin g₂ ≃ ι) {ty : Fin g → (E →+* ℂ)} {ty₂ : Fin g₂ → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (F₂ : FamilyUnif d.Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n)
    {P : (F.Di k).La →+ (Fin g → ℂ)} {P₂ : (F₂.Di k₂).La →+ (Fin g₂ → ℂ)} (hP : IsPeriod (F.Di k) ty P)
    (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂) (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La)
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a j, P (gam a) j = P₂ a (e₂.symm (e j))) :
    F₂.u k₂ P₂ ≫ d.r = F.u k P ∧ ∀ (ℓ : ι) v v₂,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ℓ) 1) v →
      IsDerivAt0 (fun z => (F₂.ex k₂ P₂ z).left) (Pi.single (e₂.symm ℓ) 1) v₂ → v₂ ≫ d.m.φ = v := by
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  have hy : (F₂.u k₂ P₂ ≫ d.r) ≫ Xo.s = spMap σ := by
    rw [Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle, ← Category.assoc, F₂.over_σ k₂ P₂ hP₂,
      GlobalTheory.ClsVal.Cmp.spMap_comp', hσ]
  let h : (Fin g₂ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (e.trans e₂.symm)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CoverExp.ex_comp_eq d.m d.pd hA hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ k k₂ hP hP₂ hy gam h
    hEF gM fun a => funext (hh a)
  refine ⟨h₁, fun ℓ v v₂ hv hv₂ => ?_⟩
  have k₁ := GlobalTheory.FibreDeriv.isDerivAt0_comp hv₂ d.m.φ
  simp only [h₂] at k₁
  have k₂ := (GlobalTheory.ExpChain.isDerivAt0_comp_linear _ (GlobalTheory.ExpChain.isHolTo_ex F k P hP) h.toLinearMap _ _).1 k₁
  have k₃ : h.toLinearMap (Pi.single (e₂.symm ℓ) 1) = Pi.single (e.symm ℓ) 1 := by
    funext j
    change (Pi.single (e₂.symm ℓ) 1 : Fin g₂ → ℂ) (e₂.symm (e j)) = _
    rw [Pi.single_apply, Pi.single_apply]
    exact if_congr (e₂.symm.apply_eq_iff_eq.trans e.eq_symm_apply.symm) rfl rfl
  rw [k₃] at k₂
  exact GlobalTheory.VerticalDeriv.isDerivAt0_unique k₂ hv

theorem wchar_generator {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) (t : Sˣ) :
    wchar (ex Dw a m) (fun i => Option.elim i t (fun _ => 1)) = (t : S) ^ m := by
  simp [wchar, Fintype.prod_option, ex]

end Geo

section Read

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

theorem read_of_over {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂))
    (hx : y₂.x ≫ C.d.r = y.x) (hu : ∀ τ i, y₂.u τ i ≫ C.d.m.φ = y.u τ i) :
    ∃ t : ℂ, t ≠ 0 ∧ ∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j), ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n,
      C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y) := by
  letI : Field (CAt C.σ₂) := inferInstanceAs (Field ℂ)
  letI : Algebra T.Q.c.F (CAt C.σ₂) := (show T.Q.c.F →+* CAt C.σ₂ from σ).toAlgebra
  letI : Algebra C.c'.F (CAt C.σ₂) :=
    (show C.c'.F →+* CAt C.σ₂ from C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt C.σ₂) := fun a => RingHom.congr_fun hσ a
  have hc : ∀ x : C.c'.F, algebraMap C.d.c₂.F (CAt C.σ₂) (C.d.eF x) = algebraMap C.c'.F (CAt C.σ₂) x := fun _ => rfl
  let y₀ : FrPt (T.Q.Xo j) T.Q.c (CAt C.σ₂) := y
  obtain ⟨z, hz, ho⟩ := GlobalTheory.FrameLift.exists_frOver C.d hc (y₀.ext C.hle hA) y₂.x hx y₂.x_over
  have hzu : y₂.u = z.u := by
    funext τ i
    refine C.d.m.cart.1.hom_ext ((hu τ i).trans (ho.2.1 τ i).symm) ?_
    rw [(y₂.tan τ i).1, (z.tan τ i).1, hz]
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen z y₂ hz.symm hzu
  refine ⟨toC (t : CAt C.σ₂), t.ne_zero, fun n a f f₂ hf₂ hp => ?_⟩
  have e₁ := GlobalTheory.NonDominant.evR_weight hf₂ ht
  rw [wchar_generator] at e₁
  have e₂ := hp (CAt C.σ₂) hA hc z (y₀.ext C.hle hA) ho
  exact e₁.trans (congrArg (fun s => (t : CAt C.σ₂) ^ n * s) e₂)

end Read

set_option maxHeartbeats 1000000 in

theorem rdU_cover_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  obtain ⟨t, ht, H⟩ := read_of_over C hσ₂ ((T.U j σ).un _ ⟨x', hx'⟩) (C.U₂.un _ ⟨x, hx⟩)
    (by rw [hu₁, hu₂]; exact k₁) fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)
  refine ⟨t, ht, fun n a _ f _ f₂ hf₂ hp => ?_⟩
  have b₁ : rdU (T.U j σ) f (T.dict j σ h).1 x' = toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un _ ⟨x', hx'⟩)) := dif_pos hx'
  have b₂ : rdU C.U₂ f₂ (C.dict₂ h).1 x = toC (evR C.d.Xo₂ C.d.c₂ f₂ (C.U₂.un _ ⟨x, hx⟩)) := dif_pos hx
  rw [b₁, b₂]
  exact H n a f f₂ hf₂ hp

end GlobalTheory.CoverFrameRead
