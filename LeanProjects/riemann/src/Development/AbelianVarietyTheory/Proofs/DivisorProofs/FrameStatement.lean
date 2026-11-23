import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleClassesRationalLiftFormsLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutationAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutationAtSmallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsAtSmallPlaceStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOf

theorem exists_padicEmbedding_detecting_prime_of_lPlace : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)),
    ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∃ e0 : K →+* PadicAlgCl l, ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 (x : K)‖ < 1 :=
  fun _ _ _ _ _ w hw => Formalism.BasicNotions.Examples₂.LB.exists_embAt w hw

theorem g_io : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (e0 : K →+* PadicAlgCl l) (σ : K →+* ℂ),
    ∃ io : PadicAlgCl l ≃+* ℂ, ∀ x, io (e0 x) = σ x := by
  intro K _ _ l _ e0 σ
  have hR : Cardinal.mk K ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ K).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  have hc := GlobalTheory.cardinalMk_padicAlgCl_eq_continuum l
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp e0 σ hR (by rw [hc]; exact Cardinal.aleph0_lt_continuum)
    (by rw [hc, Cardinal.mk_complex])

theorem g_ring : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)),
    Function.Injective (intEmb Lf) ∧ Set.range (intEmb Lf) = {x | x ∈ Lf ∧ ‖x‖ ≤ 1} := by
  intro l _ Lf
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), ?_⟩
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

theorem g_root : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : ℕ) (z : PadicAlgCl l), 0 < M →
    z ∈ Lf → z ^ M = 1 → ∃ u : (intR Lf)ˣ, intEmb Lf u = z := by
  intro l _ Lf M z hM hz hzM
  have hn : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ M = 1 := by rw [← norm_pow, hzM, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hM.ne').1 h1
  have hr := (g_ring l Lf).2
  have hz' : z ∈ Set.range (intEmb Lf) := by rw [hr]; exact ⟨hz, hn.le⟩
  have hzi : z⁻¹ ∈ Set.range (intEmb Lf) := by
    rw [hr]; exact ⟨inv_mem hz, by rw [norm_inv, hn, inv_one]⟩
  obtain ⟨a, ha⟩ := hz'
  obtain ⟨b, hb⟩ := hzi
  have hz0 : z ≠ 0 := by rintro rfl; simp at hn
  have hab : a * b = 1 := (g_ring l Lf).1 (by rw [map_mul, ha, hb, mul_inv_cancel₀ hz0, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

theorem g_lift : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l) (K : Type) [Group K]
    (f : K → ι → Matrix (Fin N) (Fin N) (PadicAlgCl l)), Function.Injective emb → (∀ τ, f 1 τ = 1) →
    (∀ κ κ' τ, f (κ * κ') τ = f κ τ * f κ' τ) → (∀ κ τ a c, f κ τ a c ∈ Set.range emb) →
    ∃ kap : K →* (ι → GL (Fin N) O), ∀ κ τ, (Matrix.GeneralLinearGroup.map emb (kap κ τ)).val = f κ τ := by
  intro l _ ι N O _ emb K _ f hinj h1 hmul hr
  choose g hg using hr
  have hmap : ∀ κ τ, (Matrix.of fun a c => g κ τ a c).map emb = f κ τ := fun κ τ => by
    ext a c; simp [hg]
  have hinjM : ∀ A B : Matrix (Fin N) (Fin N) O, A.map emb = B.map emb → A = B := fun A B h => by
    ext a c; exact hinj (congrFun (congrFun h a) c)
  let m : K → ι → Matrix (Fin N) (Fin N) O := fun κ τ => Matrix.of fun a c => g κ τ a c
  have hm1 : ∀ τ, m 1 τ = 1 := fun τ => hinjM _ _ (by rw [hmap, h1, Matrix.map_one _ (map_zero _) (map_one _)])
  have hmm : ∀ κ κ' τ, m (κ * κ') τ = m κ τ * m κ' τ := fun κ κ' τ =>
    hinjM _ _ (by rw [hmap, Matrix.map_mul, hmap, hmap, hmul])
  let u : K → ι → GL (Fin N) O := fun κ τ =>
    ⟨m κ τ, m κ⁻¹ τ, by rw [← hmm, mul_inv_cancel, hm1], by rw [← hmm, inv_mul_cancel, hm1]⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun κ τ => ?_⟩
  · funext τ; exact Units.ext (hm1 τ)
  · intro κ κ'; funext τ; exact Units.ext (hmm κ κ' τ)
  · exact hmap κ τ

theorem g_chi : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] (N : ℕ) (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l) (K : Type)
    [Group K] (kap : K →* (ι → GL (Fin N) O)) (ψ : K →* ℂˣ) (io : PadicAlgCl l ≃+* ℂ) (sh : ι → ℤ), Function.Injective emb →
    (∀ κ, ∃ u : Oˣ, emb u = io.symm (ψ κ : ℂ)) →
    ∃ chi : K →* Oˣ, ∀ κ, io (emb (chi κ) * ∏ τ, emb (kap κ τ).val.det ^ sh τ) * (ψ κ : ℂ) = 1 := by
  intro l _ ι _ N O _ emb K _ kap ψ io sh hinj hu
  choose u hu using hu
  have hU : ∀ κ κ', u (κ * κ') = u κ * u κ' := fun κ κ' => Units.ext (hinj (by
    simp only [hu, map_mul, Units.val_mul]))
  have hU1 : u 1 = 1 := Units.ext (hinj (by simp only [hu, map_one, Units.val_one]))
  let U : K →* Oˣ := { toFun := u, map_one' := hU1, map_mul' := hU }
  let dτ : ι → (K →* Oˣ) := fun τ => Matrix.GeneralLinearGroup.det.comp ((Pi.evalMonoidHom _ τ).comp kap)
  refine ⟨U⁻¹ * ∏ τ, dτ τ ^ (-sh τ), fun κ => ?_⟩
  let m : Oˣ →* (PadicAlgCl l)ˣ := Units.map (emb : O →* PadicAlgCl l)
  have key : m ((U⁻¹ * ∏ τ, dτ τ ^ (-sh τ)) κ) * ∏ τ, m (dτ τ κ) ^ sh τ = (m (U κ))⁻¹ := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.finsetProd_apply, MonoidHom.zpow_apply, map_mul, map_inv,
      map_prod, map_zpow, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have key' := congrArg Units.val key
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, m, Units.coe_map,
    MonoidHom.coe_coe] at key'
  have e2 : ∀ τ, emb (kap κ τ).val.det = emb ((dτ τ κ : Oˣ) : O) := fun τ => by
    simp [dτ, Matrix.GeneralLinearGroup.val_det_apply]
  simp only [e2]
  rw [key']
  have hUk : emb ((U κ : Oˣ) : O) = io.symm (ψ κ : ℂ) := hu κ
  rw [hUk, map_inv₀, RingEquiv.apply_symm_apply, inv_mul_cancel₀ (Units.ne_zero _)]

theorem g_fin : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (e0 : K →+* PadicAlgCl l) (M : ℕ), 0 < M →
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range e0 ∪ {z : PadicAlgCl l | z ^ M = 1})) := by
  intro K _ _ l _ e0 M hM
  let b := Module.finBasis ℚ K
  let T : Set (PadicAlgCl l) := Set.range (fun i => e0 (b i)) ∪ ((Polynomial.nthRootsFinset M (1 : PadicAlgCl l) : Finset _) : Set _)
  have hT : T.Finite := (Set.finite_range _).union (Finset.finite_toSet _)
  haveI : Finite T := hT.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range e0 ∪ {z : PadicAlgCl l | z ^ M = 1}) ≤ IntermediateField.adjoin ℚ_[l] T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro z (⟨y, rfl⟩ | hz)
    · rw [← b.sum_repr y, map_sum]
      refine IntermediateField.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
      exact IntermediateField.mul_mem _ (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ (Or.inl ⟨i, rfl⟩))
    · exact IntermediateField.subset_adjoin _ _ (Or.inr (by
        simpa [Polynomial.mem_nthRootsFinset hM] using hz))
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective

end GlobalTheory.FrameOf

namespace GlobalTheory.FrameOf

theorem inRange_and {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : InRange Q1) (h2 : InRange Q2) :
    InRange fun Fm x hx i p j P W w => Q1 Fm x hx i p j P W w ∧ Q2 Fm x hx i p j P W w := by
  unfold InRange GlobalTheory.BigOn.AtPts at h1 h2 ⊢
  refine Closed.imp (Closed.and h1 h2) fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := EvPt.and h.1 h.2
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR =>
    ⟨(hx0 x hx hle i p hp).1 hM j P W hD hN w hw hR, (hx0 x hx hle i p hp).2 hM j P W hD hN w hw hR⟩⟩

theorem inRange_imp {Q1 Q2 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (_ : Pt Fm x hx i)
      (_ : Fin (Fm.D x i).R.m) (_ : Par) (_ : Wts (Fm.D x i).what₂.Tau), HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL) → Prop}
    (h1 : InRange Q1) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i)
      (j : Fin (Fm.D x i).R.m) (P : Par) (W : Wts (Fm.D x i).what₂.Tau) (w : HeightOneSpectrum (𝓞 (Fm.D x i).what₂.LL)),
      Dict (Fm.L x i) j P W → Q1 Fm x hx i p j P W w → Q2 Fm x hx i p j P W w) : InRange Q2 := by
  unfold InRange GlobalTheory.BigOn.AtPts at h1 ⊢
  refine Closed.imp h1 fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx hle i p hp hM j P W hD hN w hw hR => f Fm x hx i p j P W w hD (hx0 x hx hle i p hp hM j P W hD hN w hw hR)⟩

theorem plc_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem conj_submatrix_map_mul_eq_mul_conj_submatrix {A B : Type} [CommRing A] [CommRing B] {n N : ℕ} (f : A →+* B) (bs : GL (Fin N) B) (rk : Fin N ≃o Fin n)
    (X Y : Matrix (Fin n) (Fin n) A) :
    (bs⁻¹).val * ((X * Y).map f).submatrix rk rk * bs.val =
      ((bs⁻¹).val * (X.map f).submatrix rk rk * bs.val) * ((bs⁻¹).val * (Y.map f).submatrix rk rk * bs.val) := by
  have h2 : ((X * Y).map f).submatrix rk rk = (X.map f).submatrix rk rk * (Y.map f).submatrix rk rk := by
    rw [Matrix.map_mul]; exact (Matrix.submatrix_mul_equiv _ _ rk rk.toEquiv rk).symm
  have hb : bs.val * (bs⁻¹).val = 1 := Units.mul_inv bs
  rw [h2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bs.val (bs⁻¹).val, hb, Matrix.one_mul]

theorem conj_submatrix_map_one_eq_one {A B : Type} [CommRing A] [CommRing B] {n N : ℕ} (f : A →+* B) (bs : GL (Fin N) B) (rk : Fin N ≃o Fin n) :
    (bs⁻¹).val * ((1 : Matrix (Fin n) (Fin n) A).map f).submatrix rk rk * bs.val = 1 := by
  have h2 : (1 : Matrix (Fin n) (Fin n) B).submatrix rk rk = 1 := Matrix.submatrix_one_equiv rk.toEquiv
  rw [Matrix.map_one f (map_zero f) (map_one f), h2, Matrix.mul_one]
  exact Units.inv_mul bs

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem kapMat_one (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l N : ℕ} [Fact l.Prime]
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (τ : D.what₂.Tau) :
    kapMat p j t ev bs rk 1 τ = 1 :=
  conj_submatrix_map_one_eq_one (ev τ) (bs τ) rk

theorem kapMat_mul (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l N : ℕ} [Fact l.Prime]
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ κ' : levJ p j t) (τ : D.what₂.Tau) :
    kapMat p j t ev bs rk (κ * κ') τ = kapMat p j t ev bs rk κ τ * kapMat p j t ev bs rk κ' τ :=
  conj_submatrix_map_mul_eq_mul_conj_submatrix (ev τ) (bs τ) rk (matOf j (κ : Bridge.Gf (Vc D j))) (matOf j (κ' : Bridge.Gf (Vc D j)))

theorem frameAt_of (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL))
    (hD : P.Nr = (Vc D j).rank) (hh : HalfAt D (Formalism.EigenvalueLevelCeiling.plc w)) (hk : KapAt p j P w) (hc : ChiAt p j w)
    (ht : TameAt p j w) (hp : PermAt p j P w) (hcm : CommAt p j P w) (hr : ReadsAt p j P W w) :
    FrameAt p j P W w := by
  intro inst
  obtain ⟨e0, he0⟩ := exists_padicEmbedding_detecting_prime_of_lPlace D.what₂.LL (Formalism.EigenvalueLevelCeiling.plc w) w (plc_mem w)
  obtain ⟨io, hio⟩ := g_io D.what₂.LL (Formalism.EigenvalueLevelCeiling.plc w) e0 D.what₂.embLL
  obtain ⟨b, sh, hR⟩ := hr
  have hev0 : ∀ τ, ∃ ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w),
      EvOk (incOf D e0 b τ) ev := fun τ => GlobalTheory.T.exists_finiteAdeleEmbeddingExtension D.host.F D.host.E (Formalism.EigenvalueLevelCeiling.plc w) (incOf D e0 b τ)
  choose ev hev using hev0
  let rk : Fin P.Nr ≃o Fin (Vc D j).rank := Fin.castOrderIso hD
  obtain ⟨bs, hb1, hbs⟩ := hk e0 b ev rk he0 hev
  obtain ⟨M, hM, hMχ⟩ := hc
  let Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) :=
    IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0 ∪ {z : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) | z ^ M = 1})
  haveI : FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf := g_fin D.what₂.LL (Formalism.EigenvalueLevelCeiling.plc w) e0 M hM
  have hLf : IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ≤ Lf :=
    IntermediateField.adjoin.mono _ _ _ Set.subset_union_left
  have hring := g_ring (Formalism.EigenvalueLevelCeiling.plc w) Lf
  obtain ⟨kap, hkap⟩ := g_lift (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr (intR Lf) (intEmb Lf) (levJ p j (p.R.mu w))
    (kapMat p j (p.R.mu w) ev bs rk) hring.1 (kapMat_one p j _ ev bs rk) (kapMat_mul p j _ ev bs rk) (fun κ τ a c => by
      rw [hring.2]; exact ⟨hLf (hbs κ τ a c).1, (hbs κ τ a c).2⟩)
  have hroot : ∀ κ, (io.symm ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ)) ^ M = 1 := fun κ => by
    rw [← map_pow, hMχ κ, map_one]
  obtain ⟨chi, hchi⟩ := g_chi (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr (intR Lf) (intEmb Lf) (levJ p j (p.R.mu w)) kap
    (levChi p j (p.R.mu w)) io sh hring.1
    (fun κ => g_root (Formalism.EigenvalueLevelCeiling.plc w) Lf M _ hM (IntermediateField.subset_adjoin _ _ (Or.inr (hroot κ))) (hroot κ))
  have hC : ChoiceOk p j w e0 b io ev bs rk sh kap chi :=
    ⟨he0, fun x => hLf (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩), hio, hev, hkap, hchi⟩
  obtain ⟨R, hRe, hRix⟩ := hR e0 io ev bs rk Lf kap chi hC hb1
  refine ⟨frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi, R, incOf D e0 b,
    ⟨⟨hring.1, Lf, inferInstance, hring.2⟩, GlobalTheory.T.finiteDoubleClasses_rational_liftFormsLevel p j (p.R.mu w), ht, hp e0 b io ev bs rk sh Lf kap chi hC,
      hcm e0 b io ev bs rk sh Lf kap chi hC⟩, ⟨?_⟩⟩
  rw [hRe, hRix]
  exact
    { rk := rk
      e := MulEquiv.refl _
      io := io
      ev := ev
      bs := bs
      sh := sh
      liftFrame_embedding_base := hio
      half := hh e0 b
      lab := fun τ => by cases b <;> simp [incOf]
      ev_rat := fun τ => (hev τ).1
      ev_int := fun τ => (hev τ).2.1
      rat := fun _ => Iff.rfl
      lev := fun _ => Iff.rfl
      kap := hkap
      chi := fun κ _ => hchi κ
      ix_inj := Subtype.val_injective
      ix_range := fun i => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨i, h⟩, rfl⟩⟩
      tr := fun _ _ => Iff.rfl
      cst := fun _ => rfl }

end Point

theorem frameSt_of_smallSt : SmallSt → FrameSt := by
  intro hS
  have h := inRange_and hS (inRange_and GlobalTheory.T.half_at_small_place (inRange_and GlobalTheory.T.kappa_at_small_place (inRange_and GlobalTheory.T.character_at_small_place (inRange_and GlobalTheory.T.tame_at_small_place
    (inRange_and GlobalTheory.T.permutation_at_small_place (inRange_and GlobalTheory.T.commutation_at_small_place GlobalTheory.T.reads_at_small_place))))))
  refine inRange_imp h fun Fm x hx i p j P W w hD hq => ?_
  obtain ⟨hs, hh, hk, hc, ht, hp, hcm, hr⟩ := hq
  exact frameAt_of p j P W w hD.Nr (hh hs) (hk hs) (hc hs) (ht hs) (hp hs) (hcm hs) (hr hs)

end GlobalTheory.FrameOf

end
