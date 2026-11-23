import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLawsOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAtSurj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Development.AutomorphicArithmetic.DivisorFrames.TangentFamiliesDistinctEmbeddingsIndependent
import Development.AutomorphicArithmetic.DivisorFrames.ArchimedeanSectionValuationBound
import Development.AutomorphicArithmetic.DivisorFrames.ArchimedeanSectionOnComponent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointDiff

section Raise

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare GlobalTheory.LevelRaise

private theorem exists_obj_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (l₂ : Level H) (c₂ : Coeff l₂) {k : Type} [Field k] [NumberField k] (b₀ : KA l →+* k)
    (o : Obj D l (baseKA l) (spMap b₀)) (hA : l₂.A = 1) :
    ∃ (k' : Type) (_ : Field k') (_ : NumberField k') (i : k →+* k') (j₂ : c₂.F →+* k')
      (o₂ : Obj D l₂ (baseKA l₂) (spMap j₂ ≫ spMap (IntermediateField.inclusion c₂.le).toRingHom)),
      Nonempty (SABMap o₂.t o.t (spMap i)) ∧
        j₂ (IntermediateField.inclusion c₂.le (baseKA l₂).ρ) = i (b₀ (baseKA l).ρ) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : k →+* ℂ, ∀ a, σ (b₀ a) = a := by
    letI : Algebra (KA l) k := b₀.toAlgebra
    haveI : Algebra.IsAlgebraic (KA l) k := Algebra.IsAlgebraic.tower_top (K := ℚ) (KA l)
    let τ : k →ₐ[KA l] ℂ := IsAlgClosed.lift
    exact ⟨τ, fun a => τ.commutes a⟩
  have hM : 0 < l₂.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l₂.three_le) l₂.A_pos
  haveI := c₂.fin
  obtain ⟨L, _, _, i, j, σ', hi, hj, hrat⟩ := exists_field o hM σ c₂.F
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap i) o.t
  let o' := ModelCompare.objOfSABMap o m
  let T : PAT H (Sp L) := ⟨t', ObjDim.isAbelianScheme o', _, ObjDim.smoothOfRelativeDimension o', ObjDim.sym,
    o'.ample, o'.ktriv⟩
  let j' : KA l₂ →+* L := j.comp (IntermediateField.inclusion c₂.le).toRingHom
  have hρ : j' (baseKA l₂).ρ = i (b₀ (baseKA l).ρ) := σ'.injective (by
    rw [← RingHom.comp_apply σ' i, hi, hσ]
    exact hj _)
  have hs : ∀ {k₁ : Type} [Field k₁] (β : L →+* k₁),
      spMap β ≫ spMap i ≫ spMap b₀ = spMap (β.comp (i.comp b₀)) := fun β => by
    rw [TorsionRat.sp_comp, TorsionRat.sp_comp]
  obtain ⟨-, I, -⟩ := o'.geom ℂ (spMap σ') _ (hs σ')
  obtain ⟨o₂, ho₂⟩ := RationalTorsion.exists_obj abelianSchemeLaws_all.1 E H D l₂ (KA l₂) (baseKA l₂) L j' σ' T I
    (fun k₁ _ _ β _ => by
      rw [hρ]
      exact (o'.geom k₁ (spMap β) _ (hs β)).1)
    (by
      have h1 := I.ζ_prim 1 one_pos
      have h2 := (baseKA l₂).ζ_prim
      rw [hA] at h2 ⊢
      rw [IsPrimitiveRoot.one_right_iff] at h1 h2
      rw [h1, h2, map_one, map_one, Units.val_one])
    (fun x hx => by
      obtain ⟨q, hq, hq'⟩ := hrat (ObjPull.pushEquiv m.cart (Over.mk (spMap σ')) x) (by rw [← map_pow, hx, map_one])
      refine ⟨Over.homMk (m.cart.1.lift q (𝟙 _) (hq.trans (Category.id_comp _).symm)) (m.cart.1.lift_snd _ _ _), ?_⟩
      apply Over.OverMorphism.ext
      apply m.cart.1.hom_ext
      · rw [Over.comp_left, ObjPull.toUnit_left', Category.assoc]
        exact (congrArg (spMap σ' ≫ ·) (m.cart.1.lift_fst _ _ _)).trans hq'
      · rw [Over.w, Over.w])
  refine ⟨L, inferInstance, inferInstance, i, j, ?_⟩
  rw [TorsionRat.sp_comp]
  exact ⟨o₂, ho₂ ▸ ⟨m⟩, hρ⟩

end Raise

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def Diff {k : Type} [Field k] [NumberField k] (δ : ℝ) (t : SAB H (Sp k)) (τ τ' : E →+* k) (m m' : ℕ) : Prop :=
  ∀ r N r' N', IsEigData t τ m r N → IsEigData t τ' m' r' N' →
    (Function.support (r - r')).Finite ∧ EigenvectorLieDegree.adDeg (r - r') (N / N') = δ

private theorem Diff.down {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}
    {t : SAB H (Sp k)} {t' : SAB H (Sp k')} (n : SABMap t' t (spMap i)) {δ : ℝ} {τ τ' : E →+* k} {m m' : ℕ}
    (h : Diff δ t' (i.comp τ) (i.comp τ') m m') : Diff δ t τ τ' m m' := by
  obtain ⟨π, ε, hu⟩ := exists_isUnder i
  intro r N r' N' h₁ h₂
  obtain ⟨f, d⟩ := h _ _ _ _ (h₁.up hu n) (h₂.up hu n)
  have e : up π ε r - up π ε r' = up π ε (r - r') := funext fun 𝔓 => by simp [up, mul_sub]
  rw [e] at f d
  have g := hu.finite_of_up f
  exact ⟨g, (hu.adDeg_up g (N / N')).symm.trans d⟩

private theorem mult_psi (Dw : Datum H) (τ : Psi H) : Dw.mult τ.1 = Dw.p ∧ Dw.mult (conjEmb τ.1) = Dw.q :=
  ⟨by unfold Datum.mult; rw [if_pos τ.2], by unfold Datum.mult; rw [if_neg (conj_not_mem τ)]⟩

private theorem diff_laws {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r₀ : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x om : ℝ} (hL : Laws U x) (hS : FlatDegree U x om) {K : Type} [Field K]
    [NumberField K] (j : c.F →+* K)
    (o : Obj Dw l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : Psi H) :
    Diff (((Dw.p : ℝ) - Dw.q) / 2 * om) o.t (EigenvectorLieDegree.embIn c j τ.1) (EigenvectorLieDegree.embIn c j (conjEmb τ.1))
      (Dw.mult τ.1) (Dw.mult (conjEmb τ.1)) := by
  rintro r N r' N' ⟨v, hv, hr, hN⟩ ⟨v', hv', hr', hN'⟩
  letI : Algebra c.F K := j.toAlgebra
  have hm := GlobalTheory.T.good_reduction_model_everywhere E H Dw l c K j o hL.pos hL.good hL.lev
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := Xo.rep _ _ inferInstance o
  have hx : f ≫ Xo.s = sOf c K := hf.trans (spMap_comp_spMap _ _)
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  obtain ⟨y, rfl, hy, hy'⟩ := UpperTheory.tangent_families_distinct_embeddings_independent E H Dw l Xo c K f hx o.t m.toSABMap τ.1 (conjEmb τ.1) hne v v' hv hv'
  obtain ⟨Z, hZ⟩ : ∃ Z : Comp Xo c, LiesOn Z y := by
    let s₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hall : ptF y s₀ ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
      rw [sUnion_irreducibleComponents]; trivial
    obtain ⟨W, hW, hq⟩ := Set.mem_sUnion.1 hall
    exact ⟨⟨W, hW⟩, fun s => Subsingleton.elim (α := PrimeSpectrum K) s₀ s ▸ hq⟩
  obtain ⟨⟨s⟩, hdeg⟩ := hS Z τ
  have hd : lineDeg s.toFrame.cInf s.toFrame.rho_vw = ((Dw.p : ℝ) - Dw.q) / 2 * om := by
    have h1 := hdeg s
    rw [s.deg_eq_toFrame, neg_neg, flatDegVal] at h1
    exact add_right_cancel h1
  let a : ArchSec U x Z (flatWt Dw τ) := .ofConst s.toFrame
  have hρ : ∀ la, ∀ w ∈ valOn Z la, w a.sig = (s.toFrame.rho_vw la : EReal) := fun la w hw =>
    (s.toFrame.val_eq hw).trans (by simp)
  obtain ⟨π, ε, hu⟩ := exists_isUnder j
  have hs := GlobalTheory.T.flatSection_ne_zero_at_numberField_point E H Dw l Xo c r₀ U x hL Z τ a K y hZ
  have pos : ∀ {m : ℕ} {v : Fin m → (epsR K ⟶ o.t.G)} {σ N}, EigenvectorLieDegree.IsArchSq o.t.G o.t.PP.L v σ N → 0 < N := by
    rintro m v σ N ⟨_, _, _, _, _, _, _, _, _, -, -, -, h, -⟩
    exact h
  have := o.t.semi.comm
  have e₁ : (fun 𝔓 => (vAdd 𝔓 (evR Xo c a.sig y) : ℝ) + (r - r') 𝔓) = up π ε s.toFrame.rho_vw :=
    funext fun 𝔓 => (UpperTheory.archimedean_section_valuation_bound E H Dw l Xo c r₀ U x hL Z τ a _ hρ K y hZ o.t m.toSABMap v v' hy hy'
      (Indep.of_eigBasis hv) (Indep.of_eigBasis hv') π ε hu.val 𝔓 (hm 𝔓) _ _ (hr 𝔓) (hr' 𝔓)).symm
  have e₂ : (fun σ : K →+* ℂ => ‖σ (evR Xo c a.sig y)‖ ^ 2 * (N / N') σ) = fun σ => s.toFrame.cInf (σ.comp j) ^ 2 :=
    funext fun σ => (UpperTheory.archimedean_section_on_component E H Dw l Xo c r₀ U x hL Z τ a K y hZ o.t m.toSABMap v v' hy hy'
      (fun i => (hv.1 i).1) (fun i => (hv'.1 i).1) σ _ _ (hN σ) (hN' σ)).symm
  have f₃ : (Function.support (r - r')).Finite := by
    have h1 := GlobalTheory.FlatRow.finite_up hu s.toFrame.finite_rho
    rw [← e₁] at h1
    refine (h1.union (finite_vAdd hs)).subset fun 𝔓 h => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact h (by linarith [hc.1, hc.2])
  refine ⟨f₃, ?_⟩
  rw [← hd, ← GlobalTheory.FlatRow.adDeg_mul (N := N / N') hs f₃ fun σ => div_pos (pos (hN σ)) (pos (hN' σ)), e₁, ← GlobalTheory.FlatRow.adDeg_sq]
  exact (congrArg _ e₂).trans (hu.adDeg_up s.toFrame.finite_rho fun σ => s.toFrame.cInf σ ^ 2)

private theorem embIn_conj {l : Level H} (c : Coeff l) {K : Type} [Field K] (j : c.F →+* K) (τ : E →+* ℂ) :
    EigenvectorLieDegree.embIn c j (conjEmb τ) = (EigenvectorLieDegree.embIn c j τ).comp (IsCMField.complexConj E).toRingEquiv.toRingHom :=
  RingHom.ext fun a => congrArg j (Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm)

theorem diff_all (hS : FlatDegreeSt) (hH : EigenvectorLieDegree.IsHostField H) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : IsKroneckerChar χ) (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) {Dw : Datum H} (hpq : 1 ≤ Dw.p + Dw.q)
    {l : Level H} (c : Coeff l) {K : Type} [Field K] [NumberField K] (j : c.F →+* K)
    (o : Obj Dw l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : Psi H) :
    Diff (((Dw.p : ℝ) - Dw.q) / 2 * (GlobalTheory.CM.logOm E χ).re) o.t (EigenvectorLieDegree.embIn c j τ.1) (EigenvectorLieDegree.embIn c j (conjEmb τ.1))
      (Dw.mult τ.1) (Dw.mult (conjEmb τ.1)) := by
  obtain ⟨l₂, hA, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ H 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ Dw l₂ hpq
  obtain ⟨c₀⟩ : Nonempty (Coeff l₂) := inferInstance
  obtain ⟨-, c₂, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ Dw l₂ Xo c₀ hpq
  obtain ⟨U, hU⟩ := GlobalTheory.FlatCore.Model.exists_laws Dw l₂ Xo c₂ hpq hA hg (hc c₂ le_rfl) h1
  have key : ∀ s, spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom = s →
      ∃ o' : Obj Dw l (baseKA l) s, o'.t = o.t := by
    rintro _ rfl
    exact ⟨o, rfl⟩
  obtain ⟨o', ho⟩ := key _ (spMap_comp_spMap _ _)
  obtain ⟨k', _, _, i, j₂, o₂, ⟨n⟩, hρ⟩ := exists_obj_level l₂ c₂ _ o' hA
  rw [ho] at n
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ₂, EigenvectorLieDegree.embIn c₂ j₂ τ₂ = i.comp (EigenvectorLieDegree.embIn c j τ.1) := by
    let g := algebraMap k' (AlgebraicClosure k')
    letI : Algebra c₂.F (AlgebraicClosure k') := (g.comp j₂).toAlgebra
    obtain ⟨τ₂, h⟩ := GlobalTheory.EmbOnto.embAt_surj c₂ (AlgebraicClosure k') (g.comp (i.comp (EigenvectorLieDegree.embIn c j τ.1)))
    exact ⟨τ₂, RingHom.ext fun a => g.injective (RingHom.congr_fun h a)⟩
  have hψ : τ₂ (H.rt : E) = H.rt0 := by
    have h2 := RingHom.congr_fun hτ₂ (H.rt : E)
    have h3 : (i.comp (EigenvectorLieDegree.embIn c j τ.1)) (H.rt : E) = j₂ (IntermediateField.inclusion c₂.le (baseKA l₂).ρ) := by
      rw [hρ]
      exact congrArg i (congrArg j (Subtype.ext τ.2))
    exact congrArg Subtype.val (j₂.injective (h2.trans h3))
  have hd := diff_laws hU (hS E H hH χ hχ Dw l₂ Xo c₂ _ U _ hU) j₂ o₂ ⟨τ₂, hψ⟩
  rw [(mult_psi Dw ⟨τ₂, hψ⟩).1, (mult_psi Dw ⟨τ₂, hψ⟩).2, embIn_conj] at hd
  rw [(mult_psi Dw τ).1, (mult_psi Dw τ).2, embIn_conj]
  refine Diff.down n ?_
  rw [← RingHom.comp_assoc, ← hτ₂]
  exact hd

end GlobalTheory.PointDiff

end
