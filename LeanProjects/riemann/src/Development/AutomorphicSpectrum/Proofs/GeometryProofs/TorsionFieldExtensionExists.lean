import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TheoremOfCubeSectionValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundlePullbackGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesIdentityPowerRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

alias torsVal_val := GlobalTheory.T.torsion_value_line_bundle_section
alias exists_lin := GlobalTheory.T.theorem_of_cube_section_value
alias exists_sec_of_gen := GlobalTheory.T.line_bundle_pullback_generator
alias exists_root_gen := GlobalTheory.T.finite_group_scheme_sum_extension
alias transl_algebra := GlobalTheory.T.values_identity_power_relation

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem exists_mulGen (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ w : LB.Gen (LB.LinComb D.t.PP.L (K := Fin 2) ![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] ![1, -((N : ℤ) ^ 2)]),
      w.IsGen := by
  obtain ⟨T, hT, -⟩ := (GlobalTheory.T.torsion_value_unique_base_change E H L D 1 th L (spMap (algebraMap (𝓞 L) L)) 1 N hN (one_pow N)).1
  obtain ⟨-, -, w, _, _, hw, -⟩ := hT
  exact ⟨w, hw⟩
end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem core (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (m : ℕ) (hm : 1 ≤ m)
    {L' : Type} [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (e : D.Ext D')
    (x : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G) (hx : x ^ m = 1)
    (W : FG D.t.PP.L D.t.G.left)
    (hW : ∀ (U : Type) [CommGroup U] (h : (D.t.G.left ⟶ D.t.G.left) → U),
      W.sum U h = h ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ m).left * (h (𝟙 D.t.G.left) ^ (m ^ 2))⁻¹)
    (e₀ : FG D.t.PP.L (Sp L'))
    (he₀ : ∀ (U : Type) [CommGroup U] (h : (Sp L' ⟶ D.t.G.left) → U), e₀.sum U h = h x.left)
    (hN : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp L') (z : Z) (J), Good D.t.PP.L z J →
      e₀.v r z J ^ (m ^ 2) * W.v (r ≫ x.left) z J *
        (W.v (r ≫ (1 : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left) z J)⁻¹ *
        ((rigFG D.t.PP).v (r ≫ spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) z J ^ (m ^ 2))⁻¹ = 1) :
    ∃ (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L'), d ≠ 0 ∧ ∀ (F : Type) [Field F] (f : L' →+* F)
      (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (b : Sp F ⟶ Sp (𝓞 L)) (xF yF : Over.mk b ⟶ D.t.G)
      (N : ℕ) (T T' : F), xF.left = spMap f ≫ x.left → yF.left = y.left ≫ e.φ → TorsVal D'.t.PP s y N T →
      TorsVal D.t.PP th (xF * yF ^ m) (N * m) T' → T ^ (m ^ 2) = f (d : L') ^ ((N * m) ^ 2) * T' := by
  classical
  obtain ⟨wI, hwI, hrig, -⟩ := e.lin
  have hPw := (isGen_iff wI).1 hwI
  have hL := D.t.PP.isLB
  have hL' := D'.t.PP.isLB
  have hY := D'.m.cart.1
  have habel : IsAbelianScheme D'.tK.G := ⟨inferInstance, D'.tK.semi.smooth, D'.princ.1, D'.tK.semi.geomConnected⟩
  have hp := (GlobalTheory.globalFns_holds _ D'.tK.G habel).2
  let Tb : Over (Sp (𝓞 L')) := Over.mk (D'.m.φ ≫ D'.t.G.hom)
  let a' : Tb ⟶ D'.t.G := Over.homMk D'.m.φ rfl
  let T₀ : Over (Sp (𝓞 L)) := Over.mk (Tb.hom ≫ spMap (algebraMap (𝓞 L) (𝓞 L')))
  let a : T₀ ⟶ D.t.G := pushPt e.cart.1.w a'
  let ρx : T₀ ⟶ Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) := Over.homMk D'.tK.G.hom (by
    show D'.tK.G.hom ≫ _ ≫ _ = (D'.m.φ ≫ D'.t.G.hom) ≫ _
    rw [hY.w, Category.assoc])
  let xY : T₀ ⟶ D.t.G := ρx ≫ x
  have hxY : xY ^ m = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨v, hvs, hv1⟩ := exists_lin D.t.cub xY a m hxY
  let ψ : T₀ ⟶ D.t.G := xY * a ^ m
  let u : FG D.t.PP.L D'.tK.G.left := (((v.mul (W.pull a.left)).mul (e₀.pull D'.tK.G.hom)).mul
    (W.pull (1 : T₀ ⟶ D.t.G).left).inv).mul (((rigFG D.t.PP).pull T₀.hom).pow (m ^ 2)).inv
  have hu : ∀ (U : Type) [CommGroup U] (h : (D'.tK.G.left ⟶ D.t.G.left) → U),
      u.sum U h = h ψ.left * (h (D'.m.φ ≫ e.φ) ^ (m ^ 2))⁻¹ := by
    intro U _ h
    simp only [u, FG.sum_mul, FG.sum_inv, FG.sum_pow, FG.sum_pull, hvs, hW, he₀, sum_rigFG, left_pow, Category.comp_id]
    rw [one_pow, ← one_left]
    have e₁ : h (D'.tK.G.hom ≫ x.left) = h xY.left := rfl
    have e₂ : h a.left = h (D'.m.φ ≫ e.φ) := rfl
    rw [e₁, ← e₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  have : CompactSpace D'.t.G.left := by
    have := D'.t.semi.quasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace D'.t.G.hom
  have : QuasiSeparatedSpace D'.t.G.left := by
    have := D'.t.semi.separated
    exact quasiSeparatedSpace_of_quasiSeparated D'.t.G.hom
  obtain ⟨s, t, ht, hs⟩ := exists_sec_of_gen (nonZeroDivisors (𝓞 L')) hY hPw hL hL' th ψ.left (m ^ 2) u hu
  refine ⟨s, t, nonZeroDivisors.ne_zero ht, ?_⟩
  intro F _ f y b xF yF N T T' hxF hyF hT hT'

  have hbc := spMap_comp' f (algebraMap (𝓞 L') L')
  obtain rfl : b = spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := by
    have h1 : xF.left ≫ D.t.G.hom = b := Over.w xF
    have h2 : x.left ≫ D.t.G.hom = _ := Over.w x
    rw [← h1, hxF, Category.assoc, h2, hbc, Category.assoc]
    rfl
  have lift₁ : ∀ q : Sp F ⟶ D'.t.G.left, q ≫ D'.t.G.hom = spMap (f.comp (algebraMap (𝓞 L') L')) →
      ∃ p : Sp F ⟶ D'.tK.G.left, p ≫ D'.m.φ = q ∧ p ≫ D'.tK.G.hom = spMap f := fun q hq =>
    ⟨hY.lift q (spMap f) (hq.trans hbc), hY.lift_fst _ _ _, hY.lift_snd _ _ _⟩
  let one' : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G := 1
  obtain ⟨p, hp1, hp2⟩ := lift₁ y.left (Over.w y)
  obtain ⟨p₀, hp₀1, hp₀2⟩ := lift₁ one'.left (Over.w one')
  obtain ⟨px, hpx1, hpx2⟩ := lift₁ (e.cart.1.lift xF.left (spMap (f.comp (algebraMap (𝓞 L') L'))) (Over.w xF))
    (e.cart.1.lift_snd _ _ _)
  have hpx3 : px ≫ D'.m.φ ≫ e.φ = xF.left := by
    rw [← Category.assoc, hpx1]; exact e.cart.1.lift_fst _ _ _
  let ρ : ∀ q : Sp F ⟶ D'.tK.G.left, q ≫ D'.tK.G.hom = spMap f →
      (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ T₀) :=
    fun q hq => Over.homMk q (by
      show q ≫ (D'.m.φ ≫ D'.t.G.hom) ≫ _ = _
      rw [hY.w, Category.assoc, ← Category.assoc q, hq, hbc, Category.assoc]
      rfl)
  have hρx : ∀ q hq, ρ q hq ≫ xY = xF := fun q hq => Over.OverMorphism.ext (by
    show q ≫ D'.tK.G.hom ≫ x.left = xF.left
    rw [← Category.assoc, hq, hxF])
  have hone : one'.left ≫ e.φ = (1 : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom e.cart (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))))))
  have hρa : ρ p hp2 ≫ a = yF := Over.OverMorphism.ext (by
    show p ≫ D'.m.φ ≫ e.φ = yF.left
    rw [← Category.assoc, hp1, hyF])
  have hρa₀ : ρ p₀ hp₀2 ≫ a = 1 := Over.OverMorphism.ext (by
    show p₀ ≫ D'.m.φ ≫ e.φ = _
    rw [← Category.assoc, hp₀1, hone])
  have hρax : ρ px hpx2 ≫ a = xF := Over.OverMorphism.ext hpx3
  have hxFm : xF ^ m = 1 := by
    rw [← hρx p hp2, ← MonObj.comp_pow, hxY, MonObj.comp_one]
  have hyN : y ^ N = 1 := hT.2.1
  have hN1 : 1 ≤ N := hT.1
  have hyFN : yF ^ N = 1 := by
    have h1 : pushPt e.cart.1.w y = yF := Over.OverMorphism.ext hyF.symm
    have h2 := map_pow (pushHom e.cart (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))))) y N
    have h3 := map_one (pushHom e.cart (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')))))
    rw [hyN, h3] at h2
    rw [← h1]
    exact h2.symm
  let z : Sp F := (⊥ : PrimeSpectrum F)
  choose J hJ using fun χ : Sp F ⟶ D.t.G.left => exists_chart hL (χ z)
  choose J' hJ' using fun χ : Sp F ⟶ D'.t.G.left => exists_chart hL' (χ z)
  have hJg : Good D.t.PP.L z J := hJ
  have hJg' : Good D'.t.PP.L z J' := hJ'
  obtain ⟨wk, hwk, E1⟩ := torsVal_val D.t.PP th (xF * yF ^ m) (N * m) T' hT' z J hJg
  obtain ⟨wn', hwn', E2⟩ := torsVal_val D'.t.PP s y N T hT z J' hJg'
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_up hPw hL hL' wn' hwn'
  obtain ⟨wm2, hwm2⟩ := exists_mulGen D th (m ^ 2) (Nat.one_le_pow _ _ hm)
  obtain ⟨wn, hwn⟩ := exists_mulGen D th N hN1

  let tF : FG D.t.PP.L D'.t.G.left := ⟨Fin 2, _, _, t₁, ht₁⟩
  have tFs : ∀ (U : Type) [CommGroup U] (h : (D'.t.G.left ⟶ D.t.G.left) → U), tF.sum U h =
      h (((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left ≫ e.φ) * (h (𝟙 D'.t.G.left ≫ e.φ) ^ (N ^ 2))⁻¹ := fun U _ h => by
    show ∏ k : Fin 2, h ((![((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left, 𝟙 D'.t.G.left] : Fin 2 → _) k ≫ e.φ) ^
      (![1, -((N : ℤ) ^ 2)] : Fin 2 → ℤ) k = _
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
    norm_cast
  have haN : D'.m.φ ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left ≫ e.φ = (a ^ N).left := by
    rw [← Category.assoc]
    have h1 : D'.m.φ ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left = (a' ^ N).left := left_pow a' N
    rw [h1]
    exact congrArg (fun q => q.left) (map_pow (pushHom e.cart Tb) a' N)
  have haa : D'.m.φ ≫ 𝟙 D'.t.G.left ≫ e.φ = a.left := by
    rw [Category.id_comp]; rfl
  have haa' : D'.m.φ ≫ e.φ = a.left := rfl
  have hψ : ψ ^ (N * m) = (a ^ N) ^ (m ^ 2) := by
    show (xY * a ^ m) ^ (N * m) = _
    rw [mul_pow, mul_comm N m, pow_mul xY, hxY, one_pow, _root_.one_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  let g₁ : FG D.t.PP.L D'.tK.G.left := ((((mulFG wk hwk).pull ψ.left).mul (u.pow ((N * m) ^ 2))).mul
    ((tF.pull D'.m.φ).pow ((m ^ 2) ^ 2)).inv).mul ((mulFG wm2 hwm2).pull (a ^ N).left).inv
  have g₁s : ∀ (U : Type) [CommGroup U] (h : (D'.tK.G.left ⟶ D.t.G.left) → U), g₁.sum U h = 1 := by
    intro U _ h
    simp only [g₁, FG.sum_mul, FG.sum_inv, FG.sum_pow, FG.sum_pull, sum_mulFG, tFs, hu, left_pow, Category.comp_id,
      haN, haa, haa', hψ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
    module
  let g₂ : FG D.t.PP.L D'.tK.G.left := (((mulFG wk hwk).pull a.left).mul ((W.pull a.left).pow (N ^ 2)).inv).mul
    ((mulFG wn hwn).pull (a ^ m).left).inv
  have g₂s : ∀ (U : Type) [CommGroup U] (h : (D'.tK.G.left ⟶ D.t.G.left) → U), g₂.sum U h = 1 := by
    intro U _ h
    have e₃ : (a ^ m) ^ N = a ^ (N * m) := by rw [← pow_mul, mul_comm]
    simp only [g₂, FG.sum_mul, FG.sum_inv, FG.sum_pow, FG.sum_pull, sum_mulFG, hW, left_pow, Category.comp_id, e₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
    module
  have R1' := g₁.v_const hL g₁s D'.tK.G.hom hp (hp2.trans hp₀2.symm) hJg
  have R2' := g₂.v_const hL g₂s D'.tK.G.hom hp (hpx2.trans hp₀2.symm) hJg
  simp only [g₁, FG.v_mul hJg, FG.v_inv, FG.v_pow hJg, FG.v_pull hJg] at R1'
  simp only [g₂, FG.v_mul hJg, FG.v_inv, FG.v_pow hJg, FG.v_pull hJg] at R2'

  let o := (1 : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left
  have pz : p ≫ ψ.left = (xF * yF ^ m).left := by
    have h1 : ρ p hp2 ≫ ψ = xF * yF ^ m := by
      show ρ p hp2 ≫ (xY * a ^ m) = _
      rw [MonObj.comp_mul, MonObj.comp_pow, hρx p hp2, hρa]
    exact congrArg (fun q => q.left) h1
  have p0z : p₀ ≫ ψ.left = xF.left := by
    have h1 : ρ p₀ hp₀2 ≫ ψ = xF := by
      show ρ p₀ hp₀2 ≫ (xY * a ^ m) = _
      rw [MonObj.comp_mul, MonObj.comp_pow, hρx p₀ hp₀2, hρa₀, one_pow, _root_.mul_one]
    exact congrArg (fun q => q.left) h1
  have paN : p ≫ (a ^ N).left = o := by
    have h1 : ρ p hp2 ≫ a ^ N = 1 := by rw [MonObj.comp_pow, hρa, hyFN]
    exact congrArg (fun q => q.left) h1
  have p0aN : p₀ ≫ (a ^ N).left = o := by
    have h1 : ρ p₀ hp₀2 ≫ a ^ N = 1 := by rw [MonObj.comp_pow, hρa₀, one_pow]
    exact congrArg (fun q => q.left) h1
  have pxam : px ≫ (a ^ m).left = o := by
    have h1 : ρ px hpx2 ≫ a ^ m = 1 := by rw [MonObj.comp_pow, hρax, hxFm]
    exact congrArg (fun q => q.left) h1
  have p0am : p₀ ≫ (a ^ m).left = o := by
    have h1 : ρ p₀ hp₀2 ≫ a ^ m = 1 := by rw [MonObj.comp_pow, hρa₀, one_pow]
    exact congrArg (fun q => q.left) h1
  have pxa : px ≫ a.left = xF.left := hpx3
  have p0a : p₀ ≫ a.left = o := congrArg (fun q => q.left) hρa₀
  have p01 : p₀ ≫ (1 : T₀ ⟶ D.t.G).left = o := by
    have h1 : ρ p₀ hp₀2 ≫ (1 : T₀ ⟶ D.t.G) = 1 := MonObj.comp_one _
    exact congrArg (fun q => q.left) h1
  have p0T : p₀ ≫ T₀.hom = spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := Over.w (ρ p₀ hp₀2)
  rw [pz, p0z, paN, p0aN, hp1, hp₀1] at R1'
  rw [pxa, p0a, pxam, p0am] at R2'
  have R1 := mul_right_cancel R1'
  have hv0 : v.v p₀ z J = 1 := hv1 _ (ρ p₀ hp₀2) z J hJg hρa₀
  have hu0 : u.v p₀ z J = e₀.v (spMap f) z J *
      ((rigFG D.t.PP).v (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) z J ^ (m ^ 2))⁻¹ := by
    simp only [u, FG.v_mul hJg, FG.v_inv, FG.v_pow hJg, FG.v_pull hJg]
    rw [hv0, p0a, p01, p0T, hp₀2, _root_.one_mul, mul_right_comm (W.v o z J), _root_.mul_inv_cancel, _root_.one_mul]
  have HN := hN (Sp F) (spMap f) z J hJg
  have o1 : spMap f ≫ (1 : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left = o := by
    show _ = (1 : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left
    rw [one_left, one_left]
    simp only [Over.mk_hom, hbc, Category.assoc]
  rw [← hxF, o1, ← Category.assoc, ← hbc] at HN

  have R2 : (mulFG wk hwk).v xF.left z J * W.v o z J ^ (N ^ 2) = (mulFG wk hwk).v o z J * W.v xF.left z J ^ (N ^ 2) := by
    have h1 := mul_right_cancel R2'
    apply Additive.ofMul.injective
    have h2 := congrArg Additive.ofMul h1
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at h2 ⊢
    linear_combination (norm := abel) h2
  have upv : ∀ r : Sp F ⟶ D'.t.G.left, val t₁ r z J =
      gw wI (r ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left) z (J ((r ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left) ≫ e.φ))
        (J' (r ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left)) *
      (gw wI r z (J (r ≫ e.φ)) (J' r) ^ (N ^ 2))⁻¹ * val wn' r z J' := by
    intro r
    have h1 := hv₁ (Sp F) r z _ _ (hJg.mem _ r) (hJg'.mem _ r)
    refine h1.trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Category.comp_id, Category.assoc]
    norm_cast
  have hyl : y.left ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left = one'.left := by rw [left_pow, hyN]
  have h1l : one'.left ≫ ((𝟙 D'.t.G : D'.t.G ⟶ D'.t.G) ^ N).left = one'.left := by
    rw [left_pow, show one' ^ N = one' from one_pow N]
  have hA := upv y.left
  have hB := upv one'.left
  rw [hyl] at hA
  rw [h1l] at hB
  have hP := (maps_iff wI _ (fun _ => eSec D.t.G) _ D'.t.PP.rig D.t.PP.rig e.cm.e _
    (rigPull_le e.cm.F e.cm.e e.cm.e_comm D.t.PP.L) (fun _ => rfl)).1 hrig
  have q₁ : spMap (f.comp (algebraMap (𝓞 L') L')) ≫ eSec D'.t.G = one'.left :=
    (one_left (G := D'.t.G) (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))))).symm
  have q₂ : (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ eSec D.t.G = one'.left ≫ e.φ :=
    (hone.trans (one_left (G := D.t.G) (Over.mk (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L')))))).symm
  have hR := hP (Sp F) (spMap (f.comp (algebraMap (𝓞 L') L'))) z
    (fun _ => J ((spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ eSec D.t.G))
    (fun _ => J' (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ eSec D'.t.G))
    (fun _ => by
      have h1 := hJg ((spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ≫ eSec D.t.G)
      rw [q₂, ← q₁] at h1
      rw [q₂, ← q₁]
      exact h1)
    (fun _ => hJg' _)
  have hS := hs (Sp F) p z J J' hJg hJg'
  have hc : p ≫ D'.m.φ ≫ D'.t.G.hom = spMap (f.comp (algebraMap (𝓞 L') L')) := by
    rw [← Category.assoc, hp1]; exact Over.w y
  rw [hc, gc_spMap, hp1, pz] at hS
  rw [e.base] at hR
  let bo : ((Sp F).presheaf.stalk z)ˣ := gw wI (Y := Sp F) one'.left z (J (one'.left ≫ e.φ)) (J' one'.left)
  let bz : ((Sp F).presheaf.stalk z)ˣ := gw wI (Y := Sp F) y.left z (J (y.left ≫ e.φ)) (J' y.left)
  have hRv : (rigFG D.t.PP).v (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) z J =
      bo * val (Z := Sp F) D'.t.PP.rig (spMap (f.comp (algebraMap (𝓞 L') L'))) z J' := by
    refine hR.trans (congrArg₂ (· * ·) ?_ rfl)
    rw [Fintype.prod_unique, zpow_one]
    show gw wI _ z (J _) (J' _) = _
    rw [q₁, q₂]
  have key := transl_algebra m N (toStk z T) (toStk z T') (sval (Z := Sp F) th (xF * yF ^ m).left z J)
    (sval (Z := Sp F) s y.left z J') (toStk z (f (t : L')))
    ((mulFG wk hwk).v o z J) ((mulFG wk hwk).v (xF * yF ^ m).left z J) ((mulFG wk hwk).v xF.left z J) (W.v o z J)
    (W.v xF.left z J) (val t₁ y.left z J) (val t₁ one'.left z J) (u.v p z J) (u.v p₀ z J) (e₀.v (spMap f) z J)
    ((rigFG D.t.PP).v (spMap (f.comp (algebraMap (𝓞 L') L')) ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) z J)
    (val (Z := Sp F) D'.t.PP.rig (spMap (f.comp (algebraMap (𝓞 L') L'))) z J')
    (val (Z := Sp F) wn' one'.left z J') (val (Z := Sp F) wn' y.left z J') bo bz
    (by have h := E1; simp only [pow_one] at h; exact h) E2 hA hB hRv hS R1 R2 hu0 HN
  apply (toStk z).injective
  rw [map_pow, map_mul, map_pow]
  exact key

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem transl_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (m : ℕ) (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G), 1 ≤ m → x ^ m = 1 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (_ : Algebra L K') (_ : IsScalarTower L K K'), ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower L K' L'] (D' : PPData H L') (e : D.Ext D'), ∃ (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L'), d ≠ 0 ∧ ∀ (F : Type) [Field F] (f : L' →+* F) (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (b : Sp F ⟶ Sp (𝓞 L)) (xF yF : Over.mk b ⟶ D.t.G) (N : ℕ) (T T' : F), xF.left = spMap ((f.comp (algebraMap K' L')).comp (algebraMap K K')) ≫ x.left → yF.left = y.left ≫ e.φ → TorsVal D'.t.PP s y N T → TorsVal D.t.PP th (xF * yF ^ m) (N * m) T' → ∃ r : ℕ, 1 ≤ r ∧ (T ^ (m ^ 2)) ^ r = (f (d : L') ^ ((N * m) ^ 2) * T') ^ r := by
  intro E _ _ _ H L _ _ D th m K _ _ _ x hm hx
  have hL := D.t.PP.isLB
  obtain ⟨w, hw⟩ := exists_mulGen D th m hm
  have hW : ∀ (U : Type) [CommGroup U] (h : (D.t.G.left ⟶ D.t.G.left) → U), (mulFG w hw).sum U h =
      h ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ m).left * (h (𝟙 D.t.G.left) ^ (m ^ 2))⁻¹ := sum_mulFG w hw
  let A : FG D.t.PP.L (Sp K) := (((mulFG w hw).pull x.left).mul
    ((mulFG w hw).pull (1 : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G).left).inv).mul
    (((rigFG D.t.PP).pull (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)))).pow (m ^ 2)).inv
  have hA : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ D.t.G.left) → U), A.sum U h = (h x.left ^ (m ^ 2))⁻¹ := by
    intro U _ h
    simp only [A, FG.sum_mul, FG.sum_inv, FG.sum_pow, FG.sum_pull, hW, sum_rigFG, left_pow, Category.comp_id, hx, one_pow]
    rw [show spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) ≫ eSec D.t.G =
      (1 : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G).left from (one_left (G := D.t.G) (Over.mk _)).symm]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  obtain ⟨K', _, _, _, e₁, he₁, hr⟩ := exists_root_gen hL (m ^ 2) (Nat.one_le_pow _ _ hm) x.left A hA
  letI : Algebra L K' := ((algebraMap K K').comp (algebraMap L K)).toAlgebra
  haveI : IsScalarTower L K K' := .of_algebraMap_eq' rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro L' _ _ _ _ _ D' eD
  have hring : (algebraMap (𝓞 L') L').comp (algebraMap (𝓞 L) (𝓞 L')) =
      (algebraMap K' L').comp ((algebraMap K K').comp ((algebraMap L K).comp (algebraMap (𝓞 L) L))) := by
    ext a
    show algebraMap (𝓞 L') L' (algebraMap (𝓞 L) (𝓞 L') a) = algebraMap K' L' (algebraMap L K' (algebraMap (𝓞 L) L a))
    rw [← IsScalarTower.algebraMap_apply L K' L']
    rfl
  have hbase : spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) =
      (spMap (algebraMap K' L') ≫ spMap (algebraMap K K')) ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) := by
    rw [← spMap_comp', hring, spMap_comp', spMap_comp', Category.assoc]
  let ρ : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶
      Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) :=
    Over.homMk (spMap (algebraMap K' L') ≫ spMap (algebraMap K K')) hbase.symm
  have hxL : (ρ ≫ x) ^ m = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have he₀ : ∀ (U : Type) [CommGroup U] (h : (Sp L' ⟶ D.t.G.left) → U), (e₁.pull (spMap (algebraMap K' L'))).sum U h =
      h (ρ ≫ x).left := by
    intro U _ h
    rw [FG.sum_pull, he₁, ← Category.assoc]
    rfl
  have hN : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp L') (z : Z) (J), Good D.t.PP.L z J →
      (e₁.pull (spMap (algebraMap K' L'))).v r z J ^ (m ^ 2) * (mulFG w hw).v (r ≫ (ρ ≫ x).left) z J *
        ((mulFG w hw).v (r ≫ (1 : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left) z J)⁻¹ *
        ((rigFG D.t.PP).v (r ≫ spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) z J ^ (m ^ 2))⁻¹ = 1 := by
    intro Z r z J hJ
    have h1 := hr Z (r ≫ spMap (algebraMap K' L')) z J hJ
    simp only [A, FG.v_mul hJ, FG.v_inv, FG.v_pow hJ, FG.v_pull hJ] at h1
    rw [FG.v_pull hJ]
    have a₁ : (r ≫ spMap (algebraMap K' L') ≫ spMap (algebraMap K K')) ≫ x.left = r ≫ (ρ ≫ x).left := by
      rw [Category.assoc]; rfl
    have a₂ : (r ≫ spMap (algebraMap K' L')) ≫ spMap (algebraMap K K') =
        r ≫ spMap (algebraMap K' L') ≫ spMap (algebraMap K K') := Category.assoc _ _ _
    have a₃ : (r ≫ spMap (algebraMap K' L') ≫ spMap (algebraMap K K')) ≫
        (1 : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G).left =
        r ≫ (1 : Over.mk (spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L'))) ⟶ D.t.G).left := by
      have h2 : ρ ≫ (1 : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G) = 1 := MonObj.comp_one _
      rw [Category.assoc]
      exact congrArg (fun q => r ≫ Over.Hom.left q) h2
    have a₄ : (r ≫ spMap (algebraMap K' L') ≫ spMap (algebraMap K K')) ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) =
        r ≫ spMap (algebraMap (𝓞 L') L') ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := by
      rw [hbase, Category.assoc]
    rw [a₂, a₁, a₃, a₄] at h1
    rw [_root_.mul_assoc (_ ^ _ ), _root_.mul_assoc (_ ^ _)] at *
    exact h1
  obtain ⟨s, d, hd, Hs⟩ := core D th m hm D' eD (ρ ≫ x) hxL (mulFG w hw) hW (e₁.pull (spMap (algebraMap K' L'))) he₀ hN
  refine ⟨s, d, hd, fun F _ f y b xF yF N T T' hxF hyF hT hT' => ⟨1, le_rfl, ?_⟩⟩
  rw [pow_one, pow_one]
  refine Hs F f y b xF yF N T T' ?_ hyF hT hT'
  rw [hxF, spMap_comp', spMap_comp', Category.assoc]
  rfl

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
