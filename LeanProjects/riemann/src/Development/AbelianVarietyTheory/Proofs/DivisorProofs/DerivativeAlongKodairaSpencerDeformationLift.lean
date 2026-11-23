import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumTrivSqZeroExtEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

open GlobalTheory.Frames

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

theorem der_fun_hor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hQ : KSIso (psiSet H) Q) (hz : z ≫ toFlag M = X.ptY Q)
    {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)} (hv : IsTanFrame (psiSet H) Q v)
    {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} (hw : IsDef Q w) {Mx : HIx Dw (psiSet H) → K}
    (hM : GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x Mx) {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w), ∃ C : VIx Dw → K, ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O),
      (evalPt zw O hzw g).snd = ∑ k, Mx k * (evalPt (zv (.inl k)) O (hzv _) g).snd +
        ∑ k, C k * (evalPt (zv (.inr k)) O (hzv _) g).snd := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hQ hz v hv zv hl w hw Mx hM zw hlw
  obtain ⟨W, zM, hzM⟩ := hQ.exists_universal
  have hWQ : FrMap (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)) W Q :=
    GlobalTheory.FlagTan.frMap_comp (hzM 0).1 (hzM 0).2.1 fun a => by simp
  obtain ⟨ZW, hZW⟩ := FunDer.der_dir M hz ho hWQ
  choose zz hzz using fun k : GlobalTheory.FlagTan.FIx Dw => (GlobalTheory.FlagTan.existsUnique_isVert Q (Pi.single k (1 : K))).exists
  choose q hq hqO using fun k => exists_tanLift M (hzz k).isDef hz ho
  have key : ∀ (w' : FrPt Xo c (DualNumber K)) (M' : HIx Dw (psiSet H) → K), IsDef Q w' →
      GlobalTheory.FlagTan.IsKS (psiSet H) Q w'.x M' → ∃ C : VIx Dw → K, ∀ (p : Sp (DualNumber K) ⟶ M.X),
        p ≫ toFlag M = X.ptY w' → ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O)
        (hzv : ∀ k : VIx Dw, ⊤ ≤ zv (.inr k) ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
          (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * M' k +
            ∑ k, C k * (evalPt (zv (.inr k)) O (hzv k) g).snd := by
    intro w' M' hw' hM'
    obtain ⟨N, hN⟩ := (hzM M').2.1.exists_isShift hw'
      (hQ.injective hw'.isTanX (hzM M').2.1.isTanX hM' (hzM M').2.2)
    obtain ⟨p₀, hp₀, hp₀O⟩ := exists_tanLift M (hzM M').2.1 hz ho
    refine ⟨fun k => N k.toF, fun p hp O g hpO hzv => ?_⟩
    have hzO : ⊤ ≤ z ⁻¹ᵁ O := by
      rw [← FunDer.red_eq M hz ho hw' hp]
      exact FunDer.top_le_comp _ _ _ hpO
    obtain ⟨hZ, a0⟩ := hZW M' _ p₀ (hzM M').1 hp₀ O g (hp₀O O hzO)
    refine ⟨hZ, ?_⟩
    rw [FunDer.der_shift M hz ho (hzM M').2.1 hN hzz hp₀ hp hq O g (hp₀O O hzO) hpO (fun k => hqO k O hzO), a0,
      GlobalTheory.FlagTan.sum_FIx]
    congr 1
    have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range GlobalTheory.FlagTan.VIx.toF),
        N k * (evalPt (q k) O (hqO k O hzO) g).snd = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hN' : ∀ σ i j, i < j → (Pi.single k (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ, i, j⟩) = 0 :=
          fun σ i j hij => by
            refine Pi.single_eq_of_ne ?_ _
            rintro rfl
            exact (Finset.mem_filter.1 hk).2 ⟨⟨σ, (i, j), hij⟩, rfl⟩
        rw [FunDer.der_vert_eq_zero M hz ho (hzz k) hN' (hq k) O g _, mul_zero]
    rw [hz0, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : zz k.toF = v (.inr k) :=
      (GlobalTheory.FlagTan.existsUnique_isVert Q _).unique (hzz k.toF) (hv.2 k)
    have e2 : q k.toF = zv (.inr k) := FunDer.lift_eq M (by rw [hq, hl, e1]) (hqO _ _ ho)
    rw [FunDer.evalPt_eq_of_eq e2 O _ (hzv k) g]
  obtain ⟨C, hC⟩ := key w Mx hw hM
  choose C' hC' using fun k => key _ _ (hv.1 k).1 (hv.1 k).2
  refine ⟨fun j => C j - ∑ k, Mx k * C' k j, fun O g hzw hzvO => ?_⟩
  obtain ⟨hZ, a⟩ := hC zw hlw O g hzw (fun k => hzvO _)
  have b : ∀ k, (evalPt (zv (.inl k)) O (hzvO _) g).snd =
      (evalPt ZW O hZ g).snd k + ∑ j, C' k j * (evalPt (zv (.inr j)) O (hzvO _) g).snd := fun k => by
    obtain ⟨hZ', b⟩ := hC' k (zv (.inl k)) (hl _) O g (hzvO _) (fun j => hzvO _)
    rw [b]
    simp [Pi.single_apply]
  rw [a, Finset.sum_congr rfl fun k _ => congrArg (Mx k * ·) (b k)]
  simp only [mul_add, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (VIx Dw)))]
  simp only [mul_comm _ (Mx _)]
  ring

end GlobalTheory.CompHS
