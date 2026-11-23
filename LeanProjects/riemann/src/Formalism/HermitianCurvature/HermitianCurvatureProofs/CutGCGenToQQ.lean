import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerStructure

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

end hs

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def Intw (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (A' : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ, trR P Bs e (A.1 Φ) = MA.actA P A' (trR P Bs e Φ)

theorem rawR_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((Φ + Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ + rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_add, Pi.add_apply, hsv_add, inner_add_right, mul_add]

theorem rawR_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((c • Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      c • rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_smul, Pi.smul_apply, hsv_smul, inner_smul_right, smul_eq_mul]
  ring

theorem toSm_smul' {u : MA.Qp P.r P.TT → ℂ} (c : ℂ) (hu : u ∈ MA.smSub P.r P.TT) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  rw [toSm_of_mem P hu, toSm_of_mem P (Subalgebra.smul_mem _ hu c)]
  rfl

end intw

section clos

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem trR_add (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (Φ + Ψ) = trR P Bs e Φ + trR P Bs e Ψ := by
  funext ρ
  simp only [trR, Pi.add_apply]
  rw [rawR_add, toSm_add P (hsm Φ ρ) (hsm Ψ ρ)]

theorem trR_smul (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (c • Φ) = c • trR P Bs e Φ := by
  funext ρ
  simp only [trR, Pi.smul_apply]
  rw [rawR_smul, toSm_smul' c (hsm Φ ρ)]

theorem actA_smulM (c : ℂ) (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • x) f = c • MA.actA P x f := by
  funext π
  show ∑ π', ((c • x) π π').1 (f π') = c • ∑ π', (x π π').1 (f π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Fintype.sum_eq_single π (fun b hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl), Matrix.one_apply_eq]
  rfl

theorem actA_alg (c : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) c) f = c • f := by
  rw [Algebra.algebraMap_eq_smul_one, actA_smulM, actA_one]

variable (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_add {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A + B) (A' + B') := by
  intro Φ
  show trR P Bs e (A.1 Φ + B.1 Φ) = _
  rw [trR_add hsm, hA, hB, actA_add]

theorem intw_mul {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A * B) (A' * B') := by
  intro Φ
  show trR P Bs e (A.1 (B.1 Φ)) = _
  rw [hA, hB, actA_mul]

theorem intw_alg (c : ℂ) : Intw P Bs e (algebraMap ℂ _ c) (algebraMap ℂ (MA.A P (MA.DQ P)) c) := by
  intro Φ
  show trR P Bs e (c • Φ) = _
  rw [trR_smul hsm, actA_alg]

theorem intw_neg {A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') : Intw P Bs e (-A) (-A') := by
  have h := intw_mul hsm (intw_alg hsm (-1)) hA
  intro Φ
  have e1 : (-A) = algebraMap ℂ _ (-1) * A := by simp
  have e2 : (-A') = algebraMap ℂ (MA.A P (MA.DQ P)) (-1) * A' := by simp
  rw [e1, e2]
  exact h Φ

theorem intw_sub {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A - B) (A' - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact intw_add hsm hA (intw_neg hsm hB)

theorem intw_zero : Intw P Bs e 0 0 := by
  intro Φ
  show trR P Bs e 0 = MA.actA P 0 (trR P Bs e Φ)
  rw [actA_zero]
  have h := trR_smul hsm 0 Φ
  rw [zero_smul, zero_smul] at h
  exact h

theorem intw_sum {ι : Type} (s : Finset ι) {A : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {A' : ι → MA.A P (MA.DQ P)} (h : ∀ i ∈ s, Intw P Bs e (A i) (A' i)) :
    Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  first | exact UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum .. | (apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' h | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp

end clos

theorem generator_to_quadratic_form : GenToQQ := by
  intro hRS hGT Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec X
  obtain ⟨d, hL, hstar, hrel, hQQ⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X
  obtain ⟨e, he, hg⟩ := hGT Wp Wq P Bs hPl hk hsec X d hL hstar hrel hQQ
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => hRS Wp Wq P Bs hPl hk e he Φ ρ
  refine ⟨e, he, fun Φ Y a b => ?_⟩

  have hζ : Intw P Bs e d.L.ζ (MA.zA P (MA.DQ P)) := fun Φ => (hg Φ).1
  have hζi : Intw P Bs e d.L.ζi (MA.ziA P (MA.DQ P)) := fun Φ => (hg Φ).2.1
  have hζb : Intw P Bs e d.L.ζb (MA.zbA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.1
  have hζbi : Intw P Bs e d.L.ζbi (MA.zbiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.1
  have hGG : Intw P Bs e d.L.GG (MA.ggA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.1
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.1
  have hnab : Intw P Bs e d.L.nab (MA.nabA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.1
  have hnabs : Intw P Bs e d.L.nabs (MA.nabsA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.2.1
  have hκ : ∀ f, Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f) := fun f Φ => (hg Φ).2.2.2.2.2.2.2.2.1 f
  have hSS : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.1 l hl
  have hSSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l)) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.2 l hl

  have hx : Intw P Bs e (d.x Y) (MA.xA P (MA.DQ P) Y) := hκ _
  have hl0 : Intw P Bs e (d.L.l0 Y) (MA.l0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nab - algebraMap ℂ _ (Y + 1/2) * (d.L.ζb * d.L.GGi))
      (-MA.nabA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnab) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζb hGGi))
  have hm0 : Intw P Bs e (d.L.m0 Y) (MA.m0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nabs - algebraMap ℂ _ (Y - 1/2) * (d.L.ζ * d.L.GGi))
      (-MA.nabsA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnabs) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζ hGGi))
  have hS21 : Intw P Bs e (d.weightedSumBis Y) (MA.weightedSumBis P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hSS l hl) (hκ _)
  have hS12 : Intw P Bs e (d.S12 Y) (MA.S12 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hκ _) (hSSs l hl)
  have hS4 : Intw P Bs e (d.S4 Y) (MA.S4 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_sum hsm _ fun j hj =>
      intw_mul hsm (intw_mul hsm (hSSs l hl) (hSS j (Finset.mem_of_mem_erase hj))) (hκ _)

  have hent : ∀ a b : Fin 2, Intw P Bs e (d.QQ Y a b) (MA.QQr P (MA.DQ P) Y a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show Intw P Bs e (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
          d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) (MA.t11 P (MA.DQ P) Y)
      exact intw_add hsm (intw_add hsm (intw_add hsm (intw_add hsm (intw_mul hsm hGGi (hκ _))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hl0))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hm0) hGGi) hS21))
        (intw_mul hsm hS12 hl0)) (intw_mul hsm hGGi hS4)
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) (MA.t12 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hS12
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) (MA.t21 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hl0) hS21
    · show Intw P Bs e (d.L.GG * d.x Y) (MA.t22 P (MA.DQ P) Y)
      exact intw_mul hsm hGG hx
  have ht : X.t Y a b = (X.QQ Y a b).1 := rfl
  rw [ht, hQQ Y]
  exact hent a b Φ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
