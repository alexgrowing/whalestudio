import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactGinfCOfOntoUni
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMapStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawScalarFormsLawsOnClassDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerXCls

variable {D : D7}

abbrev finfF (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finfF D) = 1 := by
  show finHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfF D) = 1) :
    (x ⬝ m ⬝ y).map (finfF D) = (x ⬝ y).map (finfF D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfF D) = x.map (finfF D) ⬝ m.map (finfF D) ⬝ y.map (finfF D) := by
    rw [Matrix.map_mul (f := finfF D), Matrix.map_mul (f := finfF D)]
  have e2 : (x ⬝ y).map (finfF D) = x.map (finfF D) ⬝ y.map (finfF D) := Matrix.map_mul (f := finfF D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GinfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GinfC A) :
    o.emb (a, 1) ∈ GinfC S := by
  rw [mem_GinfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfF D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfF D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trc_apply {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsm : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact hadd hx hy
  | zero => simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsm (h x) c

theorem ontoUni_of_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (hab : a = b)
    (r : K → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : OntoUni (fun k τ => (r k τ).reindex (finCongr hab) (finCongr hab))) : OntoUni r := by
  subst hab
  simpa using hr

end GlobalTheory.SeeSaw.PerXCls

open GlobalTheory.SeeSaw.PerXCls in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.SeeSaw.perX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) →
    ClsPinD t → PerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro n h y v
  have hU : OntoUni (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) :=
    ontoUni_of_reindex ρ.hT (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) hρ.uniT
  obtain ⟨_, _, _, ν, hν1, hν2, hcls⟩ := integral_eq_classSum D c.θ c.T ρ.BT hc.inf hU
  obtain ⟨hN, hInt, hBr, hne, hblk⟩ := hρ.low n h
  have hemb : ∀ k : GinfC c.T, (c.oT n h).emb (k.1, 1) ∈ GinfC (c.X n) := fun k => orth_emb_mem_GinfC _ k.2
  let y0 : FrN D (ρ.N n) := ρ.fr n y
  have hdet : ∀ (k : GinfC c.T) τ, IsUnit ((ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ).det) := by
    intro k τ
    rw [Matrix.det_mul]
    have hu := (hρ.uni n h.le).uni ⟨_, hemb k⟩ τ
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hu)).mul (y0.2 τ)
  let yk : GinfC c.T → FrN D (ρ.N n) := fun k => ⟨fun τ => ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ, hdet k⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap D.what₂.Tau (ρ.N n) ρ.NT hN (fun _ => 1) (fun _ => 1) (ρ.lam n) ρ.sg hInt (ρ.low n h) hBr
    hne (GinfC c.T) ν (fun k => ρ.rT k.1) hρ.uniT y0 yk
    (fun k => ⟨_, fun τ => hblk k.1 k.2 τ, fun τ => rfl⟩) (ρ.J v 1) (hρ.J v).1 (fun k => ρ.J v k.1)
    (fun k z z' hz => (hρ.J v).2 k.1 k.2 z z' hz)
  refine ⟨a, fun s ψ hψ F => ?_⟩
  obtain ⟨⟨A, hA1⟩, B, hB⟩ := hA s
  obtain ⟨hvol, hstab, hsum⟩ := hcls c.volT B.U B.cl B.h hB.reps
  have rdtr := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA1.1 n h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hF : IsContAut c.T (F.1 v) := isContAut_multT (hCT F.2) v
  have key : ∀ β, ∫ h' in c.volT.𝓕, trc ((t s).eT n h β) (F.1 v) h' * (t s).rd n β ψ y ((c.oT n h).emb (h', 1)) ∂c.volT.μ =
      (volLev c.volT B.U : ℂ) * ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        (a * B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
    intro β
    obtain ⟨hr1, -, hr3, hr4⟩ := rdtr β
    rw [hsum]
    · congr 1
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      have hpt : ∀ k : GinfC c.T, trc ((t s).eT n h β) (F.1 v) (B.h a' * k.1) *
          (t s).rd n β ψ y ((c.oT n h).emb (B.h a' * k.1, 1)) =
          B.ell n h β a' F (ρ.J v k.1) * (fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1))) (yk k) := by
        intro k
        rw [hB.top n h F v β a' k.1 k.2]
        congr 1
        have hm : (c.oT n h).emb (B.h a' * k.1, 1) = (c.oT n h).emb (B.h a', 1) * (c.oT n h).emb (k.1, 1) := by
          rw [← map_mul]; simp
        rw [hm]
        refine hr3 y _ _ _ (hemb k) ?_
        intro τ
        rw [Equiv.apply_symm_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ha _ (hr4 _) _
    · refine Continuous.mul ?_ ((hr1 y).2.comp ((c.oT n h).continuous_emb.comp (continuous_id.prodMk continuous_const)))
      have : trc ((t s).eT n h β) (F.1 v) = fun x => ∑ g ∈ ((t s).eT n h β).support, (t s).eT n h β g * F.1 v (x * g) :=
        funext fun x => trc_apply _ _ x
      rw [this]
      exact continuous_finset_sum _ fun g _ => continuous_const.mul (hF.2.comp (continuous_mul_right g))
    · intro γ hγ g
      rw [trc_apply, trc_apply]
      congr 1
      · refine Finset.sum_congr rfl fun g' _ => ?_
        rw [mul_assoc, hF.1 γ hγ]
      · have hm : (c.oT n h).emb (γ * g, 1) = (c.oT n h).emb (γ, 1) * (c.oT n h).emb (g, 1) := by
          rw [← map_mul]; simp
        rw [hm, (hr1 y).1 _ ((c.oT n h).emb_mem_GQ hγ (GQ _).one_mem)]
    · intro κ hκ g
      exact hB.inv n h ψ hψ F v y β g κ hκ
  have htl := hB.tail n h ψ hψ F
  unfold Tup.perT
  rw [Finset.sum_congr rfl fun β _ => key β]
  calc _ = a * ((volLev c.volT B.U : ℂ) * ∑ β, ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a' _ => by ring
    _ = _ := by rw [htl]; ring
