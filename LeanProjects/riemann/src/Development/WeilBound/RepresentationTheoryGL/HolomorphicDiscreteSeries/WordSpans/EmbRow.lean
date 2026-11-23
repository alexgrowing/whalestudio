import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem irr : Irr := by
  intro m ε K _ _ σ hU hI u w hu hw
  by_contra hcon
  push_neg at hcon
  have hJ : PI.UpqRep.Jm ε * PI.UpqRep.Jm ε = 1 := by
    unfold PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g ∈ UJset ε, ∃ h : UJ ε, um h = g := by
    intro g hg
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have h2 : PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε * g = 1 := by
      rw [Matrix.mul_assoc (PI.UpqRep.Jm ε * gᴴ), Matrix.mul_assoc (PI.UpqRep.Jm ε),
        ← Matrix.mul_assoc gᴴ, hg', hJ]
    have h1 : g * (PI.UpqRep.Jm ε * gᴴ * PI.UpqRep.Jm ε) = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, g * h ∈ UJset ε := by
    intro g hg h hh
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    have hh' : hᴴ * PI.UpqRep.Jm ε * h = PI.UpqRep.Jm ε := hh
    show (g * h)ᴴ * PI.UpqRep.Jm ε * (g * h) = PI.UpqRep.Jm ε
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * PI.UpqRep.Jm ε * (g * h) = hᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hg', hh']
  have hone : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * PI.UpqRep.Jm ε * 1 = PI.UpqRep.Jm ε
    simp
  let Sp : Submodule ℂ K := Submodule.span ℂ {x | ∃ g ∈ UJset ε, x = σ g u}
  have hSpinv : ∀ g ∈ UJset ε, ∀ x ∈ Sp, σ g x ∈ Sp := by
    intro g hg x hx
    refine Submodule.span_induction (p := fun x _ => σ g x ∈ Sp) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨h, hh, rfl⟩
      apply Submodule.subset_span
      refine ⟨g * h, hmul g hg h hh, ?_⟩
      rw [hU.1.2 g hg h hh]
      rfl
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact Sp.add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Sp.smul_mem c ha
  have hMinv : ∀ g ∈ UJset ε, ∀ v ∈ Sp.topologicalClosure, σ g v ∈ Sp.topologicalClosure := by
    intro g hg v hv
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv ⊢
    exact map_mem_closure (σ g).continuous hv (fun x hx => hSpinv g hg x hx)
  have huM : u ∈ Sp.topologicalClosure := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, hone, ?_⟩
    rw [hU.1.1]
    rfl
  have hker : Sp.topologicalClosure ≤ LinearMap.ker (innerSL ℂ w : K →ₗ[ℂ] ℂ) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro x ⟨g, hg, rfl⟩
      obtain ⟨h, rfl⟩ := hlift g hg
      show innerSL ℂ w (σ (um h) u) = 0
      rw [innerSL_apply_apply]
      exact hcon h
    · exact ContinuousLinearMap.isClosed_ker _
  rcases hI _ (Submodule.isClosed_topologicalClosure _) hMinv with h0 | htop
  · rw [h0] at huM
    exact hu ((Submodule.mem_bot ℂ).mp huM)
  · have hwM : w ∈ Sp.topologicalClosure := by
      rw [htop]
      exact Submodule.mem_top
    have hw0 := hker hwM
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hw0
    exact hw hw0

theorem emb_row {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (d : Fin (n + 1)) :
    emb e a (zi e) d = if d = zi e then 1 else 0 := by
  unfold emb zi
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases h : e.symm d with i | u
  · have hne : d ≠ e (Sum.inr ()) := by
      intro hd
      rw [hd, Equiv.symm_apply_apply] at h
      cases h
    simp [hne]
  · cases u
    have heq : d = e (Sum.inr ()) := by rw [← h, Equiv.apply_symm_apply]
    simp [heq]

theorem emb_ll {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    emb e a (e (Sum.inl i)) (e (Sum.inl j)) = a i j := by
  simp [emb]

theorem emb_rl {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (a : Matrix (Fin n) (Fin n) ℂ) (u : Unit) (j : Fin n) :
    emb e a (e (Sum.inr u)) (e (Sum.inl j)) = 0 := by
  simp [emb]

theorem phiEq : PhiEq := by
  intro n ε ε' e H H' _ _ _ _ π σ S E P hF hS hU hP η hη
  have hJJ : Jm ε' * Jm ε' = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hlift : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' → ∃ h : UJ ε', um h = g := by
    intro g hg
    have h2 : Jm ε' * gᴴ * Jm ε' * g = 1 := by
      rw [Matrix.mul_assoc (Jm ε' * gᴴ), Matrix.mul_assoc (Jm ε'), ← Matrix.mul_assoc gᴴ, hg, hJJ]
    have h1 : g * (Jm ε' * gᴴ * Jm ε') = 1 := mul_eq_one_comm.mp h2
    exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩
  have hembJ : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * Jm ε' * g = Jm ε' →
      (emb e g)ᴴ * Jm ε * emb e g = Jm ε := by
    intro g hg
    rw [jm_emb hF, emb_ct, ← emb_mul, ← emb_mul, hg]
  have hsm : ∀ x ∈ S, P x ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ := by
    intro x hx
    show PI.PhMeasCore.SmoothOnH _ _
    intro g₀ hg₀
    have hx' : PI.PhMeasCore.SmoothOnH (Jm ε) (fun g => π g x) := (hS.mem x).mp hx
    obtain ⟨U, F, hUo, hg₀U, hFc, hFeq⟩ := hx' (emb e g₀) (hembJ g₀ hg₀)
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
    letI : NormedAddCommGroup (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Matrix.normedSpace
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      { toFun := fun g => emb e g - emb e 0
        map_add' := by
          intro a b
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp
        map_smul' := by
          intro c a
          ext i j
          simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
            RingHom.id_apply]
          rcases e.symm i with i' | i' <;> rcases e.symm j with j' | j' <;> simp }
    have hembd : ContDiff ℝ (⊤ : ℕ∞) (emb e) := by
      have hfun : emb e = fun g => L g + emb e 0 := by
        funext g
        show emb e g = emb e g - emb e 0 + emb e 0
        abel
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap L).contDiff.add contDiff_const
    refine ⟨emb e ⁻¹' U, fun g => P (F (emb e g)), hUo.preimage hembd.continuous, hg₀U, ?_, ?_⟩
    · exact (P.restrictScalars ℝ).contDiff.comp_contDiffOn (hFc.comp hembd.contDiffOn (fun g hg => hg))
    · intro g hgU hgH
      have hgH' : gᴴ * Jm ε' * g = Jm ε' := hgH
      have h1 := hFeq (emb e g) hgU (hembJ g hgH')
      obtain ⟨h, rfl⟩ := hlift g hgH'
      show σ (um h) (P x) = P (F (emb e (um h)))
      rw [← h1, ← hP.2 h x]
  refine ⟨fun l => ?_, fun h => ?_⟩
  · show P (ap (E (e (Sum.inl l)) (zi e)) η) ∈ _
    unfold ap
    rw [dif_pos hη]
    exact hsm _ (Subtype.coe_prop _)
  · have hgU : emb e (um h) ∈ UJset ε := (embU hF h).2
    have hgiU : emb e (um h⁻¹) ∈ UJset ε := (embU hF h⁻¹).2
    have hu1 : um h⁻¹ * um h = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hu2 : um h * um h⁻¹ = 1 := by simp [PositivityTheory.UnitaryDecomposition.um]
    have hgg : emb e (um h⁻¹) * emb e (um h) = 1 := by rw [← emb_mul, hu1, emb_one]
    have hgg' : emb e (um h) * emb e (um h⁻¹) = 1 := by rw [← emb_mul, hu2, emb_one]
    have hinv : (emb e (um h⁻¹))⁻¹ = emb e (um h) := Matrix.inv_eq_right_inv hgg
    have hπη : π (emb e (um h)) η ∈ S := hS.stab _ hgU η hη
    have hcomp1 : ∀ y, π (emb e (um h⁻¹)) (π (emb e (um h)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgiU _ hgU, hgg, hU.1.1]
      rfl
    have hcomp2 : ∀ y, π (emb e (um h)) (π (emb e (um h⁻¹)) y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hgU _ hgiU, hgg', hU.1.1]
      rfl
    funext c0
    show P (ap (E (e (Sum.inl c0)) (zi e)) (π (emb e (um h)) η)) =
      ∑ d, (um h)⁻¹ d c0 • σ (um h) (P (ap (E (e (Sum.inl d)) (zi e)) η))
    simp only [ap, dif_pos hη, dif_pos hπη]
    have hc := hS.conj _ hgiU (e (Sum.inl c0)) (zi e) ⟨π (emb e (um h)) η, hπη⟩ ⟨η, hη⟩ (hcomp1 η).symm
    rw [hinv] at hc
    simp only [emb_row, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ite_true] at hc
    have hc2 := congrArg (fun y => P (π (emb e (um h)) y)) hc
    simp only [hcomp2, map_sum, map_smul] at hc2
    rw [hc2, ← e.sum_comp, Fintype.sum_sum_type]
    simp only [emb_rl, zero_smul, Finset.sum_const_zero, add_zero, emb_ll, um_inv]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hP.2 h]

end PositivityTheory.RgHe.SM
